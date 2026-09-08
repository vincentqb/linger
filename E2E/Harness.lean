module

public import Linger.Posix
public import Linger.Core.Status
public import Linger.Core.Render

public section

/-! # E2E.Harness — the shared harness for the pty suites, in Lean

WHY THIS IS LEAN AND NOT PYTHON. These suites drive the real `linger` binary
through real ptys, so they are `IO` and can never be theorems — the pure core is
what `Theorems/` covers, with `Tests/` pinning its behaviour at elaboration time.
What they *can* be is Lean programs, and `LingerTest.lean` was already the
precedent. The reason to move them is not proof strength, it is that a test in the
implementation's own language cannot drift from it: `field`/`status` below read
`Linger.Core.Status.name` rather than a hardcoded `"wants-you"`, so renaming a
status is a compile error instead of a silently-passing assertion.

It needed **no new syscall**. `Linger.Posix` already exposed every primitive the
Python needed — `spawnPty` (forkpty with the winsize set before exec, which the
`pty.fork()`-then-`ioctl` idiom got wrong), `winsizeSet`, `kill`, `waitpidNohang`,
`alive`, `poll`/`read`/`write`, and `getcwdOf` for the daemon-identification the
old `procs.py` did with `/proc`-or-`lsof`. So `SHIM_CAP` does not move: the C
trust boundary is unchanged by this port, which is the condition that made it
worth doing at all.

OUTPUT CONTRACT — load-bearing, do not reformat. Every check prints `PASS <name>`
or `FAIL <name>`, and each suite ends with `FAILURES: <n>`. `tests/e2e.sh` reads
both: the last line for the verdict, and the count of `PASS `/`FAIL ` lines
against a per-suite floor, so a suite that stops checking fails the gate. -/

namespace E2E.Harness

open Linger.Posix

/-- The detach key, ctrl-\\ — the one byte every suite sends to leave. -/
def detachKey : ByteArray := ByteArray.mk #[0x1C]

/-- One check. Returns 1 on failure so callers can sum. -/
def expect (cond : Bool) (name : String) : IO Nat := do
  IO.println s!"{if cond then "PASS" else "FAIL"} {name}"
  return if cond then 0 else 1

/-- Substring test — `String.splitOn` is what the repo already uses for this. -/
def has (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length ≥ 2

/-- Does `hay` contain `needle` as a contiguous byte run?

The honest test for "the client wrote *this emitter's* output": a pty stream is
bytes, not text, and comparing against `Linger.Core.Render.leaveAnsi` itself is
what stops a suite hardcoding a copy of what the implementation emits — the copy
is what goes stale when the emitter changes. -/
def hasBytes (hay : ByteArray) (needle : List UInt8) : Bool :=
  let h := hay.toList
  let n := needle.length
  (List.range (h.length + 1 - n)).any fun i => (h.drop i).take n == needle

/-- Does `hay` *begin* with `needle`? `leaveAnsi` leads with ST for a reason (a
program that died mid-OSC would otherwise eat the rest of the hand-back), so
"contains" is not enough for that one. -/
def startsWithBytes (hay : ByteArray) (needle : List UInt8) : Bool :=
  hay.toList.take needle.length == needle

/-- A `String` needle against a pty's bytes, without spelling the needle twice.
The byte-level form of `has`, for streams that also carry escape sequences. -/
def hasText (hay : ByteArray) (needle : String) : Bool :=
  hasBytes hay needle.toUTF8.toList

/-- One suite's world: where the binary is, and which `LINGER_DIR` it owns.

Per-suite and pid-suffixed, so two suites — or a suite and the developer's own
sessions — can never see each other's sockets or checkpoints. -/
structure Env where
  bin : String
  dir : String

/-- Resolve the binary next to the build and make a private state dir. -/
def Env.make (slug : String) : IO Env := do
  let cwd ← IO.currentDir
  let bin := (cwd / ".lake" / "build" / "bin" / "linger").toString
  let pid ← getpid
  let envDir ← IO.getEnv "LINGER_TEST_DIR"
  let dir : String := match envDir with
    | some d => d
    | none => s!"/tmp/linger-{slug}-{pid}"
  IO.FS.createDirAll (System.FilePath.mk dir)
  return { bin, dir }

/-- `extraEnv` for `spawnPty`: the state dir plus a predictable shell. -/
def Env.ptyEnv (e : Env) : Array String :=
  #[s!"LINGER_DIR={e.dir}", "SHELL=/bin/sh"]

/-- …and the same for `IO.Process.output`, which wants pairs. -/
def Env.procEnv (e : Env) : Array (String × Option String) :=
  #[("LINGER_DIR", some e.dir), ("SHELL", some "/bin/sh")]

/-- A live pty client: the child's pid and our end of its terminal. -/
structure Client where
  pid : UInt32
  fd : UInt32

/-- Spawn `linger <args>` on a pty of exactly this size.

The size is set **before** exec by `spawnPty`, which is the bug the Python
harness had: `pty.fork()` then `ioctl(TIOCSWINSZ)` races the child's own startup
`winsizeGet`, and that race is invisible until a suite's subject IS the geometry a
client reported (`E2E.Watch`). -/
def Env.spawn (e : Env) (args : Array String)
    (cols : UInt32 := 80) (rows : UInt32 := 24) : IO Client := do
  let (pid, fd) ← spawnPty cols rows "" e.bin args e.ptyEnv
  return { pid, fd }

/-- Everything readable within a wall-clock window; returns early on EOF. -/
partial def drain (fd : UInt32) (ms : UInt64) : IO ByteArray := do
  let deadline := (← monotonicMs) + ms
  let rec go (acc : ByteArray) : IO ByteArray := do
    if (← monotonicMs) ≥ deadline then return acc
    let revs ← poll #[fd] #[POLLIN] 100
    if revs[0]! &&& (POLLIN ||| POLLHUP ||| POLLERR) == 0 then go acc
    else match ← read fd 65536 with
      | none => return acc
      | some bs => if bs.isEmpty then return acc else go (acc ++ bs)
  go .empty

/-- Drain and decode. Lossy on purpose: a pty carries escape sequences and a
suite asserts on the printable parts, so an invalid split mid-sequence must not
throw. -/
def drainStr (fd : UInt32) (ms : UInt64) : IO String := do
  return String.fromUTF8? (← drain fd ms) |>.getD ""

/-- Type at a client. -/
def Client.type (c : Client) (s : String) : IO Unit := do
  let _ ← write c.fd s.toUTF8 0

/-- Send the detach key. Suites never touch `write` themselves. -/
def Client.detach (c : Client) : IO Unit := do
  let _ ← write c.fd detachKey 0

/-- Resize a client's terminal, as dragging the window would. -/
def Client.resize (c : Client) (cols rows : UInt32) : IO Unit :=
  winsizeSet c.fd cols rows

/-- Poll-wait for the child to be reaped, or give up.

Tolerant of ECHILD: a child already reaped (or never ours) is a child that is
gone, which is the answer the caller wants — and `bye` below promises never to
raise, so a cleanup path cannot be allowed to mask the failure that got it here. -/
def Client.reap (c : Client) (ms : UInt64 := 5000) : IO Int64 := do
  let deadline := (← monotonicMs) + ms
  let mut status : Int64 := -1
  while status == -1 && (← monotonicMs) < deadline do
    status ← try waitpidNohang c.pid catch _ => pure 0
    if status == -1 then IO.sleep 20
  return status

/-- Retire a client: detach (unless it is already gone), close, reap. Never
raises — a suite's cleanup must not mask the failure that got it here. -/
def Client.bye (c : Client) (sendDetach : Bool := true) : IO Unit := do
  if sendDetach then
    try let _ ← write c.fd detachKey 0 catch _ => pure ()
    IO.sleep 600
  try Linger.Posix.close c.fd catch _ => pure ()
  let _ ← c.reap
  pure ()

/-- Run a one-shot verb. Returns exit code, stdout, stderr — the three things
the suites assert on. -/
def Env.cli (e : Env) (args : Array String) : IO (UInt32 × String × String) := do
  let out ← IO.Process.output { cmd := e.bin, args, env := e.procEnv }
  return (out.exitCode, out.stdout, out.stderr)

/-- `linger <args>` stdout only, for the common case. -/
def Env.out (e : Env) (args : Array String) : IO String := do
  return (← e.cli args).2.1

/-- …and byte-exact, for a suite asserting on a stream rather than on text. -/
def Env.outBytes (e : Env) (args : Array String) : IO ByteArray := do
  return (← e.out args).toUTF8

/-- `Env.cli` with extra environment on top of `procEnv`.

`IO.Process.SpawnArgs.env` is processed left to right over the inherited
environment, so `extra` last is an override and `("K", none)` removes a variable
outright. Both are load-bearing for a suite whose SUBJECT is the environment:
`E2E.Terminal` needs `TERM` inherited as one value, as another, and then absent
entirely, and `E2E.Remote` needs a `PATH` whose first entry holds a fake `ssh`. -/
def Env.cliEnv (e : Env) (extra : Array (String × Option String))
    (args : Array String) : IO (UInt32 × String × String) := do
  let out ← IO.Process.output { cmd := e.bin, args, env := e.procEnv ++ extra }
  return (out.exitCode, out.stdout, out.stderr)

/-- `Env.spawn` with extra `K=V` entries on the pty child's environment: the
pty-side twin of `cliEnv`. `spawnPty`'s `extraEnv` is putenv-on-top-of-inherited
in the forked child, so the override rule is the same; `Array String` because that
is the shim's shape. The size still goes in before exec. -/
def Env.spawnEnv (e : Env) (extra : Array String) (args : Array String)
    (cols : UInt32 := 80) (rows : UInt32 := 24) : IO Client := do
  let (pid, fd) ← spawnPty cols rows "" e.bin args (e.ptyEnv ++ extra)
  return { pid, fd }

/-- Run a one-shot verb under a deadline. `none` means it was still running when
the deadline passed.

This is what makes the picker regression a FAILURE rather than a hang. Bare
`linger` must print a listing and **exit**; a full-screen picker would sit on
stdin forever. `stdin := .null` is half the guard (the child gets EOF at once) and
this deadline is the other half — without it, a regression hangs the gate instead
of failing it, which is the difference between a test and a liability.

Deliberately a piped spawn, not a pty one: the picker was tty-gated, so putting
the verb on a tty would change the premise being tested. -/
def Env.cliTimeout (e : Env) (args : Array String) (ms : UInt64)
    : IO (Option (UInt32 × String × String)) := do
  let child ← IO.Process.spawn { cmd := e.bin, args, env := e.procEnv,
                                 stdin := .null, stdout := .piped, stderr := .piped }
  let deadline := (← monotonicMs) + ms
  let mut code : Option UInt32 := none
  while code.isNone && (← monotonicMs) < deadline do
    code ← child.tryWait
    if code.isNone then IO.sleep 50
  match code with
  | none => return none          -- still running: the caller reports it as a fail
  | some c =>
    let out ← child.stdout.readToEnd
    let err ← child.stderr.readToEnd
    return some (c, out, err)

/-- Parse `k<TAB>v` lines into an association list — the shape both
`linger info` and `linger ls --porcelain` emit (`Session.infoText`). -/
def records (txt : String) : List (String × String) :=
  txt.splitOn "\n" |>.filterMap fun line =>
    match line.splitOn "\t" with
    | [k, v] => some (k, v)
    | _ => none

/-- One field of `linger info <name>`. -/
def Env.info (e : Env) (name field : String) : IO (Option String) := do
  let recs := records (← e.out #["info", name])
  return (recs.find? (·.1 == field)).map (·.2)

/-- One field of one session's `ls --porcelain` row. A `name` record opens a
row; later keys belong to it until the next one. -/
def Env.field (e : Env) (name field : String) : IO (Option String) := do
  let mut cur : Option String := none
  let mut found : Option String := none
  for (k, v) in records (← e.out #["ls", "--porcelain"]) do
    if k == "name" then cur := some v
    else if cur == some name && k == field && found.isNone then found := some v
  return found

/-- A session's status column, as the `Status` type rather than as a string
literal. This is the drift the port buys: renaming a constructor's porcelain
name is now a compile error in the suites, not a passing assertion. -/
def Env.status (e : Env) (name : String) : IO Linger.Core.Status.Status := do
  return Linger.Core.Status.ofName ((← e.field name "status").getD "")

/-- The pid of the daemon behind `name` — `tests/procs.py`'s `daemon_pids`, with
its hard half **deleted** rather than ported.

`procs.py` answered two questions: which pids are `linger __daemon <name>`
(`pgrep -f`), and which of those live in *this* `LINGER_DIR`. The second is not
optional — a real session of the same name in the developer's own dir must never
be the one that gets SIGKILLed — and it was the expensive one:
`/proc/<pid>/environ` on Linux with an `lsof -p` fallback on macOS, which AGENTS.md
counted as one of the repo's only two platform splits.

None of it is needed. `linger info <name>` is answered over
`<LINGER_DIR>/<name>.sock`, so a reply is *by construction* from the daemon in our
own directory: the isolation is structural rather than a filter over candidates.
The reply's `pid` is the child shell's (`Daemon.serve` puts it in `metaKv`), and
the daemon is that shell's parent, because the daemon is the process that called
`spawnPty` — forkpty, so parent is daemon. One `info`, one `ps -o ppid=`.

`ps -o ppid=` rather than `/proc/<pid>/stat` for exactly the reason `procs.py`
reached for lsof: same command on both platforms, so this adds no split back.
`Posix.getcwdOf` answers a different question — `spawnDetached` does not `chdir`,
so a daemon's cwd is whatever directory its spawning client was in. -/
def Env.daemonPid (e : Env) (name : String) : IO (Option UInt32) := do
  match (← e.info name "pid").bind (·.toNat?) with
  | none => return none
  | some child =>
    let out ← IO.Process.output
      { cmd := "ps", args := #["-o", "ppid=", "-p", toString child] }
    if out.exitCode != 0 then return none
    return (out.stdout.trimAscii.toString.toNat?).map UInt32.ofNat

/-- SIGKILL the daemon behind `name` and unlink its socket: the simulated crash a
reboot-resume test needs. `true` iff a daemon was found, was alive first, and is
gone after — the non-vacuity the Python only half had (`assert dpids` proved a pid
was *found*, never that the kill landed).

Unlinking the socket is load-bearing, not tidiness. `Cli.cmdList` computes its
`live` set from the socket names it can see and only then prunes the ones that fail
to connect, and the resumable rows it appends skip any name in that set. A
SIGKILLed daemon cannot unlink its own socket, so leaving the file behind hides the
session from the very listing under test. -/
def Env.crashDaemon (e : Env) (name : String) : IO Bool := do
  match ← e.daemonPid name with
  | none => return false
  | some dpid =>
    if !(← alive dpid) then return false
    kill dpid 9   -- SIGKILL: no cleanup, no checkpoint drop — a crash, not an exit
    IO.sleep 300
    try IO.FS.removeFile (System.FilePath.mk s!"{e.dir}/{name}.sock") catch _ => pure ()
    -- the daemon is double-forked (init's child, not ours), so a SIGKILLed one is
    -- reaped by init and `kill(pid, 0)` genuinely goes ESRCH — no zombie to make
    -- `alive` lie the way it would for one of our own unreaped children
    return !(← alive dpid)

/-- Kill every session named here, ignoring "no such session". -/
def Env.killAll (e : Env) (names : Array String) : IO Unit := do
  for n in names do
    let _ ← e.cli #["kill", n]
    pure ()

/-- Print the verdict line `tests/e2e.sh` reads, and return the process code. -/
def verdict (fails : Nat) : IO UInt32 := do
  IO.println s!"FAILURES: {fails}"
  return if fails == 0 then 0 else 1

end E2E.Harness
