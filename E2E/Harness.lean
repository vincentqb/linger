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
or `FAIL <name>`, and each suite ends with `FAILURES: <n>`. `E2E.Runner` requires
exit 0, last line `FAILURES: 0`, no `FAIL` line and exactly the `PASS` count that
`scripts/e2e.sh` passes, so a suite that stops checking fails the gate and so does
one that quietly grows — either way it is a reviewable edit. -/

namespace E2E.Harness

open Linger.Posix

/-- The detach key, ctrl-\\ — the one byte every suite sends to leave. -/
def detachKey : ByteArray := ByteArray.mk #[0x1C]

/-- One check. Returns 1 on failure so callers can sum. -/
def expect (cond : Bool) (name : String) : IO Nat := do
  IO.println s!"{if cond then "PASS" else "FAIL"} {name}"
  return if cond then 0 else 1

/-- Substring test (core `String.contains`; an empty needle is contained everywhere). -/
def has (haystack needle : String) : Bool := haystack.contains needle

/-- Poll `p` until it holds or `ms` elapses; the result is whether it ever held.

For an assertion that waits for something to **appear**, this replaces a fixed
`IO.sleep`. A fixed sleep budgets for the typical host and fails on a busy one:
`E2E.Agent`'s `^C` check flaked exactly once this way (2026-09-11, a full e2e run
racing a `lake build`) and then passed 4/4 in isolation with nothing changed. The
deadline keeps the assertion honest — a genuine regression still fails, it just
spends the whole budget before saying so — and the common case gets *faster*, since
it stops as soon as the marker lands instead of always sleeping the worst case.

Only for positive waits. An assertion that something did **not** happen must keep
its fixed settle time: polling for a change that should never arrive would return
early on the very first look and prove nothing. -/
def waitFor (ms : Nat) (p : IO Bool) : IO Bool := do
  let deadline := (← monotonicMs) + ms
  let mut ok ← p
  while !ok && (← monotonicMs) < deadline do
    IO.sleep 50
    ok ← p
  return ok

/-- Wait for a spawned process without letting a regression hang the suite. -/
def waitProcess {cfg : IO.Process.StdioConfig} (child : IO.Process.Child cfg) (ms : Nat) :
    IO (Option UInt32) := do
  let deadline := (← monotonicMs) + ms
  let mut code ← child.tryWait
  while code.isNone && (← monotonicMs) < deadline do
    IO.sleep 50
    code ← child.tryWait
  return code

/-- First index of `needle` in `hay`, walking the haystack once.

The primitive the other three are built on, and the reason it is `Option Nat`
rather than `Bool`: the ED-2-before-ED-3 ordering check in `E2E.Attach` needs the
positions, not just presence.

Linear-ish by construction (`O(|hay| · |needle|)`), which matters more than it
looks: the first version of `hasBytes` scanned with `(h.drop i).take n`, and
`List.drop i` is `O(i)`, so it was QUADRATIC in the haystack — against a truecolour
reattach burst of tens of kilobytes that is ~10⁹ list steps. `isPrefixOf` on the
tail walks it once instead. -/
def findFrom (needle : List UInt8) (i : Nat) : List UInt8 → Option Nat
  | [] => if needle.isEmpty then some i else none
  | h :: t => if needle.isPrefixOf (h :: t) then some i else findFrom needle (i + 1) t

def findBytes (hay : ByteArray) (needle : List UInt8) : Option Nat := findFrom needle 0 hay.toList

/-- …and the same needle spelled as text. -/
def findText (hay : ByteArray) (needle : String) : Option Nat := findBytes hay needle.toUTF8.toList

/-- Does `hay` contain `needle` as a contiguous byte run?

The honest test for "the client wrote *this emitter's* output": a pty stream is
bytes, not text, and comparing against `Linger.Core.Render.leaveAnsi` itself is
what stops a suite hardcoding a copy of what the implementation emits — the copy
is what goes stale when the emitter changes. -/
def hasBytes (hay : ByteArray) (needle : List UInt8) : Bool := (findBytes hay needle).isSome

/-- Does `hay` *begin* with `needle`? `leaveAnsi` leads with ST for a reason (a
program that died mid-OSC would otherwise eat the rest of the hand-back), so
"contains" is not enough for that one. -/
def startsWithBytes (hay : ByteArray) (needle : List UInt8) : Bool :=
  hay.toList.take needle.length == needle

/-- A `String` needle against a pty's bytes, without spelling the needle twice.
The byte-level form of `has`, for streams that also carry escape sequences. -/
def hasText (hay : ByteArray) (needle : String) : Bool := hasBytes hay needle.toUTF8.toList

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
  let dir : String :=
    match envDir with
    | some d => d
    | none => s!"/tmp/linger-{slug}-{pid}"
  IO.FS.createDirAll (System.FilePath.mk dir)
  return { bin, dir }

/-- `extraEnv` for `spawnPty`: the state dir plus a predictable shell. -/
def Env.ptyEnv (e : Env) : Array String := #[s!"LINGER_DIR={e.dir}", "SHELL=/bin/sh"]

/-- …and the same for `IO.Process.output`, which wants pairs. -/
def Env.procEnv (e : Env) : Array (String × Option String) :=
  #[("LINGER_DIR", some e.dir), ("SHELL", some "/bin/sh")]

/-- A live pty client: the child's pid and our end of its terminal. -/
structure Client where
  pid : UInt32
  fd : UInt32

/-- Spawn `linger <args>` on a pty of exactly this size, with extra `K=V` entries
on the child's environment.

The size is set **before** exec by `spawnPty`, which is the bug the Python
harness had: `pty.fork()` then `ioctl(TIOCSWINSZ)` races the child's own startup
`winsizeGet`, and that race is invisible until a suite's subject IS the geometry a
client reported (`E2E.Watch`). `spawnPty`'s `extraEnv` is putenv-on-top-of-inherited
in the forked child, so `extra` overrides `ptyEnv` by `cliEnv`'s rule; `Array String`
because that is the shim's shape. -/
def Env.spawnEnv (e : Env) (extra : Array String) (args : Array String) (cols : UInt32 := 80)
    (rows : UInt32 := 24) : IO Client := do
  let (pid, fd) ← spawnPty cols rows "" e.bin args (e.ptyEnv ++ extra)
  return { pid, fd }

/-- `Env.spawnEnv` with no extra environment. -/
def Env.spawn (e : Env) (args : Array String) (cols : UInt32 := 80) (rows : UInt32 := 24) :
    IO Client := e.spawnEnv #[] args cols rows

/-- Everything readable within a monotonic deadline; returns early on EOF. -/
def drain (fd : UInt32) (ms : Nat) : IO ByteArray := do
  let deadline := (← monotonicMs) + ms
  let mut acc := ByteArray.empty
  while (← monotonicMs) < deadline do
    let revs ← poll #[fd] #[POLLIN] 100
    if revs[0]! &&& (POLLIN ||| POLLHUP ||| POLLERR) == 0 then
      continue
    match ← read fd 65536 with
    | none =>
      return acc
    | some bs =>
      if bs.isEmpty then
        return acc
      acc := acc ++ bs
  return acc

/-- Drain and decode. Lossy on purpose: a pty carries escape sequences and a
suite asserts on the printable parts, so an invalid split mid-sequence must not
throw. -/
def drainStr (fd : UInt32) (ms : Nat) : IO String := do
  return String.fromUTF8? (← drain fd ms) |>.getD ""

/-- Type at a client. -/
def Client.type (c : Client) (s : String) : IO Unit := do
  let _ ← write c.fd s.toUTF8 0

/-- Send the detach key. Suites never touch `write` themselves. -/
def Client.detach (c : Client) : IO Unit := do
  let _ ← write c.fd detachKey 0

/-- Resize a client's terminal, as dragging the window would. -/
def Client.resize (c : Client) (cols rows : UInt32) : IO Unit := winsizeSet c.fd cols rows

/-- Poll-wait for the child to be reaped, or give up.

Tolerant of ECHILD: a child already reaped (or never ours) is a child that is
gone, which is the answer the caller wants — and `bye` below promises never to
raise, so a cleanup path cannot be allowed to mask the failure that got it here. -/
def Client.reap (c : Client) (ms : Nat := 5000) : IO Int64 := do
  let deadline := (← monotonicMs) + ms
  let mut status : Int64 := -1
  while status == -1 && (← monotonicMs) < deadline do
    status ←
      try
        waitpidNohang c.pid
      catch _ =>
        pure 0
    if status == -1 then
      IO.sleep 20
  return status

/-- Retire a client: detach (unless it is already gone), close, reap. Never
raises — a suite's cleanup must not mask the failure that got it here. -/
def Client.bye (c : Client) (sendDetach : Bool := true) : IO Unit := do
  if sendDetach then
    try
      c.detach
    catch _ =>
      pure ()
    let _ ← c.reap 600
  try
    Linger.Posix.close c.fd
  catch _ =>
    pure ()
  let _ ← c.reap
  pure ()

/-- Run a one-shot verb with extra environment on top of `procEnv`. Returns exit
code, stdout, stderr — the three things the suites assert on.

`IO.Process.SpawnArgs.env` is processed left to right over the inherited
environment, so `extra` last is an override and `("K", none)` removes a variable
outright. Both are load-bearing for a suite whose SUBJECT is the environment:
`E2E.Terminal` needs `TERM` inherited as one value, as another, and then absent
entirely, and `E2E.Remote` needs a `PATH` whose first entry holds a fake `ssh`. -/
def Env.cliEnv (e : Env) (extra : Array (String × Option String)) (args : Array String) :
    IO (UInt32 × String × String) := do
  let out ← IO.Process.output { cmd := e.bin, args, env := e.procEnv ++ extra }
  return (out.exitCode, out.stdout, out.stderr)

/-- `Env.cliEnv` with no extra environment. -/
def Env.cli (e : Env) (args : Array String) : IO (UInt32 × String × String) := e.cliEnv #[] args

/-- `linger <args>` stdout only, for the common case. -/
def Env.out (e : Env) (args : Array String) : IO String := do
  return (← e.cli args).2.1

/-- Run a one-shot verb under a deadline. `none` means it was still running when
the deadline passed.

stdin is at EOF and a deadline bounds the run, so a verb that blocks on input
fails instead of hanging (Overview's `linger ls`). -/
def Env.cliTimeout (e : Env) (args : Array String) (ms : Nat) :
    IO (Option (UInt32 × String × String)) := do
  let child ←
    IO.Process.spawn
        { cmd := e.bin, args, env := e.procEnv, stdin := .null, stdout := .piped, stderr := .piped }
  let code ← waitProcess child ms
  match code with
  | none =>
    return none -- still running: the caller reports it as a fail
  | some c =>
    let out ← child.stdout.readToEnd
    let err ← child.stderr.readToEnd
    return some (c, out, err)

/-- A stream's lines, without the empty field a trailing newline leaves.

Was duplicated verbatim in two suites, each with a comment noting the other copy.
Deliberately NOT `String.Slice.lines`, which also strips a trailing `\r`: these are
pty streams full of `\r\n`, so that would be a behaviour change dressed as a
cleanup. Worth revisiting as its own measured change. -/
def lines (s : String) : List String :=
  let l := s.splitOn "\n"
  if l.getLast? == some "" then l.dropLast else l

/-- Names in this suite's state dir ending in `ext`, sorted.

Sorted because a directory read order is not defined and the failure labels print
the list; every assertion on it is about a one-element or empty list, so order never
decides one. Was `ckptNames` in one suite and `dirNames` in another — same body, one
of them hardcoding the extension. -/
def Env.dirNames (e : Env) (ext : String) : IO (List String) := do
  let entries ← System.FilePath.readDir (System.FilePath.mk e.dir)
  let names :=
    entries.toList.filterMap fun de => if de.fileName.endsWith ext then some de.fileName else none
  return names.toArray.qsort (· < ·) |>.toList

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
    if k == "name" then
      cur := some v
    else if cur == some name && k == field && found.isNone then
      found := some v
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
  | none =>
    return none
  | some child =>
    let out ← IO.Process.output { cmd := "ps", args := #["-o", "ppid=", "-p", toString child] }
    if out.exitCode != 0 then
      return none
    return (out.stdout.trimAscii.toString.toNat?).map UInt32.ofNat

/-- SIGKILL the daemon behind `name`, leaving its socket as a real crash does.
`true` iff a daemon was found, was alive first, and is gone after. The listing
path—not the test harness—must classify and safely clean the stale socket. -/
def Env.crashDaemon (e : Env) (name : String) : IO Bool := do
  match ← e.daemonPid name with
  | none =>
    return false
  | some dpid =>
    if !(← alive dpid) then
      return false
    kill dpid 9 -- SIGKILL: no cleanup, no checkpoint drop — a crash, not an exit
    -- the daemon is double-forked (init's child, not ours), so a SIGKILLed one is
    -- reaped by init and `kill(pid, 0)` genuinely goes ESRCH — no zombie to make
    -- `alive` lie the way it would for one of our own unreaped children
    waitFor 5000 (return !(← alive dpid))

/-- Kill every session named here, ignoring "no such session". -/
def Env.killAll (e : Env) (names : Array String) : IO Unit := do
  for n in names do
    let _ ← e.cli #["kill", n]
    pure ()

/-- Print the verdict line `scripts/e2e.sh` reads, and return the process code.

Takes the `Env` so the exit point the PTY suites already go through is also
where their state directory is retired — a green run leaves nothing behind, a red one
keeps its sockets, logs and checkpoints for the post-mortem. Ten suites × one dir
per run had accumulated 538 of them in `/tmp` before this was here, and a cleanup a
new suite must remember to call is a cleanup that will be forgotten. A dir supplied
through `LINGER_TEST_DIR` is the caller's, so it is left alone either way.

Not every suite: `E2E/Coverage.lean` and `E2E/Ci.lean` print `FAILURES:` themselves,
having no state directory to retire, so the output contract above lives in three
places and they must be edited alongside this if it changes. -/
def verdict (e : Env) (fails : Nat) : IO UInt32 := do
  IO.println s!"FAILURES: {fails}"
  if fails == 0 && (← IO.getEnv "LINGER_TEST_DIR").isNone then
    try
      IO.FS.removeDirAll (System.FilePath.mk e.dir)
    catch _ =>
      pure ()
  return if fails == 0 then 0 else 1

end E2E.Harness
