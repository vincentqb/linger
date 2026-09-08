module

public import E2E.Harness
public import Linger.Core.Wire
public import Linger.Core.Listing
public import Linger.Runtime.Daemon

public section

/-! # E2E.Robust — three robustness properties that only show up under adverse timing

Ported from `tests/robust_test.py` (whose docstring says "two"; the third section
was added later and the count was never updated):

  1. §Row — a daemon too busy to answer `info` within the reply window still lists
     under its real name (SIGSTOP stands in for a burst of pty output on a loaded
     box), and its socket is not disturbed.
  2. name-ownership lock — with a stale socket present, concurrent starts of one
     name produce exactly one daemon and one shell; no daemon is left holding a
     pty nobody can reach.
  3. a child that stops reading cannot grow the daemon (runtime §Bound, input half).

WHAT THE PORT CHANGED, and why each was not optional:

* **SIGSTOP and SIGCONT are sent by NAME, not by number.** `signal.SIGSTOP` is
  portable; `19` is not. On Linux SIGSTOP is 19 and SIGCONT is 18; on macOS/BSD
  SIGSTOP is **17**, SIGCONT is **19** and 18 is SIGTSTP — so a hardcoded `kill
  dpid 19` would send SIGCONT to a running daemon (check 1 fails, nothing was ever
  stopped) and a hardcoded `18` would then send SIGTSTP and wedge the rest of the
  suite. That is exactly the class of bug AGENTS.md records for errno (`-111` for
  ECONNREFUSED compiled fine and silently disabled the stale-socket path on
  macOS), so the numbers stay out of Lean: `kill -s STOP` / `kill -s CONT` through
  `/bin/sh`, the same "one command, both platforms" move `Env.daemonPid` makes with
  `ps -o ppid=`. `Env.crashDaemon`'s `kill dpid 9` needs no such care — 9 is fixed
  by POSIX, as is everything in 1–15;
* **the SIGKILL in §2 is `Posix.kill … 9`, NOT `Env.crashDaemon`.** `crashDaemon`
  unlinks the socket on purpose (a SIGKILLed daemon cannot, and `Cli.cmdList` would
  otherwise hide the row) — and the stale socket left behind is precisely the
  premise this race needs. Using it here would delete the thing under test;
* **the busy row is compared against `Listing.humanListing`**, not against the
  literal `'? busy (busy)'`. That literal had already gone stale once: the
  Python's own comment says "The human row is now space-aligned
  (`Listing.humanRow`), not tab-separated". The expectation is now the core's
  rendering of a live row that did not answer, so the glyph comes from
  `Status.icon` and the spacing from `humanRow`;
* the porcelain check parsed nothing — `'name\tbusy' in porc` is a substring test
  on a records format. It now goes through `records` (the reader `Env.field` and
  `Core.Remote` use) and also pins the status column as `Status.name .unknown`;
* the lock check asserted only that `claim.lock` EXISTS, which its own comment
  explains is weak evidence: "lock files are deliberately never unlinked
  (unlinking defeats flock), so earlier sessions leave theirs behind". It now also
  asserts the lock is HELD — `Posix.flock` returning `-1` is another process
  holding it, which is the property, and a file existing is not;
* the reported cap is compared to `Daemon.ptyInCap` rather than only to itself.

WHAT COULD NOT BE MADE STRUCTURAL: counting daemons needs a process enumeration,
and `Env.daemonPid` cannot do it — it asks over `<LINGER_DIR>/<name>.sock`, so it
returns at most one pid by construction and `len(owners) == 1` would be vacuous.
`procs.py` scoped `pgrep -f` to our `LINGER_DIR` via `/proc/<pid>/environ` with an
`lsof -p` fallback, the platform split the harness deleted. This suite gets the
same isolation for free by making the session NAME unique to the run
(`claim-<pid>`), so a `ps` scan for `__daemon claim-<pid>` cannot see a real
session of the developer's own — no `/proc`, no `lsof`, no new split. -/

namespace E2E.Robust

open E2E.Harness
open Linger.Core.Status (Status)
open Linger.Core.Listing (humanListing rowFields rowStatus)
open Linger.Runtime.Daemon (ptyInCap)

/-- Python's `str.split()`: on any whitespace, empty fields dropped. `String.split`
returns a slice iterator on v4.32, so this goes through `splitOn` instead. -/
def words (s : String) : List String :=
  (((s.replace "\t" " ").replace "\n" " ").replace "\r" " " |>.splitOn " ").filter (· != "")

/-- `ps -eo pid,ppid,args` as (pid, ppid, whole-line) triples — `procs.py`'s
`pgrep` and `children_of` in one call.

`-ww` because the daemon's argv begins with an absolute binary path (~49 bytes
here) and `__daemon <name>` lands past column 60: macOS `ps` truncates to 80
columns even into a pipe, which would cut the name off the end of the line. The
Python never needed it because `children_of` greps for `/bin/sh`, which sits at
column ~13. If a `ps` did reject `-ww` the table comes back empty and the counts
below FAIL rather than pass — fail-closed. -/
def psTable : IO (List (Nat × Nat × String)) := do
  let out ← IO.Process.output { cmd := "ps", args := #["-e", "-ww", "-o", "pid,ppid,args"] }
  return (out.stdout.splitOn "\n").filterMap fun l =>
    match words l with
    | p :: pp :: _ =>
      match p.toNat?, pp.toNat? with
      | some pid, some ppid => some (pid, ppid, l)
      | _, _ => none
    | _ => none

/-- Send a signal by NAME. See the module docstring: the numbers for SIGSTOP and
SIGCONT differ between Linux and macOS, so they never enter Lean. `kill` through
`/bin/sh` rather than as a `cmd` because on a minimal system `kill` is only a
shell builtin, and `SHELL=/bin/sh` is already this suite's premise. -/
def signalByName (pid : UInt32) (sig : String) : IO Unit := do
  let _ ← IO.Process.output { cmd := "/bin/sh", args := #["-c", s!"kill -s {sig} {pid}"] }
  pure ()

/-- The daemon's backpressure line, as a marker rather than a regex (Lean has no
regex engine, and this needs none):

  `linger: pty input buffer full (<pending> B, cap <cap>); the child is not
   reading — dropping input until it does` -/
def fullMarker : String := "pty input buffer full ("

/-- `(pending, cap)` from the first occurrence — Python's two capture groups. -/
def parseFull (log : String) : Option (Nat × Nat) :=
  match log.splitOn fullMarker with
  | _ :: after :: _ =>
    match after.splitOn " B, cap " with
    | pend :: tail :: _ =>
      match tail.splitOn ")" with
      | cap :: _ =>
        match pend.toNat?, cap.toNat? with
        | some p, some c => some (p, c)
        | _, _ => none
      | _ => none
    | _ => none
  | _ => none

/-- How many times the daemon logged the transition. -/
def countFull (log : String) : Nat := (log.splitOn fullMarker).length - 1

def run : IO UInt32 := do
  let e ← Env.make "robust"
  let mut f := 0

  -- ── 1. busy daemon still lists correctly ──────────────────────────────────
  let _ ← e.cli #["run", "busy", "echo hi"]
  IO.sleep 1000
  -- captured while the daemon is still HEALTHY, before the SIGSTOP: `info` has to
  -- be answered for `Env.daemonPid` to work, and it is — the Python did the same,
  -- `daemon_pids('busy')[0]` on the line before `os.kill(..., SIGSTOP)`. Aborts
  -- rather than printing a check, as the Python's implicit `[0]` IndexError did:
  -- with no pid there is nothing below this line left to mean anything.
  let some dpid ← e.daemonPid "busy"
    | throw (IO.userError "no daemon answered for 'busy' — nothing to SIGSTOP")
  signalByName dpid "STOP"
  let out ← e.out #["list"]
  let porc ← e.out #["list", "--porcelain"]
  let socks ← e.dirNames ".sock"
  signalByName dpid "CONT"

  -- the leading glyph is the status column: a daemon that did not answer within
  -- the reply window is reported as unknown (`Status.icon .unknown`), which is the
  -- designed state for it — so this pins §Row *and* that a busy row is not shown
  -- as healthy. Compared against the core's own rendering of that row rather than
  -- against a copy of it: `Cli.cmdList` writes `humanListing rows` straight to
  -- stdout, and for a socket that connected but sent nothing back the row is
  -- `rowFields name []` plus `state=live` and `rowStatus (.live [])`.
  let expected := humanListing
    [rowFields "busy" [("state", "live"), ("status", Linger.Core.Status.name (rowStatus (.live [])))]]
  f := f + (← expect (out.toUTF8.toList == expected)
    s!"busy daemon lists under its name, marked unknown (got '{out.trimAscii.toString}')")
  let recs := records porc
  f := f + (← expect (recs.contains ("name", "busy")
                      && recs.contains ("status", Linger.Core.Status.name Status.unknown))
    "porcelain carries the name for a busy daemon")
  f := f + (← expect (socks == ["busy.sock"]) s!"busy daemon keeps its socket ({socks})")
  IO.sleep 400
  f := f + (← expect ((← e.cli #["send", "busy", "echo x\n"]).1 == 0)
    "busy daemon still reachable afterwards")
  e.killAll #["busy"]
  IO.sleep 500

  -- ── 2. stale socket + concurrent starts -> one owner ──────────────────────
  -- The name is unique to this run so the `ps` scan below cannot see a developer's
  -- own session of the same name. See the module docstring: this replaces
  -- `procs.py`'s `/proc/<pid>/environ`-or-`lsof` LINGER_DIR filter, and it is the
  -- same trick `Env.make` already uses for the directory.
  let claim := s!"claim-{← Linger.Posix.getpid}"
  let _ ← e.cli #["run", claim, "echo one"]
  IO.sleep 1000
  let some victim ← e.daemonPid claim
    | throw (IO.userError s!"no daemon answered for '{claim}' — nothing to SIGKILL")
  -- SIGKILL directly, NOT `Env.crashDaemon`: that unlinks the socket, and the
  -- socket left behind stale is the premise of the race below. 9 is safe to spell
  -- as a number (POSIX fixes 1–15); STOP and CONT above are not.
  Linger.Posix.kill victim 9
  IO.sleep 300
  let stale ← e.dirNames ".sock"
  f := f + (← expect (stale == [s!"{claim}.sock"])
    s!"stale socket present for the race ({stale})")

  -- eight concurrent `run <name>`, spawned before any is waited on — the Python's
  -- `[Popen(...) for _ in range(8)]` then `for p: p.wait()`
  let cfg : IO.Process.SpawnArgs :=
    { cmd := e.bin, args := #["run", claim, "echo two"], env := e.procEnv,
      stdin := .null, stdout := .null, stderr := .null }
  let kids ← (List.range 8).mapM fun _ => IO.Process.spawn cfg
  for k in kids do
    let _ ← k.wait
  IO.sleep 1500

  let ps ← psTable
  let owners := ps.filterMap fun (pid, _, args) =>
    if has args s!"__daemon {claim}" then some pid else none
  let shells := ps.filter fun (_, ppid, args) =>
    owners.contains ppid && has args "/bin/sh"
  f := f + (← expect (owners.length == 1)
    s!"exactly one daemon owns the name (got {owners.length})")
  f := f + (← expect (shells.length == 1) s!"exactly one shell (got {shells.length})")
  f := f + (← expect ((← e.cli #["send", claim, "echo y\n"]).1 == 0)
    "the surviving session is reachable")
  -- lock files are deliberately never unlinked (unlinking defeats flock), so
  -- earlier sessions leave theirs behind; ours must be among them. Listed BEFORE
  -- the flock probe, because `flock` opens the path with O_CREAT and would make
  -- the presence half of this check true by having run it.
  let locks ← e.dirNames ".lock"
  -- …and present is not held: `flock` returns `-1` when another process holds it,
  -- which is the property the file's existence only hints at. On the failing
  -- branch it returns a held fd, which must be closed or THIS process would own
  -- the name for the rest of the suite.
  let lockFd ← Linger.Posix.flock s!"{e.dir}/{claim}.lock"
  if lockFd ≥ 0 then Linger.Posix.close (UInt32.ofNat lockFd.toNatClampNeg)
  f := f + (← expect (locks.contains s!"{claim}.lock" && lockFd == -1)
    s!"ownership lock file present ({locks})")
  e.killAll #[claim]
  IO.sleep 500

  -- the lock must be re-acquirable once the owner is gone (kernel released it)
  let _ ← e.cli #["run", claim, "echo three"]
  IO.sleep 1000
  let owners2 := (← psTable).filterMap fun (pid, _, args) =>
    if has args s!"__daemon {claim}" then some pid else none
  f := f + (← expect (owners2.length == 1)
    "name is re-claimable after the owner exits (no stale lock)")
  e.killAll #[claim]
  IO.sleep 500

  -- ── 3. a child that stops reading cannot grow the daemon ──────────────────
  -- `sleep` never reads its stdin, so the pty master's input buffer fills and
  -- `flushPty` stops draining; every `.input` frame after that would append
  -- forever without the `ptyInCap` cap. Input goes in over a raw control
  -- connection (no `.attach`), which `Session.onMsg .input` routes to `.writePty`.
  --
  -- The payload is newline-terminated lines, not one long run of 'x', and that is
  -- load-bearing on macOS: measured 2026-08-19, a nonblocking write of an
  -- unterminated blob to a pty master whose slave is not reading *succeeds*
  -- forever (98 MB in 3 s) because the BSD tty layer discards an over-long
  -- canonical line instead of pushing back, so `ptyIn` never grew and the cap
  -- never tripped. With lines it is EAGAIN after ~1 KB, as on Linux.
  let _ ← e.cli #["run", "stall", "sleep", "600"]
  IO.sleep 1000
  -- the Python only used this as a truthiness test (`if sp:`), never the pid
  let sp ← e.daemonPid "stall"
  if sp.isSome then
    let r ← Linger.Posix.unixConnect s!"{e.dir}/stall.sock"
    let sock := UInt32.ofNat r.toNatClampNeg
    -- the frame is built by the implementation's own codec rather than by
    -- `bytes([0]) + struct.pack('<I', …)`: `.input` is `Wire.Msg.tag 0` and the
    -- length is `Wire.writeU32`, so a tag renumbering is a compile-time fact here
    -- instead of a silently-ignored frame. 262144 B is `Wire.maxPayload` exactly —
    -- the largest legal frame, which is what makes 64 of them ~4x the cap.
    let payload := (List.replicate 4096
      (List.replicate 63 (0x78 : UInt8) ++ [0x0A])).flatten
    let frame := ByteArray.mk
      (Linger.Core.Wire.encode (.input payload)).toArray
    for _ in List.range 64 do                     -- 16 MiB, ~4x the cap
      Linger.Posix.writeAll sock frame
    Linger.Posix.close sock
    -- the daemon logs the cap once on the transition into backpressure; its stderr
    -- is an O_APPEND file, so give the write a moment to land. The reported
    -- pending count is the bounded-buffer property itself — a full buffer that
    -- stayed <= cap is exactly "the child could not grow us".
    let logf := s!"{e.dir}/logs/stall.log"
    let readLog : IO String := do
      try IO.FS.readFile logf catch _ => pure ""
    let mut log := ""
    let mut m : Option (Nat × Nat) := none
    for _ in List.range 20 do
      if m.isNone then
        IO.sleep 200
        log ← readLog
        m := parseFull log
    f := f + (← expect m.isSome "daemon reports the full input buffer")
    -- …and the cap it reports is `Daemon.ptyInCap`, not merely some number it also
    -- compared itself against
    f := f + (← expect (match m with
                        | some (p, c) => p ≤ c && c == ptyInCap
                        | none => true)
      "pending stayed within the cap, and the cap is Daemon.ptyInCap")
    f := f + (← expect (countFull log == 1)
      "logged once on the edge, not per dropped chunk")
    f := f + (← expect ((← e.cli #["send", "stall", "echo x\n"]).1 == 0)
      "the stalled session is still reachable")
    e.killAll #["stall"]
  else
    f := f + (← expect false "stall daemon started")

  verdict f

end E2E.Robust
