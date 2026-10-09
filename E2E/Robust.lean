module

public import E2E.Harness
public import Linger.Core.Wire
public import Linger.Core.Listing
public import Linger.Runtime.Daemon
public import Linger.Runtime.Cli

public section

/-! # E2E.Robust — runtime boundaries under adverse timing

The suite covers busy-daemon listing, name ownership, bounded child input,
lock-aware stale cleanup, absolute info deadlines, bounded accept rounds, and
the slow-client output cut. Two premises are not optional:

* **SIGSTOP and SIGCONT are sent by NAME, not by number.** On Linux SIGSTOP is 19
  and SIGCONT is 18; on macOS/BSD SIGSTOP is **17**, SIGCONT is **19** and 18 is
  SIGTSTP — so a hardcoded `kill dpid 19` would send SIGCONT to a running daemon
  (check 1 fails, nothing was ever stopped) and a hardcoded `18` would then send
  SIGTSTP and wedge the rest of the suite. AGENTS.md's rule to avoid numeric errno
  values in Lean guards the same kind of platform split, so these numbers stay out
  of Lean too: `kill -s STOP` / `kill -s CONT` through `/bin/sh`, the same "one
  command, both platforms" move `Env.daemonPid` makes with `ps -o ppid=`.
  `Env.crashDaemon`'s `kill dpid 9` needs no such care — 9 is fixed by POSIX;
* **crash simulation leaves the socket behind.** A SIGKILLed daemon cannot
  unlink it; `Env.crashDaemon` preserves that premise so listing and ownership
  tests exercise production cleanup rather than test-harness cleanup.

WHAT COULD NOT BE MADE STRUCTURAL: counting daemons needs a process enumeration,
and `Env.daemonPid` cannot do it — it asks over `<LINGER_DIR>/<name>.sock`, so it
returns at most one pid by construction and counting its answers would be vacuous.
This suite instead makes the session NAME unique to the run (`claim-<pid>`), so a
`ps` scan for `__daemon claim-<pid>` cannot see a real session of the developer's
own — no `/proc`, no `lsof`, no platform split. -/

namespace E2E.Robust

open E2E.Harness
open Linger.Core.Status (Status)
open Linger.Core.Listing (humanListing rowFields rowStatus)
open Linger.Core.Session (maxClients)
open Linger.Runtime.Daemon (outbufCap ptyInCap)

/-- `ps -eo pid,ppid,args` as (pid, ppid, whole-line) triples.

`-ww` because the daemon's argv begins with an absolute binary path (~49 bytes
here) and `__daemon <name>` lands past column 60: macOS `ps` truncates to 80
columns even into a pipe, which would cut the name off the end of the line. If a
`ps` did reject `-ww` the table comes back empty and the counts below FAIL rather
than pass — fail-closed. -/
def psTable : IO (List (Nat × Nat × String)) := do
  let out ← IO.Process.output { cmd := "ps", args := #["-e", "-ww", "-o", "pid,ppid,args"] }
  return (out.stdout.splitOn "\n").filterMap fun l =>
      match (l.split Char.isWhitespace).toStringList.filter (· != "") with
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

/-- `(pending, cap)` from the first occurrence. -/
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

/-- Fake daemon that continuously emits valid info fragments without a terminator.
A silence timeout never fires; an absolute request deadline must. -/
def streamInfoServer (socketPath readyPath : String) : IO UInt32 := do
  let lfd ← Linger.Posix.unixListen socketPath
  Linger.Posix.setNonblock lfd
  IO.FS.writeFile readyPath "ready"
  let acceptDeadline := (← Linger.Posix.monotonicMs) + 5000
  let mut peer : Option UInt32 := none
  while peer.isNone && (← Linger.Posix.monotonicMs) < acceptDeadline do
    let fd ← Linger.Posix.accept lfd
    if fd ≥ 0 then
      peer := some fd.toUInt64.toUInt32
    else
      IO.sleep 20
  match peer with
  | none =>
    Linger.Posix.close lfd
    return 1
  | some fd =>
    let frame :=
      ByteArray.mk
        (Linger.Core.Wire.encode (.infoReply "pid\t1\ncmd\tstreaming\n".toUTF8.toList)).toArray
    let deadline := (← Linger.Posix.monotonicMs) + 6000
    try
      while (← Linger.Posix.monotonicMs) < deadline do
        Linger.Posix.writeAll fd frame
        IO.sleep 5
    catch _ =>
      pure ()
    Linger.Posix.close fd
    Linger.Posix.close lfd
    try
      IO.FS.removeFile socketPath
    catch _ =>
      pure ()
    return 0

/-- Exhaust only the daemon's descriptors, leaving its existing client and pty
usable. The actual accept error establishes the premise on each platform. -/
def admissionPressure (e : Env) : IO Nat := do
  let pressure : Env := { e with dir := s!"{e.dir}/admission" }
  IO.FS.createDirAll pressure.dir
  let socketPath := s!"{pressure.dir}/pressure.sock"
  let logPath := s!"{pressure.dir}/daemon.log"
  let marker := s!"{pressure.dir}/alive"
  let server ←
    IO.Process.spawn
        { cmd := "/bin/sh",
          args :=
            #["-c", "ulimit -n 24 || exit; pressure_log=$1; shift; exec \"$@\" 2>\"$pressure_log\"",
              "sh", logPath, e.bin, "__daemon", "pressure", pressure.dir, "/bin/sh"],
          env := pressure.procEnv, stdin := .null, stdout := .null, stderr := .null }
  let owned ← IO.mkRef (#[] : Array UInt32)
  let child ← IO.mkRef (none : Option UInt32)
  try
    unless (← waitFor 5000 (System.FilePath.pathExists socketPath)) do
      throw (IO.userError "descriptor-pressure daemon did not start")
    let raw ← Linger.Posix.unixConnect socketPath
    unless raw ≥ 0 do
      throw (IO.userError "descriptor-pressure control client could not connect")
    let control := raw.toUInt64.toUInt32
    owned.modify (·.push control)
    let initial ← Linger.Runtime.Cli.readInfo control
    let some pidText :=
      initial.find? (·.1 == "pid") |>.map
        (·.2) | throw (IO.userError "descriptor-pressure daemon did not report its child")
    let some pid := pidText.toNat? | throw (IO.userError "invalid child pid")
    child.set (some pid.toUInt32)
    for _ in List.range maxClients do
      let peer ← Linger.Posix.unixConnect socketPath true
      if peer ≥ 0 then
        owned.modify (·.push peer.toUInt64.toUInt32)
    let exhausted ←
      waitFor 3000 do
          let log ← IO.FS.readFile logPath
          return has log "accept:"
    let mut f ← expect exhausted "descriptor pressure reaches the daemon's accept syscall"
    if exhausted then
      IO.sleep (UInt32.ofNat (2 * Linger.Runtime.Daemon.acceptRetryMs + 100))
    let log ← IO.FS.readFile logPath
    f :=
      f +
        (←
          expect
              (exhausted && (log.splitOn "client admission paused").length == 2 &&
                (← server.tryWait).isNone)
              "sustained descriptor pressure reports once and preserves the daemon")
    let usable ←
      try
        let current ← Linger.Runtime.Cli.readInfo control
        Linger.Runtime.Client.sendMsg control
            (.input "printf alive > \"$LINGER_DIR/alive\"\n".toUTF8.toList)
        let ran ← waitFor 3000 (System.FilePath.pathExists marker)
        pure (ran && current.contains ("pid", pidText) && (← server.tryWait).isNone)
      catch _ =>
        pure false
    f :=
      f + (← expect usable "descriptor exhaustion preserves the same responsive daemon and shell")
    -- Release the accepted idle clients and the kernel backlog before probing
    -- admission again; the original control client remains connected.
    for peer in (← owned.get).drop 1 do
      Linger.Posix.close peer
    owned.set #[control]
    let recovered ←
      waitFor 5000 do
          let reply ← pressure.cliTimeout #["info", "pressure"] 2500
          return reply.any fun (rc, text, _) => rc == 0 && (records text).contains ("pid", pidText)
    f := f + (← expect recovered "new connections recover after descriptor pressure clears")
    return f
  finally
    for fd in ← owned.get do
      Linger.Posix.close fd
    let _ ← pressure.cliTimeout #["kill", "pressure"] 3000
    if (← waitProcess server 3000).isNone then
      server.kill
      let _ ← server.wait
    if let some pid← child.get then
      if ← Linger.Posix.alive pid then
        Linger.Posix.kill pid 9

/-- Diagnostic output can fail along with the operation it reports, such as
when checkpoints and logs share a full filesystem. Exercise each recovery path. -/
def failedDiagnostics : IO Nat := do
  let rt : Linger.Runtime.Daemon.Rt :=
    { st := Linger.Core.Session.State.boot (Linger.Core.Vt.Vt.init 80 24) [] [], listenFd := 0,
      ptyFd := 0, childPid := 0, sockPath := "",
      saveCkpt := fun _ => throw (IO.userError "injected checkpoint save failure"),
      dropCkpt := throw (IO.userError "injected checkpoint delete failure") }
  let full :=
    (Linger.Core.Buf.bufOffer ptyInCap .empty (ByteArray.mk (Array.replicate ptyInCap 0))).1
  let cases : List (String × IO Bool) :=
    [("checkpoint save", do
        let (_, feedback) ← Linger.Runtime.Daemon.runEffect rt .checkpoint
        pure
            (match feedback with
            | [.checkpointFailed] => true
            | _ => false)),
      ("checkpoint delete", do
        let (_, feedback) ← Linger.Runtime.Daemon.runEffect rt .dropCheckpoint
        pure feedback.isEmpty),
      ("input backpressure", do
        let next ← Linger.Runtime.Daemon.queuePty { rt with ptyIn := full } [0]
        pure (next.ptyInFull && Linger.Core.Buf.owedLen next.ptyIn == ptyInCap))]
  let stderr ← IO.getStderr
  let mut f := 0
  for (label, check) in cases do
    let attempts ← IO.mkRef (0 : Nat)
    let broken : IO.FS.Stream :=
      { stderr with
        putStr := fun _ => do
          attempts.modify (· + 1)
          throw (IO.userError "injected diagnostic write failure") }
    let recovered ←
      IO.withStderr broken do
          try
            check
          catch _ =>
            pure false
    f :=
      f +
        (←
          expect (recovered && (← attempts.get) == 1)
              s!"{label} recovery survives a failed diagnostic write")
  return f

def run : IO UInt32 := do
  let e ← Env.make "robust"
  let mut f := 0
  -- ── 1. busy daemon still lists correctly ──────────────────────────────────
  let _ ← e.cli #["run", "busy", "echo hi"]
  IO.sleep 1000
  -- captured while the daemon is still HEALTHY, before the SIGSTOP: `info` has to
  -- be answered for `Env.daemonPid` to work. Aborts rather than printing a check:
  -- with no pid there is nothing below this line left to mean anything.
  let some dpid ←
    e.daemonPid "busy" | throw (IO.userError "no daemon answered for 'busy' — nothing to SIGSTOP")
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
  let expected :=
    humanListing
      [rowFields "busy"
          [("state", "live"), ("status", Linger.Core.Status.name (rowStatus (.live [])))]]
  f :=
    f +
      (←
        expect (out.toUTF8.toList == expected)
            s!"busy daemon lists under its name, marked unknown (got '{out.trimAscii.toString}')")
  let recs := records porc
  f :=
    f +
      (←
        expect
            (recs.contains ("name", "busy") &&
              recs.contains ("status", Linger.Core.Status.name Status.unknown))
            "porcelain carries the name for a busy daemon")
  f := f + (← expect (socks == ["busy.sock"]) s!"busy daemon keeps its socket ({socks})")
  IO.sleep 400
  f :=
    f +
      (←
        expect ((← e.cli #["send", "busy", "echo x\n"]).1 == 0)
            "busy daemon still reachable afterwards")
  e.killAll #["busy"]
  IO.sleep 500
  -- ── 2. stale socket + concurrent starts -> one owner ──────────────────────
  -- The name is unique to this run so the `ps` scan below cannot see a developer's
  -- own session of the same name (see the module docstring), the same trick
  -- `Env.make` already uses for the directory.
  let claim := s!"claim-{← Linger.Posix.getpid}"
  let _ ← e.cli #["run", claim, "echo one"]
  IO.sleep 1000
  unless (← e.crashDaemon claim) do
    throw (IO.userError s!"daemon for '{claim}' did not crash")
  let stale ← e.dirNames ".sock"
  f := f + (← expect (stale == [s!"{claim}.sock"]) s!"stale socket present for the race ({stale})")
  -- eight concurrent `run <name>`, spawned before any is waited on
  let cfg : IO.Process.SpawnArgs :=
    { cmd := e.bin, args := #["run", claim, "echo two"], env := e.procEnv, stdin := .null,
      stdout := .null, stderr := .null }
  let kids ← (List.range 8).mapM fun _ => IO.Process.spawn cfg
  for k in kids do
    let _ ← k.wait
  IO.sleep 1500
  let ps ← psTable
  let owners :=
    ps.filterMap fun (pid, _, args) => if has args s!"__daemon {claim}" then some pid else none
  let shells := ps.filter fun (_, ppid, args) => owners.contains ppid && has args "/bin/sh"
  f :=
    f + (← expect (owners.length == 1) s!"exactly one daemon owns the name (got {owners.length})")
  f := f + (← expect (shells.length == 1) s!"exactly one shell (got {shells.length})")
  f :=
    f +
      (←
        expect ((← e.cli #["send", claim, "echo y\n"]).1 == 0) "the surviving session is reachable")
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
  if lockFd ≥ 0 then
    Linger.Posix.close (UInt32.ofNat lockFd.toNatClampNeg)
  f :=
    f +
      (←
        expect (locks.contains s!"{claim}.lock" && lockFd == -1)
            s!"ownership lock file present ({locks})")
  e.killAll #[claim]
  IO.sleep 500
  -- the lock must be re-acquirable once the owner is gone (kernel released it)
  let _ ← e.cli #["run", claim, "echo three"]
  IO.sleep 1000
  let owners2 :=
    (← psTable).filterMap fun (pid, _, args) =>
      if has args s!"__daemon {claim}" then some pid else none
  f :=
    f +
      (← expect (owners2.length == 1) "name is re-claimable after the owner exits (no stale lock)")
  e.killAll #[claim]
  IO.sleep 500
  -- ── 3. a child that stops reading cannot grow the daemon ──────────────────
  -- `sleep` never reads its stdin, so the pty master's input buffer fills and
  -- `flushPty` stops draining; every `.input` frame after that would append
  -- forever without the `ptyInCap` cap. Input goes in over a raw control
  -- connection (no `.attach`), which `Session.onMsg .input` routes to `.writePty`.
  --
  -- The payload is newline-terminated lines, not one long run of 'x', and that is
  -- load-bearing on macOS: there a nonblocking write of an unterminated blob to a
  -- pty master whose slave is not reading *succeeds* forever (measured: 98 MB in
  -- 3 s), because the BSD tty layer discards an over-long canonical line instead
  -- of pushing back, so `ptyIn` never grew and the cap never tripped. With lines
  -- it is EAGAIN after ~1 KB, as on Linux.
  let _ ← e.cli #["run", "stall", "sleep", "600"]
  IO.sleep 1000
  -- only whether a daemon answers matters here, not its pid
  let sp ← e.daemonPid "stall"
  if sp.isSome then
    let r ← Linger.Posix.unixConnect s!"{e.dir}/stall.sock"
    let sock := UInt32.ofNat r.toNatClampNeg
    -- the frame is built by the implementation's own codec: `.input` is
    -- `Wire.Msg.tag 0` and the length is `Wire.writeU32`, so a tag renumbering is
    -- a compile-time fact here instead of a silently-ignored frame. 262144 B is
    -- `Wire.maxPayload` exactly — the largest legal frame, which is what makes 64
    -- of them ~4x the cap.
    let payload := (List.replicate 4096 (List.replicate 63 (0x78 : UInt8) ++ [0x0A])).flatten
    let frame := ByteArray.mk (Linger.Core.Wire.encode (.input payload)).toArray
    for _ in List.range 64 do -- 16 MiB, ~4x the cap
      Linger.Posix.writeAll sock frame
    Linger.Posix.close sock
    -- the daemon logs the cap once on the transition into backpressure; its stderr
    -- is an O_APPEND file, so give the write a moment to land. The reported
    -- pending count is the bounded-buffer property itself — a full buffer that
    -- stayed <= cap is exactly "the child could not grow us".
    let logf := s!"{e.dir}/logs/stall.log"
    let readLog : IO String := do
      try
        IO.FS.readFile logf
      catch _ =>
        pure ""
    let _ ← waitFor 4000 (return (parseFull (← readLog)).isSome)
    let log ← readLog
    let m := parseFull log
    f := f + (← expect m.isSome "daemon reports the full input buffer")
    -- …and the cap it reports is `Daemon.ptyInCap`, not merely some number it also
    -- compared itself against
    f :=
      f +
        (←
          expect (m.any fun (p, c) => p ≤ c && c == ptyInCap)
              "pending stayed within the cap, and the cap is Daemon.ptyInCap")
    f := f + (← expect (countFull log == 1) "logged once on the edge, not per dropped chunk")
    f :=
      f +
        (←
          expect ((← e.cli #["send", "stall", "echo x\n"]).1 == 0)
              "the stalled session is still reachable")
    e.killAll #["stall"]
    IO.sleep 500
  else
    f := f + (← expect false "stall daemon started")
  -- ── 4. a held ownership lock makes a failed connect non-stale ─────────────
  let heldName := "lock-held"
  let heldSocket := s!"{e.dir}/{heldName}.sock"
  let heldLock ← Linger.Posix.flock s!"{e.dir}/{heldName}.lock"
  if heldLock < 0 then
    throw (IO.userError "could not acquire lock-held test lock")
  IO.FS.writeFile heldSocket "not-a-socket" -- failed connect while the name is owned
  let (heldRc, heldOut, heldErr) ← e.cli #["list"]
  let heldSocks ← e.dirNames ".sock"
  f :=
    f +
      (←
        expect (heldRc == 0 && heldSocks.contains s!"{heldName}.sock" && has heldOut heldName)
            s!"list preserves a failed-connect owned socket (rc={heldRc}, sockets={heldSocks}, out='{heldOut}', err='{heldErr}')")
  Linger.Posix.close heldLock.toUInt64.toUInt32
  try
    IO.FS.removeFile heldSocket
  catch _ =>
    pure ()
  -- ── 5. info has an absolute deadline, not a silence deadline ──────────────
  let streamPath := s!"{e.dir}/streaming.sock"
  let streamReady := s!"{e.dir}/streaming.ready"
  let self ← IO.appPath
  let streamServer ←
    IO.Process.spawn
        { cmd := self.toString, args := #["--stream-info-server", streamPath, streamReady],
          stdout := .null, stderr := .null }
  unless (← waitFor 5000 (System.FilePath.pathExists streamReady)) do
    throw (IO.userError "streaming info server did not become ready")
  let t0 ← Linger.Posix.monotonicMs
  let listing ←
    IO.Process.spawn
        { cmd := e.bin, args := #["list"], env := e.procEnv, stdout := .null, stderr := .null }
  let listCode ← waitProcess listing 3500
  let elapsed := (← Linger.Posix.monotonicMs) - t0
  if listCode.isNone then
    listing.kill
    let _ ← listing.wait
  let streamCode ← waitProcess streamServer 3000
  if streamCode.isNone then
    streamServer.kill
    let _ ← streamServer.wait
  f :=
    f +
      (←
        expect (listCode == some 0 && elapsed < 3500 && streamCode == some 0)
            s!"continuous info traffic cannot extend the request deadline ({elapsed}ms)")
  -- ── 6. one listener round accepts at most the pure roster cap ─────────────
  let acceptPath := s!"{e.dir}/accept-bound.sock"
  let lfd ← Linger.Posix.unixListen acceptPath
  Linger.Posix.setNonblock lfd
  let (sleepPid, ptyFd) ← Linger.Posix.spawnPty 80 24 "" "sleep" #["600"] #[]
  Linger.Posix.setNonblock ptyFd
  let mut peers : Array UInt32 := #[]
  for _ in List.range (2 * maxClients) do
    let fd ← Linger.Posix.unixConnect acceptPath
    if fd ≥ 0 then
      peers := peers.push fd.toUInt64.toUInt32
  let rt : Linger.Runtime.Daemon.Rt :=
    { st := Linger.Core.Session.State.boot (Linger.Core.Vt.Vt.init 80 24) [] [], listenFd := lfd,
      ptyFd, childPid := sleepPid, sockPath := acceptPath, saveCkpt := fun _ => pure (),
      dropCkpt := pure () }
  let (bounded, connected) ← Linger.Runtime.Daemon.pollRound rt
  f :=
    f +
      (←
        expect
            (peers.size == 2 * maxClients && bounded.conns.length ≤ maxClients &&
              connected.length ≤ maxClients)
            s!"one poll round accepts at most maxClients ({bounded.conns.length})")
  for c in bounded.conns do
    Linger.Posix.close c.fd
  for fd in peers do
    Linger.Posix.close fd
  Linger.Posix.close lfd
  Linger.Posix.close ptyFd
  Linger.Posix.kill sleepPid 9
  IO.sleep 100
  let _ ← Linger.Posix.waitpidNohang sleepPid
  try
    IO.FS.removeFile acceptPath
  catch _ =>
    pure ()
  -- ── 7. the slow-client output cut is wired into the real runtime ──────────
  let cutPath := s!"{e.dir}/output-cut.sock"
  let cutListen ← Linger.Posix.unixListen cutPath
  let cutPeerRaw ← Linger.Posix.unixConnect cutPath
  let cutFdRaw ← Linger.Posix.accept cutListen
  let cutPeer := cutPeerRaw.toUInt64.toUInt32
  let cutFd := cutFdRaw.toUInt64.toUInt32
  Linger.Posix.setNonblock cutFd
  let id := cutFd.toNat
  let st0 := Linger.Core.Session.State.boot (Linger.Core.Vt.Vt.init 80 24) [] []
  let st := (Linger.Core.Session.step st0 (.connected id)).1
  let full := ByteArray.mk (Array.replicate outbufCap (0 : UInt8))
  let q := (Linger.Core.Buf.bufEnqueue outbufCap .empty full).1
  let cutRt : Linger.Runtime.Daemon.Rt :=
    { st, listenFd := cutListen, ptyFd := cutFd, childPid := 1,
      conns := [{ fd := cutFd, out := q }], sockPath := cutPath, saveCkpt := fun _ => pure (),
      dropCkpt := pure () }
  let (cutRt', follow) ← Linger.Runtime.Daemon.runEffect cutRt (.send id .done)
  let peerEof ← Linger.Posix.read cutPeer 1
  let pumped ← Linger.Runtime.Daemon.pump cutRt' follow
  let attached := (Linger.Core.Session.infoFields pumped.st).find? (·.1 == "clients") |>.map (·.2)
  let closed :=
    match follow with
    | [.closed got] => got == id
    | _ => false
  f :=
    f +
      (←
        expect
            (Linger.Core.Buf.owedLen q == outbufCap && (cutRt'.conn? cutFd).isNone && closed &&
              peerEof.isNone &&
              attached == some "0")
            "crossing outbufCap closes the peer and feeds .closed into the session")
  Linger.Posix.close cutPeer
  Linger.Posix.close cutListen
  try
    IO.FS.removeFile cutPath
  catch _ =>
    pure ()
  -- ── 8. cancelling an unread reply cannot kill the session ────────────────
  let resetName := "peer-reset"
  try
    let _ ← e.cli #["run", resetName, "true"]
    let initialPid ← e.info resetName "pid"
    let raw ← Linger.Posix.unixConnect s!"{e.dir}/{resetName}.sock"
    unless raw ≥ 0 do
      throw (IO.userError "unread-reply peer could not connect")
    let fd := raw.toUInt64.toUInt32
    let ready ←
      try
        Linger.Posix.writeAll fd (ByteArray.mk (Linger.Core.Wire.encode .info).toArray)
        let revs ← Linger.Posix.poll #[fd] #[Linger.Posix.POLLIN] 3000
        pure (revs[0]! &&& Linger.Posix.POLLIN != 0)
      finally
        Linger.Posix.close fd
    -- The echoed input does not contain the contiguous output marker.
    let sent ← e.cliTimeout #["send", resetName, "printf 'PEER-%s\\n' 'ALIVE'\n"] 3000
    let ran ←
      waitFor 3000 do
          let captured ← e.cliTimeout #["capture", resetName] 1000
          return captured.any fun (rc, text, _) => rc == 0 && has text "PEER-ALIVE"
    let finalPid ← e.info resetName "pid"
    f :=
      f +
        (←
          expect
              (ready && initialPid.isSome && finalPid == initialPid &&
                sent.any (fun (rc, _, _) => rc == 0) &&
                ran)
              "closing a peer with an unread reply preserves the same usable session shell")
  finally
    e.killAll #[resetName]
  f := f + (← failedDiagnostics)
  f := f + (← admissionPressure e)
  verdict e f

end E2E.Robust
