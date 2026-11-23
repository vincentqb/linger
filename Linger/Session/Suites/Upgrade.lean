module

public import Verify.Harness
import Linger.Session.CoreCode.Build
import Linger.Session.CoreCode.Wire

public section

/-! # Linger.Session.Suites.Upgrade — a session moves onto a new binary, its program running on

`linger upgrade` asks each daemon to replace its own image with the binary that asked, in place,
by an exec that keeps the daemon's process, its program and its descriptors (`Os.Exec.Keeps`),
and the new image resumes from the handoff (`handoff_carries`). The program sees nothing: the
suite's program reports, every tenth of a second, a counter, its parent and its terminal, and
the client attached across the upgrade receives every line once, in order, from the same
parent on the same terminal; a waiter keeps waiting and hears the real ending; keystrokes reach
a program after it as before. The upgrade's target is a second copy of the built binary, so
the daemon's image is seen to change. A target that names no format this version writes,
cannot be run, or fails leaves the daemon serving, as it was (`upgrade_probes`), and a daemon
whose `info` names no handoff format is reported as started by an older linger, never asked.

A writable attach by a binary of a higher build hands the daemon over to that binary first
(`attach_upgrades`). The suite makes a binary of build 0 by rewriting the digits of the built
binary's stamp in a copy (`copyAsBuildZero`), and that copy starts the sessions: an attach by the
built binary hands its daemon over, in the same process, the program keeping its pid and a client
attached across it every line; an attach by an equal build or a lower one, a read-only attach,
`ls` and `capture` leave the daemon as it is; and a daemon that refuses, here because its program
stopped inside a control sequence, serves on as it was, while the attach says why on one line and
attaches. -/

namespace Linger.Session.Suites.Upgrade

open Verify.Harness
open Os.Shell

/-- The program the session runs: one line `tick:<n>:<parent>:<terminal>` every tenth of a
second, with no blank in it, so the client's repaint of a row shows it as written. -/
def ticker : String :=
  "i=0; while :; do i=$((i+1)); echo \"tick:$i:$(ps -o ppid= -p $$ | tr -d ' '):$(tty)\"; " ++
    "sleep 0.1; done"

/-- The ticks a client's output shows, in order: each counter with the parent and terminal its
line named, less the blanks a repaint draws after it. A line cut short by the end of the output
is left out. -/
def ticks (text : String) : List (Nat × String × String) :=
  (text.splitOn "tick:").drop 1 |>.filterMap fun piece =>
    match
      (piece.takeWhile (fun c => c != '\r' && c != '\n' && c != '\x1b')).toString.splitOn ":" with
    | [n, parent, tty] =>
      if piece.contains '\n' || piece.contains '\r' then
        n.toNat?.map fun n => (n, parent, tty.trimAscii.toString)
      else none
    | _ => none

/-- Whether each counter is one more than the one before it. -/
def consecutive : List Nat → Bool
  | a :: b :: rest => b == a + 1 && consecutive (b :: rest)
  | _ => true

/-- `linger <args>` run as the binary at `bin`, in the suite's state directory, within
`hangMs`: its status, standard output and standard error, `none` when it did not end. -/
def runAs (e : Env) (bin : String) (args : Array String) : IO (Option (UInt32 × String × String)) :=
  do
  let child ←
    IO.Process.spawn
        { cmd := bin, args, env := e.procEnv, stdin := .null, stdout := .piped, stderr := .piped }
  let out ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
  let err ← IO.asTask child.stderr.readToEnd Task.Priority.dedicated
  match ← waitProcess child hangMs with
  | none =>
    reapOrKill child 0
    return none
  | some code =>
    let text (t : Task (Except IO.Error String)) : IO String := do
      match ← IO.wait t with
      | .ok s =>
        return s
      | .error _ =>
        return ""
    return some (code, ← text out, ← text err)

/-- The binary the process `pid` runs, from `/proc`; `none` where there is none. -/
def imageOf (pid : UInt32) : IO (Option String) := do
  unless ← System.FilePath.pathExists "/proc/self/exe" do
    return none
  try
    return some (← IO.FS.realPath s!"/proc/{pid}/exe").toString
  catch _ =>
    return some ""

/-- Ask the daemon behind `socket` for an upgrade to `target` over the wire, as `linger upgrade`
does: `some why` for a refusal, `none` for `done`, and `some ""` for no answer within
`hangMs`. -/
def askUpgrade (socket target : String) : IO (Option String) := do
  let r ← unixConnect socket
  if r < 0 then
    return some "no daemon answers"
  let fd := r.toUInt64.toUInt32
  try
    writeAll fd (ByteArray.mk (Linger.Session.Wire.encode (.upgrade target.toUTF8.toList)).toArray)
    let deadline := (← monotonicMs) + hangMs
    let mut decoder : Linger.Session.Wire.Decoder := {}
    while (← monotonicMs) < deadline do
      let revs ← poll #[fd] #[POLLIN] 100
      if revs[0]! &&& (POLLIN ||| POLLHUP ||| POLLERR) == 0 then
        continue
      let some bytes ← read fd 65536 | return some "the connection closed"
      let (next, msgs) := decoder.feed bytes.toList
      decoder := next
      for m in msgs do
        match m with
        | .done =>
          return none
        | .err why =>
          return some (String.fromUTF8? (ByteArray.mk why.toArray) |>.getD "?")
        | _ =>
          pure ()
    return some ""
  finally
    close fd

/-- A daemon an older linger started, as far as `upgrade` asks it: it answers one `info` with
the fields of a level-4 daemon, which name no handoff format, and then nothing. -/
def olderDaemon (socket : String) : IO Unit := do
  let lfd ← unixListen socket
  try
    setNonblock lfd
    let some fd ← acceptWithin lfd hangMs | return
    try
      -- the request: whatever the client sends first, once it arrives
      discard <| poll #[fd] #[POLLIN] hangMs.toInt32
      discard <| read fd 65536
      let reply := "pid\t1\nprotocol\t4\nversion\t0.1\n".toUTF8.toList
      writeAll fd (ByteArray.mk (Linger.Session.Wire.encode (.infoReply reply)).toArray)
      writeAll fd (ByteArray.mk (Linger.Session.Wire.encode .done).toArray)
      -- the client reads the answer and leaves
      discard <| drain fd hangMs
    finally
      close fd
  finally
    close lfd

/-- Where `needle` first begins in `hay`, at `start` or later. -/
def indexOf (hay needle : ByteArray) (start : Nat := 0) : Option Nat :=
  Id.run do
    for i in [start:hay.size + 1 - needle.size] do
      if (List.range needle.size).all fun j => hay.get! (i + j) == needle.get! j then
        return some i
    return none

/-- The places a binary's bytes hold the stamp `Linger.Session.Build.stamp`: where each run of
its digits begins, and how many digits it has. -/
def stampsIn (bytes : ByteArray) : List (Nat × Nat) :=
  Id.run do
    let marker := "linger-build:".toUTF8
    let mut found : List (Nat × Nat) := []
    let mut pos := 0
    -- a binary holds its stamp once, or a few times where the compiler copies a literal
    for _ in [0:8] do
      let some i := indexOf bytes marker pos | break
      let start := i + marker.size
      let mut len := 0
      for k in [start:bytes.size] do
        let c := bytes.get! k
        if c < 48 || c > 57 then
          break
        len := len + 1
      found := found ++ [(start, len)]
      pos := start + len
    return found

/-- Write to `dst` a copy of the linger binary at `src` that is build 0: each run of its stamp's
digits rewritten as zeros, as many as there were, which `Linger.Session.Build.number` reads as 0
when the copy runs. macOS refuses to run a binary whose bytes no longer match its signature, so
there the copy is signed again, ad hoc, as the linker signed it. Whether `src` held a stamp. -/
def copyAsBuildZero (src dst : String) : IO Bool := do
  let bytes ← IO.FS.readBinFile src
  let places := stampsIn bytes
  if places.isEmpty || places.any (·.2 == 0) then
    return false
  let mut out := bytes
  for (start, len) in places do
    for j in [0:len] do
      out := out.set! (start + j) 48
  IO.FS.writeBinFile dst out
  discard <| IO.Process.output { cmd := "chmod", args := #["+x", dst] }
  if System.Platform.isOSX then
    discard <| IO.Process.output { cmd := "codesign", args := #["--force", "--sign", "-", dst] }
  return true

/-- `linger <args>` run as the binary at `bin` on a pty of 80 by 24, in the suite's state
directory, as `Env.spawn` runs the built binary. -/
def spawnAs (e : Env) (bin : String) (args : Array String) : IO Client := do
  let (pid, fd) ← spawnPty 80 24 "" bin args e.ptyEnv
  return { pid, fd }

/-- The upgrade suite. -/
def run : IO UInt32 :=
  Env.suite "upgrade" fun e => do
    let next := s!"{e.dir}/linger-next"
    discard <| IO.Process.output { cmd := "cp", args := #[e.bin, next] }
    -- the program titles its window, which the session keeps across the upgrade
    let (startRc, _, _) ←
      e.cli #["start", "u", "/bin/sh", "-c", "printf '\\033]2;carried over\\007'; " ++ ticker]
    let (catRc, _, _) ← e.cli #["start", "c", "/bin/cat"]
    let labelRc : UInt32 := 0
    let pidBefore ← e.info "u" "pid"
    let daemonBefore ← e.daemonPid "u"
    let catDaemon ← e.daemonPid "c"
    let client ← e.spawn #["attach", "u"]
    let seen ← IO.mkRef ByteArray.empty
    let started ←
      client.awaitText seen (fun b => (ticks (String.fromUTF8? b |>.getD "")).length ≥ 3)
    let waiter ←
      IO.Process.spawn
          { cmd := e.bin, args := #["wait", "u"], env := e.procEnv, stdin := .null, stdout := .null,
            stderr := .piped }
    let (sendRc, _, _) ← e.cli #["send", "c", "before\n"]
    discard <|
        waitFor patienceMs do
          return has (← e.out #["capture", "c"]) "before"
    -- every live session, the ticker and the cat, moves onto the second copy
    let upgraded ← runAs e next #["upgrade"]
    let (upRc, upOut, upErr) := upgraded.getD (999, "", "")
    let lastAt := ((ticks (String.fromUTF8? (← seen.get) |>.getD "")).getLast?.map (·.1)).getD 0
    let after ←
      client.awaitText seen (ms := hangMs) fun b =>
          (ticks (String.fromUTF8? b |>.getD "")).any (·.1 ≥ lastAt + 20)
    expect
        (startRc == 0 && catRc == 0 && labelRc == 0 && started && upRc == 0 &&
          has upOut "upgraded u" &&
          has upOut "upgraded c")
        s!"upgrade with no name moves every live session onto the binary that asked \
          ({upRc}: {upOut} {upErr})"
    let shown := ticks (String.fromUTF8? (← seen.get) |>.getD "")
    let counters := shown.map (·.1)
    expect (after && consecutive counters && (counters.getLast?.getD 0) ≥ lastAt + 20)
        s!"the attached client receives every line of the program's output once, in order, \
          across the upgrade (upgraded after {lastAt}: {counters})"
    let parents := (shown.map (·.2.1)).eraseDups
    expect
        (daemonBefore.isSome && parents == [toString (daemonBefore.getD 0)] &&
          (← e.daemonPid "u") == daemonBefore &&
          (← e.info "u" "pid") == pidBefore)
        s!"the program keeps its pid and its parent, the daemon, whose pid stays its own \
          ({parents})"
    let terminals := (shown.map (·.2.2)).eraseDups
    expect (terminals.length == 1 && terminals.all (·.startsWith "/dev/"))
        s!"the program keeps its terminal ({terminals})"
    let image ← imageOf (daemonBefore.getD 0)
    expectMeasured image.isSome (image.all (· == next))
        s!"the daemon runs the binary that asked ({image})"
    expect (!(← System.FilePath.pathExists s!"{e.dir}/logs/u.handoff"))
        "the new image removes the handoff it took"
    expect ((← e.info "u" "title") == some "carried over") "the session's title is carried over"
    let (sendAfterRc, _, _) ← e.cli #["send", "c", "after\n"]
    let echoed ←
      waitFor patienceMs do
          return has (← e.out #["capture", "c"]) "after"
    expect (sendRc == 0 && sendAfterRc == 0 && echoed && (← e.daemonPid "c") == catDaemon)
        "keystrokes reach the program after the upgrade as before"
    expect
        ((← client.ending 0).isNone && !hasText (← seen.get) "ended" &&
          !hasText (← seen.get) "lost")
        "the attached client is not told the session ended, and stays attached"
    expect ((← waitProcess waiter 0).isNone) "a waiter keeps waiting across the upgrade"
    -- targets that do not take the handoff leave the daemon serving, as it was
    let refuses := s!"{e.dir}/refuses"
    IO.FS.writeFile refuses "#!/bin/sh\necho 99\n"
    let fails := s!"{e.dir}/fails"
    IO.FS.writeFile fails "#!/bin/sh\nexit 1\n"
    for script in [refuses, fails] do
      discard <| IO.Process.output { cmd := "chmod", args := #["+x", script] }
    let socket := s!"{e.dir}/u.sock"
    let mut refusals : List (Option String) := []
    for target in [refuses, fails, s!"{e.dir}/missing"] do
      refusals := refusals ++ [← askUpgrade socket target]
    let before := (ticks (String.fromUTF8? (← seen.get) |>.getD "")).getLast?.map (·.1)
    let kept ←
      client.awaitText seen (ms := hangMs) fun b =>
          (ticks (String.fromUTF8? b |>.getD "")).any (·.1 ≥ (before.getD 0) + 5)
    let imageAfter ← imageOf (daemonBefore.getD 0)
    expect
        (refusals.all (·.any (fun why => has why "keeps running")) && kept &&
          consecutive ((ticks (String.fromUTF8? (← seen.get) |>.getD "")).map (·.1)) &&
          (← e.daemonPid "u") == daemonBefore &&
          imageAfter.all (· == next))
        s!"a target that names no format this one writes, fails or cannot be run is refused, \
          and the daemon serves on as it was ({refusals})"
    -- a daemon an older linger started is never asked
    let older ← IO.asTask (olderDaemon s!"{e.dir}/old.sock") Task.Priority.dedicated
    discard <|
        waitFor patienceMs do
          System.FilePath.pathExists s!"{e.dir}/old.sock"
    let oldAnswer ← runAs e next #["upgrade", "old"]
    discard <| IO.wait older
    expect
        (oldAnswer.any fun (rc, _, err) =>
          rc != 0 && has err "started by an older linger; it keeps running")
        s!"a daemon an older linger started is reported as such and keeps running ({oldAnswer})"
    -- the session's real ending reaches the client and the waiter
    let (killRc, _, _) ← e.cli #["kill", "u"]
    let waited ← waitProcess waiter hangMs
    expect (killRc == 0 && waited == some 129 && (← client.ending patienceMs).isSome)
        s!"the waiter and the client hear the session's real ending, once it ends ({waited})"
    client.bye false
    reapOrKill waiter 0
    e.killAll #["c"]
    -- an attach by a binary of a higher build hands the session's daemon over to that binary
    -- first: a copy of build 0 starts the ticker, and a client of its own build watches it
    let older := s!"{e.dir}/linger-older"
    let stamped ← copyAsBuildZero e.bin older
    let built := toString Linger.Session.Build.number
    let builtImage := (← IO.FS.realPath e.bin).toString
    let olderImage ←
      if stamped then
        pure (← IO.FS.realPath older).toString
      else
        pure ""
    let aStart ← runAs e older #["start", "a", "/bin/sh", "-c", ticker]
    let aDaemon ← e.daemonPid "a"
    let aPid ← e.info "a" "pid"
    let aBuild ← e.info "a" "build"
    let aImage ← imageOf (aDaemon.getD 0)
    expect (stamped && aStart.any (·.1 == 0) && aBuild == some "0" && aImage == some olderImage)
        s!"a copy whose stamp says build 0 reports build 0, and its session's daemon runs it \
          ({aBuild}, {aImage})"
    let watcher ← spawnAs e older #["attach", "a"]
    let watched ← IO.mkRef ByteArray.empty
    let watching ←
      watcher.awaitText watched (fun b => (ticks (String.fromUTF8? b |>.getD "")).length ≥ 3)
    let typist ← e.spawn #["attach", "a"]
    let typed ← IO.mkRef ByteArray.empty
    let attached ←
      typist.awaitText typed (ms := hangMs) fun b =>
          (ticks (String.fromUTF8? b |>.getD "")).length ≥ 2
    let handed ←
      waitFor patienceMs do
          return (← e.info "a" "build") == some built
    let lastAt := ((ticks (String.fromUTF8? (← watched.get) |>.getD "")).getLast?.map (·.1)).getD 0
    let carried ←
      watcher.awaitText watched (ms := hangMs) fun b =>
          (ticks (String.fromUTF8? b |>.getD "")).any (·.1 ≥ lastAt + 10)
    let shown := ticks (String.fromUTF8? (← watched.get) |>.getD "")
    expect
        (watching && attached && handed && (← imageOf (aDaemon.getD 0)) == some builtImage &&
          (← e.daemonPid "a") == aDaemon)
        s!"a writable attach by a higher build hands the daemon over to its own binary first: the \
          daemon, in the same process, runs that binary and reports its build \
          ({← e.info "a" "build"}, {← imageOf (aDaemon.getD 0)})"
    expect
        (carried && consecutive (shown.map (·.1)) && (← e.info "a" "pid") == aPid &&
          (shown.map (·.2.1)).eraseDups == [toString (aDaemon.getD 0)])
        s!"the program keeps its pid and its parent, and a client attached across the hand-over \
          receives every line once, in order ({shown.map (·.1)})"
    expect (!hasText (← typed.get) "kept the older daemon")
        "a hand-over the daemon takes says nothing"
    typist.bye
    watcher.bye
    -- an attach by an equal build or a lower one hands nothing over
    let same := s!"{e.dir}/linger-same"
    discard <| IO.Process.output { cmd := "cp", args := #[e.bin, same] }
    let mut leftAsIs := true
    for bin in [same, older] do
      let viewer ← spawnAs e bin #["attach", "a"]
      let seen ← IO.mkRef ByteArray.empty
      let looked ← viewer.awaitText seen fun b => (ticks (String.fromUTF8? b |>.getD "")).length ≥ 2
      viewer.bye
      leftAsIs := leftAsIs && looked && !hasText (← seen.get) "kept the older daemon"
    expect
        (leftAsIs && (← imageOf (aDaemon.getD 0)) == some builtImage &&
          (← e.info "a" "build") == some built)
        s!"an attach by an equal build or a lower one leaves the daemon as it is, and says nothing \
          ({← imageOf (aDaemon.getD 0)})"
    -- a read-only attach, `ls` and `capture` by a higher build ask for nothing
    let wStart ← runAs e older #["start", "w", "/bin/cat"]
    let wDaemon ← e.daemonPid "w"
    let reader ← e.spawn #["attach", "--read-only", "w"]
    let reading ←
      waitFor patienceMs do
          return (← e.info "w" "clients") == some "1"
    reader.bye
    let (lsRc, _, _) ← e.cli #["ls"]
    let (captureRc, _, _) ← e.cli #["capture", "w"]
    expect
        (wStart.any (·.1 == 0) && reading && lsRc == 0 && captureRc == 0 &&
          (← e.info "w" "build") == some "0" &&
          (← imageOf (wDaemon.getD 0)) == some olderImage)
        s!"a read-only attach, `ls` and `capture` by a higher build leave the daemon as it is \
          ({← e.info "w" "build"})"
    -- a hand-over the daemon refuses, here because its program stopped inside a control sequence,
    -- says why on one line, and the attach goes on
    let rStart ←
      runAs e older #["start", "r", "/bin/sh", "-c", "printf 'r-ready\\033['; exec sleep 600"]
    let rDaemon ← e.daemonPid "r"
    let rReady ←
      waitFor patienceMs do
          return has (← e.out #["capture", "r"]) "r-ready"
    let refusing ← e.spawn #["attach", "r"]
    let rSeen ← IO.mkRef ByteArray.empty
    let rShown ← refusing.awaitText rSeen (ms := hangMs) fun b => hasText b "r-ready"
    let rText := String.fromUTF8? (← rSeen.get) |>.getD ""
    let told := (rText.splitOn "kept the older daemon: ").length - 1
    refusing.bye
    expect
        (rStart.any (·.1 == 0) && rReady && rShown && told == 1 &&
          has rText "partway through a control sequence")
        s!"a hand-over the daemon refuses says why on one line, and the attach goes on ({told})"
    expect ((← e.info "r" "build") == some "0" && (← imageOf (rDaemon.getD 0)) == some olderImage)
        "the daemon that refused the hand-over serves on as it was"
    e.killAll #["a", "w", "r"]

end Linger.Session.Suites.Upgrade
