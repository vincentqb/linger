module

public import Verify.Harness
import Linger.App.CoreCode.Wait
import Linger.Display.CoreCode.Alert
import Linger.Display.CoreCode.Status
import Linger.Session.WorldCode.Client
import Linger.Session.WorldCode.Daemon
import Linger.Session.CoreCode.Checkpoint
import Linger.Session.CoreCode.Wire
import Linger.Target.CoreCode.Name
public import Linger.Session.CoreSpec

public section

/-! # Linger.Session.Suites.Attach — attach, detach, reattach, mirror, wait, hand-back, scrollback

The core session lifecycle plus the two things a client owes the user's terminal on
the way in and out.

The hand-back is compared against the emitter, not a copy of it: every expected
sequence is `Render.modeSet` / `csiNum` / `csiPlain` / `escSeq` / `escCharset` of
the same argument `leaveAnsi` passes, and the ST check also requires `leaveAnsi`
**verbatim** (`hasBytes back leaveAnsi`). The per-sequence loop is kept for failure
localisation: green sequence lines plus a red `verbatim` line means the right
sequences in the wrong order or spacing, which one whole-blob comparison could not
tell you.

WHAT COULD NOT BE DERIVED: the printf'd full-screen-app state in check 9 is the
*application's* bytes, not linger's, so `modeSet 1049 true` and `csiNum2 5 10 0x72`
are used only as spellers for two standard sequences — that is not a tie to an
emitter, and it should not be read as one. -/

namespace Linger.Session.Suites.Attach

open Terminal
open Verify.Harness
open Terminal.Render (leaveAnsi modeSet csiNum csiNum2 csiPlain escSeq escCharset titleAnsi
  shapeAnsi)
open Terminal.Vt (Vt)
open Linger.Session (outputChunk)
open Linger.Session.Shell.Daemon (outbufCap)

/-- Drive the actual effect interpreter with real sockets and counted checkpoint
hooks. Keeping the roster in this process prevents a reconnect from reusing the
closed fd and accidentally hiding a phantom attached client. -/
def closeFeedback (e : Env) : IO Unit := do
  let path := s!"{e.dir}/close-feedback.sock"
  let listener ← Os.Shell.unixListen path
  try
    for exiting in [false, true] do
      let peer ← Os.Shell.unixConnect path
      let accepted ← Os.Shell.accept listener
      if peer < 0 || accepted < 0 then
        throw (IO.userError "close-feedback socket was not accepted")
      let fd := accepted.toUInt64.toUInt32
      let saved ← IO.mkRef (0 : Nat)
      let dropped ← IO.mkRef (0 : Nat)
      let st :=
        (Linger.Session.run (.boot (Terminal.Vt.Vt.init 20 5) [] [])
            [.connected fd.toNat,
              .bytes fd.toNat (Linger.Session.Wire.encode (.attach .writable 20 5)),
              .ptyOut "pending checkpoint".toUTF8.toList]).1
      let rt : Linger.Session.Shell.Daemon.Rt :=
        { st, listenFd := listener, ptyFd := 0, childPid := 0, conns := [{ fd }],
          saveCkpt := fun _ => saved.modify (· + 1), dropCkpt := dropped.modify (· + 1) }
      try
        let events :=
          if exiting then [.childExited (.exited 0), .tick Linger.Session.ckptIntervalMs]
          else [.bytes fd.toNat (Linger.Session.Wire.encode .detachAll)]
        let after ← Linger.Session.Shell.Daemon.pump rt events
        -- saves run on their own thread; wait for them as the daemon does before exiting
        let after ← Linger.Session.Shell.Daemon.finishSaves after
        let clients := (Linger.Session.infoFields after.st).lookup "clients"
        if exiting then
          -- the attached client saw the end, which deletes the checkpoint once; the queued
          -- tick, which would save the pending change, is discarded with the rest of the queue
          expect (after.exiting && (← saved.get) == 0 && (← dropped.get) == 1)
              "child exit seen by an attached client deletes the checkpoint once and discards \
                queued events"
        else
          expect (clients == some "0" && after.conns.isEmpty && (← saved.get) == 1)
              "detach-all removes the size owner and checkpoints the last detach"
      finally
        Os.Shell.close peer.toUInt64.toUInt32
  finally
    Os.Shell.close listener
    IO.FS.removeFile path

/-- The hazards `leaveAnsi` undoes, each spelled with the emitter's own primitive
and the same argument `leaveAnsi` passes it — so this list cannot become a stale
copy of the emitter. Every group must appear in the epilogue.

From `Render.leaveAnsi`'s docstring, which is where the *reasons* live: a shell
that inserts instead of overwriting, addresses relative to a stale region, does
not wrap or scrolls inside six lines (`4l`, `?6l`, `?7h`, `CSI r`); a cursor you
cannot see or that keeps the program's shape, pastes arriving wrapped in `ESC [ 200 ~`,
clicks or focus changes arriving as garbage on the command line (`?25h`, `CSI 0 SP q`,
`?2004l`, the mouse modes, `?1004l`); arrow and keypad keys sending application forms the
line editor does not bind (`?1l`, `ESC >`); line-drawing ASCII (`( B`, `) B`, `SI`); a
coloured prompt (`SGR 0`); the session's window title (empty `OSC 2 BEL`). termios restores
none of it — that is the kernel's line discipline, not the terminal's state. -/
def leaveCases : List (List (List UInt8) × String) :=
  [([modeSet 1049 false], "leaves the alt screen"), ([csiNum 4 0x6C], "clears insert mode"),
    ([modeSet 25 true], "shows the cursor"),
    ([shapeAnsi 0], "restores the terminal's own cursor shape"),
    ([modeSet 2004 false], "clears bracketed paste"),
    ([modeSet 1000 false, modeSet 1002 false, modeSet 1003 false, modeSet 1006 false],
      "clears mouse reporting"),
    ([modeSet 1004 false], "clears focus events"),
    ([modeSet 1 false, escSeq 0x3E], "restores normal cursor/keypad keys"),
    ([modeSet 6 false], "clears origin mode"), ([modeSet 7 true], "restores autowrap"),
    ([csiPlain 0x72], "restores the full scroll region"),
    ([escCharset 0x28 0x42, escCharset 0x29 0x42, [0x0F]], "restores the ASCII charset"),
    ([csiNum 0 0x6D], "resets the pen"), ([titleAnsi (Vt.init 1 1)], "clears the window title")]

/-- A full-screen application's opening sequences, as the shell's `printf` writes
them: alt screen, mouse reporting (1000 + SGR 1006), cursor hidden, an editor's
insert-mode bar cursor (`CSI 6 SP q`, as leanvim writes it), bracketed
paste, autowrap off, a six-line scroll region, DEC line drawing, a bold red pen,
application cursor keys, application keypad, a nonempty title followed by a
truncated title. The unfinished title exceeds the mediator's candidate cap so
it reaches the client before detach. Literal `\033` for `printf` to interpret. -/
def appStateCmd : String :=
  "printf '\\033[?1049h\\033[?1000h\\033[?1006h\\033[?25l\\033[6 q\\033[?2004h" ++
    "\\033[?7l\\033[5;10r\\033(0\\033[1;31;4m\\033[?1h\\033=X" ++
    "\\033]2;hostile-detach\\007\\033]2;truncated-detach" ++
    String.ofList (List.replicate Terminal.Mediation.oscCap 'x') ++
    "'; exec sleep 600\r"

/-- A ring of per-cell truecolour rows — the shape whose bytes the scrollback
budget exists for: ~40 B per column instead of one. -/
def tcScript : String :=
  "i=1\n" ++ "while [ $i -le 60 ]; do\n" ++ "  j=1\n" ++ "  while [ $j -le 20 ]; do\n" ++
    "    printf \"\\033[38;2;%d;20;30m\\033[48;2;40;%d;60mX\" " ++
    "$((i % 200)) $((j * 11 % 200))\n" ++
    "    j=$((j+1))\n" ++
    "  done\n" ++
    "  printf \"\\033[0m tcline-%d\\n\" $i\n" ++
    "  i=$((i+1))\n" ++
    "done\n"

/-- `wait`, `info`, `ls` and `capture` see an ended session's status, not its screen: the result
of `w5`, whose program ended while nobody was attached, stays listed until one attach shows its
last screen and how its program ended, and is discarded once that client leaves, its end record
still answering `wait`. -/
private def unseenChecks (e : Env) : IO Unit := do
  let _ ← e.cli #["capture", "w5"]
  expect ((← e.status "w5") == .exitedBad)
      "an ended session nobody saw stays listed after wait, info, ls and capture"
  let looker ← e.spawn #["attach", "w5"]
  let shown ← looker.awaitNeedle "exit 37"
  looker.detach
  let told ← drainStr looker.fd hangMs
  let lookerRc ← looker.reap patienceMs
  looker.bye (sendDetach := false)
  let (afterRc, _, _) ← e.cli #["wait", "w5"]
  expect
      (shown && has told "ended (status 37)" && (← e.field "w5" "status").isNone &&
        !(← System.FilePath.pathExists s!"{e.dir}/w5.ckpt") &&
        (← e.info "w5" "pid").isNone &&
        afterRc == 37)
      s!"the first attach to an ended session shows its last screen and how it ended, and \
        discards it once it leaves ({lookerRc}, {afterRc}, {told})"

/-- A `find` result in a failure label: `-1` for absent. -/
private def idxStr (o : Option Nat) : String := (o.map toString).getD "-1"

/-- What a program sets on its terminal, the session's terminal keeps: an editor's insert-mode
bar cursor, as leanvim writes it (`CSI 6 SP q`, the application's bytes, spelled as such),
reaches the client live, and a reattach's repaint sets it again. -/
private def shapeChecks (e : Env) (cols rows : UInt32) : IO Unit := do
  let bar : List UInt8 := [0x1B, 0x5B, 0x36, 0x20, 0x71]
  let s1 ← e.spawn #["attach", "shape"] cols rows
  let _ ← waitFor 4000 (return (← e.info "shape" "clients") == some "1")
  s1.type "printf '\\033[6 q'; echo bar-$((40+2))\r"
  let live ← IO.mkRef ByteArray.empty
  let barred ← s1.awaitText live (hasText · "bar-42")
  s1.detach
  let _ ← s1.awaitText live (hasBytes · Terminal.Render.leaveAnsi)
  let _ ← s1.reap 2000
  s1.bye (sendDetach := false)
  let s2 ← e.spawn #["attach", "shape"] cols rows
  let burst ← IO.mkRef ByteArray.empty
  let shaped ← s2.awaitText burst (hasBytes · bar)
  expect (barred && hasBytes (← live.get) bar && shaped)
      "reattach: a program's bar cursor comes back with the repaint"
  s2.bye
  e.killAll #["shape"]

/-- Whether the job whose pid a shell wrote to `path` ends within `patienceMs`: the jobs these
checks start sleep far longer, so one that was left running cannot pass, however fast the host.
A job that outlives that is ended here, so a failed check leaves nothing running. -/
private def jobEnds (path : String) : IO Bool := do
  let pidIn : IO (Option UInt32) := do
    try
      return ((← IO.FS.readFile path).trimAscii.toString.toNat?).map UInt32.ofNat
    catch _ =>
      return none
  unless ← waitFor patienceMs (return (← pidIn).isSome) do
    return false
  let some job ← pidIn | return false
  let ended ← waitFor patienceMs (return !(← Os.Shell.alive job))
  unless ended do
    Os.Shell.kill job 9
  return ended

/-- Focus reports reach the program. One that enabled focus reporting reads nothing from a
watcher, then `Session.focusReport true` when a client that can type attaches and
`Session.focusReport false` when it detaches; one that did not enable it reads none. Each
program copies every byte it reads to a file, and a marker sent after each step orders what
must already be there. -/
def focusChecks (e : Env) : IO Unit := do
  let inputOf := fun (name : String) => s!"{e.dir}/{name}.input"
  let read : String → IO (List UInt8) := fun name => do
    return ((← (IO.FS.readBinFile (inputOf name)).toBaseIO).toOption.map (·.toList)).getD []
  -- pass every byte through at once, maybe enable focus reporting, say so, then copy input
  let script :=
    "stty -icanon -echo min 1; printf \"$1\"; printf ready; exec dd bs=1 of=\"$2\" 2>/dev/null"
  let startProbe : String → String → IO Unit := fun name enable => do
    let _ ← e.cli #["start", name, "/bin/sh", "-c", script, "sh", enable, inputOf name]
  let readyIn : String → IO Bool := fun name =>
    waitFor 5000 (return has (← e.out #["capture", "--history", name]) "ready")
  let attachAndLeave : Array String → String → IO Bool := fun args name => do
    let client ← e.spawn args 80 24
    let joined ← waitFor 4000 (return (← e.info name "clients") == some "1")
    client.bye
    let left ← waitFor 4000 (return (← e.info name "clients") == some "0")
    return joined && left
  let mark := "W".toUTF8.toList
  -- `send` delivers the marker after everything the step before it wrote to the program
  let marked : String → List UInt8 → IO Bool := fun name expected => do
    let _ ← e.cli #["send", name, "W"]
    waitFor 4000 (return (← read name) == expected)
  startProbe "focus" "\\033[?1004h"
  startProbe "nofocus" ""
  let ready := (← readyIn "focus") && (← readyIn "nofocus")
  let watched ← attachAndLeave #["attach", "--read-only", "focus"] "focus"
  expect (ready && watched && (← marked "focus" mark))
      s!"a program that enabled focus reporting reads nothing from a watcher ({← read "focus"})"
  let typist ← e.spawn #["attach", "focus"] 80 24
  let focusedIn ← waitFor 4000 (return (← read "focus") == mark ++ Linger.Session.focusReport true)
  typist.bye
  let focusedOut ←
    waitFor 4000 do
        return (← read "focus") ==
            mark ++ Linger.Session.focusReport true ++ Linger.Session.focusReport false
  expect (focusedIn && focusedOut)
      s!"a program that enabled focus reporting reads focus in on attach and out on detach \
        ({← read "focus"})"
  let plain ← attachAndLeave #["attach", "nofocus"] "nofocus"
  expect (plain && (← marked "nofocus" mark))
      s!"a program that did not enable focus reporting reads no focus report ({← read "nofocus"})"
  e.killAll #["focus", "nofocus"]

/-- A terminal with no size yet, as `ssh -tt`, `docker exec -t` and a new `pty.openpty` give
before their first resize, attaches writable: the program reads what it types, the session takes
its size once it has one, and a terminal whose size drops back to 0×0 types on and leaves the
session's size alone. Each check reads the expansion, not the typed text, which the terminal
echoes whether or not the shell ran it. -/
def unsizedChecks (e : Env) : IO Unit := do
  let name := "unsized"
  let (startRc, _, _) ← e.cli #["start", name, "/bin/sh"]
  let ran (marker : String) : IO Bool :=
    waitFor patienceMs (return has (← e.out #["capture", "--history", name]) marker)
  let size : IO (Option String × Option String) := do
    return (← e.info name "cols", ← e.info name "rows")
  let typist ← e.spawn #["attach", name] 0 0
  try
    let joined ← waitFor patienceMs (return (← e.info name "clients") == some "1")
    typist.type "echo unsized-$((21+21))\r"
    -- its own terminal shows the answer too, and reading it keeps the client's output flowing
    let shown ← typist.awaitText (← IO.mkRef ByteArray.empty) (hasText · "unsized-42")
    expect (startRc == 0 && joined && shown && (← ran "unsized-42"))
        "a writable attach from a terminal with no size yet types into the session"
    typist.resize 100 30
    expect (← waitFor patienceMs (return (← size) == (some "100", some "30")))
        "a terminal that attached with no size sizes the session once it has one"
    let sized ← e.spawn #["attach", name] 90 25
    try
      let resized ← waitFor patienceMs (return (← size) == (some "90", some "25"))
      sized.resize 0 0
      -- Each round the client reads its size before its input and its daemon's output, so once
      -- its terminal shows the answer to a line typed after the resize, it has sent the 0×0, and
      -- the next line follows it on the same connection.
      sized.type "echo first-$((1+1))\r"
      let answered ← sized.awaitText (← IO.mkRef ByteArray.empty) (hasText · "first-2")
      sized.type "echo zero-$((20+22))\r"
      expect (resized && answered && (← ran "zero-42") && (← size) == (some "90", some "25"))
          "a terminal whose size drops to 0x0 types on and leaves the session's size alone"
    finally
      sized.bye
  finally
    typist.bye
  e.killAll #[name]

/-- SIGKILL ends a process within a second (`Signal.Ends`): a process that sleeps and one that
keeps a CPU busy, each ignoring SIGHUP, SIGINT, SIGQUIT and SIGTERM, has ended, killed by signal 9,
by this check's first look once a second has passed since SIGKILL, as the daemon's own wait looks.
Each is this suite's own child, left unreaped until the check has looked, so its end shows as it
happens. -/
private def sigkillChecks : IO Unit := do
  for (kind, body) in [("sleeping", "exec sleep 600"), ("busy", "while :; do :; done")] do
    let child ←
      IO.Process.spawn
          { cmd := "/bin/sh", args := #["-c", s!"trap '' HUP INT QUIT TERM; echo up; {body}"],
            stdin := .null, stdout := .piped, stderr := .null }
    let up := (← child.stdout.getLine).trimAscii.toString == "up"
    let pid := child.pid
    Os.Shell.kill pid 9
    let sent ← Os.Shell.monotonicMs
    let ended : IO Bool := return (← Os.Shell.peekNohang pid) != .running
    let mut gone ← ended
    while !gone do
      unless ← Os.Shell.nap (sent + 1000) 10 do
        break
      gone ← ended
    gone ← ended
    let took := (← Os.Shell.monotonicMs) - sent
    let how ← Os.Shell.peekNohang pid
    reapOrKill child 0
    expect (up && gone && how == .signaled 9)
        s!"SIGKILL ends a {kind} process that ignores every other signal within a second \
          ({repr how} after {took} ms)"

/-- A daemon an earlier linger started, at `socketPath`, for one connection. `level-2` answers
`info` as a daemon at protocol level 2 does, with `protocol` 2, and refuses the attach of level 3
as a message it does not know; `unleveled` answers `info` with no `protocol` field and drops the
attach without a reply, as a daemon from before the field did; `silent` answers nothing, as a
stopped daemon. It ends once the client leaves: 0 when no attach came, 3 when one did, and 1 when
no client came or the client never left. -/
def olderDaemon (socketPath readyPath mode : String) : IO UInt32 := do
  let lfd ← Os.Shell.unixListen socketPath
  Os.Shell.setNonblock lfd
  try
    IO.FS.writeFile readyPath "ready"
    let some fd ← acceptWithin lfd hangMs | return 1
    try
      let fields := "pid\t1\ncmd\tfixture\n" ++ if mode == "level-2" then "protocol\t2\n" else ""
      let send (m : Linger.Session.Wire.Msg) : IO Unit := do
        -- a client that refused may close before the last write
        try
          Linger.Session.Shell.Client.sendMsg fd m
        catch _ =>
          pure ()
      let mut dec : Linger.Session.Wire.Decoder := {}
      let mut attached := false
      let deadline := (← Os.Shell.monotonicMs) + hangMs
      while (← Os.Shell.monotonicMs) < deadline do
        let revs ← Os.Shell.poll #[fd] #[Os.Shell.POLLIN] 100
        if revs[0]! &&& (Os.Shell.POLLIN ||| Os.Shell.POLLHUP ||| Os.Shell.POLLERR) == 0 then
          continue
        -- a client that left closes the connection or resets it
        let received ←
          try
            Os.Shell.read fd 65536
          catch _ =>
            pure none
        let some bytes := received | return if attached then 3 else 0
        let (next, msgs) := dec.feed bytes.toList
        dec := next
        for m in msgs do
          match m with
          | .info =>
            if mode != "silent" then
              send (.infoReply fields.toUTF8.toList)
              send .done
          | .attach _ _ _ =>
            attached := true
            if mode == "level-2" then
              send (.err "unknown message".toUTF8.toList)
          | _ =>
            pure ()
      return 1
    finally
      Os.Shell.close fd
  finally
    Os.Shell.close lfd

/-- A session whose daemon an earlier linger started is refused, by a writable attach and by a
watcher alike, within the time its `info` answer may take, `Client.replySilenceMs`, with the
session's name and its level, and is sent no attach: a level-2 daemon refuses the attach of
level 3 as a message it does not know, and one from before the level was reported drops it
without a reply, so an attach sent blind shows a bare refusal or waits for the detach key. -/
def olderDaemonChecks (e : Env) : IO Unit := do
  let self ← IO.appPath
  let bound := Linger.Session.Shell.Client.replySilenceMs.toNatClampNeg + patienceMs
  for (mode, said, options) in
    [("level-2", "(protocol 2)", #[]), ("unleveled", "(no protocol level)", #[]),
      ("silent", "did not say which protocol it speaks", #[]),
      ("level-2", "(protocol 2)", #["--read-only"])] do
    let name := s!"older-{mode}{if options.isEmpty then "" else "-watched"}"
    let socketPath := s!"{e.dir}/{name}.sock"
    let readyPath := s!"{e.dir}/{name}.ready"
    let server ←
      IO.Process.spawn
          { cmd := self.toString, args := #["--older-daemon", socketPath, readyPath, mode],
            stdout := .null, stderr := .null }
    try
      unless ← waitFor patienceMs (System.FilePath.pathExists readyPath) do
        throw (IO.userError s!"older daemon {name} did not become ready")
      let start ← Os.Shell.monotonicMs
      let client ← e.spawn (#["attach"] ++ options ++ #[name])
      try
        -- refused, the client exits, so this reads to its end of file
        let output ← drain client.fd bound
        let elapsed := (← Os.Shell.monotonicMs) - start
        let code ← client.reap patienceMs
        let served ← waitProcess server patienceMs
        expect
            (code == 1 && hasText output s!"linger: session '{name}'" && hasText output said &&
              elapsed < bound &&
              served == some 0)
            s!"attach {String.intercalate " " (options.toList ++ [name])} refuses a daemon an older \
              linger started, naming the session and its level, within {bound} ms and without \
              attaching (exit {code}, {elapsed} ms, daemon {served})"
      finally
        client.bye
    finally
      reapOrKill server 0
      for path in [socketPath, readyPath] do
        try
          IO.FS.removeFile path
        catch _ =>
          pure ()

/-- How many times `needle` occurs in `hay`, counting overlapping occurrences. -/
private def occurrences (needle : List UInt8) : List UInt8 → Nat
  | [] => 0
  | hay@(_ :: rest) => (if needle.isPrefixOf hay then 1 else 0) + occurrences needle rest

/-- A client attached to one session tells its terminal, with one OSC 9 desktop notification,
`<name>: <its notification's text, or bell>`, when another local session changes into asking: once
per change into asking, so again only after a look cleared the ask and the session asked anew;
never for its own session, whose bell its terminal hears as it rings; and never for a session that
already asked when it attached, which its title counts from the first sample. -/
def alertChecks (e : Env) : IO Unit := do
  let asks := Linger.Display.Status.name .asks
  let _ ← e.typeIn "alert-early" #["printf", "'\\a'"]
  let _ ← e.typeIn "alert-other" #["true"]
  let early ← waitFor patienceMs (return (← e.field "alert-early" "status") == some asks)
  let c ← e.spawn #["attach", "alert-own"] 80 24
  let out ← IO.mkRef ByteArray.empty
  try
    let attached ← waitFor patienceMs (return (← e.info "alert-own" "clients") == some "1")
    -- the title counts the early ask once the first sample is in: from then on, an ask is news
    let counted := Linger.Display.Status.summary [.asks]
    c.type "echo own-$((1+1))\r"
    let titled ← c.awaitText out (hasText · counted)
    c.type "printf '\\a'; echo own-$((2+2))\r"
    let rang ← c.awaitText out (hasText · "own-4")
    let _ ← e.cli #["send", "alert-other", "printf '\\a'\n"]
    let told := Linger.Display.Alert.notification "alert-other" ""
    let once ← c.awaitText out (hasBytes · told)
    -- three more samples, in which a repeat would show
    let _ ← c.awaitText out (fun _ => false) (ms := 3500)
    let first := (← out.get).toList
    let osc9 := [0x1B, 0x5D, 0x39, 0x3B]
    expect
        (early && attached && titled && rang && once && occurrences osc9 first == 1 &&
          occurrences told first == 1)
        s!"an attached client tells its terminal once that another session asks, and never of its \
          own or of one that asked before it attached ({occurrences osc9 first} notifications)"
    -- a look clears the ask; asking anew is a new change into asking
    let _ ← e.cli #["capture", "alert-other"]
    let cleared ← waitFor patienceMs (return (← e.field "alert-other" "status") != some asks)
    -- the client samples the cleared ask before the next one, as its title shows, which counts
    -- the early ask alone again: an ask cleared and raised again between two samples is no
    -- change the samples show
    let mark := (← out.get).size
    let resampled ← c.awaitText out (hasText · counted) (start := mark)
    let _ ← e.cli #["send", "alert-other", "printf '\\033]9;review ready\\033\\\\'\n"]
    let again := Linger.Display.Alert.notification "alert-other" "review ready"
    let anew ← c.awaitText out (hasBytes · again)
    let _ ← c.awaitText out (fun _ => false) (ms := 2500)
    let all := (← out.get).toList
    expect (cleared && resampled && anew && occurrences osc9 all == 2 && occurrences again all == 1)
        s!"an ask after a look is told again, with its notification's text \
          ({occurrences osc9 all} notifications)"
  finally
    c.bye
  e.killAll #["alert-early", "alert-other", "alert-own"]

/-- The attach suite: attach, detach, reattach, mirroring, waiting, hand-back and
scrollback, the alerts of another session's ask, the refusal of a daemon an older linger started, and that nothing of an ended
session's terminal session outlives it. -/
def run : IO UInt32 :=
  Env.suite "attach" fun e => do
    alertChecks e
    sigkillChecks
    closeFeedback e
    focusChecks e
    unsizedChecks e
    olderDaemonChecks e
    -- one source for the pty geometry and for the off-the-screen window below
    let cols : UInt32 := 80
    let rows : UInt32 := 24
    let receiver := Vt.init cols.toNat rows.toNat
    -- The emitter supplies the expected default bytes; public VT observers check
    -- the terminal state reached by the actual output stream.
    let emptyTitle := titleAnsi receiver
    -- 1. attach creates a live shell. Assert on the EXPANSION, not the typed text:
    -- the tty echoes what was typed, so `marker-$((21+21))` would appear on screen
    -- even if nothing ran; only `marker-42` says the shell executed it.
    let c1 ← e.spawn #["attach", "demo"] cols rows
    let _ ← waitFor 4000 (return (← e.info "demo" "clients") == some "1")
    c1.type "echo marker-$((21+21))\r"
    let out ← drain c1.fd 2000
    expect (hasText out "marker-42") "attach: command executes, output streams back"
    -- 2. ctrl-\ detaches; the client exits but the session lives. WNOHANG waitpid
    -- sees the child gone (`Client.reap` returns the status; `-1` is "still running").
    c1.detach
    let st1 ← c1.reap 2000
    expect (st1 ≥ 0) "detach: client exited on ctrl-backslash"
    c1.bye (sendDetach := false) -- fd and any zombie only; the client already left
    expect (has (← e.out #["ls"]) "demo") "detach: session still listed"
    -- 3. background output while detached reaches the emulator: a session with zero
    -- clients still advances
    let _ ← e.cli #["send", "demo", "echo while-detached-$((40+2))\n"]
    expect
        (←
          waitFor 4000 (return has (← e.out #["capture", "--history", "demo"]) "while-detached-42"))
        "session advances while nobody attached"
    -- 4. reattach: restore shows the old screen contents
    let c2 ← e.spawn #["attach", "demo"] cols rows
    let out2 ← drain c2.fd 1500
    expect (hasText out2 "marker-42" && hasText out2 "while-detached-42")
        "reattach: restore replays prior screen"
    -- The repaint is one synchronized update: the first bytes the attaching client writes open
    -- it, and the history and the screen arrive before it closes.
    let synced :=
      match findBytes out2 Render.syncEnd with
      | some close =>
        let inside := out2.extract Render.syncBegin.length close
        out2.toList.take Render.syncBegin.length == Render.syncBegin &&
          !hasBytes inside Render.syncBegin &&
          hasText inside "marker-42" &&
          hasText inside "while-detached-42"
      | none => false
    expect synced "reattach: the repaint opens the client's output and is one synchronized update"
    shapeChecks e cols rows
    -- 5. two clients mirror output
    let c3 ← e.spawn #["attach", "demo"] cols rows
    let out3 ← drain c3.fd 1000
    c2.type "printf '\\033]2;hostile-exit\\007'; echo both-$((2+1))\r"
    -- the title precedes the echo in the stream, so it has arrived with `both-3`
    let mirror2 ← IO.mkRef ByteArray.empty
    let mirror3 ← IO.mkRef ByteArray.empty
    let _ ← c2.awaitText mirror2 (hasText · "both-3")
    let _ ← c3.awaitText mirror3 (hasText · "both-3")
    let o2 ← mirror2.get
    let o3 ← mirror3.get
    expect (hasText o2 "both-3" && hasText o3 "both-3") "two clients mirror the session"
    let receiver2 := (receiver.feed out2.toList).feed o2.toList
    let receiver3 := (receiver.feed out3.toList).feed o3.toList
    expect (has receiver2.windowTitle "hostile-exit" && has receiver3.windowTitle "hostile-exit")
        "shell exit: both receivers hold the application's nonempty title"
    -- 6. exit inside the shell ends the session and notifies clients, who saw it end, so
    -- nothing of it stays listed; its end record still answers `wait`
    c2.type "exit\r"
    -- Read both handbacks while the clients exit: Darwin discards a closed pty's unread
    -- output after about a second.
    let drain2 ← IO.asTask (drain c2.fd 4000)
    let drain3 ← IO.asTask (drain c3.fd 4000)
    expect
        (←
          waitFor 4000 do
              return (← e.field "demo" "status").isNone && (← e.info "demo" "pid").isNone &&
                  !(← System.FilePath.pathExists s!"{e.dir}/demo.ckpt"))
        "shell exit in an attached session ends it, and nothing of it stays listed"
    let (seenRc, _, _) ← e.cli #["wait", "demo"]
    expect (seenRc == 0) s!"a seen ending's record still answers wait (rc={seenRc})"
    let exit2 ← IO.ofExcept (← IO.wait drain2)
    let exit3 ← IO.ofExcept (← IO.wait drain3)
    let handed2 := receiver2.feed exit2.toList
    let handed3 := receiver3.feed exit3.toList
    expect
        (hasBytes exit2 emptyTitle && hasBytes exit3 emptyTitle && handed2.windowTitle.isEmpty &&
          handed2.atBoundary &&
          handed3.windowTitle.isEmpty &&
          handed3.atBoundary)
        "shell exit clears the title on both attached terminals"
    c2.bye (sendDetach := false)
    c3.bye (sendDetach := false)
    -- 7. wait returns the exit status. `typeIn` types its command into the session
    -- shell, so the command must `exec` to make its status the shell's.
    let _ ← e.typeIn "w2" #["exec sh -c \"sleep 0.5; exit 7\""]
    let t0 ← Os.Shell.monotonicMs
    let (rc, _, _) ← e.cli #["wait", "w2"]
    let took := (← Os.Shell.monotonicMs) - t0
    expect (rc == 7 && took ≥ 200)
        s!"wait blocks until exit and returns status (rc={rc}, took={took}ms)"
    -- A death by signal reads as 128 plus its number, and wait says which signal it was.
    let _ ← e.typeIn "w3" #["exec sh -c 'sleep 0.5; kill -TERM $$'"]
    let (termRc, _, termErr) ← e.cli #["wait", "w3"]
    expect (termRc == 143 && has termErr "killed by signal 15")
        s!"wait reports a death by signal (rc={termRc})"
    -- The session ends with its program, even while a background job holds its terminal, and
    -- the job ends with it.
    let jobFile := s!"{e.dir}/w4.job"
    let _ ← e.typeIn "w4" #[s!"sleep 600 & echo $! > {jobFile}; exec sh -c 'sleep 0.5; exit 3'"]
    let waited ← e.cliTimeout #["wait", "w4"] hangMs
    let jobEnded ← jobEnds jobFile
    expect (waited.map (·.1) == some 3 && jobEnded)
        "a session ends with its program while a background job holds its terminal, and so does the job"
    -- A session that ended with nobody waiting still answers, from its name's end record, and
    -- stays listed as ended with its status.
    let _ ← e.typeIn "w5" #["exec sh -c 'exit 37'"]
    let ended ←
      waitFor 5000 do
          return (← e.status "w5") == .exitedBad && (← e.field "w5" "exit") == some "37"
    let (lateRc, _, _) ← e.cli #["wait", "w5"]
    let (infoRc, lateInfo, _) ← e.cli #["ls", "w5", "--porcelain"]
    expect (ended && lateRc == 37 && infoRc == 0 && has lateInfo "exit\t37")
        s!"an ended session's record answers wait and info (rc={lateRc})"
    let (neverRc, _, neverErr) ← e.cli #["wait", "w-never"]
    expect (neverRc == 127 && has neverErr "no session") "wait on a name no session took exits 127"
    let (bothRc, _, _) ← e.cli #["wait", "w3", "w5"]
    expect (bothRc == 37) s!"wait reports the last of several sessions (rc={bothRc})"
    unseenChecks e
    -- A time limit stops the wait with 124 and leaves the session running. Its program runs for
    -- 30 s, so a 124 says the limit, not the program, ended the wait, and the wait lasted at least
    -- the limit: load can only lengthen it.
    let _ ← e.typeIn "w6" #["exec sleep 30"]
    let limitStart ← Os.Shell.monotonicMs
    let limited ← e.cliTimeout #["wait", "--timeout", "0.5", "w6"] hangMs
    let limitMs := (← Os.Shell.monotonicMs) - limitStart
    let running := (← e.info "w6" "pid").isSome
    expect
        (limited.map (·.1) == some 124 && limited.any (has ·.2.2 "timed out") && 400 ≤ limitMs &&
          running)
        s!"wait --timeout stops waiting and leaves the session running ({limitMs} ms)"
    -- kill returns once the session has ended, and the record says how: by its hangup.
    let (killRc, _, _) ← e.cli #["kill", "w6"]
    let (_, killedInfo, _) ← e.cli #["ls", "w6", "--porcelain"]
    expect (killRc == 0 && has killedInfo "signal\t1")
        s!"kill returns once the session has ended (rc={killRc})"
    let trapFile := s!"{e.dir}/w7.trapped"
    let _ ←
      e.typeIn "w7" #[s!"exec sh -c \"trap '' HUP; : > {trapFile}; while :; do sleep 1; done\""]
    let trapped ← waitFor 3000 (System.FilePath.pathExists trapFile)
    let (stubbornRc, _, _) ← e.cli #["kill", "w7"]
    let (_, stubbornInfo, _) ← e.cli #["ls", "w7", "--porcelain"]
    expect (trapped && stubbornRc == 0 && has stubbornInfo "signal\t9")
        "kill ends a program that ignores SIGHUP"
    -- Nothing of the session's terminal session outlives it: not a background job of a shell
    -- that kill ends, nor one that ignores SIGHUP after its program exits by itself.
    let job8 := s!"{e.dir}/w8.job"
    let _ ← e.typeIn "w8" #[s!"sleep 600 & echo $! > {job8}"]
    let started ← waitFor 3000 (System.FilePath.pathExists job8)
    let (bgKillRc, _, _) ← e.cli #["kill", "w8"]
    let bgEnded ← jobEnds job8
    expect (started && bgKillRc == 0 && bgEnded) "kill ends the session's background jobs"
    let job9 := s!"{e.dir}/w9.job"
    let _ ← e.typeIn "w9" #[s!"exec sh -c \"trap '' HUP; sleep 600 & echo \\$! > {job9}; exit 37\""]
    let (ownRc, _, _) ← e.cli #["wait", "w9"]
    let ownEnded ← jobEnds job9
    expect (ownRc == 37 && ownEnded)
        s!"a session's end ends a job of its terminal session that ignores SIGHUP (rc={ownRc})"
    -- With no daemon, kill discards a saved session, and then finds none.
    let savedPath := s!"{e.dir}/w-saved.ckpt"
    IO.FS.writeBinFile savedPath
        (Linger.Session.Checkpoint.saveBytes ⟨Terminal.Vt.Vt.init 20 2, e.dir, []⟩)
    let (savedRc, _, _) ← e.cli #["kill", "w-saved"]
    let discarded := !(← System.FilePath.pathExists savedPath)
    let (absentRc, _, absentErr) ← e.cli #["kill", "w-saved"]
    expect (savedRc == 0 && discarded && absentRc == 127 && has absentErr "no session")
        "kill discards a saved session, then finds none"
    -- A transport loss is neither a detach nor a successful wait.
    let lost ← e.spawn #["attach", "attach-lost"] cols rows
    let _ ← waitFor 4000 (return (← e.info "attach-lost" "clients") == some "1")
    let lostInitial ← drain lost.fd 300
    -- Exceed the mediator's buffer so the unfinished OSC reaches the terminal;
    -- keep the child quiet afterwards so nothing completes it before handback.
    lost.type
        ("printf '\\033]2;hostile-lost\\007\\033]2;truncated-lost" ++
          String.ofList (List.replicate Terminal.Mediation.oscCap 'x') ++
          "'; exec sleep 600\r")
    let lostDirty ← drain lost.fd 800
    let lostReceiver := (receiver.feed lostInitial.toList).feed lostDirty.toList
    expect (has lostReceiver.windowTitle "hostile-lost" && !lostReceiver.atBoundary)
        "connection loss: the receiver holds a nonempty title before a truncated OSC"
    unless (← e.crashDaemon "attach-lost") do
      throw (IO.userError "attach-lost daemon did not crash")
    let lostBytes ← drain lost.fd 2000
    let lostHanded := lostReceiver.feed lostBytes.toList
    let lostOut := String.fromUTF8? lostBytes |>.getD ""
    let lostCode ← lost.reap 3000
    expect (lostCode == 1 && has lostOut "connection lost")
        "attach exits 1 when its daemon disappears"
    expect
        (hasBytes lostBytes emptyTitle && lostHanded.windowTitle.isEmpty && lostHanded.atBoundary)
        "connection loss clears the title after a truncated OSC"
    lost.bye (sendDetach := false)
    let _ ← e.typeIn "wait-lost" #["sleep", "600"]
    let waiter ←
      IO.Process.spawn
          { cmd := e.bin, args := #["wait", "wait-lost"], env := e.procEnv, stdout := .null,
            stderr := .piped }
    IO.sleep 800
    unless (← e.crashDaemon "wait-lost") do
      throw (IO.userError "wait-lost daemon did not crash")
    let waitCode ← waitOrKill waiter 3000
    let waitErr ← waiter.stderr.readToEnd
    expect (waitCode == some 125 && has waitErr "outcome unknown")
        "wait exits 125, its outcome unknown, when the daemon disappears"
    -- However long a wait has lasted, the kill that ends its session tells it how the program
    -- ended, and so does an attached client. The program ignores SIGHUP, so the daemon's ending
    -- lasts until SIGKILL ends it, and the wait began longer ago than its patience for a name
    -- held with no daemon answering.
    let trap10 := s!"{e.dir}/w10.trapped"
    let _ ←
      e.typeIn "w10" #[s!"exec sh -c \"trap '' HUP; : > {trap10}; while :; do sleep 1; done\""]
    let trapped10 ← waitFor patienceMs (System.FilePath.pathExists trap10)
    let longWaiter ←
      IO.Process.spawn
          { cmd := e.bin, args := #["wait", "w10"], env := e.procEnv, stdout := .null,
            stderr := .piped }
    let viewer ← e.spawn #["attach", "--read-only", "w10"] cols rows
    let viewing ← waitFor patienceMs (return (← e.info "w10" "clients") == some "1")
    IO.sleep (Linger.App.Wait.heldNameMs + 1000).toUInt32
    let stillWaiting := (← longWaiter.tryWait).isNone
    let (longKillRc, _, _) ← e.cli #["kill", "w10"]
    let longCode ← waitOrKill longWaiter hangMs
    let longErr ← longWaiter.stderr.readToEnd
    let viewerOut ← IO.mkRef ByteArray.empty
    let viewerTold ← viewer.awaitText viewerOut (hasText · "ended (killed by signal 9)")
    let viewerCode ← viewer.reap patienceMs
    viewer.bye (sendDetach := false)
    expect
        (trapped10 && stillWaiting && longKillRc == 0 && longCode == some 137 &&
          has longErr "killed by signal 9")
        s!"a wait older than its patience hears how the killed program ended (rc={longCode})"
    expect (viewing && viewerTold && viewerCode == 137)
        s!"an attached client hears how the killed program ended (rc={viewerCode})"
    -- 8. An empty chooser offers the default name without creating it on entry.
    let defaults : Env := { e with dir := s!"{e.dir}/default" }
    let defaultName := Linger.Target.Name.defaultName
    let m ← defaults.spawnEnv #[s!"HOME={defaults.dir}"] #["attach"] cols rows
    try
      let screen ← IO.mkRef ByteArray.empty
      let offered ← m.awaitText screen (hasText · s!"+ Create {defaultName}") (ms := 5000)
      let absent := (← defaults.out #["ls", "--porcelain"]).isEmpty
      m.type "\r"
      let created ←
        waitFor 5000 do
            return has (← defaults.out #["ls", "--porcelain"]) s!"name\t{defaultName}\n"
      expect (offered && absent && created)
          "bare attach creates the default session only after accepting Create"
      m.detach
    finally
      m.bye (sendDetach := false)
      defaults.killAll #[defaultName]
    -- 9. detach hands the terminal back (`Render.leaveAnsi`). A full-screen app's
    --    opening sequences are set from inside the session; after ctrl-\ the client
    --    must undo every one of them, or the user's shell is left on the alt screen
    --    with mouse reporting on, no cursor, a six-line scroll region and every
    --    ASCII character rendered as a box glyph. termios restores none of this.
    let h ← e.spawn #["attach", "hyg"] cols rows
    let _ ← waitFor 4000 (return (← e.info "hyg" "clients") == some "1")
    let initial ← drain h.fd 300
    h.type appStateCmd
    -- The truncated title is the application's last output; once all of it has
    -- arrived the stream is quiet, so the handback below is the next thing read.
    let truncated :=
      ("\x1b]2;truncated-detach" ++ String.ofList (List.replicate Terminal.Mediation.oscCap 'x'))
    let app ← IO.mkRef ByteArray.empty
    let _ ← h.awaitText app (hasText · truncated)
    let dirty ← app.get
    -- non-vacuity for the checks below: the app state really got out to the
    -- client's terminal, so there is something to undo. These two needles are the
    -- APPLICATION's bytes — `modeSet`/`csiNum2` are used here only to spell two
    -- standard sequences, not as a tie to an emitter.
    expect (hasBytes dirty (modeSet 1049 true) && hasBytes dirty (csiNum2 5 10 0x72))
        "hygiene: the app state really reached the client terminal"
    let dirtyReceiver := (receiver.feed initial.toList).feed dirty.toList
    expect
        (dirtyReceiver.inAlt && has dirtyReceiver.windowTitle "hostile-detach" &&
          !dirtyReceiver.atBoundary)
        "detach: the alternate-screen receiver holds a nonempty title before a truncated OSC"
    h.detach
    let back ← drain h.fd 1500
    let handedBack := dirtyReceiver.feed back.toList
    for (seqs, what) in leaveCases do
      expect (seqs.all (fun s => hasBytes back s)) ("detach " ++ what)
    expect (!handedBack.inAlt && handedBack.windowTitle.isEmpty && handedBack.atBoundary)
        "detach clears the title after neutralizing a truncated OSC"
    -- ST first, and the whole constant verbatim. The leading `ESC \` is not
    -- decoration: a program that died mid-OSC/DCS (a crashed sixel writer, a
    -- truncated title) leaves the receiver's parser in a string state that would
    -- swallow this entire stream, exactly as it swallowed `restore` before cd7c17b.
    -- The `hasBytes … leaveAnsi` conjunct is needed because the groups above can
    -- all be present in the wrong order or with bytes wedged between them, and
    -- `leave_canonical_all` proves the CONTENTS while no theorem can see that the
    -- client actually writes them.
    expect (startsWithBytes back (escSeq 0x5C) && hasBytes back leaveAnsi)
        "detach leads with ST (a program that died mid-OSC/DCS would eat the rest)"
    h.bye (sendDetach := false)
    e.killAll #["hyg"]
    -- 9b. A signal that ends the client hands the terminal back as a detach does, and then the
    --    signal ends the client, as it ends a program that does not catch it, so its caller sees
    --    the signal itself, which a shell reports as 128 plus its number: SIGTERM, as a logout
    --    sends, SIGHUP, as a closed window sends, and SIGINT. Its session stays, with nobody
    --    attached.
    for (sig, what) in [((15 : UInt32), "SIGTERM"), (1, "SIGHUP"), (2, "SIGINT")] do
      let name := s!"sig{sig}"
      let c ← e.spawn #["attach", name] cols rows
      let shown ← IO.mkRef ByteArray.empty
      c.type s!"echo {name}-$((40+2))\r"
      let ready ← c.awaitText shown (hasText · s!"{name}-42")
      let mark := (← shown.get).size
      Os.Shell.kill c.pid sig
      let handed ← c.awaitText shown (hasBytes · leaveAnsi) (start := mark)
      let ended ← c.ending patienceMs
      let left ← waitFor 4000 (return (← e.info name "clients") == some "0")
      expect (ready && handed && ended == some (.signaled sig.toUInt8) && left)
          s!"{what} hands the terminal back and then ends the client ({repr ended})"
      c.bye (sendDetach := false)
      e.killAll #[name]
    -- If the hand-back write fails, termios restoration must still run. stdout is a
    -- second terminal, so attach passes its tty check and enters raw mode; closing that
    -- terminal's only master while attached makes the hand-back write fail. The shells
    -- publish each file the check waits for by rename, so a file that exists is complete.
    let _ ← e.typeIn "raw-cleanup" #["sleep", "600"]
    let text (path : String) : IO String := return (← readText path).trimAscii.toString
    let outTty := s!"{e.dir}/raw-cleanup.out-tty"
    let (outPid, outFd) ←
      Os.Shell.spawnPty cols rows "" "sh"
          #["-c", s!"tty > {outTty}.tmp && mv {outTty}.tmp {outTty}; exec sleep 600"] e.ptyEnv
    let _ ← waitFor 5000 (return (← text outTty).startsWith "/dev/")
    let rawTty := s!"{e.dir}/raw-cleanup.tty"
    let beforePath := s!"{e.dir}/raw-cleanup.before"
    let modesPath := s!"{e.dir}/raw-cleanup.modes"
    let cleanupScript :=
      s!"tty > {rawTty}; before=$(stty -g); \
         printf '%s\\n' \"$before\" > {beforePath}.tmp && mv {beforePath}.tmp {beforePath}; \
         {e.bin} attach raw-cleanup >{← text outTty} 2>/dev/null; rc=$?; after=$(stty -g); \
         printf '%s\\n%s\\n%s\\n' \"$before\" \"$after\" \"$rc\" > {modesPath}.tmp && \
         mv {modesPath}.tmp {modesPath}"
    let (rawPid, rawFd) ← Os.Shell.spawnPty cols rows "" "sh" #["-c", cleanupScript] e.ptyEnv
    let rawProbe : Verify.Harness.Client := { pid := rawPid, fd := rawFd }
    -- attach registers before it enters raw mode, so wait for the mode itself. The tty
    -- path is written before `before`, and only a successful, nonempty read counts.
    let entered ←
      waitFor 5000 do
          let before := withoutPendin (← text beforePath)
          if before.isEmpty then
            return false
          let now ←
            IO.Process.output { cmd := "/bin/sh", args := #["-c", s!"stty -g < {← text rawTty}"] }
          let mode := withoutPendin now.stdout.trimAscii.toString
          return now.exitCode == 0 && !mode.isEmpty && mode != before
    -- Closing the only master hangs up stdout; its sleep is reaped with it.
    ({ pid := outPid, fd := outFd } : Verify.Harness.Client).bye (sendDetach := false)
    rawProbe.detach
    let _ ← waitFor 5000 (System.FilePath.pathExists modesPath)
    expect
        (match (← text modesPath).splitOn "\n" with
        | [before, after, rc] =>
          entered && !before.isEmpty && withoutPendin before == withoutPendin after && rc != "0"
        | _ => false)
        "attach restores tty mode even when leaveAnsi cannot be written"
    rawProbe.bye (sendDetach := false)
    e.killAll #["raw-cleanup"]
    -- 10. LINGER_NO_DETACH_KEY, set to any value, empty included, disables the ctrl-\
    --     detach key (help promise, `detachEnabled_writable`, and the mirror of check 2).
    --     With the env var set, ctrl-\ is ordinary input: the client stays attached and
    --     the byte reaches the session's pty.
    for (value, name) in [("1", "nd"), ("", "nd-empty")] do
      let nd ← e.spawnEnv #[s!"LINGER_NO_DETACH_KEY={value}"] #["attach", name] cols rows
      let _ ← waitFor 4000 (return (← e.info name "clients") == some "1")
      let _ ← drain nd.fd 300
      nd.detach -- would detach if the key were enabled
      IO.sleep 500
      -- `-1` from WNOHANG waitpid is "still running"
      expect ((← Os.Shell.waitpidNohang nd.pid) == -1)
          s!"LINGER_NO_DETACH_KEY={value}: ctrl-\\ does not detach (client still attached)"
      expect (has (← e.out #["ls"]) name) s!"LINGER_NO_DETACH_KEY={value}: session still live"
      nd.type "echo nd-$((20+2))\r" -- still interactive: input reaches the pty
      expect (← waitFor 4000 (return has (← e.out #["capture", "--history", name]) "nd-22"))
          s!"LINGER_NO_DETACH_KEY={value}: input still reaches the session"
      e.killAll #[name]
      nd.bye (sendDetach := false)
    -- 11. the scrollback reaches the client's own scrollback. `restore` paints the
    --     session's ring first and scrolls it off, so the reattach burst carries lines
    --     that are no longer on the screen at all — and the client's wheel-scroll,
    --     search and selection find them. The `ED 3` that stops a second attach
    --     stacking a second copy is emitted AFTER the `ED 2` (the order ncurses
    --     `clear(1)` sends), because `restoreBody` already clears before `screensAnsi`.
    let s1 ← e.spawn #["attach", "sb"] cols rows
    let _ ← waitFor 4000 (return (← e.info "sb" "clients") == some "1")
    let _ ← drain s1.fd 300
    s1.type "i=1; while [ $i -le 60 ]; do echo sbline-$i; i=$((i+1)); done\r"
    let _ ←
      waitFor 4000 (return (lines (← e.out #["capture", "--history", "sb"])).contains "sbline-60")
    let _ ← drain s1.fd 1200
    -- exact-line membership, not substring: the typed line the tty echoed back
    -- contains `sbline-$i`, and only the shell's output lines are the markers
    -- themselves; `has` would weaken it.
    let histS := lines (← e.out #["capture", "--history", "sb"])
    expect
        (histS.contains "sbline-1" && !(histS.drop (histS.length - rows.toNat)).contains "sbline-1")
        "scrollback: the early lines are in the ring, off the 24-row screen"
    s1.detach
    let _ ← waitFor 4000 (return (← e.info "sb" "clients") == some "0")
    s1.bye (sendDetach := false)
    let s2 ← e.spawn #["attach", "sb"] cols rows
    let burst ← drain s2.fd 2000
    expect ((findText burst "sbline-1").isSome)
        "scrollback: a line that scrolled off the screen is replayed on reattach"
    expect ((findText burst "sbline-60").isSome) "scrollback: the screen is still replayed too"
    -- ED 2 is `restoreBody`'s clean slate, ED 3 is `scrollbackAnsi`'s ring clear:
    -- the needles are those two emitters, so the check is about the ORDER of the
    -- implementation's own writes and not about two byte literals.
    let i2 := findBytes burst (csiNum 2 0x4A)
    let i3 := findBytes burst (csiNum 3 0x4A)
    let edOk :=
      match i2, i3 with
      | some a, some b => a < b
      | _, _ => false
    expect edOk s!"scrollback: ED 3 present and after ED 2 (2J at {idxStr i2}, 3J at {idxStr i3})"
    expect (burst.size < outputChunk)
        s!"scrollback: the reattach burst fits one outputChunk ({burst.size} bytes, \
        cap {outputChunk}; outbufCap is {outbufCap} and disconnects)"
    s2.type "echo alive-$((20+22))\r"
    let alive ← IO.mkRef ByteArray.empty
    expect (← s2.awaitText alive (hasText · "alive-42"))
        "scrollback: the client survives the burst and is still interactive"
    --     …and again with a ring of per-cell truecolour rows, which is the shape
    --     whose bytes the budget exists for: ~40 B per column instead of one.
    let tc := s!"{e.dir}/tc.sh"
    IO.FS.writeFile tc tcScript
    s2.type s!"sh {tc}\r"
    let truecolour ← IO.mkRef ByteArray.empty
    let _ ← s2.awaitText truecolour (hasText · "tcline-60") (ms := 8000)
    let _ ← drain s2.fd 1500
    s2.detach
    let _ ← waitFor 4000 (return (← e.info "sb" "clients") == some "0")
    s2.bye (sendDetach := false)
    let s3 ← e.spawn #["attach", "sb"] cols rows
    let burstTc ← drain s3.fd 2500
    expect ((findText burstTc "tcline-1").isSome)
        "scrollback: a truecolour line that scrolled off is replayed too"
    expect (burstTc.size < outbufCap)
        s!"scrollback: the truecolour burst stays under outbufCap \
        ({burstTc.size} bytes, cap {outbufCap})"
    s3.type "echo tc-alive-$((21+21))\r"
    let tcAlive ← IO.mkRef ByteArray.empty
    expect (← s3.awaitText tcAlive (hasText · "tc-alive-42"))
        "scrollback: the client survives the truecolour burst"
    s3.bye (sendDetach := false)
    e.killAll #["sb", "w2"]

end Linger.Session.Suites.Attach
