module

public import Verify.Harness
import Linger.Session.Shell.Inventory
import Linger.Session.Shell.Client
import Linger.Session.Checkpoint
import Linger.Terminal.Mediation
public import Linger.Session.Spec
import SoftwareChallenge.Commands

public section

/-! # Linger.Session.Suites.Agent — the agent verbs: see and drive a session one-shot

Ported from `tests/agent_test.py`; the spec is `specs/archive/agent-cli.md`.

Step 1: `linger info <name>` and the observability fields — geometry + cursor
(what `capture` needs), `alt`, and `outseq` (the change cursor: "look again only
when it moved"). Step 2: `linger capture <name>` — the screen as plain text, one
line per row, and capturing marks the session seen. Step 3: `linger send <name> -`
— stdin to the pty byte-exact. Step 4: `linger resize` — applies detached (down to
the child's own winsize, via `stty size`), refused while a client is attached. All
pinned against the rendered porcelain/bytes, end to end.

`alt` and `unseen` compare to `toString false` / `toString true`, because that is
literally what `Session.infoFields` emits (`toString` of a `Bool`), and the default size
compares to `Session.bootVt none`, the screen a daemon boots with when no checkpoint
loads. One fact could NOT be tied to the implementation — read before adding a check:
"capture is exactly one line per row" cannot be tied to `Render.screenText`, because the
row count is a property of a `Vt` this process does not hold. `rows` comes from the
session's own `info`, which is as close as the porcelain gets. -/

namespace Linger.Session.Suites.Agent

open Verify.Harness

/-- A field as a natural number: `none` when it is absent, empty or not all digits. -/
def num (o : Option String) : Option Nat :=
  o.bind fun s => if s.all Char.isDigit then s.toNat? else none

/-- `text` has `line` as a whole line followed by a nonempty one: a command's output
and then the shell's next prompt. -/
def outputThenPrompt (text line : String) : Bool :=
  let rows := lines text
  (rows.zip rows.tail).any fun (row, next) => row == line && !next.isEmpty

/-- `linger send <name> -` with `payload` on its stdin, byte-exact.

`IO.Process.output`'s `input?` argument *is* the mechanism, so no new harness
primitive is needed: core spawns with `stdin := .piped`, `takeStdin`s the handle
away from the `Child`, writes, flushes, and then drops it — and dropping the last
reference is what closes the pipe. That close is load-bearing, not hygiene:
`Cli.cmdSendStdin` has **no timeout on purpose** ("a slow producer feeding a pipe
is legitimate"), so a sender that kept the handle open would hang here instead of
failing.

`putStr` writes the payload's UTF-8, and every payload below is ASCII or a single
C0 byte, so the pipe carries exactly those bytes. A payload that is not valid
UTF-8 would need `spawn` + `takeStdin` + `Handle.write` on a `ByteArray`; nothing
here does. -/
def sendStdin (e : Env) (name payload : String) : IO UInt32 := do
  let out ←
    IO.Process.output { cmd := e.bin, args := #["send", name, "-"], env := e.procEnv }
        (some payload)
  return out.exitCode

/-- One fake daemon: accept a connection, send an over-cap frame header, close.
The CLI must report protocol loss rather than a successful request. -/
def malformedServer (socketPath readyPath : String) : IO UInt32 := do
  let lfd ← Linger.Os.Shell.unixListen socketPath
  Linger.Os.Shell.setNonblock lfd
  IO.FS.writeFile readyPath "ready"
  let rc ←
    match ← acceptWithin lfd 5000 with
    | none =>
      pure 1
    | some fd =>
      let tooLarge := UInt32.ofNat (Linger.Session.Wire.maxPayload + 1)
      Linger.Os.Shell.writeAll fd
          (ByteArray.mk ((0 : UInt8) :: Linger.Session.Wire.writeU32 tooLarge).toArray)
      Linger.Os.Shell.close fd
      pure 0
  Linger.Os.Shell.close lfd
  try
    IO.FS.removeFile socketPath
  catch _ =>
    pure ()
  return rc

/-- Two info conversations, one for `get` and one for listing. Failure modes
first send plausible fields: neither a partial label nor a healthy-looking
prefix may be mistaken for a completed answer. The socket path stays for the
caller to check that listing did not unlink a connected peer. -/
def infoServer (socketPath readyPath mode : String) : IO UInt32 := do
  let lfd ← Linger.Os.Shell.unixListen socketPath
  Linger.Os.Shell.setNonblock lfd
  try
    IO.FS.writeFile readyPath "ready"
    for _ in [:2] do
      let some fd ← acceptWithin lfd 5000 | return 1
      try
        let ready ← Linger.Os.Shell.poll #[fd] #[Linger.Os.Shell.POLLIN] 2000
        if ready[0]! == 0 then
          return 1
        let _ ← Linger.Os.Shell.read fd 65536
        let _ ←
          try
            if mode != "empty" then
              Linger.Session.Shell.Client.sendMsg fd
                  (.infoReply "pid\t1\ncmd\tfixture\nlabel.partial\tvalue\n".toUTF8.toList)
            match mode with
            | "eof" =>
              pure ()
            | "timeout" =>
              IO.sleep 2400
            | "refused" =>
              Linger.Session.Shell.Client.sendMsg fd (.err "info refused\x1b[31m".toUTF8.toList)
            | "malformed" =>
              Linger.Os.Shell.writeAll fd
                  (ByteArray.mk
                    ((0 : UInt8) ::
                        Linger.Session.Wire.writeU32
                          (UInt32.ofNat (Linger.Session.Wire.maxPayload + 1))).toArray)
            | "exited" =>
              Linger.Session.Shell.Client.sendMsg fd (.exited 17)
            | "utf8" =>
              Linger.Session.Shell.Client.sendMsg fd (.infoReply [0xFF])
              Linger.Session.Shell.Client.sendMsg fd .done
            | "record" =>
              Linger.Session.Shell.Client.sendMsg fd (.infoReply "broken record\n".toUTF8.toList)
              Linger.Session.Shell.Client.sendMsg fd .done
            | "cap" =>
              let fieldStart := "padding\t".toUTF8.toList
              let payload :=
                fieldStart ++
                  List.replicate (Linger.Session.Wire.maxPayload - fieldStart.length - 1)
                    (UInt8.ofNat 120) ++
                  [10]
              for _ in
                [:Linger.Session.Shell.Inventory.infoReplyCap / Linger.Session.Wire.maxPayload +
                    1] do
                Linger.Session.Shell.Client.sendMsg fd (.infoReply payload)
              Linger.Session.Shell.Client.sendMsg fd .done
            | "complete" =>
              Linger.Session.Shell.Client.sendMsg fd
                  (.infoReply "label.second\tanother\n".toUTF8.toList)
              Linger.Session.Shell.Client.sendMsg fd .done
            | "failed-info" =>
              Linger.Session.Shell.Client.sendMsg fd (.infoReply "exit\t7\n".toUTF8.toList)
              Linger.Session.Shell.Client.sendMsg fd .done
            | "empty" =>
              Linger.Session.Shell.Client.sendMsg fd .done
            | _ =>
              return 1
          catch _ =>
            -- A client may reject the frame and close before the last write.
            pure ()
        pure ()
      finally
        Linger.Os.Shell.close fd
    return 0
  finally
    Linger.Os.Shell.close lfd

private def checkInfo (e : Env) (mode : String) (error : Option String) : IO Unit := do
  let name := s!"info-{mode}"
  let socketPath := s!"{e.dir}/{name}.sock"
  let readyPath := s!"{e.dir}/{name}.ready"
  let self ← IO.appPath
  let server ←
    IO.Process.spawn
        { cmd := self.toString, args := #["--info-server", socketPath, readyPath, mode],
          stdout := .null, stderr := .piped }
  try
    unless (← waitFor 5000 (System.FilePath.pathExists readyPath)) do
      throw (IO.userError s!"{mode} info server did not become ready")
    let (rc, out, err) ← e.cli #["get", name]
    let (lrc, listing, _) ← e.cli #["ls", "--porcelain"]
    let serverRc ← waitProcess server 5000
    let recs := records listing
    let pathKept ← System.FilePath.pathExists socketPath
    match error with
    | some why =>
      expect (rc == 1 && out.isEmpty && has err why && !has err "\x1b")
          s!"get rejects {mode} info without printing partial labels"
      expect
          (serverRc == some 0 && lrc == 0 && pathKept && recs.contains ("name", name) &&
            recs.contains ("state", "live") &&
            recs.contains ("status", Linger.Display.Status.name .unknown) &&
            !recs.any (fun kv => kv.1 == "cmd" || kv.1.startsWith "label."))
          s!"listing retains {mode} info peer as live/unknown without partial fields"
    | none =>
      let expected := if mode == "empty" then "" else "partial=value\nsecond=another\n"
      expect (serverRc == some 0 && rc == 0 && out == expected && err.isEmpty)
          s!"get accepts {mode} info terminated by done"
  finally
    reapOrKill server 0
    IO.FS.removeFile socketPath
    IO.FS.removeFile readyPath

/-- `start` from `cwd`, with `extra` on top of the suite's environment: exit status and stderr. -/
private def startIn (e : Env) (cwd : String) (extra : Array (String × Option String))
    (args : Array String) : IO (UInt32 × String) := do
  let out ←
    IO.Process.output
        { cmd := e.bin, args := #["start"] ++ args, env := e.procEnv ++ extra, cwd := some cwd }
  return (out.exitCode, out.stderr)

/-- The names `ls --porcelain` lists. -/
private def listed (e : Env) : IO (List String) := do
  return (← e.out #["ls", "--porcelain"]).splitOn "\n" |>.filterMap fun line =>
      (line.dropPrefix? "name\t").map (·.toString)

/-- `start` runs an exact argv in a new session, in the caller's directory and environment,
refuses a name a live or saved session holds, and leaves nothing behind when the program cannot
start: VERA's request N1. -/
private def startChecks (e : Env) : IO Unit := do
  let work := s!"{e.dir}/start work"
  IO.FS.createDirAll work
  let (rc, err) ←
    startIn e work #[("CANARY", none), ("MARK", some "m1")]
        #["st1", "/bin/sh", "-c", "pwd; env; printf '%s\\n' \"$1\"; sleep 30", "sh", "$(touch t)"]
  let shown ← waitFor 4000 (return has (← e.out #["capture", "--history", "st1"]) "$(touch t)")
  let history ← e.out #["capture", "--history", "st1"]
  expect
      (rc == 0 && err.isEmpty && shown && has history work && has history "MARK=m1" &&
        has history "LINGER_SESSION=st1" &&
        !(← System.FilePath.pathExists s!"{work}/t"))
      s!"start runs its argv exactly, in the caller's directory and environment (rc={rc})"
  let pid ← e.info "st1" "pid"
  -- the program's environment is exactly the caller's, but for the terminal's and the session's
  -- name; the shell that writes it out may add its own few
  let envFile := s!"{work}/env.out"
  let caller := ["PATH=/usr/bin:/bin", s!"LINGER_DIR={e.dir}", "SHELL=/bin/sh", "MARK=m2"]
  let exact ←
    IO.Process.output
        { cmd := "/usr/bin/env",
          args :=
            #["-i"] ++ caller.toArray ++
              #[e.bin, "start", "st0", "/bin/sh", "-c", "exec env > \"$1\"", "sh", envFile],
          cwd := some work }
  let (envRc, _, _) ← e.cli #["wait", "st0"]
  let seen :=
    ((← IO.FS.readFile envFile).splitOn "\n").filter fun line =>
      !line.isEmpty && !["PWD=", "OLDPWD=", "SHLVL=", "_="].any (line.startsWith ·)
  let expected :=
    caller ++
      ["LINGER_SESSION=st0", "TERM=xterm-256color", "TERM_PROGRAM=linger",
        s!"TERM_PROGRAM_VERSION={Linger.Terminal.Mediation.versionNumber}"]
  expect
      (exact.exitCode == 0 && envRc == 0 && seen.length == expected.length &&
        expected.all seen.contains)
      s!"start passes the caller's environment exactly, but for TERM* and LINGER_SESSION ({seen})"
  let (liveRc, liveErr) ← startIn e work #[] #["st1", "true"]
  expect (liveRc == 1 && has liveErr "is running" && (← e.info "st1" "pid") == pid)
      "start refuses a name a live session holds, and says so"
  let savedPath := s!"{e.dir}/stsv.ckpt"
  let saved := Linger.Session.Checkpoint.saveBytes ⟨Linger.Terminal.Vt.Vt.init 20 2, work, []⟩
  IO.FS.writeBinFile savedPath saved
  let (savedRc, savedErr) ← startIn e work #[] #["stsv", "true"]
  expect
      (savedRc == 1 && has savedErr "is saved" && (← e.info "stsv" "pid").isNone &&
        (← IO.FS.readBinFile savedPath).toList == saved.toList)
      "start refuses a name a saved session holds, without resuming it"
  IO.FS.removeFile savedPath
  let before ← listed e
  let (missingRc, missingErr) ← startIn e work #[] #["stm", "linger-no-such-program-42"]
  let (deniedRc, deniedErr) ← startIn e work #[] #["stn", "/etc/passwd"]
  let after ← listed e
  let noRecords :=
    !(← System.FilePath.pathExists s!"{e.dir}/stm.end") &&
      !(← System.FilePath.pathExists s!"{e.dir}/stn.end")
  expect
      (missingRc == 127 && has missingErr "not found" && deniedRc == 126 &&
        has deniedErr "cannot be run" &&
        before == after &&
        noRecords)
      s!"a program that cannot start returns 127 or 126 and leaves nothing behind \
        ({missingRc}, {deniedRc})"
  -- a directory the daemon cannot enter: the command runs in it, and takes its search
  -- permission away first
  let locked := s!"{e.dir}/start locked"
  IO.FS.createDirAll locked
  let root := (← Linger.Os.Shell.getuid) == 0
  let lockedRun ←
    IO.Process.output
        { cmd := "/bin/sh", args := #["-c", "chmod 000 . && exec \"$0\" start stc true", e.bin],
          env := e.procEnv, cwd := some locked }
  discard <| IO.Process.output { cmd := "chmod", args := #["755", locked] }
  expect
      (root ||
        lockedRun.exitCode == 125 && has lockedRun.stderr "cannot enter" &&
          !(← System.FilePath.pathExists s!"{e.dir}/stc.end"))
      s!"start in a directory it cannot enter returns 125 and leaves nothing behind \
        ({lockedRun.exitCode})"
  e.killAll #["st1"]
  let (runRc, _, runErr) ← e.cli #["run", "st-run", "true"]
  let (shortRc, _, shortErr) ← e.cli #["r", "st-run"]
  let (infoRc, _, _) ← e.cli #["info", "st-run"]
  expect
      (runRc == 2 && shortRc == 2 && shortErr == runErr && has runErr "removed" &&
        has runErr "start" &&
        has runErr "resume" &&
        has runErr "send" &&
        infoRc == 127)
      s!"run is removed: it returns 2, points to start, resume and send, and starts nothing \
        ({runRc}, {shortRc}, {infoRc})"

/-- An ended session is a result: it stays listed with how its program ended and what it left on
the screen, `start` refuses its name, and `kill` discards it, after which `wait` still answers
from the name's end record. -/
private def endedChecks (e : Env) : IO Unit := do
  let work := s!"{e.dir}/ended work"
  IO.FS.createDirAll work
  -- the marker is an expansion, so only the program's output, not an echo, can show it
  let (okRc, _) ← startIn e work #[] #["end-ok", "/bin/sh", "-c", "echo DONE-$((6*7))"]
  let (badRc, _) ← startIn e work #[] #["end-bad", "/bin/sh", "-c", "echo FAILED-$((6*7)); exit 3"]
  let (sigRc, _) ← startIn e work #[] #["end-sig", "/bin/sh", "-c", "kill -TERM $$"]
  let ended ←
    waitFor 5000 do
        return (← e.status "end-ok") == .exitedOk && (← e.status "end-bad") == .exitedBad &&
            (← e.status "end-sig") == .exitedBad
  expect
      (okRc == 0 && badRc == 0 && sigRc == 0 && ended && (← e.field "end-ok" "exit") == some "0" &&
        (← e.field "end-bad" "exit") == some "3" &&
        (← e.field "end-sig" "signal") == some "15" &&
        (← e.field "end-ok" "state") == some "resumable")
      "an ended session stays listed, saved, with how its program ended"
  let human := lines (← e.out #["ls"])
  let says := fun (name detail : String) =>
    human.any fun row => has row s!" {name} " && has row detail
  expect
      (says "end-ok" "ended (status 0)" && says "end-bad" "ended (status 3)" &&
        says "end-sig" "ended (killed by signal 15)")
      s!"the listing says how each ended session's program ended ({human})"
  -- what asks for someone comes first: the failed endings before the clean one
  let order := human.filterMap fun row => ["end-bad", "end-ok", "end-sig"].find? (has row s!" {·} ")
  expect (order == ["end-bad", "end-sig", "end-ok"])
      s!"the listing puts the failed endings before the clean one ({order})"
  let (sumRc, summary, _) ← e.cli #["ls", "--summary"]
  expect (sumRc == 0 && summary == Linger.Display.Status.summary [.exitedBad, .exitedBad] ++ "\n")
      s!"the attention summary counts failed endings and not a clean one ({summary})"
  let (capRc, capOut, _) ← e.cli #["capture", "end-bad"]
  expect (capRc == 0 && has capOut "FAILED-42") "capture shows what an ended program left"
  let savedPath := s!"{e.dir}/end-bad.ckpt"
  -- read as a value, so a missing checkpoint is a failed check rather than an exception
  let saved ← (IO.FS.readBinFile savedPath).toBaseIO
  let (startRc, startErr) ← startIn e work #[] #["end-bad", "true"]
  expect
      (startRc == 1 && has startErr "ended (status 3)" && has startErr "kill it to discard it" &&
        saved.isOk &&
        (← (IO.FS.readBinFile savedPath).toBaseIO).toOption.map (·.toList) ==
          saved.toOption.map (·.toList) &&
        (← e.status "end-bad") == .exitedBad)
      s!"start refuses an ended session's name, saying how it ended ({startErr})"
  let (killRc, _, _) ← e.cli #["kill", "end-bad"]
  let (goneRc, _, _) ← e.cli #["capture", "end-bad"]
  let (waitRc, _, _) ← e.cli #["wait", "end-bad"]
  expect
      (killRc == 0 && !(← listed e).contains "end-bad" && goneRc == 127 && waitRc == 3 &&
        (← e.status "end-ok") == .exitedOk)
      s!"kill discards an ended session, and wait still answers from its record \
        ({killRc}, {goneRc}, {waitRc})"
  e.killAll #["end-ok", "end-sig"]
  expect ((← listed e).all fun name => !name.startsWith "end-")
      "kill discards every ended session it names"

/-- The agent suite: the one-shot verbs that see and drive a session. `send -` checks that the
program reads the bytes it is sent, byte for byte, and `start` that it runs with its words, in the
caller's directory and with the caller's environment. -/
@[exercises Linger.Session.Pty.Delivers, exercises Linger.Session.Spawn.Runs,
  exercises Linger.Session.Record.Kept]
def run : IO UInt32 :=
  Env.suite "agent" fun e => do
    startChecks e
    endedChecks e
    for (mode, why) in
      [("eof", "connection lost"), ("timeout", "no reply"), ("refused", "info refused"),
        ("malformed", "invalid response"), ("exited", "ended before"), ("utf8", "invalid UTF-8"),
        ("record", "invalid info record"), ("cap", "info reply exceeds")] do
      checkInfo e mode (some why)
    checkInfo e "complete" none
    checkInfo e "empty" none
    -- ── Step 1: info ──────────────────────────────────────────────────────────
    let _ ← e.typeIn "ag" #["true"] -- upsert a headless session (default shell)
    IO.sleep 1500
    let fresh := Linger.Session.bootVt none
    expect
        ((← e.info "ag" "cols") == some (toString fresh.colCount) &&
          (← e.info "ag" "rows") == some (toString fresh.rowCount))
        s!"headless session reports the {fresh.colCount}x{fresh.rowCount} default size"
    expect ((← e.info "ag" "alt") == some (toString false)) "alt is false outside a full-screen app"
    expect ((num (← e.info "ag" "cursorx")).isSome && (num (← e.info "ag" "cursory")).isSome)
        "cursor position is reported as numbers"
    expect ((num (← e.info "ag" "outseq")).isSome) "outseq is reported as a number"
    -- outseq moves when output happens — the change cursor
    let before := (num (← e.info "ag" "outseq")).getD 0
    let _ ← e.typeIn "ag" #["echo", "MOVED"]
    expect (← waitFor 4000 (return (num (← e.info "ag" "outseq")).getD 0 > before))
        "outseq increases after output"
    -- geometry follows an attached terminal. `Env.spawn` sets the winsize before
    -- exec, so the client's own startup `winsizeGet` already reads the size this
    -- check asks for.
    let attCols : UInt32 := 100
    let attRows : UInt32 := 30
    let cl ← e.spawn #["attach", "ag"] attCols attRows
    expect
        (←
          waitFor 4000 do
              return (← e.info "ag" "cols") == some (toString attCols) &&
                  (← e.info "ag" "rows") == some (toString attRows))
        "info reflects the attached terminal size"
    cl.bye -- detach, close, reap
    -- info against a missing session fails cleanly, quoting the name it looked for.
    let (irc, _, ierr) ← e.cli #["info", "nosuch"]
    expect (irc == 127 && has ierr "no session 'nosuch'")
        "info on a missing session exits 127 with a message"
    -- All arguments are valid; the daemon rejects the entry beyond its label cap.
    let labels := (List.range (Linger.Session.maxLabels + 1)).map fun i => s!"probe-{i}=value"
    let (lrc, _, lerr) ← e.cli (#["set", "ag"] ++ labels.toArray)
    expect (lrc == 1 && has lerr "too many labels")
        "a daemon-rejected label exits 1 with its reason"
    let _ ← e.cli #["clear", "ag"]
    -- A malformed daemon response must also fail. The fake server is this suite
    -- binary in a child mode, so the wire bytes and maxPayload come from Core.
    let badPath := s!"{e.dir}/malformed.sock"
    let badReady := s!"{e.dir}/malformed.ready"
    let self ← IO.appPath
    let badServer ←
      IO.Process.spawn
          { cmd := self.toString, args := #["--malformed-server", badPath, badReady],
            stdout := .null, stderr := .piped }
    unless (← waitFor 5000 (System.FilePath.pathExists badReady)) do
      throw (IO.userError "malformed-frame server did not become ready")
    let (mrc, _, merr) ← e.cli #["set", "malformed", "k=v"]
    let serverRc ← badServer.wait
    expect (serverRc == 0 && mrc == 1 && has merr "invalid response")
        "a malformed daemon response exits 1"
    -- ── Step 2: capture ───────────────────────────────────────────────────────
    let _ ← e.typeIn "ag" #["echo", "CAPTURED-MARKER"]
    -- the command's own output line, then the prompt after it: the shell is idle
    -- again, so the capture below sees everything it printed. `--history` leaves
    -- attention alone for the seen check.
    let _ ←
      waitFor 4000
          (return outputThenPrompt (← e.out #["capture", "--history", "ag"]) "CAPTURED-MARKER")
    let (capRc, capOut, _) ← e.cli #["capture", "ag"]
    let lines := capOut.splitOn "\n"
    let rows := (num (← e.info "ag" "rows")).getD 0
    expect (capRc == 0 && lines.contains "CAPTURED-MARKER") "capture shows what the session printed"
    -- screenText is LF-terminated per row: split yields rows + one trailing ''
    expect (lines.length == rows + 1 && lines.getLast? == some "")
        "capture is exactly one line per row"
    -- capture marks the session seen (the porcelain unseen flag flips)
    expect
        ((← e.info "ag" "unseen") == some (toString false) &&
          num (← e.info "ag" "behind") == some 0)
        "capture marks the session seen"
    let _ ← e.typeIn "ag" #["echo", "again"]
    expect (← waitFor 4000 (return (← e.info "ag" "unseen") == some (toString true)))
        "output after a capture reads unseen again"
    -- capture is the screen, not the transcript: flood past one screen and the
    -- capture stays `rows` lines while history grows beyond it
    let _ ← e.typeIn "ag" #["seq", "1", "60"]
    let _ ←
      waitFor 4000 do
          return ((← e.out #["capture", "--history", "ag"]).splitOn "\n").length > rows + 1
    let cap2 := (← e.out #["capture", "ag"]).splitOn "\n"
    let hist := (← e.out #["capture", "--history", "ag"]).splitOn "\n"
    expect (cap2.length == rows + 1 && hist.length > cap2.length)
        "capture stays screen-sized while history grows"
    expect ((← e.cli #["capture", "nosuch"]).1 == 127) "capture on a missing session exits 127"
    -- ── Step 3: send - (raw stdin) ────────────────────────────────────────────
    -- a full command line with its newline arrives verbatim and executes. The
    -- marker is asserted on the *expansion* (GOT-42), which the typed line does
    -- not contain — the tty echoes typed input onto the screen, so asserting on
    -- the typed text would pass even if the newline was lost and nothing ran
    -- (SCRATCHPAD 2026-08-19).
    let src ← sendStdin e "ag" "echo \"GOT-$((40+2))\"\n"
    expect
        (src == 0 &&
          (←
            waitFor 4000
                (do
                  return has (← e.out #["capture", "ag"]) "GOT-42")))
        "send - delivers bytes verbatim (newline included: it ran)"
    -- a control byte works: ^C interrupts a foreground child, after which the
    -- queued next line is read and runs (same trick: the typed line says
    -- INTER""RUPTED-OK, only the executed output says INTERRUPTED-OK)
    --
    -- The child ANNOUNCES itself and the suite waits for that rather than sleeping a
    -- fixed second, so a slow host cannot make this look like a broken `^C`. The
    -- extra check is a discriminator: "the child never started" and "^C did not reach
    -- it" are different bugs, and separating them is what identified the one
    -- environment that breaks this assertion — a `&`-launched `./scripts/verify.sh`. That
    -- environment is now refused rather than described: see the "SIGINT must be
    -- deliverable" check in `scripts/verify.sh`, which holds the probe, the measurement and
    -- the reasoning, and is the only copy of them.
    let _ ← e.typeIn "ag" #["sh -c 'echo RUN\"\"NING-NOW; sleep 100'"]
    expect
        (←
          waitFor 5000
              (do
                return has (← e.out #["capture", "ag"]) "RUNNING-NOW"))
        "send - the foreground child is up (the ^C below has something to interrupt)"
    let _ ← sendStdin e "ag" "\x03"
    IO.sleep 500
    let _ ← e.typeIn "ag" #["echo", "INTER\"\"RUPTED-OK"]
    expect
        (←
          waitFor 5000
              (do
                return has (← e.out #["capture", "ag"]) "INTERRUPTED-OK"))
        "send - carries ^C (the foreground child died, the shell came back)"
    expect ((← sendStdin e "ag" "") == 0) "send - with empty stdin exits 0"
    expect ((← sendStdin e "nosuch" "x") == 127) "send - on a missing session exits 127"
    -- Keep stdin open and idle, then crash the daemon. The sender must observe the
    -- socket, not wait forever for producer EOF.
    let _ ← e.typeIn "send-lost" #["sleep", "600"]
    let sender0 ←
      IO.Process.spawn
          { cmd := e.bin, args := #["send", "send-lost", "-"], env := e.procEnv, stdin := .piped,
            stdout := .null, stderr := .piped }
    let (senderIn, sender) ← sender0.takeStdin
    IO.sleep 400
    unless (← e.crashDaemon "send-lost") do
      throw (IO.userError "send-lost daemon did not crash")
    let senderCode ← waitOrKill sender 3000
    try
      senderIn.flush
    catch _ =>
      pure ()
    let senderErr ← sender.stderr.readToEnd
    expect (senderCode == some 1 && has senderErr "connection lost")
        "send - exits 1 when the daemon dies while stdin is idle"
    e.killAll #["ag"]
    -- ── Step 4: resize ────────────────────────────────────────────────────────
    let _ ← e.typeIn "rz" #["true"]
    let rzCols : UInt32 := 120
    let rzRows : UInt32 := 40
    let (rrc, _, _) ← e.cli #["resize", "rz", toString rzCols, toString rzRows]
    expect
        (rrc == 0 &&
          (←
            waitFor 4000 do
                return (← e.info "rz" "cols") == some (toString rzCols) &&
                    (← e.info "rz" "rows") == some (toString rzRows)))
        "control resize applies to a detached session"
    -- the pty winsize followed too: the child's own stty sees it (SIGWINCH path).
    -- `stty size` prints rows then cols, so the expected string is built from the
    -- two numbers above rather than being a third copy of them.
    let _ ← e.typeIn "rz" #["stty", "size"]
    expect (← waitFor 4000 (return has (← e.out #["capture", "rz"]) s!"{rzRows} {rzCols}"))
        "the child observes the new winsize (stty size: 40 120)"
    -- an attached client owns the size: refused, loudly, and nothing moves
    let ownCols : UInt32 := 80
    let ownRows : UInt32 := 24
    let owner ← e.spawn #["attach", "rz"] ownCols ownRows
    let _ ←
      waitFor 4000 do
          return (← e.info "rz" "clients") == some "1" &&
              (← e.info "rz" "cols") == some (toString ownCols)
    let newCols : UInt32 := 90
    let newRows : UInt32 := 25
    let (frc, _, ferr) ← e.cli #["resize", "rz", toString newCols, toString newRows]
    expect (frc == 1 && has ferr "owns the size") "resize is refused while a client is attached"
    expect ((← e.info "rz" "cols") == some (toString ownCols)) "a refused resize moved nothing"
    owner.bye
    let (arc, _, _) ← e.cli #["resize", "rz", toString newCols, toString newRows]
    expect (arc == 0 && (← waitFor 4000 (return (← e.info "rz" "cols") == some (toString newCols))))
        "resize applies again once the client detached"
    -- client-side validation accepts exactly `clampDim`'s range. Both probes are
    -- the boundary itself: 0 is the largest rejected value below the range, and
    -- `clampDim` saturating means `clampDim 5000 + 1` is the smallest rejected
    -- value above it.
    let tooBig := Linger.Terminal.Vt.clampDim 5000 + 1
    let (zrc, _, _) ← e.cli #["resize", "rz", "0", "10"]
    let (brc, _, _) ← e.cli #["resize", "rz", toString tooBig, "10"]
    expect (zrc == 2 && brc == 2) "zero and oversize are rejected client-side"
    expect ((← e.cli #["resize", "nosuch", "80", "24"]).1 == 127)
        "resize on a missing session exits 127"
    e.killAll #["rz"]
    -- An empty or unset SHELL names no program: a resume falls back to the default shell
    -- (`shellOf_absent`). The harness sets SHELL for every other session.
    for (kind, shell) in [("empty", some ""), ("unset", none)] do
      let name := s!"shell-{kind}"
      let (startRc, _, _) ← e.cli #["start", name, "/bin/sh", "-c", "exit 0"]
      let ended ← waitFor 5000 (return (← e.status name) == .exitedOk)
      let resumed ←
        IO.Process.output
            { cmd := e.bin, args := #["resume", name],
              env := #[("LINGER_DIR", some e.dir), ("SHELL", shell)] }
      let (sendRc, _, _) ← e.cli #["send", name, s!"echo {kind}-shell-$((40+2))\n"]
      expect
          (startRc == 0 && ended && resumed.exitCode == 0 && sendRc == 0 &&
            (←
              waitFor 5000
                  (do
                    return has (← e.out #["capture", name]) s!"{kind}-shell-42")))
          s!"an {kind} SHELL still resumes a session running the default shell \
            ({startRc}, {resumed.exitCode}, {sendRc})"
      e.killAll #[name]

end Linger.Session.Suites.Agent
