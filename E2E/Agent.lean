module

public import E2E.Harness
import Linger.Runtime.Cli

public section

/-! # E2E.Agent — the agent verbs: see and drive a session one-shot

Ported from `tests/agent_test.py`; the spec is `specs/archive/agent-cli.md`.

Step 1: `linger info <name>` and the observability fields — geometry + cursor
(what `capture` needs), `alt`, and `outseq` (the change cursor: "look again only
when it moved"). Step 2: `linger capture <name>` — the screen as plain text, one
line per row, and capturing marks the session seen. Step 3: `linger send <name> -`
— stdin to the pty byte-exact. Step 4: `linger resize` — applies detached (down to
the child's own winsize, via `stty size`), refused while a client is attached. All
pinned against the rendered porcelain/bytes, end to end.

`alt` and `unseen` compare to `toString false` / `toString true`, because that is
literally what `Session.infoFields` emits (`toString` of a `Bool`). Two facts could
NOT be tied to the implementation — read before adding a check:

* the 80×24 default is a literal `Vt.init 80 24` inside `Daemon.serve`, so a
  Lean-side tie would restate the constant rather than derive it;
* "capture is exactly one line per row" could not be tied to
  `Render.screenText` either — the row count is a property of a `Vt` this
  process does not hold. `rows` comes from the session's own `info`, which is as
  close as the porcelain gets. -/

namespace E2E.Agent

open E2E.Harness

/-- A field as a natural number: `none` when it is absent, empty or not all digits. -/
def num (o : Option String) : Option Nat := o.bind (·.toNat?)

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
is legitimate, and EOF is the only exit"), so a port that kept the handle alive
would hang here instead of failing.

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
  let lfd ← Linger.Posix.unixListen socketPath
  Linger.Posix.setNonblock lfd
  IO.FS.writeFile readyPath "ready"
  let rc ←
    match ← acceptWithin lfd 5000 with
    | none =>
      pure 1
    | some fd =>
      let tooLarge := UInt32.ofNat (Linger.Core.Wire.maxPayload + 1)
      Linger.Posix.writeAll fd
          (ByteArray.mk ((0 : UInt8) :: Linger.Core.Wire.writeU32 tooLarge).toArray)
      Linger.Posix.close fd
      pure 0
  Linger.Posix.close lfd
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
  let lfd ← Linger.Posix.unixListen socketPath
  Linger.Posix.setNonblock lfd
  try
    IO.FS.writeFile readyPath "ready"
    for _ in [:2] do
      let some fd ← acceptWithin lfd 5000 | return 1
      try
        let ready ← Linger.Posix.poll #[fd] #[Linger.Posix.POLLIN] 2000
        if ready[0]! == 0 then
          return 1
        let _ ← Linger.Posix.read fd 65536
        let _ ←
          try
            if mode != "empty" then
              Linger.Runtime.Client.sendMsg fd
                  (.infoReply "pid\t1\ncmd\tfixture\nlabel.partial\tvalue\n".toUTF8.toList)
            match mode with
            | "eof" =>
              pure ()
            | "timeout" =>
              IO.sleep 2400
            | "refused" =>
              Linger.Runtime.Client.sendMsg fd (.err "info refused\x1b[31m".toUTF8.toList)
            | "malformed" =>
              Linger.Posix.writeAll fd
                  (ByteArray.mk
                    ((0 : UInt8) ::
                        Linger.Core.Wire.writeU32
                          (UInt32.ofNat (Linger.Core.Wire.maxPayload + 1))).toArray)
            | "exited" =>
              Linger.Runtime.Client.sendMsg fd (.exited 17)
            | "utf8" =>
              Linger.Runtime.Client.sendMsg fd (.infoReply [0xFF])
              Linger.Runtime.Client.sendMsg fd .done
            | "record" =>
              Linger.Runtime.Client.sendMsg fd (.infoReply "broken record\n".toUTF8.toList)
              Linger.Runtime.Client.sendMsg fd .done
            | "cap" =>
              let fieldStart := "padding\t".toUTF8.toList
              let payload :=
                fieldStart ++
                  List.replicate (Linger.Core.Wire.maxPayload - fieldStart.length - 1)
                    (UInt8.ofNat 120) ++
                  [10]
              for _ in [:Linger.Runtime.Cli.infoReplyCap / Linger.Core.Wire.maxPayload + 1] do
                Linger.Runtime.Client.sendMsg fd (.infoReply payload)
              Linger.Runtime.Client.sendMsg fd .done
            | "complete" =>
              Linger.Runtime.Client.sendMsg fd (.infoReply "label.second\tanother\n".toUTF8.toList)
              Linger.Runtime.Client.sendMsg fd .done
            | "failed-info" =>
              Linger.Runtime.Client.sendMsg fd (.infoReply "exit\t7\n".toUTF8.toList)
              Linger.Runtime.Client.sendMsg fd .done
            | "empty" =>
              Linger.Runtime.Client.sendMsg fd .done
            | _ =>
              return 1
          catch _ =>
            -- A client may reject the frame and close before the last write.
            pure ()
        pure ()
      finally
        Linger.Posix.close fd
    return 0
  finally
    Linger.Posix.close lfd

def checkInfo (e : Env) (mode : String) (error : Option String) : IO Unit := do
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
            recs.contains ("status", Linger.Core.Status.name .unknown) &&
            !recs.any (fun kv => kv.1 == "cmd" || kv.1.startsWith "label."))
          s!"listing retains {mode} info peer as live/unknown without partial fields"
    | none =>
      let expected := if mode == "empty" then "" else "partial=value\nsecond=another\n"
      expect (serverRc == some 0 && rc == 0 && out == expected && err.isEmpty)
          s!"get accepts {mode} info terminated by done"
  finally
    try
      if (← server.tryWait).isNone then
        server.kill
        let _ ← server.wait
    catch _ =>
      pure () -- waitProcess already reaped it.
    IO.FS.removeFile socketPath
    IO.FS.removeFile readyPath

def run : IO UInt32 :=
  Env.suite "agent" fun e => do
    for (mode, why) in
      [("eof", "connection lost"), ("timeout", "no reply"), ("refused", "info refused"),
        ("malformed", "invalid response"), ("exited", "ended before"), ("utf8", "invalid UTF-8"),
        ("record", "invalid info record"), ("cap", "info reply exceeds")] do
      checkInfo e mode (some why)
    checkInfo e "complete" none
    checkInfo e "empty" none
    -- ── Step 1: info ──────────────────────────────────────────────────────────
    let _ ← e.cli #["run", "ag", "true"] -- upsert a headless session (default shell)
    IO.sleep 1500
    expect ((← e.info "ag" "cols") == some "80" && (← e.info "ag" "rows") == some "24")
        "headless session reports the 80x24 default size"
    expect ((← e.info "ag" "alt") == some (toString false)) "alt is false outside a full-screen app"
    expect ((num (← e.info "ag" "cursorx")).isSome && (num (← e.info "ag" "cursory")).isSome)
        "cursor position is reported as numbers"
    expect ((num (← e.info "ag" "outseq")).isSome) "outseq is reported as a number"
    -- outseq moves when output happens — the change cursor
    let before := (num (← e.info "ag" "outseq")).getD 0
    let _ ← e.cli #["run", "ag", "echo", "MOVED"]
    let _ ← waitFor 4000 (return (num (← e.info "ag" "outseq")).getD 0 > before)
    let after := (num (← e.info "ag" "outseq")).getD 0
    expect (after > before) "outseq increases after output"
    -- geometry follows an attached terminal. `Env.spawn` sets the winsize before
    -- exec, so the client's own startup `winsizeGet` already reads the size this
    -- check asks for.
    let attCols : UInt32 := 100
    let attRows : UInt32 := 30
    let cl ← e.spawn #["attach", "ag"] attCols attRows
    let _ ←
      waitFor 4000 do
          return (← e.info "ag" "cols") == some (toString attCols) &&
              (← e.info "ag" "rows") == some (toString attRows)
    expect
        ((← e.info "ag" "cols") == some (toString attCols) &&
          (← e.info "ag" "rows") == some (toString attRows))
        "info reflects the attached terminal size"
    cl.bye -- detach, close, reap
    -- info against a missing session fails cleanly, quoting the name it looked for.
    let (irc, _, ierr) ← e.cli #["info", "nosuch"]
    expect (irc == 1 && has ierr "no session 'nosuch'")
        "info on a missing session exits 1 with a message"
    -- All arguments are valid; the daemon rejects the entry beyond its label cap.
    let labels := (List.range (Linger.Core.Session.maxLabels + 1)).map fun i => s!"probe-{i}=value"
    let (lrc, _, lerr) ← e.cli (#["set", "ag"] ++ labels.toArray)
    expect (lrc == 1 && has lerr "too many labels")
        "a daemon-rejected label exits 1 with its reason"
    let _ ← e.cli #["clear", "ag"]
    -- A malformed daemon response must also fail. The fake server is this e2e
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
    let _ ← e.cli #["run", "ag", "echo", "CAPTURED-MARKER"]
    -- the command's own output line, then the prompt after it: the shell is idle
    -- again, so the capture below sees everything it printed. `--history` leaves
    -- attention alone for the seen check.
    let _ ←
      waitFor 4000
          (return outputThenPrompt (← e.out #["capture", "--history", "ag"]) "CAPTURED-MARKER")
    let (capRc, capOut, _) ← e.cli #["capture", "ag"]
    let lines := capOut.splitOn "\n"
    let rows := (num (← e.info "ag" "rows")).getD 0
    expect (capRc == 0 && has capOut "CAPTURED-MARKER") "capture shows what the session printed"
    -- screenText is LF-terminated per row: split yields rows + one trailing ''
    expect (lines.length == rows + 1 && lines.getLast? == some "")
        "capture is exactly one line per row"
    -- capture marks the session seen (the porcelain unseen flag flips)
    expect
        ((← e.info "ag" "unseen") == some (toString false) &&
          num (← e.info "ag" "behind") == some 0)
        "capture marks the session seen"
    let _ ← e.cli #["run", "ag", "echo", "again"]
    let _ ← waitFor 4000 (return (← e.info "ag" "unseen") == some (toString true))
    expect ((← e.info "ag" "unseen") == some (toString true))
        "output after a capture reads unseen again"
    -- capture is the screen, not the transcript: flood past one screen and the
    -- capture stays `rows` lines while history grows beyond it
    let _ ← e.cli #["run", "ag", "seq", "1", "60"]
    let _ ←
      waitFor 4000 do
          return ((← e.out #["capture", "--history", "ag"]).splitOn "\n").length > rows + 1
    let cap2 := (← e.out #["capture", "ag"]).splitOn "\n"
    let hist := (← e.out #["capture", "--history", "ag"]).splitOn "\n"
    expect (cap2.length == rows + 1 && hist.length > cap2.length)
        "capture stays screen-sized while history grows"
    expect ((← e.cli #["capture", "nosuch"]).1 == 1) "capture on a missing session exits 1"
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
    -- environment that breaks this assertion — a `&`-launched `./scripts/e2e.sh`. That
    -- environment is now refused rather than described: see the "SIGINT must be
    -- deliverable" check in `scripts/e2e.sh`, which holds the probe, the measurement and
    -- the reasoning, and is the only copy of them.
    let _ ← e.cli #["run", "ag", "sh -c 'echo RUN\"\"NING-NOW; sleep 100'"]
    expect
        (←
          waitFor 5000
              (do
                return has (← e.out #["capture", "ag"]) "RUNNING-NOW"))
        "send - the foreground child is up (the ^C below has something to interrupt)"
    let _ ← sendStdin e "ag" "\x03"
    IO.sleep 500
    let _ ← e.cli #["run", "ag", "echo", "INTER\"\"RUPTED-OK"]
    expect
        (←
          waitFor 5000
              (do
                return has (← e.out #["capture", "ag"]) "INTERRUPTED-OK"))
        "send - carries ^C (the foreground child died, the shell came back)"
    expect ((← sendStdin e "ag" "") == 0) "send - with empty stdin exits 0"
    expect ((← sendStdin e "nosuch" "x") == 1) "send - on a missing session exits 1"
    -- Keep stdin open and idle, then crash the daemon. The sender must observe the
    -- socket, not wait forever for producer EOF.
    let _ ← e.cli #["run", "send-lost", "sleep", "600"]
    let sender0 ←
      IO.Process.spawn
          { cmd := e.bin, args := #["send", "send-lost", "-"], env := e.procEnv, stdin := .piped,
            stdout := .null, stderr := .piped }
    let (senderIn, sender) ← sender0.takeStdin
    IO.sleep 400
    unless (← e.crashDaemon "send-lost") do
      throw (IO.userError "send-lost daemon did not crash")
    let senderCode ← waitProcess sender 3000
    try
      senderIn.flush
    catch _ =>
      pure ()
    if senderCode.isNone then
      sender.kill
      let _ ← sender.wait
    let senderErr ← sender.stderr.readToEnd
    expect (senderCode == some 1 && has senderErr "connection lost")
        "send - exits 1 when the daemon dies while stdin is idle"
    e.killAll #["ag"]
    -- ── Step 4: resize ────────────────────────────────────────────────────────
    let _ ← e.cli #["run", "rz", "true"]
    let rzCols : UInt32 := 120
    let rzRows : UInt32 := 40
    let (rrc, _, _) ← e.cli #["resize", "rz", toString rzCols, toString rzRows]
    let _ ←
      waitFor 4000 do
          return (← e.info "rz" "cols") == some (toString rzCols) &&
              (← e.info "rz" "rows") == some (toString rzRows)
    expect
        (rrc == 0 && (← e.info "rz" "cols") == some (toString rzCols) &&
          (← e.info "rz" "rows") == some (toString rzRows))
        "control resize applies to a detached session"
    -- the pty winsize followed too: the child's own stty sees it (SIGWINCH path).
    -- `stty size` prints rows then cols, so the expected string is built from the
    -- two numbers above rather than being a third copy of them.
    let _ ← e.cli #["run", "rz", "stty", "size"]
    let _ ← waitFor 4000 (return has (← e.out #["capture", "rz"]) s!"{rzRows} {rzCols}")
    expect (has (← e.out #["capture", "rz"]) s!"{rzRows} {rzCols}")
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
    let _ ← waitFor 4000 (return (← e.info "rz" "cols") == some (toString newCols))
    expect (arc == 0 && (← e.info "rz" "cols") == some (toString newCols))
        "resize applies again once the client detached"
    -- client-side validation accepts exactly `clampDim`'s range. Both probes are
    -- the boundary itself: 0 is the largest rejected value below the range, and
    -- `clampDim` saturating means `clampDim 5000 + 1` is the smallest rejected
    -- value above it.
    let tooBig := Linger.Core.Vt.clampDim 5000 + 1
    let (zrc, _, _) ← e.cli #["resize", "rz", "0", "10"]
    let (brc, _, _) ← e.cli #["resize", "rz", toString tooBig, "10"]
    expect (zrc == 2 && brc == 2) "zero and oversize are rejected client-side"
    expect ((← e.cli #["resize", "nosuch", "80", "24"]).1 == 1)
        "resize on a missing session exits 1"
    e.killAll #["rz"]
    -- An empty SHELL names no program: creation falls back to the default shell.
    let created ←
      IO.Process.output
          { cmd := e.bin, args := #["run", "shell-empty", "echo empty-shell-$((40+2))"],
            env := #[("LINGER_DIR", some e.dir), ("SHELL", some "")] }
    expect
        (created.exitCode == 0 &&
          (←
            waitFor 5000
                (do
                  return has (← e.out #["capture", "shell-empty"]) "empty-shell-42")))
        "an empty SHELL still creates a session running the default shell"
    e.killAll #["shell-empty"]

end E2E.Agent
