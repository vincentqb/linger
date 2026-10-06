module

public import E2E.Harness
public import Linger.Core.Wire
public import Linger.Runtime.Cli

public section

/-! # E2E.Agent — the agent verbs: see and drive a session one-shot

Ported from `tests/agent_test.py`; the spec is `specs/archive/agent-cli.md`.

Step 1: `linger info <name>` and the observability fields — geometry + cursor
(what `capture` needs), `alt`, and `outseq` (the change cursor: "look again only
when it moved"). Step 2: `linger capture <name>` — the screen as plain text, one
line per row, and capturing marks the session seen. Step 3: `linger send <name> -`
— stdin to the pty byte-exact (the oracles assert on shell *expansions*: the tty
echoes typed input onto the screen, so a typed-text marker would pass even if the
bytes never ran; see SCRATCHPAD 2026-08-19). Step 4: `linger resize` — applies
detached (down to the child's own winsize, via `stty size`), refused while a
client is attached. All pinned against the rendered porcelain/bytes, end to end.

WHAT THE PORT TIGHTENED, and what it could not — read before adding a check:

* every geometry assertion compares against the number this suite *asked* for
  (the `let`s below), not against a second copy of it spelled out as a string;
* the oversize `resize` probe is derived from `Vt.clampDim` instead of the flat
  `5000` the Python used. `clampDim` saturates, so `clampDim n + 1` is the
  SMALLEST value the client must reject — the boundary, not a value well past
  it. If `Cli`'s own `1000` literal ever drifts from `clampDim`'s range, this
  is the check that fails;
* `alt` and `unseen` compare to `toString false` / `toString true`, because that
  is literally what `Session.infoFields` emits (`toString` of a `Bool`);
* the 80×24 default could NOT be tied to anything: it is a literal
  `Vt.init 80 24` inside `Daemon.serve`, so a Lean-side tie would restate the
  constant rather than derive it;
* "capture is exactly one line per row" could not be tied to
  `Render.screenText` either — the row count is a property of a `Vt` this
  process does not hold. `rows` comes from the session's own `info`, which is as
  close as the porcelain gets. -/

namespace E2E.Agent

open E2E.Harness

/-- Python's `.isdigit()` and `int(...)` in one move: `String.toNat?` is `none`
for the empty string and for anything carrying a non-digit, which is exactly what
`''.isdigit()` being False stood for at the two "is reported as a number" checks. -/
def num (o : Option String) : Option Nat := o.bind (·.toNat?)

/-- `linger send <name> -` with `payload` on its stdin, byte-exact.

`IO.Process.output`'s `input?` argument *is* the mechanism, so no new harness
primitive is needed: core spawns with `stdin := .piped`, `takeStdin`s the handle
away from the `Child`, writes, flushes, and then drops it — and dropping the last
reference is what closes the pipe. That close is load-bearing, not hygiene:
`Cli.cmdSendStdin` has **no timeout on purpose** ("a slow producer feeding a pipe
is legitimate, and EOF is the only exit"), so a port that kept the handle alive
would hang here instead of failing.

`putStr` writes the payload's UTF-8, and all three payloads below are ASCII or a
single C0 byte, so the bytes on the pipe are the Python's bytes exactly. A
payload that is not valid UTF-8 would need `spawn` + `takeStdin` + `Handle.write`
on a `ByteArray`; nothing here does. -/
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
  let deadline := (← Linger.Posix.monotonicMs) + 5000
  let mut client : Option UInt32 := none
  while client.isNone && (← Linger.Posix.monotonicMs) < deadline do
    let fd ← Linger.Posix.accept lfd
    if fd ≥ 0 then
      client := some fd.toUInt64.toUInt32
    else
      IO.sleep 20
  let rc ←
    match client with
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
      let deadline := (← Linger.Posix.monotonicMs) + 5000
      let mut peer : Option UInt32 := none
      while peer.isNone && (← Linger.Posix.monotonicMs) < deadline do
        let fd ← Linger.Posix.accept lfd
        if fd ≥ 0 then
          peer := some fd.toUInt64.toUInt32
        else
          IO.sleep 20
      let some fd := peer | return 1
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

def checkInfo (e : Env) (mode : String) (error : Option String) : IO Nat := do
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
      let getCheck ←
        expect (rc == 1 && out.isEmpty && has err why && !has err "\x1b")
            s!"get rejects {mode} info without printing partial labels"
      let listCheck ←
        expect
            (serverRc == some 0 && lrc == 0 && pathKept && recs.contains ("name", name) &&
              recs.contains ("state", "live") &&
              recs.contains ("status", Linger.Core.Status.name .unknown) &&
              !recs.any (fun kv => kv.1 == "cmd" || kv.1.startsWith "label."))
            s!"listing retains {mode} info peer as live/unknown without partial fields"
      return getCheck + listCheck
    | none =>
      let expected := if mode == "empty" then "" else "partial=value\nsecond=another\n"
      return ←
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

def run : IO UInt32 := do
  let e ← Env.make "agent"
  let mut f := 0
  for (mode, why) in
    [("eof", "connection lost"), ("timeout", "no reply"), ("refused", "info refused"),
      ("malformed", "invalid response"), ("exited", "ended before"), ("utf8", "invalid UTF-8"),
      ("record", "invalid info record"), ("cap", "info reply exceeds")] do
    f := f + (← checkInfo e mode (some why))
  f := f + (← checkInfo e "complete" none)
  f := f + (← checkInfo e "empty" none)
  -- ── Step 1: info ──────────────────────────────────────────────────────────
  let _ ← e.cli #["run", "ag", "true"] -- upsert a headless session (default shell)
  IO.sleep 1500
  f :=
    f +
      (←
        expect ((← e.info "ag" "cols") == some "80" && (← e.info "ag" "rows") == some "24")
            "headless session reports the 80x24 default size")
  f :=
    f +
      (←
        expect ((← e.info "ag" "alt") == some (toString false))
            "alt is false outside a full-screen app")
  f :=
    f +
      (←
        expect ((num (← e.info "ag" "cursorx")).isSome && (num (← e.info "ag" "cursory")).isSome)
            "cursor position is reported as numbers")
  f := f + (← expect ((num (← e.info "ag" "outseq")).isSome) "outseq is reported as a number")
  -- outseq moves when output happens — the change cursor
  let before := (num (← e.info "ag" "outseq")).getD 0
  let _ ← e.cli #["run", "ag", "echo", "MOVED"]
  IO.sleep 1200
  let after := (num (← e.info "ag" "outseq")).getD 0
  f := f + (← expect (after > before) "outseq increases after output")
  -- geometry follows an attached terminal. `Env.spawn` sets the winsize BEFORE
  -- exec, so the `pty.fork()`-then-`ioctl(TIOCSWINSZ)` race the Python had
  -- against the client's own startup `winsizeGet` is gone — and this check is
  -- the one whose subject is precisely the size a client reported.
  let attCols : UInt32 := 100
  let attRows : UInt32 := 30
  let cl ← e.spawn #["attach", "ag"] attCols attRows
  IO.sleep 1500
  f :=
    f +
      (←
        expect
            ((← e.info "ag" "cols") == some (toString attCols) &&
              (← e.info "ag" "rows") == some (toString attRows))
            "info reflects the attached terminal size")
  cl.bye -- detach, close, reap
  -- info against a missing session fails cleanly. The quoted name is part of
  -- the message `requireLiveBounded` prints, so the port pins it: the Python
  -- accepted any "no session" text at all.
  let (irc, _, ierr) ← e.cli #["info", "nosuch"]
  f :=
    f +
      (←
        expect (irc == 1 && has ierr "no session 'nosuch'")
            "info on a missing session exits 1 with a message")
  -- All arguments are valid; the daemon rejects the entry beyond its label cap.
  let labels := (List.range (Linger.Core.Session.maxLabels + 1)).map fun i => s!"probe-{i}=value"
  let (lrc, _, lerr) ← e.cli (#["set", "ag"] ++ labels.toArray)
  f :=
    f +
      (←
        expect (lrc == 1 && has lerr "too many labels")
            "a daemon-rejected label exits 1 with its reason")
  let _ ← e.cli #["clear", "ag"]
  -- A malformed daemon response must also fail. The fake server is this e2e
  -- binary in a child mode, so the wire bytes and maxPayload come from Core.
  let badPath := s!"{e.dir}/malformed.sock"
  let badReady := s!"{e.dir}/malformed.ready"
  let self ← IO.appPath
  let badServer ←
    IO.Process.spawn
        { cmd := self.toString, args := #["--malformed-server", badPath, badReady], stdout := .null,
          stderr := .piped }
  unless (← waitFor 5000 (System.FilePath.pathExists badReady)) do
    throw (IO.userError "malformed-frame server did not become ready")
  let (mrc, _, merr) ← e.cli #["set", "malformed", "k=v"]
  let serverRc ← badServer.wait
  f :=
    f +
      (←
        expect (serverRc == 0 && mrc == 1 && has merr "invalid response")
            "a malformed daemon response exits 1")
  -- ── Step 2: capture ───────────────────────────────────────────────────────
  let _ ← e.cli #["run", "ag", "echo", "CAPTURED-MARKER"]
  IO.sleep 1200
  let (capRc, capOut, _) ← e.cli #["capture", "ag"]
  let lines := capOut.splitOn "\n"
  let rows := (num (← e.info "ag" "rows")).getD 0
  f :=
    f +
      (←
        expect (capRc == 0 && has capOut "CAPTURED-MARKER")
            "capture shows what the session printed")
  -- screenText is LF-terminated per row: split yields rows + one trailing ''
  f :=
    f +
      (←
        expect (lines.length == rows + 1 && lines.getLast? == some "")
            "capture is exactly one line per row")
  -- capture marks the session seen (the porcelain unseen flag flips)
  f :=
    f +
      (←
        expect
            ((← e.info "ag" "unseen") == some (toString false) &&
              num (← e.info "ag" "behind") == some 0)
            "capture marks the session seen")
  let _ ← e.cli #["run", "ag", "echo", "again"]
  IO.sleep 1200
  f :=
    f +
      (←
        expect ((← e.info "ag" "unseen") == some (toString true))
            "output after a capture reads unseen again")
  -- capture is the screen, not the transcript: flood past one screen and the
  -- capture stays `rows` lines while history grows beyond it
  let _ ← e.cli #["run", "ag", "seq", "1", "60"]
  IO.sleep 1500
  let cap2 := (← e.out #["capture", "ag"]).splitOn "\n"
  let hist := (← e.out #["history", "ag"]).splitOn "\n"
  f :=
    f +
      (←
        expect (cap2.length == rows + 1 && hist.length > cap2.length)
            "capture stays screen-sized while history grows")
  f :=
    f + (← expect ((← e.cli #["capture", "nosuch"]).1 == 1) "capture on a missing session exits 1")
  -- ── Step 3: send - (raw stdin) ────────────────────────────────────────────
  -- a full command line with its newline arrives verbatim and executes. The
  -- marker is asserted on the *expansion* (GOT-42), which the typed line does
  -- not contain — the tty echoes typed input onto the screen, so asserting on
  -- the typed text would pass even if the newline was lost and nothing ran.
  let src ← sendStdin e "ag" "echo \"GOT-$((40+2))\"\n"
  f :=
    f +
      (←
        expect
            (src == 0 &&
              (←
                waitFor 4000
                    (do
                      return has (← e.out #["capture", "ag"]) "GOT-42")))
            "send - delivers bytes verbatim (newline included: it ran)")
  -- a control byte works: ^C interrupts a foreground child, after which the
  -- queued next line is read and runs (same trick: the typed line says
  -- INTER""RUPTED-OK, only the executed output says INTERRUPTED-OK)
  --
  -- The child ANNOUNCES itself and the suite waits for that rather than sleeping a
  -- fixed second, so a slow host cannot make this look like a broken `^C`. The
  -- extra check is a discriminator: "the child never started" and "^C did not reach
  -- it" are different bugs, and separating them is what identified the one
  -- environment that breaks this assertion — a `&`-launched `./tests/e2e.sh`. That
  -- environment is now refused rather than described: see the "SIGINT must be
  -- deliverable" check in `tests/e2e.sh`, which holds the probe, the measurement and
  -- the reasoning, and is the only copy of them.
  let _ ← e.cli #["run", "ag", "sh -c 'echo RUN\"\"NING-NOW; sleep 100'"]
  f :=
    f +
      (←
        expect
            (←
              waitFor 5000
                  (do
                    return has (← e.out #["capture", "ag"]) "RUNNING-NOW"))
            "send - the foreground child is up (the ^C below has something to interrupt)")
  let _ ← sendStdin e "ag" "\x03"
  IO.sleep 500
  let _ ← e.cli #["run", "ag", "echo", "INTER\"\"RUPTED-OK"]
  f :=
    f +
      (←
        expect
            (←
              waitFor 5000
                  (do
                    return has (← e.out #["capture", "ag"]) "INTERRUPTED-OK"))
            "send - carries ^C (the foreground child died, the shell came back)")
  f := f + (← expect ((← sendStdin e "ag" "") == 0) "send - with empty stdin exits 0")
  f := f + (← expect ((← sendStdin e "nosuch" "x") == 1) "send - on a missing session exits 1")
  -- Keep stdin open and idle, then crash the daemon. The sender must observe the
  -- socket, not wait forever for producer EOF.
  let _ ← e.cli #["run", "send-lost", "sleep", "600"]
  IO.sleep 800
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
  f :=
    f +
      (←
        expect (senderCode == some 1 && has senderErr "connection lost")
            "send - exits 1 when the daemon dies while stdin is idle")
  e.killAll #["ag"]
  -- ── Step 4: resize ────────────────────────────────────────────────────────
  let _ ← e.cli #["run", "rz", "true"]
  IO.sleep 1500
  let rzCols : UInt32 := 120
  let rzRows : UInt32 := 40
  let (rrc, _, _) ← e.cli #["resize", "rz", toString rzCols, toString rzRows]
  IO.sleep 1000
  f :=
    f +
      (←
        expect
            (rrc == 0 && (← e.info "rz" "cols") == some (toString rzCols) &&
              (← e.info "rz" "rows") == some (toString rzRows))
            "control resize applies to a detached session")
  -- the pty winsize followed too: the child's own stty sees it (SIGWINCH path).
  -- `stty size` prints rows then cols, so the expected string is built from the
  -- two numbers above rather than being a third copy of them.
  let _ ← e.cli #["run", "rz", "stty", "size"]
  IO.sleep 1200
  f :=
    f +
      (←
        expect (has (← e.out #["capture", "rz"]) s!"{rzRows} {rzCols}")
            "the child observes the new winsize (stty size: 40 120)")
  -- an attached client owns the size: refused, loudly, and nothing moves
  let ownCols : UInt32 := 80
  let ownRows : UInt32 := 24
  let owner ← e.spawn #["attach", "rz"] ownCols ownRows
  IO.sleep 1500
  let newCols : UInt32 := 90
  let newRows : UInt32 := 25
  let (frc, _, ferr) ← e.cli #["resize", "rz", toString newCols, toString newRows]
  f :=
    f +
      (←
        expect (frc == 1 && has ferr "owns the size")
            "resize is refused while a client is attached")
  f :=
    f +
      (←
        expect ((← e.info "rz" "cols") == some (toString ownCols)) "a refused resize moved nothing")
  owner.bye
  let (arc, _, _) ← e.cli #["resize", "rz", toString newCols, toString newRows]
  IO.sleep 800
  f :=
    f +
      (←
        expect (arc == 0 && (← e.info "rz" "cols") == some (toString newCols))
            "resize applies again once the client detached")
  -- client-side validation: 1..1000 (clampDim's range). Both probes are the
  -- boundary itself: 0 is the largest rejected value below the range, and
  -- `clampDim` saturating means `clampDim 5000 + 1` is the smallest rejected
  -- value above it. The Python's flat 5000 could not tell "the CLI rejects
  -- 1001" from "the CLI rejects some number far outside".
  let tooBig := Linger.Core.Vt.clampDim 5000 + 1
  let (zrc, _, _) ← e.cli #["resize", "rz", "0", "10"]
  let (brc, _, _) ← e.cli #["resize", "rz", toString tooBig, "10"]
  f := f + (← expect (zrc == 2 && brc == 2) "zero and oversize are rejected client-side")
  f :=
    f +
      (←
        expect ((← e.cli #["resize", "nosuch", "80", "24"]).1 == 1)
            "resize on a missing session exits 1")
  e.killAll #["rz"]
  verdict e f

end E2E.Agent
