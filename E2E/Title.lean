module

public import E2E.Harness
public import Linger.Core.Terminal
public import Linger.Core.Title
public import Linger.Runtime.Client
import Linger.Core.Remote

public section

/-! Attached titles observed through a real client pty. The child is this
executable in raw mode, so only explicit probe inputs produce application output.
The receiver uses the public VT parser and its title/boundary projections.

`e2e title <binary>` also drives a saved predecessor or an assembled CLI without
rebuilding it. The pipe-error cases instead exercise Client.attach linked into
the E2E driver; changing the CLI argument cannot change that implementation.
`e2e --title-probe` is the child dispatch, not a test suite. -/

namespace E2E.Title

open E2E.Harness
open Linger.Posix
open Linger.Core.Status (Status icon)
open Linger.Core.Terminal.Title (maxChars)
open Linger.Core.Vt (Vt)

/-- Application bytes, deliberately independent of the title emitter under test. -/
private def editor : ByteArray := "\x1b]2;editor\x07".toUTF8

/-- At the full title budget, Unicode makes byte-based clipping observable too. -/
private def longEditor : String := String.ofList (List.replicate maxChars '😀')

/-- A short OSC stays in the daemon's query buffer until completion. Exceed
that public cap so the client actually receives an unfinished, ignored OSC. -/
private def openOsc : ByteArray :=
  ("\x1b]999;" ++ String.ofList (List.replicate (Linger.Core.Terminal.oscCap + 1) 'x')).toUTF8

/-- Raw foreground program: lower-case keys open a partial sequence, their
upper-case partners finish it; `r` repeats an identical title, `p` answers a
liveness probe, and `q` exits. No shell prompt or startup file supplies output. -/
def probe : IO UInt32 := do
  let saved ← termRaw stdinFd
  try
    writeAll stdoutFd (editor ++ "\r\nTITLE-READY\r\n".toUTF8)
    let mut running := true
    while running do
      match ← read stdinFd 1 with
      | none =>
        running := false
      | some bytes =>
        for b in bytes.toList do
          match b.toNat with
          | 111 =>
            writeAll stdoutFd openOsc
          | 79 =>
            writeAll stdoutFd (ByteArray.mk #[0x07])
          | 100 =>
            writeAll stdoutFd "\x1bPtitle-probe".toUTF8
          | 68 =>
            writeAll stdoutFd "\x1b\\".toUTF8
          | 117 =>
            writeAll stdoutFd (ByteArray.mk #[0xE2])
          | 85 =>
            writeAll stdoutFd (ByteArray.mk #[0x82, 0xAC])
          | 114 =>
            writeAll stdoutFd editor
          | 108 =>
            writeAll stdoutFd ("\x1b]2;" ++ longEditor ++ "\x07").toUTF8
          | 112 =>
            writeAll stdoutFd "\r\nTITLE-PONG\r\n".toUTF8
          | 113 =>
            running := false
          | _ =>
            pure ()
    return 0
  finally
    termRestore stdinFd saved

/-- Exercise the public attach implementation linked into this executable.
Its status helpers re-enter E2ETest, where only the fixture environment enables
the invalid-byte sample. Preserve the real attach outcome. -/
def attachProbe (name : String) : IO UInt32 := do
  let some fd ← Linger.Runtime.Client.connect name | return 2
  let outcome ← Linger.Runtime.Client.attach name fd
  match outcome with
  | .detached =>
    return 0
  | _ =>
    return 4

/-- The first sample writes invalid UTF-8 to the selected pipe; subsequent
samples return a valid summary. File gates keep the unknown title observable
without racing the one-second sampling interval. All state is fixture-owned. -/
def sampleProbe (pipe : String) : IO UInt32 := do
  unless pipe == "stdout" || pipe == "stderr" do
    return 2
  let some dir ← IO.getEnv "LINGER_DIR" | return 2
  let countPath := s!"{dir}/sample-count"
  let previous ←
    if ← System.FilePath.pathExists countPath then
      IO.FS.readFile countPath
    else
      pure "0"
  let serial := previous.toNat?.getD 0 + 1
  IO.FS.writeFile countPath (toString serial)
  IO.FS.writeFile s!"{dir}/sample-{serial}.pid" (toString (← getpid))
  let gate := if serial == 1 then "release-invalid" else "release-valid"
  unless ← waitFor 8000 (System.FilePath.pathExists s!"{dir}/{gate}") do
    return 5
  if serial == 1 then
    let destination ←
      if pipe == "stdout" then
        IO.getStdout
      else
        IO.getStderr
    destination.write (ByteArray.mk #[0xFF])
    destination.flush
    IO.FS.writeFile s!"{dir}/invalid-emitted" pipe
  else
    writeAll stdoutFd ((Linger.Core.Status.summary [.wantsYou]) ++ "\n").toUTF8
    IO.FS.writeFile s!"{dir}/valid-emitted" (toString serial)
  return 0

private structure Receiver where
  vt : Vt := Vt.init 80 24
  bytes : ByteArray := ByteArray.empty

private def receive (c : Client) (seen : IO.Ref Receiver) (ms : Nat := 100) : IO Unit := do
  let bytes ← drain c.fd ms
  seen.modify fun s => { vt := s.vt.feed bytes.toList, bytes := s.bytes ++ bytes }

private def awaitOutput (c : Client) (seen : IO.Ref Receiver) (p : Receiver → Bool)
    (ms : Nat := 4000) :
    IO Bool := waitFor ms do
    receive c seen
    return p (← seen.get)

private def titleIs (title : String) (s : Receiver) : Bool :=
  s.vt.atBoundary && s.vt.windowTitle == title

private def since (s : Receiver) (start : Nat) : ByteArray := s.bytes.extract start s.bytes.size

private def startProbe (e : Env) (name : String) : IO Bool := do
  let self ← IO.appPath
  let (code, _, _) ←
    e.cliEnv #[("ENV", none), ("BASH_ENV", none)]
        #["run", name, s!"exec {Linger.Core.Remote.shellQuote self.toString} --title-probe"]
  let ready ←
    waitFor 4000 do
        return has (← e.out #["capture", name]) "TITLE-READY"
  return code == 0 && ready

/-- One other session, either read or carrying unread output. Capture is used
only for an intentional acknowledgment; status and info must leave it unread. -/
private def attention (e : Env) (unread : Bool) : IO Bool := do
  let args := if unread then #["send", "title-other", "p"] else #["capture", "title-other"]
  let (code, _, _) ← e.cli args
  let settled ←
    waitFor 4000 do
        return (← e.status "title-other") == (if unread then Status.wantsYou else Status.idle)
  return code == 0 && settled

/-- This fixture has exactly one possible unread session; its glyph is shared
with the listing. Summary classification itself is covered by E2E.Status. -/
private def expectedTitle (unread : Bool) : String :=
  let summary := Linger.Core.Status.summary (if unread then [.wantsYou] else [])
  Linger.Core.Title.compose "title-main" "editor" summary maxChars

private def splitCase (e : Env) (c : Client) (seen : IO.Ref Receiver)
    (label startKey endKey : String) (opening closing : ByteArray) (unread : Bool) : IO Nat := do
  let before ← seen.get
  let start := before.bytes.size
  let (openCode, _, _) ← e.cli #["send", "title-main", startKey]
  let opened ← awaitOutput c seen fun s => hasBytes (since s start) opening.toList
  let incomplete ← seen.get
  let changed ← attention e unread
  -- Allow a stale in-flight sample to complete, then a fresh sample after the
  -- one-second interval, including the response budget and client polling.
  receive c seen 2500
  let held ← seen.get
  let mut failures ←
    expect
        (openCode == 0 && opened && !incomplete.vt.atBoundary && changed &&
          held.bytes.size == incomplete.bytes.size &&
          !held.vt.atBoundary &&
          held.vt.windowTitle == before.vt.windowTitle)
        s!"{label}: attention refresh waits for the application boundary"
  let (closeCode, _, _) ← e.cli #["send", "title-main", endKey]
  let completed ← awaitOutput c seen (titleIs (expectedTitle unread))
  let after ← seen.get
  failures :=
    failures +
      (←
        expect
            (closeCode == 0 && completed &&
              hasBytes (since after start) (opening ++ closing).toList)
            s!"{label}: completion preserves bytes and emits the pending title")
  return failures

/-- Pipe-reader errors are optional sampling failures, not attach failures.
The actual session CLI stays fixed; this executable supplies the linked Client
under test and its controlled status subprocesses. -/
private def pipeCase (base : Env) (pipe : String) : IO Nat := do
  let e := { base with dir := s!"{base.dir}/pipe-{pipe}" }
  IO.FS.createDirAll e.dir
  let name := s!"title-{pipe}"
  let self ← IO.appPath
  let attaching := { e with bin := self.toString }
  let mut failures := 0
  try
    let ready ← startProbe e name
    let c ← attaching.spawnEnv #[s!"LINGER_E2E_TITLE_PIPE={pipe}"] #["--title-attach-probe", name]
    let seen ← IO.mkRef ({} : Receiver)
    try
      let initial ←
        awaitOutput c seen (titleIs (Linger.Core.Title.compose name "editor" "" maxChars))
      IO.FS.writeFile s!"{e.dir}/release-invalid" ""
      let unknown ←
        awaitOutput c seen
            (titleIs
              (Linger.Core.Title.compose name "editor" (String.singleton (icon .unknown)) maxChars))
      let pingStart := (← seen.get).bytes.size
      c.type "p"
      let responsive ← awaitOutput c seen fun s => hasText (since s pingStart) "TITLE-PONG"
      failures :=
        failures +
          (←
            expect
                (ready && initial && unknown && responsive &&
                  (← System.FilePath.pathExists s!"{e.dir}/invalid-emitted") &&
                  (← e.info name "clients") == some "1")
                s!"invalid helper {pipe}: unknown title leaves the attachment responsive")
      IO.FS.writeFile s!"{e.dir}/release-valid" ""
      let recovered ←
        awaitOutput c seen
            (titleIs
              (Linger.Core.Title.compose name "editor" (Linger.Core.Status.summary [.wantsYou])
                maxChars))
      let recoveryStart := (← seen.get).bytes.size
      c.type "p"
      let answered ← awaitOutput c seen fun s => hasText (since s recoveryStart) "TITLE-PONG"
      failures :=
        failures +
          (←
            expect
                (recovered && answered &&
                  (← System.FilePath.pathExists s!"{e.dir}/valid-emitted") &&
                  (← e.info name "clients") == some "1")
                s!"invalid helper {pipe}: a subsequent valid sample recovers the title")
      let detachStart := (← seen.get).bytes.size
      c.detach
      let cleared ← awaitOutput c seen (titleIs "")
      let code ← c.reap 2000
      let handedBack := hasBytes (since (← seen.get) detachStart) Linger.Core.Render.leaveAnsi
      let samplePids ← e.dirNames ".pid"
      let helpersGone ←
        waitFor 2000 do
            samplePids.allM fun file => do
                let pid := (← IO.FS.readFile s!"{e.dir}/{file}").toNat?.getD 0
                return pid > 0 && !(← alive (UInt32.ofNat pid))
      let before := (← e.info name "outseq").bind (·.toNat?)
      let (sendCode, _, _) ← e.cli #["send", name, "p"]
      let survived ←
        waitFor 4000 do
            let after := (← e.info name "outseq").bind (·.toNat?)
            return before.isSome && after.getD 0 > before.getD 0 &&
                has (← e.out #["capture", name]) "TITLE-PONG"
      failures :=
        failures +
          (←
            expect
                (cleared && code == 0 && handedBack && helpersGone && sendCode == 0 && survived &&
                  (← e.info name "clients") == some "0")
                s!"invalid helper {pipe}: detach clears the title and retires its helpers")
      IO.FS.writeBinFile s!"{e.dir}/attach.pty" (← seen.get).bytes
    finally
      c.bye (sendDetach := false)
  finally
    e.killAll #[name]
  return failures

def run (binary : Option String := none) : IO UInt32 := do
  let initial ← Env.make "title"
  let e := { initial with bin := binary.getD initial.bin }
  let mut failures := 0
  try
    let ready ← startProbe e "title-main"
    let c ← e.spawn #["attach", "title-main"] 80 24
    let seen ← IO.mkRef ({} : Receiver)
    try
      let composed ← awaitOutput c seen (titleIs (expectedTitle false))
      failures :=
        failures +
          (←
            expect (ready && composed && hasText (← seen.get).bytes "TITLE-READY")
                "attach composes the session name and the application's editor title")
      let otherReady ← startProbe e "title-other"
      let changed ← attention e true
      let before := ((← e.info "title-other" "behind").getD "").toNat?
      let refreshed ← awaitOutput c seen (titleIs (expectedTitle true))
      failures :=
        failures +
          (←
            expect (otherReady && changed && refreshed)
                "unread output elsewhere refreshes the title while the application is silent")
      let (infoCode, _, _) ← e.cli #["info", "title-other"]
      let after := ((← e.info "title-other" "behind").getD "").toNat?
      failures :=
        failures +
          (←
            expect
                (infoCode == 0 && before.isSome && before.getD 0 > 0 && after == before &&
                  (← e.status "title-other") == Status.wantsYou)
                "info and asynchronous title sampling leave the unread count intact")
      failures :=
        failures + (← splitCase e c seen "OSC" "o" "O" openOsc (ByteArray.mk #[0x07]) false)
      failures :=
        failures +
          (← splitCase e c seen "DCS" "d" "D" "\x1bPtitle-probe".toUTF8 "\x1b\\".toUTF8 true)
      failures :=
        failures +
          (←
            splitCase e c seen "UTF-8" "u" "U" (ByteArray.mk #[0xE2]) (ByteArray.mk #[0x82, 0xAC])
                false)
      let unread ← attention e true
      let prefixed ← awaitOutput c seen (titleIs (expectedTitle true))
      let repeatStart := (← seen.get).bytes.size
      let (repeatCode, _, _) ← e.cli #["send", "title-main", "r"]
      let repeated ←
        awaitOutput c seen fun s =>
            titleIs (expectedTitle true) s && hasBytes (since s repeatStart) editor.toList &&
              hasBytes (since s repeatStart) (Linger.Core.Terminal.Title.ansi (expectedTitle true))
      failures :=
        failures +
          (←
            expect (unread && prefixed && repeatCode == 0 && repeated)
                "an identical application OSC title reasserts the shared context and attention suffix")
      let summary := Linger.Core.Status.summary [.wantsYou]
      let (longCode, _, _) ← e.cli #["send", "title-main", "l"]
      let clipped ←
        awaitOutput c seen
            (titleIs (Linger.Core.Title.compose "title-main" longEditor summary maxChars))
      let displayed := (← seen.get).vt.windowTitle
      failures :=
        failures +
          (←
            expect
                (longCode == 0 && clipped && displayed.length == maxChars &&
                  displayed.endsWith (" · " ++ summary))
                "a long Unicode application title preserves attention within the shared title budget")
      -- Detach with an unfinished DCS as well: handback must neutralize the
      -- receiver before clearing its title, without terminating the program.
      let detachStart := (← seen.get).bytes.size
      let (openCode, _, _) ← e.cli #["send", "title-main", "d"]
      let incomplete ←
        awaitOutput c seen fun s =>
            !s.vt.atBoundary && hasText (since s detachStart) "\x1bPtitle-probe"
      c.detach
      let cleared ← awaitOutput c seen (titleIs "")
      let exited ← c.reap 2000
      failures :=
        failures +
          (←
            expect (openCode == 0 && incomplete && cleared && exited == 0)
                "detach clears the title at a complete boundary and exits promptly")
      let (finishCode, _, _) ← e.cli #["send", "title-main", "D"]
      let (pingCode, _, _) ← e.cli #["send", "title-main", "p"]
      let answered ←
        waitFor 4000 do
            return has (← e.out #["capture", "title-main"]) "TITLE-PONG"
      failures :=
        failures +
          (←
            expect
                (finishCode == 0 && pingCode == 0 && answered &&
                  (← e.info "title-main" "clients") == some "0")
                "the raw foreground program remains alive and answers after detach")
    finally
      c.bye (sendDetach := false)
  finally
    e.killAll #["title-main", "title-other"]
  for pipe in ["stdout", "stderr"] do
    failures := failures + (← pipeCase e pipe)
  verdict e failures

end E2E.Title
