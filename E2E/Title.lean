module

import E2E.Harness
import Linger.Core.Terminal
import Linger.Core.Title
import Linger.Runtime.Client
import Linger.Core.Remote

public section

/-! Attached titles observed through a real client pty. The child is this
executable in raw mode, so only explicit probe inputs produce application output.
The receiver uses the public VT parser and its title/boundary projections.

`e2e title <binary>` also drives a saved predecessor or an assembled CLI without
rebuilding it. The sampler cases instead exercise Client.attach linked into the
E2E driver with a gated fixture sampler; changing the CLI argument cannot change
that implementation. `e2e --title-probe` is the child dispatch, not a test suite. -/

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

/-- A quiet window over which an attached client samples its title about three times. -/
def idleWindowMs : Nat := 3000

/-- The client's own CPU over `idleWindowMs`, about five times the cost measured
when it was set. Sampling spawns no process, so the client reaps no children. -/
def idleBudgetMs : Nat := 100

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

/-- A fixture-owned counter file, zero until written. -/
private def counter (path : String) : IO Nat := do
  if ← System.FilePath.pathExists path then
    return (← IO.FS.readFile path).toNat?.getD 0
  return 0

/-- The title sampler the probe attaches with. Samples run one at a time: the first
waits for `release-failure` and fails, later ones wait for `release-valid` and report
one unread session. File gates keep each state observable without racing the
one-second interval; every finished sample, failed or not, is counted. -/
def fixtureSample (dir : String) : IO String := do
  let serial := (← counter s!"{dir}/sample-count") + 1
  IO.FS.writeFile s!"{dir}/sample-count" (toString serial)
  try
    let gate := if serial == 1 then "release-failure" else "release-valid"
    unless ← waitFor 8000 (System.FilePath.pathExists s!"{dir}/{gate}") do
      throw (IO.userError "the fixture never released this title sample")
    if serial == 1 then
      throw (IO.userError "fixture title sample failure")
    return Linger.Core.Status.summary [.wantsYou]
  finally
    IO.FS.writeFile s!"{dir}/sample-finished" (toString serial)

/-- Exercise the public attach implementation linked into this executable, with
`fixtureSample` as its title sampler. Preserve the real attach outcome, and report
a sample still running once attach has returned. -/
def attachProbe (name : String) : IO UInt32 := do
  let some dir ← IO.getEnv "LINGER_DIR" | return 2
  let some fd ← Linger.Runtime.Client.connect name | return 2
  let outcome ← Linger.Runtime.Client.attach name fd (fixtureSample dir)
  if (← counter s!"{dir}/sample-count") != (← counter s!"{dir}/sample-finished") then
    return 5
  match outcome with
  | .detached =>
    return 0
  | _ =>
    return 4

private structure Receiver where
  vt : Vt := Vt.init 80 24
  bytes : ByteArray := ByteArray.empty

private def receive (c : Client) (seen : IO.Ref Receiver) (ms : Nat := 100) : IO Unit := do
  let bytes ← drain c.fd ms
  seen.modify fun s => { vt := s.vt.feed bytes.toList, bytes := s.bytes ++ bytes }

private def awaitOutput (c : Client) (seen : IO.Ref Receiver) (p : Receiver → Bool)
    (ms : Nat := patienceMs) :
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
    waitFor patienceMs do
        return (← e.status "title-other") == (if unread then Status.wantsYou else Status.idle)
  return code == 0 && settled

/-- This fixture has exactly one possible unread session; its glyph is shared
with the listing. Summary classification itself is covered by E2E.Status. -/
private def expectedTitle (unread : Bool) : String :=
  let summary := Linger.Core.Status.summary (if unread then [.wantsYou] else [])
  Linger.Core.Title.compose "title-main" "editor" summary maxChars

private def splitCase (e : Env) (c : Client) (seen : IO.Ref Receiver)
    (label startKey endKey : String) (opening closing : ByteArray) (unread : Bool) : IO Unit := do
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
  expect
      (openCode == 0 && opened && !incomplete.vt.atBoundary && changed &&
        held.bytes.size == incomplete.bytes.size &&
        !held.vt.atBoundary &&
        held.vt.windowTitle == before.vt.windowTitle)
      s!"{label}: attention refresh waits for the application boundary"
  let (closeCode, _, _) ← e.cli #["send", "title-main", endKey]
  let completed ← awaitOutput c seen (titleIs (expectedTitle unread))
  let after ← seen.get
  expect (closeCode == 0 && completed && hasBytes (since after start) (opening ++ closing).toList)
      s!"{label}: completion preserves bytes and emits the pending title"

/-- Ask the probe program for a pong and wait for it in the output that follows. -/
private def ping (c : Client) (seen : IO.Ref Receiver) : IO Bool := do
  let start := (← seen.get).bytes.size
  c.type "p"
  awaitOutput c seen fun s => hasText (since s start) "TITLE-PONG"

/-- A title sample is optional work on its own task, not part of the attachment.
The actual session CLI stays fixed; this executable supplies the linked Client
under test and the gated `fixtureSample`. -/
private def sampleCase (base : Env) : IO Unit := do
  let e := { base with dir := s!"{base.dir}/sampler" }
  IO.FS.createDirAll e.dir
  let name := "title-sampler"
  let self ← IO.appPath
  let attaching := { e with bin := self.toString }
  let titled (summary : String) :=
    titleIs (Linger.Core.Title.compose name "editor" summary maxChars)
  let count (file : String) := counter s!"{e.dir}/{file}"
  try
    let ready ← startProbe e name
    let c ← attaching.spawn #["--title-attach-probe", name]
    let seen ← IO.mkRef ({} : Receiver)
    try
      let initial ← awaitOutput c seen (titled "")
      let blocked ← waitFor 4000 (return (← count "sample-count") == 1)
      let responsive ← ping c seen
      expect
          (ready && initial && blocked && responsive && (← count "sample-finished") == 0 &&
            (← e.info name "clients") == some "1")
          "a blocked title sample leaves the attachment responsive"
      IO.FS.writeFile s!"{e.dir}/release-failure" ""
      let unknown ← awaitOutput c seen (titled (String.singleton (icon .unknown)))
      let responsive ← ping c seen
      expect (unknown && responsive && (← e.info name "clients") == some "1")
          "a failed title sample shows unknown attention and the attachment stays responsive"
      IO.FS.writeFile s!"{e.dir}/release-valid" ""
      let recovered ← awaitOutput c seen (titled (Linger.Core.Status.summary [.wantsYou]))
      let answered ← ping c seen
      expect (recovered && answered && (← e.info name "clients") == some "1")
          "a later title sample recovers the attention summary"
      -- Hold the next sample, then detach while it is outstanding.
      IO.FS.removeFile s!"{e.dir}/release-valid"
      let outstanding ←
        waitFor 4000 do
            return (← count "sample-count") > (← count "sample-finished")
      let held ← count "sample-count"
      let detachStart := (← seen.get).bytes.size
      c.detach
      let cleared ← awaitOutput c seen (titleIs "")
      let released ← waitFor 2000 (return (← e.info name "clients") == some "0")
      let joining := (← c.reap 300) == -1
      IO.FS.writeFile s!"{e.dir}/release-valid" ""
      let code ← c.reap 2000
      let handedBack := hasBytes (since (← seen.get) detachStart) Linger.Core.Render.leaveAnsi
      let before := (← e.info name "outseq").bind (·.toNat?)
      let (sendCode, _, _) ← e.cli #["send", name, "p"]
      let survived ←
        waitFor 4000 do
            let after := (← e.info name "outseq").bind (·.toNat?)
            return before.isSome && after.getD 0 > before.getD 0 &&
                has (← e.out #["capture", name]) "TITLE-PONG"
      expect
          (outstanding && cleared && released && joining && code == 0 && handedBack &&
            (← count "sample-finished") == held &&
            sendCode == 0 &&
            survived)
          "detach releases the session at once and joins the outstanding title sample"
      IO.FS.writeBinFile s!"{e.dir}/attach.pty" (← seen.get).bytes
    finally
      c.bye (sendDetach := false)
  finally
    e.killAll #[name]

def run (binary : Option String := none) : IO UInt32 :=
  Env.suite "title" fun initial => do
    let e := { initial with bin := binary.getD initial.bin }
    try
      let ready ← startProbe e "title-main"
      let c ← e.spawn #["attach", "title-main"] 80 24
      let seen ← IO.mkRef ({} : Receiver)
      try
        let composed ← awaitOutput c seen (titleIs (expectedTitle false))
        expect (ready && composed && hasText (← seen.get).bytes "TITLE-READY")
            "attach composes the session name and the application's editor title"
        let start ← processCpuMs c.pid
        receive c seen idleWindowMs
        let cost :=
          match start, ← processCpuMs c.pid with
          | some (before, _), some (after, children) => some (after - before, children)
          | _, _ => none
        expect (cost.all fun (own, children) => children == 0 && own ≤ idleBudgetMs)
            s!"an idle attached client samples its title in its own process within {idleBudgetMs} ms of CPU per {idleWindowMs} ms where /proc reports it (own, children: {cost})"
        let otherReady ← startProbe e "title-other"
        let changed ← attention e true
        let before := ((← e.info "title-other" "behind").getD "").toNat?
        let refreshed ← awaitOutput c seen (titleIs (expectedTitle true))
        expect (otherReady && changed && refreshed)
            "unread output elsewhere refreshes the title while the application is silent"
        let (infoCode, _, _) ← e.cli #["info", "title-other"]
        let after := ((← e.info "title-other" "behind").getD "").toNat?
        expect
            (infoCode == 0 && before.isSome && before.getD 0 > 0 && after == before &&
              (← e.status "title-other") == Status.wantsYou)
            "info and asynchronous title sampling leave the unread count intact"
        splitCase e c seen "OSC" "o" "O" openOsc (ByteArray.mk #[0x07]) false
        splitCase e c seen "DCS" "d" "D" "\x1bPtitle-probe".toUTF8 "\x1b\\".toUTF8 true
        splitCase e c seen "UTF-8" "u" "U" (ByteArray.mk #[0xE2]) (ByteArray.mk #[0x82, 0xAC]) false
        let unread ← attention e true
        let prefixed ← awaitOutput c seen (titleIs (expectedTitle true))
        let repeatStart := (← seen.get).bytes.size
        let (repeatCode, _, _) ← e.cli #["send", "title-main", "r"]
        let repeated ←
          awaitOutput c seen fun s =>
              titleIs (expectedTitle true) s && hasBytes (since s repeatStart) editor.toList &&
                hasBytes (since s repeatStart)
                  (Linger.Core.Terminal.Title.ansi (expectedTitle true))
        expect (unread && prefixed && repeatCode == 0 && repeated)
            "an identical application OSC title reasserts the shared context and attention suffix"
        let summary := Linger.Core.Status.summary [.wantsYou]
        let (longCode, _, _) ← e.cli #["send", "title-main", "l"]
        let clipped ←
          awaitOutput c seen
              (titleIs (Linger.Core.Title.compose "title-main" longEditor summary maxChars))
        let displayed := (← seen.get).vt.windowTitle
        expect
            (longCode == 0 && clipped && displayed.length == maxChars &&
              displayed.endsWith (" · " ++ summary))
            "a long Unicode application title preserves attention within the shared title budget"
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
        expect (openCode == 0 && incomplete && cleared && exited == 0)
            "detach clears the title at a complete boundary and exits promptly"
        let (finishCode, _, _) ← e.cli #["send", "title-main", "D"]
        let (pingCode, _, _) ← e.cli #["send", "title-main", "p"]
        let answered ←
          waitFor 4000 do
              return has (← e.out #["capture", "title-main"]) "TITLE-PONG"
        expect
            (finishCode == 0 && pingCode == 0 && answered &&
              (← e.info "title-main" "clients") == some "0")
            "the raw foreground program remains alive and answers after detach"
      finally
        c.bye (sendDetach := false)
    finally
      e.killAll #["title-main", "title-other"]
    sampleCase e

end E2E.Title
