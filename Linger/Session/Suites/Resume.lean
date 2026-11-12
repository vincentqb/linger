module

public import Verify.Harness
import Linger.Session.Checkpoint
import Linger.Session.Shell.Daemon
public import Linger.Session.Spec
import SoftwareChallenge.Commands

public section

/-! # Linger.Session.Suites.Resume — reboot-resume: checkpoint, crash, restore

Ported from `tests/resume_test.py`.

Checkpoint on last detach, daemon SIGKILLed (simulated crash/reboot), session
listed as resumable, attach restores the old screen and labels and starts a fresh
shell in the saved cwd. The resumable row is compared as a `Status`, not as a
substring of the listing, which some *other* row's `(resumable)` could also match. -/

namespace Linger.Session.Suites.Resume

open Verify.Harness
open Linger.Display.Status (Status)

/-- Child-side winsize probe. It must execute inside the resumed session's pty;
reading the parent process's tty would test the harness instead. -/
def winsizeProbe (resultPath : String) : IO UInt32 := do
  let (cols, rows) ← Os.Shell.winsizeGet Os.Shell.stdinFd
  IO.FS.writeFile resultPath s!"{cols} {rows}"
  return 0

/-- Exercise the real effect interpreter with one failed save and no further
output. The injected clock checks retry cadence without waiting a minute. -/
def checkpointRetry : IO Unit := do
  let attempts ← IO.mkRef (0 : Nat)
  let saved ← IO.mkRef ([] : List (String × String))
  let labels := [("quiet", "kept")]
  let rt : Linger.Session.Shell.Daemon.Rt :=
    { st := Linger.Session.State.boot (Terminal.Vt.Vt.init 20 5) labels [], listenFd := 0,
      ptyFd := 0, childPid := 0,
      saveCkpt := fun st => do
        attempts.modify (· + 1)
        if (← attempts.get) == 1 then
          throw (IO.userError "injected save failure")
        saved.set st.labels,
      dropCkpt := pure () }
  let interval := Linger.Session.ckptIntervalMs
  let rt ← Linger.Session.Shell.Daemon.pump rt [.ptyOut [65], .tick interval]
  -- the save runs on its own thread; its failure comes back as the next round's event
  let (rt, failed) ← Linger.Session.Shell.Daemon.collectSave rt true
  let rt ← Linger.Session.Shell.Daemon.pump rt (failed ++ [.tick (interval + 1)])
  let before ← attempts.get
  let rt ← Linger.Session.Shell.Daemon.pump rt [.tick (interval + interval)]
  let _ ← Linger.Session.Shell.Daemon.finishSaves rt
  expect (before == 1 && (← attempts.get) == 2 && (← saved.get) == labels)
      "a failed quiet checkpoint retries at the next cadence with its state intact"

/-- The daemon's peak resident set after `scaleRun`, in KiB: about five times the 319 MB measured
when it was set, so only a pathological regression exceeds it. Memory does not grow with the
host's load. -/
def scaleBudgetKb : Nat := 1600000

/-- What `scaleRun` saw: whether each step completed, what it produced and how long it took. -/
structure Scale where
  /-- Whether the screen showed the marker printed after the 10,050 lines. -/
  filled : Bool
  /-- The exit status of `capture --history`; `none` when it was still running at `hangMs`. -/
  historyRc : Option UInt32
  /-- How many lines `capture --history` printed. -/
  historyLines : Nat
  /-- Whether a reattach at 200x50 replayed the marker. -/
  replayed : Bool
  /-- Whether the detach checkpoint on disk came to hold the full ring. -/
  saved : Bool
  /-- That checkpoint's size in bytes. -/
  size : UInt64
  /-- The daemon's peak resident set in KiB, where `/proc` reports it. -/
  peak : Option Nat
  /-- Milliseconds from typing the fill to the marker on the screen. -/
  fillMs : Nat
  /-- Milliseconds `capture --history` took. -/
  captureMs : Nat
  /-- Milliseconds from the reattach to the replayed marker. -/
  replayMs : Nat
  /-- Milliseconds from the detach to the full checkpoint on disk. -/
  saveMs : Nat

/-- A 200-column session with its 10,000-row history ring full of varied text, which neither
run-length coding nor trailing blanks shorten: fill it, export it with `capture --history`,
replay it to a reattach and checkpoint it on the detach. Every wait is `hangMs`, which only a
hang outlasts. Theorems bound what the model computes; the resume suite checks what this
produced and `Linger.Session.Suites.Perf` reports what it cost. -/
def scaleRun (e : Env) : IO Scale := do
  let name := "scale"
  try
    let _ ← e.typeIn name #["true"]
    let _ ← e.cli #["resize", name, "200", "50"]
    let start ← Os.Shell.monotonicMs
    let _ ←
      e.typeIn name
          #["awk 'BEGIN { for (i = 0; i < 10050; i++) { s = \"\"; for (j = 0; j < 20; j++) s = s sprintf(\"%09d \", 20 * i + j); print s } }'; echo SCALE-$((40+2))"]
    let filled ← waitFor hangMs (return has (← e.out #["capture", name]) "SCALE-42")
    let fillMs := (← Os.Shell.monotonicMs) - start
    let start ← Os.Shell.monotonicMs
    let history ← e.cliTimeout #["capture", "--history", name] hangMs
    let captureMs := (← Os.Shell.monotonicMs) - start
    let client ← e.spawn #["attach", name] 200 50
    let (replayed, replayMs, saved, saveMs, size) ←
      try
        let start ← Os.Shell.monotonicMs
        let replayed ← client.awaitNeedle "SCALE-42" hangMs
        let replayMs := (← Os.Shell.monotonicMs) - start
        let start ← Os.Shell.monotonicMs
        client.detach
        -- The detach save runs on its own thread, so the daemon answers at once: the save is
        -- done when the checkpoint on disk holds the full ring, which the rename makes whole.
        let ckpt := System.FilePath.mk s!"{e.dir}/{name}.ckpt"
        let full := (Terminal.Vt.sbCap * 200).toUInt64
        let sizeOf : IO UInt64 := do
          return ((← ckpt.metadata.toBaseIO).toOption.map (·.byteSize)).getD 0
        let saved ← waitFor hangMs (return (← sizeOf) ≥ full)
        let saveMs := (← Os.Shell.monotonicMs) - start
        pure (replayed, replayMs, saved, saveMs, ← sizeOf)
      finally
        client.bye (sendDetach := false)
    -- A daemon that did not answer cannot be measured, so its check fails.
    let peak ←
      if saved then
        e.daemonPeakKb name
      else
        pure none
    let scale : Scale :=
      { filled, historyRc := history.map (·.1),
        historyLines := (history.map fun (_, text, _) => (lines text).length).getD 0, replayed,
        saved, size, peak, fillMs, captureMs, replayMs, saveMs }
    return scale
  finally
    e.killAll #[name]

/-- What `scaleRun` produced, whatever it cost: the full ring exported, replayed and saved, and
the daemon's peak resident set where `/proc` reports it. -/
private def scaleChecks (e : Env) : IO Unit := do
  let s ← scaleRun e
  expect (s.filled && s.historyRc == some 0 && s.historyLines ≥ Terminal.Vt.sbCap + 50)
      s!"a full ring at 200 columns fills and exports with capture --history ({s.historyLines} lines)"
  expect (s.replayed && s.saved)
      s!"reattach replays a full ring and detach checkpoints it ({s.size} bytes)"
  expectMeasured s.peak.isSome (s.saved && s.peak.all (· ≤ scaleBudgetKb))
      s!"the daemon's peak resident set stays within {scaleBudgetKb} KiB ({s.peak} KiB)"

/-- A resume runs in its saved directory, or in `$HOME` when that is gone, and says so; with
HOME unset or empty it refuses and leaves the saved session as it was (`Env.resumeDir`). -/
private def directoryChecks (e : Env) : IO Unit := do
  let home := s!"{e.dir}/home"
  let kept := s!"{e.dir}/kept"
  IO.FS.createDirAll home
  IO.FS.createDirAll kept
  let gone := s!"{e.dir}/gone"
  let save (name dir : String) : IO Unit :=
    IO.FS.writeBinFile s!"{e.dir}/{name}.ckpt"
      (Linger.Session.Checkpoint.saveBytes ⟨Terminal.Vt.Vt.init 40 5, dir, []⟩)
  save "rk" kept
  let (keptRc, _, _) ← e.cliEnv #[("HOME", some home)] #["resume", "rk"]
  expect
      (keptRc == 0 && (← e.info "rk" "start_dir") == some kept &&
        (← e.info "rk" "saved_dir").isNone)
      "a resume runs in its saved directory"
  save "rm" gone
  let (movedRc, _, movedErr) ← e.cliEnv #[("HOME", some home)] #["resume", "rm"]
  expect
      (movedRc == 0 && has movedErr s!"resumed in {home}" &&
        (← e.info "rm" "start_dir") == some home &&
        (← e.info "rm" "saved_dir") == some gone)
      s!"a resume whose directory is gone runs in HOME, and says so (rc={movedRc})"
  let mut refused := true
  for (name, value) in [("ru", none), ("re", some "")] do
    save name gone
    let (rc, _, _) ← e.cliEnv #[("HOME", value)] #["resume", name]
    refused :=
      refused && rc != 0 && (← e.info name "pid").isNone &&
        (← System.FilePath.pathExists s!"{e.dir}/{name}.ckpt")
    IO.FS.removeFile s!"{e.dir}/{name}.ckpt"
  expect refused "a resume whose directory is gone refuses when HOME is unset or empty"
  e.killAll #["rk", "rm"]

/-- Whether no process holds the lock at `path`: `flock` takes it, and lets it go at once. -/
private def lockFree (path : String) : IO Bool := do
  let fd ← Os.Shell.flock path
  if fd < 0 then
    return false
  Os.Shell.close fd.toUInt64.toUInt32
  return true

/-- A request's answer is true (`start_answer_true`). A daemon whose request's ticket is gone, as
when the command that asked took it, starts nothing and reports nothing. A resume whose daemon
cannot load its checkpoint within the command's 30 s wait answers 124, that nothing starts, and
the daemon starts nothing once it has loaded it: a FIFO holds the load until the command has
answered. -/
private def answerChecks (e : Env) : IO Unit := do
  let report := s!"{e.dir}/logs/taken.start-check"
  IO.FS.createDirAll s!"{e.dir}/logs"
  let ran ← e.cliTimeout #["__start", report, "taken", e.dir, "/bin/sh", "-c", "exit 0"] hangMs
  expect
      (ran.any (·.1 == 0) && !(← System.FilePath.pathExists report) &&
        !(← e.dirNames ".sock").contains "taken.sock" &&
        !(← e.dirNames ".end").contains "taken.end" &&
        !(← e.dirNames ".ckpt").contains "taken.ckpt")
      s!"a daemon whose request's ticket is gone starts nothing and reports nothing \
        ({ran.map (·.1)})"
  e.killAll #["taken"]
  let a : Env := { e with dir := s!"{e.dir}/answer" }
  IO.FS.createDirAll a.dir
  let fifo := s!"{a.dir}/late.ckpt"
  let source := s!"{a.dir}/late.src"
  IO.FS.writeBinFile source
      (Linger.Session.Checkpoint.saveBytes ⟨Terminal.Vt.Vt.init 40 5, a.dir, []⟩)
  let made ← IO.Process.output { cmd := "mkfifo", args := #[fifo] }
  let begun ← Os.Shell.monotonicMs
  let fed ← IO.mkRef (none : Option UInt32)
  let resumed ←
    try
      -- the command's 30 s wait, then only a hang
      a.cliTimeout #["resume", "late"] (30000 + hangMs)
    finally
      let feed ←
        IO.Process.spawn
            { cmd := "sh", args := #["-c", s!"cat '{source}' > '{fifo}'"], stdin := .null,
              stdout := .null, stderr := .null }
      fed.set (← waitOrKill feed hangMs)
  let waitedMs := (← Os.Shell.monotonicMs) - begun
  let settled ← waitFor patienceMs (lockFree s!"{a.dir}/late.lock")
  IO.FS.removeFile fifo
  let sockets ← a.dirNames ".sock"
  let left :=
    (← System.FilePath.readDir s!"{a.dir}/logs").toList.filter (·.fileName.startsWith "late.start-")
  a.endSessions
  expect
      (made.exitCode == 0 &&
        resumed.any (fun (rc, _, err) => rc == 124 && has err "starts nothing") &&
        waitedMs ≥ 30000 &&
        (← fed.get) == some 0 &&
        settled &&
        !sockets.contains "late.sock" &&
        left.isEmpty)
      s!"a resume whose daemon does not answer within 30 s answers 124, that nothing starts, \
        and its daemon starts nothing once it could ({resumed.map (·.1)}, {waitedMs} ms, \
        settled={settled}, left {left.map (·.fileName)})"

/-- The resume suite: checkpoint, crash and restore, and where a resume runs. -/
@[exercises Linger.Session.Spawn.Runs]
def run : IO UInt32 :=
  Env.suite "resume" fun e => do
    directoryChecks e
    answerChecks e
    checkpointRetry
    scaleChecks e
    -- one source for the pty geometry and for the off-the-screen window below
    let cols : UInt32 := 80
    let rows : UInt32 := 24
    let marker := "survives-the-reboot-42"
    -- create a session working in this suite's directory, leave a marker on screen and
    -- a label
    let boot ← e.spawn #["attach", "boot"] cols rows
    let _ ← waitFor 4000 (return (← e.info "boot" "clients") == some "1")
    boot.type s!"cd '{e.dir}' && echo survives-the-reboot-$((40+2))\r"
    let _ ← drain boot.fd 1500
    -- …then push it off the screen. Before scrollback replay the marker below had
    -- to be on the visible grid for the reattach assertion to pass, so that
    -- assertion proved only that the *screen* survived the checkpoint. With 60
    -- lines after it on a 24-row terminal it is in the ring, and the same
    -- assertion now proves the ring survived the checkpoint AND reached the
    -- terminal. It fails against a restore that drops history.
    boot.type "i=1; while [ $i -le 60 ]; do echo filler-$i; i=$((i+1)); done\r"
    let _ ← drain boot.fd 2000
    -- exact-line membership, not substring: the typed line the tty echoed back
    -- says `echo survives-the-reboot-$((40+2))`, and only the shell's *output*
    -- line is the marker itself; `has` would weaken it.
    let hist0 := lines (← e.out #["capture", "--history", "boot"])
    expect (hist0.contains marker && !(hist0.drop (hist0.length - rows.toNat)).contains marker)
        "the pre-reboot marker is in the ring, off the 24-row screen"
    let _ ← e.cli #["set", "boot", "k=v"]
    -- detach (last attached client): the machine checkpoints here
    boot.detach
    -- the save runs on its own thread, so the daemon answers at once: it is on disk once the
    -- checkpoint holds the label set just before the detach
    let _ ← waitFor 4000 (return (← e.info "boot" "clients") == some "0")
    let _ ←
      waitFor 4000 do
          match ← (IO.FS.readBinFile s!"{e.dir}/boot.ckpt").toBaseIO with
          | .ok bytes =>
            return (Linger.Session.Checkpoint.loadBytes bytes).any (·.labels.contains ("k", "v"))
          | .error _ =>
            return false
    boot.bye (sendDetach := false) -- fd and zombie only; the client already left
    let ckpts ← e.dirNames ".ckpt"
    let ckptOk := ckpts == ["boot.ckpt"]
    -- …and it is a checkpoint in THIS format, compared against the writer's own
    -- tag. Read only when the name check passed, so a missing file is a FAIL line
    -- rather than an exception that costs the `FAILURES:` verdict entirely.
    let magicOk ←
      if ckptOk then
        do
          let bytes ← IO.FS.readBinFile s!"{e.dir}/boot.ckpt"
          pure (startsWithBytes bytes Linger.Session.Checkpoint.magic)
      else
        pure false
    expect (ckptOk && magicOk) s!"checkpoint written on last detach ({ckpts})"
    -- simulate reboot: SIGKILL the DAEMON (the pid in `list` is the shell —
    -- killing that ends the program, which leaves an ended session, not an
    -- interrupted one). Aborts the
    -- suite rather than printing a check: with no crash there is nothing below
    -- this line left to mean anything.
    unless (← e.crashDaemon "boot") do
      throw (IO.userError "daemon for this LINGER_DIR not found, or the SIGKILL did not land")
    expect ((← e.status "boot") == Status.resumable && has (← e.out #["list"]) "boot")
        "killed session listed as resumable"
    -- attach again: fresh shell, restored screen, restored labels, saved cwd
    let boot2 ← e.spawn #["attach", "boot"] cols rows
    let replay ← IO.mkRef ByteArray.empty
    expect (← boot2.awaitText replay (hasText · marker) (ms := 5000))
        "reattach replays the pre-reboot scrollback, not just the screen"
    boot2.type "pwd -P\r"
    -- The checkpoint records the physical cwd, which is what `pwd -P` prints whatever
    -- `PWD` the fresh shell inherits.
    let savedCwd ← IO.FS.realPath e.dir
    expect (has (← drainStr boot2.fd 1500) savedCwd.toString) "fresh shell starts in the saved cwd"
    expect (has (← e.out #["get", "boot"]) "k=v") "labels survive the reboot"
    -- a clean exit keeps the session as a result: its last screen stays saved, listed as
    -- ended with status 0. The marker is an expansion, so the typed line cannot show it.
    boot2.type "echo LAST-$((6*7)); exit\r"
    let ended ← waitFor 5000 (return (← e.status "boot") == Status.exitedOk)
    let ckpts2 ← e.dirNames ".ckpt"
    expect
        (ended && (← e.field "boot" "exit") == some "0" && ckpts2 == ["boot.ckpt"] &&
          has (← e.out #["capture", "boot"]) "LAST-42")
        s!"a clean exit keeps the last screen, listed as ended with status 0 ({ckpts2})"
    boot2.bye (sendDetach := false)
    -- writable attach resumes an ended session: its last screen, labels and directory, under
    -- a fresh shell
    let boot3 ← e.spawn #["attach", "boot"] cols rows
    let replay3 ← IO.mkRef ByteArray.empty
    let restored ← boot3.awaitText replay3 (hasText · "LAST-42") (ms := 5000)
    expect
        (restored &&
          (←
            waitFor 4000 do
                return (← e.status "boot") != Status.exitedOk && (← e.info "boot" "pid").isSome) &&
          has (← e.out #["get", "boot"]) "k=v")
        "attach resumes an ended session with its last screen and labels"
    boot3.type "exit\r"
    let _ ← waitFor 5000 (return (← e.status "boot") == Status.exitedOk)
    boot3.bye (sendDetach := false)
    -- `resume` runs an ended session's program again without attaching and leaves a live one as
    -- it is; a name no session holds starts nothing
    let (resumedRc, _, _) ← e.cli #["resume", "boot"]
    let live ←
      waitFor 4000 do
          return (← e.status "boot") != Status.exitedOk && (← e.info "boot" "pid").isSome
    let pid ← e.info "boot" "pid"
    let (againRc, _, _) ← e.cli #["resume", "boot"]
    expect
        (resumedRc == 0 && live && has (← e.out #["capture", "--history", "boot"]) "LAST-42" &&
          has (← e.out #["get", "boot"]) "k=v" &&
          againRc == 0 &&
          (← e.info "boot" "pid") == pid)
        "resume runs an ended session's program again on its last screen, and leaves a live one as it is"
    let (missingRc, _, missingErr) ← e.cli #["resume", "nosuch"]
    expect
        (missingRc == 127 && has missingErr "no session 'nosuch'" &&
          !(← System.FilePath.pathExists s!"{e.dir}/nosuch.ckpt") &&
          !(← System.FilePath.pathExists s!"{e.dir}/nosuch.sock"))
        "resume of a name no session holds starts nothing and exits 127"
    e.killAll #["boot"]
    let ckpts3 ← e.dirNames ".ckpt"
    expect (ckpts3 == [] && !has (← e.out #["ls"]) "boot")
        s!"kill discards an ended session's checkpoint ({ckpts3})"
    -- corrupt checkpoint: daemon must start fresh, not crash.
    --
    -- Written with `Checkpoint.magic`: a foreign tag would only reach `stripMagic`'s
    -- reject, the shallowest branch there is. With the real tag the file gets past
    -- the version gate and dies in the body, which is the branch a torn write takes.
    --
    -- The body is deterministic: 80 and 24 read back as the geometry (LEB128,
    -- single bytes under 128), then the grid's length is an `rNat` over a run of
    -- 0xFF — all continuation bytes, so it runs off the end of the list and `load`
    -- is `none` for certain. A random body is a random branch, and a flake here
    -- would be unreproducible.
    let corrupt := Linger.Session.Checkpoint.magic ++ [80, 24] ++ List.replicate 198 (0xFF : UInt8)
    IO.FS.writeBinFile s!"{e.dir}/corrupt.ckpt" (ByteArray.mk corrupt.toArray)
    -- a resume runs a saved session's program again or nothing, so it refuses what it cannot
    -- read and leaves it where it is
    let (refusedRc, _, refusedErr) ← e.cli #["resume", "corrupt"]
    let kept ← (IO.FS.readBinFile s!"{e.dir}/corrupt.ckpt").toBaseIO
    expect
        (refusedRc == 1 && has refusedErr "cannot be read" &&
          kept.toOption.map (·.toList) == some corrupt &&
          (← e.info "corrupt" "pid").isNone)
        s!"corrupt checkpoint: resume refuses it and leaves it (rc={refusedRc})"
    -- …while attach starts fresh
    let fresh ← e.spawn #["attach", "corrupt"] cols rows
    let _ ← waitFor 4000 (return (← e.info "corrupt" "clients") == some "1")
    fresh.type "echo fresh-start-$((40+2))\r"
    expect
        (←
          waitFor 4000 (return has (← e.out #["capture", "--history", "corrupt"]) "fresh-start-42"))
        "corrupt checkpoint: attach starts fresh, no crash"
    fresh.bye
    e.killAll #["corrupt"]
    -- ── the resumed pty is born at the CHECKPOINT's size, not a fixed 80x24 ────
    -- Measured with NO sizing attach: `resume` and `send` never send `.attach`,
    -- so nothing reconciles the pty with the restored Vt. With an attach the
    -- assertion passes either way (`.resizePty` fixes the winsize in
    -- milliseconds), which is the version of this test that cannot fail.
    let gCols : UInt32 := 100
    let gRows : UInt32 := 40
    let geom ← e.spawn #["attach", "geom"] gCols gRows
    let _ ← waitFor 4000 (return (← e.info "geom" "clients") == some "1")
    geom.type "echo geom-ready\r"
    let _ ← drain geom.fd 1200
    geom.detach -- last detach → checkpoint at 100x40
    let _ ← waitFor 4000 (return (← e.info "geom" "clients") == some "0")
    -- the save runs on its own thread: wait for a checkpoint at the attached size
    let _ ←
      waitFor 4000 do
          match ← (IO.FS.readBinFile s!"{e.dir}/geom.ckpt").toBaseIO with
          | .ok bytes =>
            return (Linger.Session.Checkpoint.loadBytes bytes).any (·.vt.colCount == gCols.toNat)
          | .error _ =>
            return false
    geom.bye (sendDetach := false)
    let _ ← e.crashDaemon "geom" -- simulated reboot; tolerated if already gone
    let sizePath := s!"{e.dir}/geom.size"
    -- The probe must run on the far side of the resumed pty; this suite binary is
    -- already a Lean child probe for the terminal suite, so reuse it rather than
    -- embedding a second-language ioctl script.
    let probe ← IO.appPath
    let _ ← e.typeIn "geom" #[probe.toString, "--winsize-probe", sizePath]
    -- `writeFile` creates the file before it writes, so wait for its contents
    let _ ←
      waitFor 5000 do
          if ← System.FilePath.pathExists sizePath then
            return !(← IO.FS.readFile sizePath).isEmpty
          return false
    let got ←
      if (← System.FilePath.pathExists sizePath) then
        pure ((← IO.FS.readFile sizePath).trimAscii.toString.splitOn " ")
      else
        pure []
    expect (got == [toString gCols, toString gRows])
        s!"resumed pty is born at the checkpoint size, not 80x24 ({got})"
    e.killAll #["geom"]
    -- Save failure: a bad tmp path is reported, but the daemon keeps serving.
    let saveFail ← e.spawn #["attach", "save-fail"] cols rows
    let _ ← waitFor 4000 (return (← e.info "save-fail" "clients") == some "1")
    let _ ← drain saveFail.fd 300
    let saveTmp := s!"{e.dir}/save-fail.ckpt.tmp"
    IO.FS.createDirAll saveTmp
    -- Produce output *after* the bad tmp path exists. The last-detach save fires
    -- only when there is something new to save, and the daemon's first tick is
    -- eligible immediately (`lastCkptMs` starts at 0), so it can checkpoint the
    -- shell's prompt — clearing `dirty` — before this point in the test. Asserted
    -- rather than slept on: a silent miss here used to look like a save-report bug.
    saveFail.type "echo save-fail-dirty\n"
    let seen ← IO.mkRef ByteArray.empty
    let dirtied ← saveFail.awaitText seen (hasText · "save-fail-dirty") (ms := 3000)
    expect dirtied "session has unsaved output once the bad tmp path exists"
    saveFail.detach
    let _ ← waitFor 4000 (return (← e.info "save-fail" "clients") == some "0")
    saveFail.bye (sendDetach := false)
    let saveReported ←
      waitFor 5000
          (do
            return has (← e.log "save-fail") "checkpoint save failed")
    let saveLog ← e.log "save-fail"
    let savePid ← e.info "save-fail" "pid"
    expect (saveReported && savePid.isSome)
        s!"checkpoint save failure is reported without killing the daemon (pid={savePid}, log='{saveLog}')"
    IO.FS.removeDirAll saveTmp
    e.killAll #["save-fail"]
    -- Existing but unreadable recovery state is not equivalent to no checkpoint. A resume
    -- says why at once. An attach's daemon exits, so the client gives up after the 3 s floor,
    -- long before the 30 s cap. The client says the same either way, so only when it gives up
    -- tells them apart: the wait ends 17 s after the floor and 10 s before the cap, as far from
    -- each as the product's own constants allow, so neither the host's load nor a client that
    -- waited out the cap can be mistaken for the other.
    let readPath := s!"{e.dir}/read-fail.ckpt"
    IO.FS.createDirAll readPath
    let readStart ← Os.Shell.monotonicMs
    let readResume ← e.cliTimeout #["resume", "read-fail"] hangMs
    let reader ← e.spawn #["attach", "read-fail"] cols rows
    let readOut ← IO.mkRef ByteArray.empty
    let gaveUp ← reader.awaitText readOut (hasText · "see ") (ms := 20000)
    let readRc ← reader.reap patienceMs
    reader.bye (sendDetach := false)
    let readMs := (← Os.Shell.monotonicMs) - readStart
    let readSockets ← e.dirNames ".sock"
    let readLog ← e.log "read-fail"
    expect
        (readResume.any (fun (rc, _, err) => rc == 125 && has err "checkpoint read failed") &&
          gaveUp &&
          readRc == 1 &&
          has readLog "checkpoint read failed" &&
          !readSockets.contains "read-fail.sock")
        s!"checkpoint read failure is visible, does not start fresh and gives up long before \
          the 30 s cap ({readResume.map (·.1)}, {readRc}, {readMs} ms)"
    e.killAll #["read-fail"]
    IO.FS.removeDirAll readPath
    -- A daemon that holds its locks but needs longer than the 3 s floor to listen still
    -- serves the attach that started it; a FIFO checkpoint holds its load for 4 s.
    let slowPath := s!"{e.dir}/slow.ckpt"
    let made ← IO.Process.output { cmd := "mkfifo", args := #[slowPath] }
    let release ←
      IO.Process.spawn
          { cmd := "sh", args := #["-c", s!"sleep 4; printf not-a-checkpoint > '{slowPath}'"],
            stdin := .null, stdout := .null, stderr := .null }
    let slowStart ← Os.Shell.monotonicMs
    let slow ← e.spawn #["attach", "slow"] cols rows
    let attached ← waitFor hangMs (return (← e.info "slow" "clients") == some "1")
    let slowMs := (← Os.Shell.monotonicMs) - slowStart
    let _ ← waitOrKill release hangMs
    slow.bye
    expect (made.exitCode == 0 && attached && slowMs ≥ 3000)
        s!"a daemon slower than the 3 s window to listen still connects ({slowMs} ms)"
    e.killAll #["slow"]
    -- Delete failure is observable in the daemon log instead of silently leaving
    -- recovery state behind.
    let _ ← e.typeIn "drop-fail" #["sleep", "600"]
    let dropPath := s!"{e.dir}/drop-fail.ckpt"
    try
      IO.FS.removeFile dropPath
    catch _ =>
      pure ()
    IO.FS.createDirAll dropPath
    let _ ← e.cli #["kill", "drop-fail"]
    let dropReported ←
      waitFor 3000
          (do
            return has (← e.log "drop-fail") "checkpoint delete failed")
    expect (dropReported && (← System.FilePath.pathExists dropPath))
        "checkpoint delete failure is reported"
    -- …and reporting it is not the same as surviving it. A logged cleanup failure
    -- must still let `.exit` run: this suite leaked a `drop-fail` daemon that
    -- outlived its run by two hours, because nothing here asked.
    expect
        (←
          waitFor 5000
              (do
                return (← e.daemonPid "drop-fail").isNone))
        "a reported delete failure still lets the daemon exit"
    IO.FS.removeDirAll dropPath
    e.killAll #["drop-fail"]

end Linger.Session.Suites.Resume
