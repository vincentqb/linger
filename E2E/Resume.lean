module

public import E2E.Harness
public import Linger.Core.Checkpoint
public import Linger.Runtime.Daemon

public section

/-! # E2E.Resume — reboot-resume: checkpoint, crash, restore

Ported from `tests/resume_test.py`.

Checkpoint on last detach, daemon SIGKILLed (simulated crash/reboot), session
listed as resumable, attach restores the old screen and labels and starts a fresh
shell in the saved cwd.

WHAT THE PORT TIGHTENED:

* **the daemon is identified structurally, not by heuristic.** `tests/procs.py`
  had to ask `pgrep -f '__daemon <name>'` and then filter the candidates down to
  the ones whose `LINGER_DIR` is ours — Linux via `/proc/<pid>/environ`, macOS
  via `lsof -p` because there is no `/proc` and `ps -Eww` prints no environment
  there. `Env.daemonPid` asks the daemon over `<LINGER_DIR>/<name>.sock`
  instead, so the isolation is by construction. See its docstring;
* **the SIGKILL is verified.** The Python `assert dpids` proved a pid was
  *found*; `Env.crashDaemon` returns whether it was alive before and is gone
  after. That assert's role — abort, do not print a check — is kept exactly, so
  this suite still runs 9 checks and not 10;
* **the checkpoint is checked to be this format**, by `Checkpoint.magic` rather
  than a byte string copied into the test, both when reading the one `save`
  wrote and when writing the corrupt one (see below);
* the resumable row is compared as a `Status`, not as the substring
  `'resumable'` anywhere in the listing — the Python's `'resumable' in ls` would
  also have matched some *other* row's `(resumable)`. -/

namespace E2E.Resume

open E2E.Harness
open Linger.Core.Status (Status)

/-- Child-side winsize probe. It must execute inside the resumed session's pty;
reading the parent process's tty would test the harness instead. -/
def winsizeProbe (resultPath : String) : IO UInt32 := do
  let (cols, rows) ← Linger.Posix.winsizeGet Linger.Posix.stdinFd
  IO.FS.writeFile resultPath s!"{cols} {rows}"
  return 0

def daemonLog (e : Env) (name : String) : IO String := do
  try
    IO.FS.readFile s!"{e.dir}/logs/{name}.log"
  catch _ =>
    pure ""

/-- Exercise the real effect interpreter with one failed save and no further
output. The injected clock checks retry cadence without waiting a minute. -/
def checkpointRetry : IO Nat := do
  let attempts ← IO.mkRef (0 : Nat)
  let saved ← IO.mkRef ([] : List (String × String))
  let labels := [("quiet", "kept")]
  let rt : Linger.Runtime.Daemon.Rt :=
    { st := Linger.Core.Session.State.boot (Linger.Core.Vt.Vt.init 20 5) labels [], listenFd := 0,
      ptyFd := 0, childPid := 0, sockPath := "",
      saveCkpt := fun st => do
        attempts.modify (· + 1)
        if (← attempts.get) == 1 then
          throw (IO.userError "injected save failure")
        saved.set st.labels,
      dropCkpt := pure () }
  let interval := Linger.Core.Session.ckptIntervalMs
  let rt ← Linger.Runtime.Daemon.pump rt [.ptyOut [65], .tick interval]
  let rt ← Linger.Runtime.Daemon.pump rt [.tick (interval + 1)]
  let before ← attempts.get
  let _ ← Linger.Runtime.Daemon.pump rt [.tick (interval + interval)]
  expect (before == 1 && (← attempts.get) == 2 && (← saved.get) == labels)
      "a failed quiet checkpoint retries at the next cadence with its state intact"

def run : IO UInt32 := do
  let e ← Env.make "resume"
  let mut f ← checkpointRetry
  -- one source for the pty geometry and for the off-the-screen window below
  let cols : UInt32 := 80
  let rows : UInt32 := 24
  let marker := "survives-the-reboot-42"
  -- create a session working in /tmp, leave a marker on screen and a label
  let boot ← e.spawn #["attach", "boot"] cols rows
  IO.sleep 800
  boot.type "cd /tmp && echo survives-the-reboot-$((40+2))\r"
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
  -- line is the marker itself. That is what Python's `x in <list of lines>`
  -- meant, and `has` would have weakened it.
  let hist0 := lines (← e.out #["history", "boot"])
  f :=
    f +
      (←
        expect (hist0.contains marker && !(hist0.drop (hist0.length - rows.toNat)).contains marker)
            "the pre-reboot marker is in the ring, off the 24-row screen")
  let _ ← e.cli #["set", "boot", "k=v"]
  -- detach (last attached client): the machine checkpoints here
  boot.detach
  IO.sleep 800
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
        pure (startsWithBytes bytes Linger.Core.Checkpoint.magic)
    else
      pure false
  f := f + (← expect (ckptOk && magicOk) s!"checkpoint written on last detach ({ckpts})")
  -- simulate reboot: SIGKILL the DAEMON (the pid in `list` is the shell —
  -- killing that is a clean exit and rightly drops the checkpoint). Aborts the
  -- suite rather than printing a check, exactly as the Python `assert` did: with
  -- no crash there is nothing below this line left to mean anything.
  unless (← e.crashDaemon "boot") do
    throw (IO.userError "daemon for this LINGER_DIR not found, or the SIGKILL did not land")
  f :=
    f +
      (←
        expect ((← e.status "boot") == Status.resumable && has (← e.out #["list"]) "boot")
            "killed session listed as resumable")
  -- attach again: fresh shell, restored screen, restored labels, saved cwd
  let boot2 ← e.spawn #["attach", "boot"] cols rows
  IO.sleep 1000
  f :=
    f +
      (←
        expect (has (← drainStr boot2.fd 1500) marker)
            "reattach replays the pre-reboot scrollback, not just the screen")
  boot2.type "pwd\r"
  f := f + (← expect (has (← drainStr boot2.fd 1500) "/tmp") "fresh shell starts in the saved cwd")
  f := f + (← expect (has (← e.out #["get", "boot"]) "k=v") "labels survive the reboot")
  -- clean exit drops the checkpoint
  boot2.type "exit\r"
  IO.sleep 1000
  let ckpts2 ← e.dirNames ".ckpt"
  f := f + (← expect (ckpts2 == []) s!"clean exit drops the checkpoint ({ckpts2})")
  boot2.bye (sendDetach := false)
  -- corrupt checkpoint: daemon must start fresh, not crash.
  --
  -- Written with `Checkpoint.magic`, not with the Python's `b'LINGER\x01'`:
  -- that is not this format's tag at all ("LINGE…" ≠ "LNGR"), so it only ever
  -- reached `stripMagic`'s reject — the shallowest branch there is, and the one
  -- a *version bump* would keep it on forever. With the real tag the file gets
  -- past the version gate and dies in the body, which is the branch a torn
  -- write takes.
  --
  -- The body is deterministic rather than `os.urandom`: 80 and 24 read back as
  -- the geometry (LEB128, single bytes under 128), then the grid's length is an
  -- `rNat` over a run of 0xFF — all continuation bytes, so it runs off the end
  -- of the list and `load` is `none` for certain. A random body is a random
  -- branch, and a flake here would be unreproducible.
  IO.FS.writeBinFile s!"{e.dir}/corrupt.ckpt"
      (ByteArray.mk
        (Linger.Core.Checkpoint.magic ++ [80, 24] ++ List.replicate 198 (0xFF : UInt8)).toArray)
  let _ ← e.cli #["run", "corrupt", "echo fresh-start-ok"]
  IO.sleep 800
  f :=
    f +
      (←
        expect (has (← e.out #["history", "corrupt"]) "fresh-start-ok")
            "corrupt checkpoint: daemon starts fresh, no crash")
  e.killAll #["corrupt"]
  -- ── the resumed pty is born at the CHECKPOINT's size, not a fixed 80x24 ────
  -- Measured with NO sizing attach: `run` sends only `.input`, never `.attach`,
  -- so nothing reconciles the pty with the restored Vt. With an attach the
  -- assertion passes either way (`.resizePty` fixes the winsize in
  -- milliseconds), which is the version of this test that cannot fail.
  -- (The Python needed a second `spawn_attach_sized` helper here because its
  -- first one hardcoded 80x24. `Env.spawn` takes the size — and sets it before
  -- exec, so the ioctl race went with the duplication.)
  let gCols : UInt32 := 100
  let gRows : UInt32 := 40
  let geom ← e.spawn #["attach", "geom"] gCols gRows
  IO.sleep 800
  geom.type "echo geom-ready\r"
  let _ ← drain geom.fd 1200
  geom.detach -- last detach → checkpoint at 100x40
  IO.sleep 800
  geom.bye (sendDetach := false)
  let _ ← e.crashDaemon "geom" -- simulated reboot; tolerated if already gone
  let sizePath := s!"{e.dir}/geom.size"
  -- The probe must run on the far side of the resumed pty; this e2e binary is
  -- already a Lean child probe for the terminal suite, so reuse it rather than
  -- embedding a second-language ioctl script.
  let probe ← IO.appPath
  let _ ← e.cli #["run", "geom", probe.toString, "--winsize-probe", sizePath]
  IO.sleep 1500
  let got ←
    if (← System.FilePath.pathExists sizePath) then
      pure ((← IO.FS.readFile sizePath).trimAscii.toString.splitOn " ")
    else
      pure []
  f :=
    f +
      (←
        expect (got == [toString gCols, toString gRows])
            s!"resumed pty is born at the checkpoint size, not 80x24 ({got})")
  e.killAll #["geom"]
  -- Save failure: a bad tmp path is reported, but the daemon keeps serving.
  let saveFail ← e.spawn #["attach", "save-fail"] cols rows
  IO.sleep 800
  let _ ← drain saveFail.fd 300
  let saveTmp := s!"{e.dir}/save-fail.ckpt.tmp"
  IO.FS.createDirAll saveTmp
  -- Produce output *after* the bad tmp path exists. The last-detach save fires
  -- only when there is something new to save, and the daemon's first tick is
  -- eligible immediately (`lastCkptMs` starts at 0), so it can checkpoint the
  -- shell's prompt — clearing `dirty` — before this point in the test. Asserted
  -- rather than slept on: a silent miss here used to look like a save-report bug.
  saveFail.type "echo save-fail-dirty\n"
  let seen ← IO.mkRef ""
  let dirtied ←
    waitFor 3000 do
        let chunk ← drainStr saveFail.fd 200
        seen.modify (· ++ chunk)
        return has (← seen.get) "save-fail-dirty"
  f := f + (← expect dirtied "session has unsaved output once the bad tmp path exists")
  saveFail.detach
  IO.sleep 800
  saveFail.bye (sendDetach := false)
  let saveReported ←
    waitFor 5000
        (do
          return has (← daemonLog e "save-fail") "checkpoint save failed")
  let saveLog ← daemonLog e "save-fail"
  let savePid ← e.info "save-fail" "pid"
  f :=
    f +
      (←
        expect (saveReported && savePid.isSome)
            s!"checkpoint save failure is reported without killing the daemon (pid={savePid}, log='{saveLog}')")
  IO.FS.removeDirAll saveTmp
  e.killAll #["save-fail"]
  IO.sleep 500
  -- Existing but unreadable recovery state is not equivalent to no checkpoint.
  let readPath := s!"{e.dir}/read-fail.ckpt"
  IO.FS.createDirAll readPath
  let (readRc, _, readErr) ← e.cli #["run", "read-fail", "echo", "must-not-start"]
  let readSockets ← e.dirNames ".sock"
  f :=
    f +
      (←
        expect
            (readRc == 1 && has readErr "checkpoint read failed" &&
              !readSockets.contains "read-fail.sock")
            "checkpoint read failure is visible and does not start fresh")
  e.killAll #["read-fail"]
  IO.sleep 300
  IO.FS.removeDirAll readPath
  -- Delete failure is observable in the daemon log instead of silently leaving
  -- recovery state behind.
  let _ ← e.cli #["run", "drop-fail", "sleep", "600"]
  IO.sleep 800
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
          return has (← daemonLog e "drop-fail") "checkpoint delete failed")
  f :=
    f +
      (←
        expect (dropReported && (← System.FilePath.pathExists dropPath))
            "checkpoint delete failure is reported")
  -- …and reporting it is not the same as surviving it. A logged cleanup failure
  -- must still let `.exit` run: this suite leaked a `drop-fail` daemon that
  -- outlived its run by two hours, because nothing here asked.
  f :=
    f +
      (←
        expect
            (←
              waitFor 5000
                  (do
                    return (← e.daemonPid "drop-fail").isNone))
            "a reported delete failure still lets the daemon exit")
  IO.FS.removeDirAll dropPath
  e.killAll #["drop-fail"]
  verdict e f

end E2E.Resume
