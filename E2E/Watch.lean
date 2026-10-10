module

public import E2E.Harness
import Linger.Core.Checkpoint

public section

/-! # E2E.Watch — read-only live and saved attachment

WHAT THIS CAN AND CANNOT CATCH — read before adding a check. Read-only is enforced
DAEMON-side, not by `Client.attach`'s three `!readOnly` guards:

* guard A, `sendMsg fd (.attach 0 0)` — the 0×0 geometry IS the read-only marker
  on the wire. `onMsg .attach` derives `sizer := cols != 0 && rows != 0` from it
  and everything else follows. Removing A is observable three ways; break-verified,
  checks 3, 6 and 8 below each catch it.
* guard B (resize suppression) and guard C (keystroke suppression) — BOTH are
  semantic no-ops. `onMsg .resize` drops a non-sizer's resize and `onMsg .input`
  drops a non-sizer's input (`onMsg_input_readonly`), so removing either changes
  no observable byte. They are defence in depth, held by grep gates in
  `scripts/gates.sh` — the `SHIM_CAP` species of oracle.

So: do not add a check here claiming to catch B or C. It cannot. -/

namespace E2E.Watch

open E2E.Harness
open Linger.Core.Status (Status)

/-- Saved viewing is a terminal client over one immutable checkpoint, with no
daemon lifetime. Exercise resize, ownership and chooser behavior independently
of the live observer checks. -/
def checkpointChecks (e : Env) : IO Unit := do
  let vt :=
    (Linger.Core.Vt.Vt.init 40 4).feedBytes
      "older\r\nhistory\r\nfirst\r\nsecond\r\nthird\r\nsaved-screen-at-the-right\x1b]2;editor\x07".toUTF8
  let bytes := ByteArray.mk (Linger.Core.Checkpoint.save ⟨vt, "/tmp", [("saved", "yes")]⟩).toArray
  let path := s!"{e.dir}/saved.ckpt"
  IO.FS.writeBinFile path bytes
  let viewer ← e.spawn #["attach", "--read-only", "saved"] 40 4
  try
    let output ← drain viewer.fd 1500
    let rendered := hasBytes output (Linger.Core.Render.restore vt)
    expect rendered "read-only attach replays the saved terminal and scrollback"
    if !rendered then
      return
    let title := ((Linger.Core.Vt.Vt.init 40 4).feed output.toList).windowTitle
    expect (has title "saved" && has title "editor" && has title "~")
        "a saved view identifies the session, application and checkpoint in its title"
    viewer.type "echo unwanted-input\r"
    let quiet ← drain viewer.fd 400
    expect
        (quiet.isEmpty && (← IO.FS.readBinFile path).toList == bytes.toList &&
          !(← System.FilePath.pathExists s!"{e.dir}/saved.sock"))
        "saved viewing discards input without changing the checkpoint or starting a daemon"
    for lock in [s!"{e.dir}/saved.lock", s!"{e.dir}/.locks/saved.lock"] do
      let fd ← Linger.Posix.flock lock
      expect (fd ≥ 0) "saved viewing releases ownership after loading"
      if fd ≥ 0 then
        Linger.Posix.close fd.toUInt64.toUInt32
    viewer.resize 12 2
    let narrow ← drain viewer.fd 500
    expect (hasBytes narrow (Linger.Core.Render.restore (vt.resize 12 2)))
        "saved viewing redraws at the viewer's terminal size"
    viewer.resize 40 4
    let wide ← drain viewer.fd 500
    expect (hasBytes wide (Linger.Core.Render.restore vt))
        "expanding a saved view restores the original snapshot after clipping"
    viewer.detach
    let back ← drain viewer.fd 1000
    expect
        ((← viewer.reap 1000) == 0 && hasBytes back Linger.Core.Render.leaveAnsi &&
          (← IO.FS.readBinFile path).toList == bytes.toList)
        "saved viewing detaches with canonical terminal handback and unchanged checkpoint"
  finally
    viewer.bye
    e.killAll #["--read-only"]
  -- A saved view forwards nothing and raw mode clears ISIG: the detach key is its
  -- only exit, so the writable-attach opt-out must not remove it.
  let pinned ← e.spawnEnv #["LINGER_NO_DETACH_KEY=1"] #["attach", "--read-only", "saved"] 40 4
  try
    let _ ← drain pinned.fd 1000
    pinned.detach
    let back ← drain pinned.fd 2000
    expect ((← pinned.reap 2000) == 0 && hasText back "detached from")
        "ctrl-\\ leaves a saved view even with LINGER_NO_DETACH_KEY set"
  finally
    pinned.bye
  for (cols, rows, expected) in [(0, 0, vt), (0, 2, vt.resize 40 2), (12, 0, vt.resize 12 4)] do
    let unsized ← e.spawn #["attach", "--read-only", "saved"] cols rows
    try
      let output ← drain unsized.fd 1000
      expect (hasBytes output (Linger.Core.Render.restore expected))
          s!"saved viewing uses checkpoint dimensions when terminal size is unspecified ({cols}x{rows})"
    finally
      unsized.bye
  for lock in [s!"{e.dir}/saved.lock", s!"{e.dir}/.locks/saved.lock"] do
    let fd ← Linger.Posix.flock lock
    unless fd ≥ 0 do
      throw (IO.userError s!"fixture lock unavailable: {lock}")
    try
      let blocked ← e.spawn #["attach", "--read-only", "saved"] 40 4
      try
        let output ← drain blocked.fd 1500
        expect
            ((← blocked.reap 1000) == 1 && hasText output "owned by another process" &&
              !hasBytes output (Linger.Core.Render.restore vt))
            "read-only attach refuses a checkpoint still owned by a daemon"
      finally
        blocked.bye
    finally
      Linger.Posix.close fd.toUInt64.toUInt32
  IO.FS.writeBinFile s!"{e.dir}/bad.ckpt" ⟨#[1, 2, 3]⟩
  let bad ← e.spawn #["attach", "--read-only", "bad"]
  try
    let err ← drainStr bad.fd 1000
    expect ((← bad.reap 1000) == 1 && has err "no live session or readable checkpoint")
        "read-only attach rejects corrupt checkpoint bytes"
  finally
    bad.bye
  IO.FS.writeBinFile s!"{e.dir}/--read-only.ckpt" bytes
  let literal ← e.spawn #["attach", "--read-only", "--", "--read-only"] 40 4
  try
    let output ← drain literal.fd 1000
    expect
        (hasBytes output (Linger.Core.Render.restore vt) &&
          !(← System.FilePath.pathExists s!"{e.dir}/--read-only.sock"))
        "an option-like name remains an exact read-only target after --"
  finally
    literal.bye
  IO.FS.writeBinFile s!"{e.dir}/--history.ckpt" bytes
  let (literalRc, literalText, _) ← e.cli #["capture", "--", "--history"]
  expect (literalRc == 0 && literalText.toUTF8.toList == Linger.Core.Render.screenText vt)
      "capture -- distinguishes the literal --history name from its option"
  let chooser ←
    e.spawnEnv #[s!"XDG_CONFIG_HOME={e.dir}/config", "NO_COLOR=1"] #["attach", "--read-only"] 100 24
  try
    let initial ← drainStr chooser.fd 1200
    expect (has initial "Find a session" && !has initial "Create")
        "the read-only chooser offers existing sessions without creation"
    chooser.type "no-match\r"
    let noMatch ← drainStr chooser.fd 500
    expect
        (has noMatch "No matching sessions" &&
          !(← System.FilePath.pathExists s!"{e.dir}/no-match.sock"))
        "Enter on an unmatched read-only query cannot create a session"
    chooser.type "\x15saved\r"
    let selected ← drain chooser.fd 800
    expect
        (hasBytes selected (Linger.Core.Render.restore (vt.resize 100 24)) &&
          !(← System.FilePath.pathExists s!"{e.dir}/saved.sock"))
        "read-only selection opens the checkpoint without resuming a program"
    chooser.detach
    let returned ← drainStr chooser.fd 1000
    chooser.type "\x1b"
    let _ ← drain chooser.fd 400
    expect (has returned "Find a session" && (← chooser.reap 1000) == 130)
        "detaching a saved view returns to the read-only chooser"
  finally
    chooser.bye
    e.killAll #["saved", "no-match", "--read-only"]

def runCheckpoint : IO UInt32 := Env.suite "watch-checkpoint" checkpointChecks

def run : IO UInt32 :=
  Env.suite "watch" fun e => do
    -- 1. read-only attachment cannot create a session.
    let missing ← e.spawn #["attach", "--read-only", "nosuch"]
    let err ← drainStr missing.fd 1500
    let rc ← missing.reap
    missing.bye (sendDetach := false)
    expect (rc == 1) "read-only attach to a missing session exits 1"
    expect (has err "no live session or readable checkpoint for 'nosuch'")
        "read-only attach reports the exact missing session"
    expect (!has (← e.out #["ls"]) "nosuch") "read-only attach creates no session"
    -- the session under test: one real client at 80x24
    let real ← e.spawn #["attach", "w"] 80 24
    let _ ← waitFor 4000 (return (← e.info "w" "clients") == some "1")
    let _ ← drain real.fd 500
    expect ((← e.info "w" "cols") == some "80") "session starts 80 wide"
    -- 2. the watcher attaches, at a DIFFERENT geometry
    let obs ← e.spawn #["attach", "--read-only", "w"] 100 30
    let _ ← waitFor 4000 (return (← e.info "w" "clients") == some "2")
    let _ ← drain obs.fd 1000 -- swallow the restore burst
    expect ((← e.info "w" "clients") == some "2")
        "the watcher counts as a client (so it really is attached)"
    -- 3. …and never owns the geometry
    expect ((← e.info "w" "cols") == some "80" && (← e.info "w" "rows") == some "24")
        "a 100x30 watcher does not resize the session (guard A)"
    -- 4. keystrokes at the watcher never reach the pty. Assert on the EXPANSION,
    -- not the typed text: if input were forwarded the shell would both echo and
    -- run it, and the arithmetic result is the discriminating string.
    obs.type "echo wmark-$((21+21))\r"
    IO.sleep 1200
    expect (!has (← e.out #["capture", "w"]) "wmark-42")
        "the watcher's keyboard does not reach the pty"
    -- 5. non-vacuity for 4: the watcher really is receiving output
    real.type "echo mirror-$((20+22))\r"
    let mirrored ← IO.mkRef ByteArray.empty
    expect (← obs.awaitText mirrored (hasText · "mirror-42"))
        "the watcher mirrors the session output"
    -- 6. resizing the watcher's own terminal moves nothing. The only way to make
    -- guard B's code path execute at all: `lastSize` is seeded with the real size,
    -- so nothing is sent until the terminal actually changes.
    obs.resize 120 40
    IO.sleep 800
    expect ((← e.info "w" "cols") == some "80")
        "resizing the watcher's terminal does not resize the session"
    -- 7/8. a watcher is not the size owner, so `linger resize` still applies.
    -- With guard A intact `sizeOwner` is none and controlResize applies; with A
    -- removed the watcher owns the size and this returns 1 with "owns the size".
    real.bye
    let _ ← waitFor 4000 (return (← e.info "w" "clients") == some "1")
    expect ((← e.info "w" "clients") == some "1") "only the watcher is left"
    let (rzc, _, _) ← e.cli #["resize", "w", "90", "25"]
    expect (rzc == 0 && (← e.info "w" "cols") == some "90")
        "a watcher does not own the size, so `linger resize` applies"
    -- 9. ctrl-\ detaches a watcher, through the shared hand-back. Drain first:
    -- the resize made the shell redraw, and that output sits ahead of the
    -- epilogue — the leading-ST check is about what the CLIENT writes on its way
    -- out, so the buffer has to be empty when it starts.
    let _ ← drain obs.fd 800
    obs.detach
    let back ← drain obs.fd 2000
    let backStr := String.fromUTF8? back |>.getD ""
    expect (has backStr "detached from") "ctrl-\\ detaches the watcher"
    -- Compared against the session's OWN emitter rather than a hardcoded byte
    -- string, so the suite cannot drift from what the implementation hands back.
    -- `leave_canonical_all` is what proves the contents; this is that the client
    -- actually writes them, which no theorem can see.
    let leave := Linger.Core.Render.leaveAnsi
    expect (startsWithBytes back (leave.take 2))
        "a watcher hands the terminal back too (leaveAnsi's leading ST)"
    expect (hasBytes back leave) "the watcher writes leaveAnsi verbatim, byte for byte"
    obs.bye (sendDetach := false)
    expect (has (← e.out #["ls"]) "w") "the session survives the watcher leaving"
    -- A read-only attach forwards no input, so the writable-attach opt-out must
    -- not take away its only exit.
    let pinned ← e.spawnEnv #["LINGER_NO_DETACH_KEY=1"] #["attach", "--read-only", "w"] 80 24
    let _ ← waitFor 4000 (return (← e.info "w" "clients") == some "1")
    let _ ← drain pinned.fd 500
    pinned.detach
    let pinnedBack ← drain pinned.fd 2000
    expect ((← pinned.reap 2000) == 0 && hasText pinnedBack "detached from")
        "ctrl-\\ leaves a live read-only view even with LINGER_NO_DETACH_KEY set"
    pinned.bye (sendDetach := false)
    -- 10. watching marks the session SEEN — a read-only verb with a write effect.
    -- `onMsg .attach` sets `lookSeq := s.outSeq` for ANY attach, 0x0 included, so
    -- Read-only attach clears `wants-you`. The status suite only ever exercised that
    -- through `attach`. Compared as a `Status`, not a string literal.
    let _ ← e.cli #["send", "w", "echo unread-marker\n"]
    let _ ← waitFor 4000 (return (← e.status "w") == Status.wantsYou)
    expect ((← e.status "w") == Status.wantsYou) "output with nobody watching reads wants-you"
    let obs2 ← e.spawn #["attach", "--read-only", "w"] 80 24
    let _ ← waitFor 4000 (return (← e.info "w" "clients") == some "1")
    let _ ← drain obs2.fd 500
    obs2.bye
    let _ ← waitFor 4000 (return (← e.status "w") != Status.wantsYou)
    expect ((← e.status "w") != Status.wantsYou)
        "watching marks the session seen (a read-only verb that writes)"
    let _ ← e.cli #["run", "watch-lost", "sleep", "600"]
    let lost ← e.spawn #["attach", "--read-only", "watch-lost"] 80 24
    let _ ← waitFor 4000 (return (← e.info "watch-lost" "clients") == some "1")
    let _ ← drain lost.fd 300
    unless (← e.crashDaemon "watch-lost") do
      throw (IO.userError "watch-lost daemon did not crash")
    let lostOut ← drainStr lost.fd 2000
    let lostCode ← lost.reap 3000
    expect (lostCode == 1 && has lostOut "connection lost")
        "read-only attach exits 1 when its daemon disappears"
    lost.bye (sendDetach := false)
    e.killAll #["w"]
    checkpointChecks e

end E2E.Watch
