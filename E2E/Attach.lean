module

public import E2E.Harness
public import Linger.Core.Session
public import Linger.Runtime.Daemon

public section

/-! # E2E.Attach — attach, detach, reattach, mirror, wait, hand-back, scrollback

Ported from `tests/attach_test.py`, the largest suite: the core session lifecycle
plus the two things a client owes the user's terminal on the way in and out.

WHAT THE PORT TIGHTENED — read before adding or changing a check:

* **the hand-back is compared against the emitter, not a copy of it.** The Python
  spelled twelve escape sequences as byte literals and asserted each appeared in
  the detach epilogue. Every one is now `Render.modeSet` / `csiNum` / `csiPlain` /
  `escSeq` / `escCharset` of the same argument `leaveAnsi` passes, so the loop
  cannot drift from what the implementation emits — and the ST check additionally
  requires `leaveAnsi` **verbatim** (`hasBytes back leaveAnsi`, the `E2E.Watch`
  move). The per-sequence loop is kept for failure localisation: green sequence
  lines plus a red `verbatim` line means the right sequences in the wrong order or
  spacing, which one whole-blob comparison could not tell you;
* `back.index(b'\x1b\\') == 0` **raised** `ValueError` when the ST was absent —
  the assertion crashed the suite instead of failing it, losing the `FAILURES:`
  verdict. `startsWithBytes` is total;
* the two burst budgets are `Session.outputChunk` and `Daemon.outbufCap`, not the
  literals `65536` and `4194304` the Python's own message spelled twice;
* the ED-2/ED-3 needles are `csiNum 2 0x4A` / `csiNum 3 0x4A` — `restoreBody`'s
  clean-slate clear and `scrollbackAnsi`'s ring-clear, the two emitters whose
  ORDER the check is about;
* the geometry is set **before** exec (`Env.spawn` → `spawnPty`), so the
  `pty.fork()`-then-`ioctl(TIOCSWINSZ)` race against the client's own startup
  `winsizeGet` is gone;
* check 2 was **vacuous**: `expect(wpid == pid or drain(fd, 1.0) is not None, …)`
  — a Python `bytes` is never `None`, so the disjunction was always true and the
  check could not fail. It is now the honest reading: the child was reaped.
  (AGENTS.md: a test that cannot fail is worthless.)

WHAT COULD NOT BE DERIVED: the printf'd full-screen-app state in check 10 is the
*application's* bytes, not linger's, so `modeSet 1049 true` and `csiNum2 5 10 0x72`
are used only as spellers for two standard sequences — that is not a tie to an
emitter, and it should not be read as one. -/

namespace E2E.Attach

open E2E.Harness
open Linger.Core.Render (leaveAnsi modeSet csiNum csiNum2 csiPlain escSeq escCharset titleAnsi)
open Linger.Core.Vt (Vt)
open Linger.Core.Session (outputChunk)
open Linger.Runtime.Daemon (outbufCap)

/-- Drive the actual effect interpreter with real sockets and counted checkpoint
hooks. Keeping the roster in this process prevents a reconnect from reusing the
closed fd and accidentally hiding a phantom attached client. -/
def closeFeedback (e : Env) : IO Nat := do
  let path := s!"{e.dir}/close-feedback.sock"
  let listener ← Linger.Posix.unixListen path
  let mut failures := 0
  try
    for exiting in [false, true] do
      let peer ← Linger.Posix.unixConnect path
      let accepted ← Linger.Posix.accept listener
      if peer < 0 || accepted < 0 then
        throw (IO.userError "close-feedback socket was not accepted")
      let fd := accepted.toUInt64.toUInt32
      let saved ← IO.mkRef (0 : Nat)
      let dropped ← IO.mkRef (0 : Nat)
      let st :=
        (Linger.Core.Session.run (.boot (Linger.Core.Vt.Vt.init 20 5) [] [])
            [.connected fd.toNat, .bytes fd.toNat (Linger.Core.Wire.encode (.attach 20 5)),
              .ptyOut "pending checkpoint".toUTF8.toList]).1
      let rt : Linger.Runtime.Daemon.Rt :=
        { st, listenFd := listener, ptyFd := 0, childPid := 0, conns := [{ fd }], sockPath := path,
          saveCkpt := fun _ => saved.modify (· + 1), dropCkpt := dropped.modify (· + 1) }
      try
        let events :=
          if exiting then [.childExited 0, .tick Linger.Core.Session.ckptIntervalMs]
          else [.bytes fd.toNat (Linger.Core.Wire.encode .detachAll)]
        let after ← Linger.Runtime.Daemon.pump rt events
        let clients := (Linger.Core.Session.infoFields after.st).lookup "clients"
        failures :=
          failures +
            (←
              if exiting then
                expect (after.exiting && (← saved.get) == 0 && (← dropped.get) == 1)
                    "child exit discards queued events without recreating its checkpoint"
              else
                expect (clients == some "0" && after.conns.isEmpty && (← saved.get) == 1)
                    "detach-all removes the size owner and checkpoints the last detach")
      finally
        Linger.Posix.close peer.toUInt64.toUInt32
  finally
    Linger.Posix.close listener
    IO.FS.removeFile path
  return failures

/-- The thirteen hazards `leaveAnsi` undoes, each spelled with the emitter's own
primitive and the same argument `leaveAnsi` passes it — so this list cannot become
a stale copy of the emitter. Every group must appear in the epilogue.

From `Render.leaveAnsi`'s docstring, which is where the *reasons* live: a shell
that inserts instead of overwriting, addresses relative to a stale region, does
not wrap or scrolls inside six lines (`4l`, `?6l`, `?7h`, `CSI r`); a cursor you
cannot see, pastes arriving wrapped in `ESC [ 200 ~`, clicks or focus changes
arriving as garbage on the command line (`?25h`, `?2004l`, the mouse modes,
`?1004l`); arrow and keypad keys sending application forms the line editor does
not bind (`?1l`, `ESC >`); line-drawing ASCII (`( B`, `) B`, `SI`); a coloured
prompt (`SGR 0`); the session's window title (empty `OSC 2 BEL`). termios restores
none of it — that is the kernel's line discipline, not the terminal's state. -/
def leaveCases : List (List (List UInt8) × String) :=
  [([modeSet 1049 false], "leaves the alt screen"), ([csiNum 4 0x6C], "clears insert mode"),
    ([modeSet 25 true], "shows the cursor"), ([modeSet 2004 false], "clears bracketed paste"),
    ([modeSet 1000 false, modeSet 1002 false, modeSet 1003 false, modeSet 1006 false],
      "clears mouse reporting"),
    ([modeSet 1004 false], "clears focus events"),
    ([modeSet 1 false, escSeq 0x3E], "restores normal cursor/keypad keys"),
    ([modeSet 6 false], "clears origin mode"), ([modeSet 7 true], "restores autowrap"),
    ([csiPlain 0x72], "restores the full scroll region"),
    ([escCharset 0x28 0x42, escCharset 0x29 0x42, [0x0F]], "restores the ASCII charset"),
    ([csiNum 0 0x6D], "resets the pen"), ([titleAnsi (Vt.init 1 1)], "clears the window title")]

/-- A full-screen application's opening sequences, as the shell's `printf` writes
them: alt screen, mouse reporting (1000 + SGR 1006), cursor hidden, bracketed
paste, autowrap off, a six-line scroll region, DEC line drawing, a bold red pen,
application cursor keys, application keypad, a nonempty title followed by a
truncated title. The unfinished title exceeds the mediator's candidate cap so
it reaches the client before detach. Literal `\033` for `printf` to interpret. -/
def appStateCmd : String :=
  "printf '\\033[?1049h\\033[?1000h\\033[?1006h\\033[?25l\\033[?2004h" ++
    "\\033[?7l\\033[5;10r\\033(0\\033[1;31;4m\\033[?1h\\033=X" ++
    "\\033]2;hostile-detach\\007\\033]2;truncated-detach" ++
    String.ofList (List.replicate Linger.Core.Terminal.oscCap 'x') ++
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

def run : IO UInt32 := do
  let e ← Env.make "attach"
  let mut f ← closeFeedback e
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
  IO.sleep 800
  c1.type "echo marker-$((21+21))\r"
  let out ← drain c1.fd 2000
  f := f + (← expect (hasText out "marker-42") "attach: command executes, output streams back")
  -- 2. ctrl-\ detaches; the client exits but the session lives.
  --
  -- The Python here was `wpid == pid or drain(fd, 1.0) is not None` — and a
  -- `bytes` is never `None`, so the right-hand side was always true and the check
  -- could not fail. This is what it meant to say: WNOHANG waitpid saw the child
  -- gone (`Client.reap` returns the status; `-1` is "still running").
  c1.detach
  IO.sleep 500
  let st1 ← c1.reap 1500
  f := f + (← expect (st1 ≥ 0) "detach: client exited on ctrl-backslash")
  c1.bye (sendDetach := false) -- fd and any zombie only; the client already left
  f := f + (← expect (has (← e.out #["list"]) "demo") "detach: session still listed")
  -- 3. background output while detached reaches the emulator (§Detach: a session
  -- with zero clients still advances)
  let _ ← e.cli #["send", "demo", "echo while-detached-$((40+2))\n"]
  IO.sleep 800
  f :=
    f +
      (←
        expect (has (← e.out #["history", "demo"]) "while-detached-42")
            "session advances while nobody attached")
  -- 4. reattach: restore shows the old screen contents
  let c2 ← e.spawn #["attach", "demo"] cols rows
  let out2 ← drain c2.fd 1500
  f :=
    f +
      (←
        expect (hasText out2 "marker-42" && hasText out2 "while-detached-42")
            "reattach: restore replays prior screen")
  -- 5. two clients mirror output
  let c3 ← e.spawn #["attach", "demo"] cols rows
  let out3 ← drain c3.fd 1000
  c2.type "printf '\\033]2;hostile-exit\\007'; echo both-$((2+1))\r"
  IO.sleep 800
  let o2 ← drain c2.fd 1000
  let o3 ← drain c3.fd 1000
  f := f + (← expect (hasText o2 "both-3" && hasText o3 "both-3") "two clients mirror the session")
  let receiver2 := (receiver.feed out2.toList).feed o2.toList
  let receiver3 := (receiver.feed out3.toList).feed o3.toList
  f :=
    f +
      (←
        expect
            (has receiver2.windowTitle "hostile-exit" && has receiver3.windowTitle "hostile-exit")
            "shell exit: both receivers hold the application's nonempty title")
  -- 6. exit inside the shell ends the session and notifies clients
  c2.type "exit\r"
  IO.sleep 1000
  f := f + (← expect (!has (← e.out #["list"]) "demo") "shell exit ends the session")
  let exit2 ← drain c2.fd 1000
  let exit3 ← drain c3.fd 500
  let handed2 := receiver2.feed exit2.toList
  let handed3 := receiver3.feed exit3.toList
  f :=
    f +
      (←
        expect
            (hasBytes exit2 emptyTitle && hasBytes exit3 emptyTitle &&
              handed2.windowTitle.isEmpty &&
              handed2.atBoundary &&
              handed3.windowTitle.isEmpty &&
              handed3.atBoundary)
            "shell exit clears the title on both attached terminals")
  c2.bye (sendDetach := false)
  c3.bye (sendDetach := false)
  -- 7. wait returns the exit status.
  --
  -- The first attempt is kept because the Python kept it, and its comment is the
  -- reason the second one is shaped the way it is: `run` spawns a shell and TYPES
  -- the command, so the shell itself does not exit with the command's status —
  -- `sh -c "sleep 0.3; exit 7"` runs as a child and the shell survives it. The
  -- command has to REPLACE the shell, hence `exec` in `w2`. (`run` types its argv
  -- space-joined, so the quoting inside the single argv element below is parsed by
  -- the session's own shell, exactly as in the Python.)
  let _ ← e.cli #["run", "w1", "sh -c \"sleep 0.3; exit 7\""]
  let _ ← e.cli #["kill", "w1"]
  IO.sleep 300
  let _ ← e.cli #["run", "w2", "exec sh -c \"sleep 0.5; exit 7\""]
  let t0 ← Linger.Posix.monotonicMs
  let (rc, _, _) ← e.cli #["wait", "w2"]
  let took := (← Linger.Posix.monotonicMs) - t0
  f :=
    f +
      (←
        expect (rc == 7 && took ≥ 200)
            s!"wait blocks until exit and returns status (rc={rc}, took={took}ms)")
  -- A transport loss is neither a detach nor a successful wait.
  let lost ← e.spawn #["attach", "attach-lost"] cols rows
  IO.sleep 800
  let lostInitial ← drain lost.fd 300
  -- Exceed the mediator's buffer so the unfinished OSC reaches the terminal;
  -- keep the child quiet afterwards so nothing completes it before handback.
  lost.type
      ("printf '\\033]2;hostile-lost\\007\\033]2;truncated-lost" ++
        String.ofList (List.replicate Linger.Core.Terminal.oscCap 'x') ++
        "'; exec sleep 600\r")
  let lostDirty ← drain lost.fd 800
  let lostReceiver := (receiver.feed lostInitial.toList).feed lostDirty.toList
  f :=
    f +
      (←
        expect (has lostReceiver.windowTitle "hostile-lost" && !lostReceiver.atBoundary)
            "connection loss: the receiver holds a nonempty title before a truncated OSC")
  unless (← e.crashDaemon "attach-lost") do
    throw (IO.userError "attach-lost daemon did not crash")
  let lostBytes ← drain lost.fd 2000
  let lostHanded := lostReceiver.feed lostBytes.toList
  let lostOut := String.fromUTF8? lostBytes |>.getD ""
  let lostCode ← lost.reap 3000
  f :=
    f +
      (←
        expect (lostCode == 1 && has lostOut "connection lost")
            "attach exits 1 when its daemon disappears")
  f :=
    f +
      (←
        expect
            (hasBytes lostBytes emptyTitle && lostHanded.windowTitle.isEmpty &&
              lostHanded.atBoundary)
            "connection loss clears the title after a truncated OSC")
  lost.bye (sendDetach := false)
  let _ ← e.cli #["run", "wait-lost", "sleep", "600"]
  IO.sleep 800
  let waiter ←
    IO.Process.spawn
        { cmd := e.bin, args := #["wait", "wait-lost"], env := e.procEnv, stdout := .null,
          stderr := .piped }
  IO.sleep 800
  unless (← e.crashDaemon "wait-lost") do
    throw (IO.userError "wait-lost daemon did not crash")
  let waitCode ← waitProcess waiter 3000
  if waitCode.isNone then
    waiter.kill
    let _ ← waiter.wait
  let waitErr ← waiter.stderr.readToEnd
  f :=
    f +
      (←
        expect (waitCode == some 1 && has waitErr "connection lost")
            "wait exits 1 when the daemon disappears")
  -- 8. bare `attach` (no name) attaches the shared `Name.defaultName` session.
  let m ← e.spawn #["attach"] cols rows
  IO.sleep 800
  f :=
    f +
      (←
        expect (has (← e.out #["list"]) "main")
            "bare `attach` creates the default session \"main\"")
  m.detach
  IO.sleep 400
  m.bye (sendDetach := false)
  e.killAll #["main"]
  -- 9. detach hands the terminal back (`Render.leaveAnsi`). A full-screen app's
  --    opening sequences are set from inside the session; after ctrl-\ the client
  --    must undo every one of them, or the user's shell is left on the alt screen
  --    with mouse reporting on, no cursor, a six-line scroll region and every
  --    ASCII character rendered as a box glyph. termios restores none of this.
  let h ← e.spawn #["attach", "hyg"] cols rows
  IO.sleep 800
  let initial ← drain h.fd 300
  h.type appStateCmd
  IO.sleep 600
  let dirty ← drain h.fd 800
  -- non-vacuity for the checks below: the app state really got out to the
  -- client's terminal, so there is something to undo. These two needles are the
  -- APPLICATION's bytes — `modeSet`/`csiNum2` are used here only to spell two
  -- standard sequences, not as a tie to an emitter.
  f :=
    f +
      (←
        expect (hasBytes dirty (modeSet 1049 true) && hasBytes dirty (csiNum2 5 10 0x72))
            "hygiene: the app state really reached the client terminal")
  let dirtyReceiver := (receiver.feed initial.toList).feed dirty.toList
  f :=
    f +
      (←
        expect
            (dirtyReceiver.inAlt && has dirtyReceiver.windowTitle "hostile-detach" &&
              !dirtyReceiver.atBoundary)
            "detach: the alternate-screen receiver holds a nonempty title before a truncated OSC")
  h.detach
  let back ← drain h.fd 1500
  let handedBack := dirtyReceiver.feed back.toList
  for (seqs, what) in leaveCases do
    f := f + (← expect (seqs.all (fun s => hasBytes back s)) ("detach " ++ what))
  f :=
    f +
      (←
        expect (!handedBack.inAlt && handedBack.windowTitle.isEmpty && handedBack.atBoundary)
            "detach clears the title after neutralizing a truncated OSC")
  -- ST first, and the whole constant verbatim. The leading `ESC \` is not
  -- decoration: a program that died mid-OSC/DCS (a crashed sixel writer, a
  -- truncated title) leaves the receiver's parser in a string state that would
  -- swallow this entire stream, exactly as it swallowed `restore` before cd7c17b.
  -- The `hasBytes … leaveAnsi` conjunct is the port's addition: the groups
  -- above can all be present in the wrong order or with bytes wedged between
  -- them, and `leave_canonical_all` proves the CONTENTS while no theorem can see
  -- that the client actually writes them.
  f :=
    f +
      (←
        expect (startsWithBytes back (escSeq 0x5C) && hasBytes back leaveAnsi)
            "detach leads with ST (a program that died mid-OSC/DCS would eat the rest)")
  h.bye (sendDetach := false)
  e.killAll #["hyg"]
  -- If the hand-back write fails, termios restoration must still run. Command-local
  -- stdout closure leaves the shell's stdin attached to the pty and makes the
  -- first cleanup action fail deterministically.
  let _ ← e.cli #["run", "raw-cleanup", "sleep", "600"]
  IO.sleep 800
  let modesPath := s!"{e.dir}/raw-cleanup.modes"
  let cleanupScript :=
    s!"before=$(stty -g); {e.bin} attach raw-cleanup 1>&- 2>/dev/null || true; \
       after=$(stty -g); printf '%s\\n%s\\n' \"$before\" \"$after\" > {modesPath}"
  let (rawPid, rawFd) ← Linger.Posix.spawnPty cols rows "" "sh" #["-c", cleanupScript] e.ptyEnv
  let rawProbe : Client := { pid := rawPid, fd := rawFd }
  let modesReady ← waitFor 5000 (System.FilePath.pathExists modesPath)
  let modes ←
    if modesReady then
      pure ((← IO.FS.readFile modesPath).splitOn "\n")
    else
      pure []
  f :=
    f +
      (←
        expect
            (match modes with
            | before :: after :: _ => !before.isEmpty && before == after
            | _ => false)
            "attach restores tty mode even when leaveAnsi cannot be written")
  rawProbe.bye (sendDetach := false)
  e.killAll #["raw-cleanup"]
  -- 10. LINGER_NO_DETACH_KEY=1 disables the ctrl-\ detach key (README promise, and
  --     the mirror of check 2). With the env var set, ctrl-\ is ordinary input: the
  --     client stays attached and the byte reaches the session's pty.
  --
  -- `Env.spawn` cannot carry a third env entry, so this one goes through
  -- `spawnPty` directly with `e.ptyEnv` extended — the same call `Env.spawn`
  -- makes, and still with the winsize set before exec.
  let (ndPid, ndFd) ←
    Linger.Posix.spawnPty cols rows "" e.bin #["attach", "nd"]
        (e.ptyEnv.push "LINGER_NO_DETACH_KEY=1")
  let nd : Client := { pid := ndPid, fd := ndFd }
  IO.sleep 800
  let _ ← drain nd.fd 300
  nd.detach -- would detach if the key were enabled
  IO.sleep 500
  -- `-1` from WNOHANG waitpid is "still running", which is Python's `wpid == 0`
  f :=
    f +
      (←
        expect ((← Linger.Posix.waitpidNohang nd.pid) == -1)
            "LINGER_NO_DETACH_KEY: ctrl-\\ does not detach (client still attached)")
  f := f + (← expect (has (← e.out #["list"]) "nd") "LINGER_NO_DETACH_KEY: session still live")
  nd.type "echo nd-$((20+2))\r" -- still interactive: input reaches the pty
  IO.sleep 600
  f :=
    f +
      (←
        expect (has (← e.out #["history", "nd"]) "nd-22")
            "LINGER_NO_DETACH_KEY: input still reaches the session")
  e.killAll #["nd"]
  IO.sleep 400
  nd.bye (sendDetach := false)
  -- 11. the scrollback reaches the client's own scrollback
  --     (specs/archive/scrollback-fidelity.md). `restore` used to repaint the screen and
  --     drop everything above it. It now paints the session's ring first and
  --     scrolls it off, so the reattach burst carries lines that are no longer on
  --     the screen at all — and the client's wheel-scroll, search and selection
  --     find them. The `ED 3` that stops a second attach stacking a second copy is
  --     emitted AFTER the `ED 2` (the order ncurses `clear(1)` sends), because
  --     `restoreBody` already clears before `screensAnsi`.
  let s1 ← e.spawn #["attach", "sb"] cols rows
  IO.sleep 800
  let _ ← drain s1.fd 300
  s1.type "i=1; while [ $i -le 60 ]; do echo sbline-$i; i=$((i+1)); done\r"
  IO.sleep 1200
  let _ ← drain s1.fd 1200
  -- exact-line membership, not substring: the typed line the tty echoed back
  -- contains `sbline-$i`, and only the shell's output lines are the markers
  -- themselves. That is what Python's `x in <list of lines>` meant, and `has`
  -- would have weakened it.
  let histS := lines (← e.out #["history", "sb"])
  f :=
    f +
      (←
        expect
            (histS.contains "sbline-1" &&
              !(histS.drop (histS.length - rows.toNat)).contains "sbline-1")
            "scrollback: the early lines are in the ring, off the 24-row screen")
  s1.detach
  IO.sleep 600
  s1.bye (sendDetach := false)
  let s2 ← e.spawn #["attach", "sb"] cols rows
  let burst ← drain s2.fd 2000
  f :=
    f +
      (←
        expect ((findText burst "sbline-1").isSome)
            "scrollback: a line that scrolled off the screen is replayed on reattach")
  f :=
    f +
      (←
        expect ((findText burst "sbline-60").isSome) "scrollback: the screen is still replayed too")
  -- ED 2 is `restoreBody`'s clean slate, ED 3 is `scrollbackAnsi`'s ring clear:
  -- the needles are those two emitters, so the check is about the ORDER of the
  -- implementation's own writes and not about two byte literals.
  let i2 := findBytes burst (csiNum 2 0x4A)
  let i3 := findBytes burst (csiNum 3 0x4A)
  let edOk :=
    match i2, i3 with
    | some a, some b => a < b
    | _, _ => false
  f :=
    f +
      (←
        expect edOk
            s!"scrollback: ED 3 present and after ED 2 (2J at {idxStr i2}, 3J at {idxStr i3})")
  f :=
    f +
      (←
        expect (burst.size < outputChunk)
            s!"scrollback: the reattach burst fits one outputChunk ({burst.size} bytes, \
       cap {outputChunk}; outbufCap is {outbufCap} and disconnects)")
  s2.type "echo alive-$((20+22))\r"
  IO.sleep 800
  f :=
    f +
      (←
        expect (hasText (← drain s2.fd 1200) "alive-42")
            "scrollback: the client survives the burst and is still interactive")
  --     …and again with a ring of per-cell truecolour rows, which is the shape
  --     whose bytes the budget exists for: ~40 B per column instead of one.
  let tc := s!"{e.dir}/tc.sh"
  IO.FS.writeFile tc tcScript
  s2.type s!"sh {tc}\r"
  IO.sleep 2500
  let _ ← drain s2.fd 1500
  s2.detach
  IO.sleep 600
  s2.bye (sendDetach := false)
  let s3 ← e.spawn #["attach", "sb"] cols rows
  let burstTc ← drain s3.fd 2500
  f :=
    f +
      (←
        expect ((findText burstTc "tcline-1").isSome)
            "scrollback: a truecolour line that scrolled off is replayed too")
  f :=
    f +
      (←
        expect (burstTc.size < outbufCap)
            s!"scrollback: the truecolour burst stays under outbufCap \
       ({burstTc.size} bytes, cap {outbufCap})")
  s3.type "echo tc-alive-$((21+21))\r"
  IO.sleep 1000
  f :=
    f +
      (←
        expect (hasText (← drain s3.fd 1500) "tc-alive-42")
            "scrollback: the client survives the truecolour burst")
  s3.bye (sendDetach := false)
  e.killAll #["sb", "w2"]
  verdict e f

end E2E.Attach
