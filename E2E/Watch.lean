module

public import E2E.Harness

public section

/-! # E2E.Watch — `linger watch`, the read-only mirror

pin-the-gaps item 1. The verb had ZERO coverage of any kind before this suite:
no pty test, no fixture, no theorem naming it. `tests/e2e.sh` step 4's "mirror" is
two-client mirroring, not this.

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
  `tests/gates.sh` — the `SHIM_CAP` species of oracle.

So: do not add a check here claiming to catch B or C. It cannot. -/

namespace E2E.Watch

open E2E.Harness
open Linger.Core.Status (Status)

def run : IO UInt32 := do
  let e ← Env.make "watch"
  let mut f := 0
  -- 1. a watcher cannot conjure a session (attach is an upsert; watch is not)
  let (rc, _, err) ← e.cli #["watch", "nosuch"]
  f := f + (← expect (rc == 1) "watch of a missing session exits 1")
  f := f + (← expect (has err "no session 'nosuch'") "watch of a missing session says so on stderr")
  f :=
    f +
      (← expect (!has (← e.out #["ls"]) "nosuch") "watch created no session (it is not an upsert)")
  -- the session under test: one real client at 80x24
  let real ← e.spawn #["attach", "w"] 80 24
  IO.sleep 1500
  let _ ← drain real.fd 500
  f := f + (← expect ((← e.info "w" "cols") == some "80") "session starts 80 wide")
  -- 2. the watcher attaches, at a DIFFERENT geometry
  let obs ← e.spawn #["watch", "w"] 100 30
  IO.sleep 1500
  let _ ← drain obs.fd 1000 -- swallow the restore burst
  f :=
    f +
      (←
        expect ((← e.info "w" "clients") == some "2")
            "the watcher counts as a client (so it really is attached)")
  -- 3. …and never owns the geometry
  f :=
    f +
      (←
        expect ((← e.info "w" "cols") == some "80" && (← e.info "w" "rows") == some "24")
            "a 100x30 watcher does not resize the session (guard A)")
  -- 4. keystrokes at the watcher never reach the pty. Assert on the EXPANSION,
  -- not the typed text: if input were forwarded the shell would both echo and
  -- run it, and the arithmetic result is the discriminating string.
  obs.type "echo wmark-$((21+21))\r"
  IO.sleep 1200
  f :=
    f +
      (←
        expect (!has (← e.out #["capture", "w"]) "wmark-42")
            "the watcher's keyboard does not reach the pty (guard A)")
  -- 5. non-vacuity for 4: the watcher really is receiving output
  real.type "echo mirror-$((20+22))\r"
  IO.sleep 1000
  f :=
    f +
      (← expect (has (← drainStr obs.fd 1500) "mirror-42") "the watcher mirrors the session output")
  -- 6. resizing the watcher's own terminal moves nothing. The only way to make
  -- guard B's code path execute at all: `lastSize` is seeded with the real size,
  -- so nothing is sent until the terminal actually changes.
  obs.resize 120 40
  IO.sleep 800
  f :=
    f +
      (←
        expect ((← e.info "w" "cols") == some "80")
            "resizing the watcher's terminal does not resize the session")
  -- 7/8. a watcher is not the size owner, so `linger resize` still applies.
  -- With guard A intact `sizeOwner` is none and controlResize applies; with A
  -- removed the watcher owns the size and this returns 1 with "owns the size".
  real.bye
  IO.sleep 500
  f := f + (← expect ((← e.info "w" "clients") == some "1") "only the watcher is left")
  let (rzc, _, _) ← e.cli #["resize", "w", "90", "25"]
  f :=
    f +
      (←
        expect (rzc == 0 && (← e.info "w" "cols") == some "90")
            "a watcher does not own the size, so `linger resize` applies")
  -- 9. ctrl-\ detaches a watcher, through the shared hand-back. Drain first:
  -- the resize made the shell redraw, and that output sits ahead of the
  -- epilogue — the leading-ST check is about what the CLIENT writes on its way
  -- out, so the buffer has to be empty when it starts.
  let _ ← drain obs.fd 800
  obs.detach
  let back ← drain obs.fd 2000
  let backStr := String.fromUTF8? back |>.getD ""
  f := f + (← expect (has backStr "stopped watching") "ctrl-\\ detaches the watcher")
  -- Compared against the session's OWN emitter rather than a hardcoded byte
  -- string, so the suite cannot drift from what the implementation hands back.
  -- `leave_canonical_all` is what proves the contents; this is that the client
  -- actually writes them, which no theorem can see.
  let leave := Linger.Core.Render.leaveAnsi
  f :=
    f +
      (←
        expect (startsWithBytes back (leave.take 2))
            "a watcher hands the terminal back too (leaveAnsi's leading ST)")
  f := f + (← expect (hasBytes back leave) "the watcher writes leaveAnsi verbatim, byte for byte")
  obs.bye (sendDetach := false)
  f := f + (← expect (has (← e.out #["ls"]) "w") "the session survives the watcher leaving")
  -- 10. watching marks the session SEEN — a read-only verb with a write effect.
  -- `onMsg .attach` sets `lookSeq := s.outSeq` for ANY attach, 0x0 included, so
  -- `linger watch` clears `wants-you`. The status suite only ever exercised that
  -- through `attach`. Compared as a `Status`, not a string literal.
  let _ ← e.cli #["send", "w", "echo unread-marker\n"]
  IO.sleep 1200
  f :=
    f +
      (← expect ((← e.status "w") == Status.wantsYou) "output with nobody watching reads wants-you")
  let obs2 ← e.spawn #["watch", "w"] 80 24
  IO.sleep 1500
  let _ ← drain obs2.fd 500
  obs2.bye
  IO.sleep 500
  f :=
    f +
      (←
        expect ((← e.status "w") != Status.wantsYou)
            "watching marks the session seen (a read-only verb that writes)")
  e.killAll #["w"]
  verdict f

end E2E.Watch
