"""`linger watch` — the read-only mirror (abduco's `-r`), end to end.

pin-the-gaps item 1. Before this suite the verb had ZERO coverage of any kind:
no pty test, no fixture, no theorem naming it. `e2e.sh` step 4's "mirror" is
two-client mirroring (`attach_test.py` step 5), not this.

WHAT THIS CAN AND CANNOT CATCH — read before adding an assertion. Read-only is
enforced DAEMON-side, not by `Client.attach`'s three `!readOnly` guards:

  * guard A, `sendMsg fd (.attach 0 0)` — the 0x0 geometry IS the read-only
    marker on the wire. `onMsg .attach` derives `sizer := cols != 0 && rows != 0`
    from it, and everything else follows. Removing A is observable three
    independent ways; break-verified, assertions 3, 5 and 7 below each catch it.
  * guard B, resize suppression, and guard C, keystroke suppression — BOTH are
    semantic no-ops. `onMsg .resize` drops a non-sizer's resize and `onMsg .input`
    drops a non-sizer's input (`onMsg_input_readonly`), so removing either guard
    changes no observable byte. They are defence in depth, and `e2e.sh` carries a
    grep gate for each — the `SHIM_CAP` idiom, because a source-tree property
    cannot be a theorem and must not be faked as a pty assertion.

So: do not add an assertion here claiming to catch B or C. It cannot.
"""
import os
import sys
import time

from harness import bye, cli, drain, expect, make_env, resize, spawn

LDIR, ENV = make_env('watch')
linger, info, field = cli(ENV)

fails = 0

# ── 1. a watcher cannot conjure a session (attach is an upsert; watch is not) ──
r = linger('watch', 'nosuch')
fails += expect(r.returncode == 1, 'watch of a missing session exits 1')
fails += expect(b"no session 'nosuch'" in r.stderr,
                'watch of a missing session says so on stderr')
fails += expect('nosuch' not in linger('ls').stdout.decode(),
                'watch created no session (it is not an upsert)')

# ── the session under test: one real client at 80x24 ──────────────────────────
pid_r, fd_r = spawn(ENV, ['attach', 'w'], rows=24, cols=80)
time.sleep(1.5)
drain(fd_r, 0.5)
fails += expect(info('w').get('cols') == '80', 'session starts 80 wide')

# ── 2. the watcher attaches, at a DIFFERENT geometry ─────────────────────────
pid_w, fd_w = spawn(ENV, ['watch', 'w'], rows=30, cols=100)
time.sleep(1.5)
drain(fd_w, 1.0)          # swallow the restore burst so it cannot satisfy #4

fails += expect(info('w').get('clients') == '2',
                'the watcher counts as a client (so it really is attached)')

# ── 3. …and never owns the geometry ──────────────────────────────────────────
g = info('w')
fails += expect(g.get('cols') == '80' and g.get('rows') == '24',
                'a 100x30 watcher does not resize the session (guard A)')

# ── 4. keystrokes at the watcher never reach the pty ─────────────────────────
# Assert on the EXPANSION, not the typed text: if input were forwarded the shell
# would both echo and run it, and the arithmetic result is the discriminating
# string (the same argument as agent_test.py's send assertions).
os.write(fd_w, b'echo wmark-$((21+21))\r')
time.sleep(1.2)
fails += expect('wmark-42' not in linger('capture', 'w').stdout.decode(),
                "the watcher's keyboard does not reach the pty (guard A)")

# ── 5. non-vacuity for #4: the watcher really is receiving output ────────────
os.write(fd_r, b'echo mirror-$((20+22))\r')
time.sleep(1.0)
fails += expect(b'mirror-42' in drain(fd_w, 1.5),
                'the watcher mirrors the session output')

# ── 6. resizing the watcher's own terminal moves nothing ─────────────────────
# The only way to make guard B's code path execute at all: `lastSize` is seeded
# with the real size, so nothing is sent until the terminal actually changes.
resize(fd_w, 40, 120)
time.sleep(0.8)
fails += expect(info('w').get('cols') == '80',
                "resizing the watcher's terminal does not resize the session")

# ── 7. a watcher is not the size owner, so `linger resize` still applies ─────
# Detach the real client, leaving ONLY the watcher. With guard A intact
# `sizeOwner` is none and controlResize applies; with A removed the watcher owns
# the size and this comes back rc 1 with "owns the size" — the inverse of
# agent_test.py's refusal assertion, and it fails loudly in the other direction.
bye(pid_r, fd_r)
time.sleep(0.5)
fails += expect(info('w').get('clients') == '1', 'only the watcher is left')
rz = linger('resize', 'w', '90', '25')
fails += expect(rz.returncode == 0 and info('w').get('cols') == '90',
                'a watcher does not own the size, so `linger resize` applies')

# ── 8. ctrl-\ detaches a watcher, through the shared hand-back ───────────────
# Drain first: step 7's resize made the shell redraw, and that output sits ahead
# of the epilogue in the pty buffer — `index(...) == 0` is about what the CLIENT
# writes on its way out, so the buffer has to be empty when it starts.
drain(fd_w, 0.8)
os.write(fd_w, b'\x1c')
back = drain(fd_w, 2.0)
fails += expect(b'stopped watching' in back, 'ctrl-\\ detaches the watcher')
fails += expect(back.index(b'\x1b\\') == 0,
                'a watcher hands the terminal back too (leaveAnsi leads with ST)')
fails += expect(b'\x1b[?1049l' in back and b'\x1b[0m' in back,
                'the watcher runs the full leaveAnsi epilogue')
bye(pid_w, fd_w, send_detach=False)
fails += expect('w' in linger('ls').stdout.decode(),
                'the session survives the watcher leaving')

# ── 9. watching marks the session SEEN — a read-only verb with a write effect ─
# `onMsg .attach` sets `lookSeq := s.outSeq` for ANY attach, 0x0 included
# (Session.lean), so `linger watch` clears `wants-you`. status_test.py only ever
# exercised that through `attach`; this is the one place the read-only verb is
# not read-only, and it was unpinned.
linger('send', 'w', 'echo unread-marker\n')
time.sleep(1.2)
fails += expect(field('w', 'status') == 'wants-you',
                'output with nobody watching reads wants-you')
pid_w2, fd_w2 = spawn(ENV, ['watch', 'w'], rows=24, cols=80)
time.sleep(1.5)
drain(fd_w2, 0.5)
bye(pid_w2, fd_w2)
time.sleep(0.5)
fails += expect(field('w', 'status') != 'wants-you',
                'watching marks the session seen (a read-only verb that writes)')

linger('kill', 'w')
print('FAILURES:', fails)
sys.exit(1 if fails else 0)
