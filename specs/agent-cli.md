# agent-cli — one-shot verbs so another agent can see and drive a session

Status: active
Updated: 2026-08-19

## Where this stands — read this first

**Next step: Step 1.** Nothing implemented yet.

- Step 1 → info fields (`cols rows cursorx cursory alt outseq`) + `linger info <name>`
- Step 2 → `linger capture <name>` (wire tag 16, `Render.screenText`, marks seen)
- Step 3 → `linger send <name> -` (raw stdin bytes)
- Step 4 → `linger resize <name> <cols> <rows>` (control resize, never fights a live user)

## Goal

linger already has the tmux-style control plane: per-session socket, framed
protocol (§Frame makes unknown tags safe data), and one-shot verbs (`run`,
`send`, `history`, `wait`, `ls --porcelain`, labels). An agent can drive a
session today, but it cannot cheaply *see* it: there is no screen-only dump, no
geometry (`info` reports neither `cols` nor `rows`, so even `history | tail`
can't isolate the screen), no cursor, no change cursor, no raw byte input, and
no way to set the size of a detached session so wrap is deterministic.

Four additions close that, all as one-shot verbs against the existing protocol.
No persistent control stream (tmux `-CC`) and no JSON: the proven `k\tv`
porcelain is the house format.

The agent loop this enables:

    linger run work 'make test'          # upsert + run
    linger resize work 120 40            # deterministic wrap (no user attached)
    linger info work                     # cols/rows/cursor/alt/outseq/exit…
    linger capture work                  # the screen, one line per row
    printf 'y\n' | linger send work -    # exact bytes (Enter, ^C, escapes)
    …poll: capture again when `outseq` moved; `linger wait work` for exit

## Decisions (made, with reasons — don't re-litigate silently)

1. **Capture counts as a look; `history` stays an export.** `lookSeq` is a
   session-level "last looked" mark (deliberately not per-viewer), and a capture
   delivers the very content `unseen` is about — after one, "output arrived
   while nobody was watching" is false. `watch` (a 0×0 observer attach) already
   marks seen, so a read-only viewer counting as a viewer is precedent, and
   `behind` becomes exactly "output events since my capture", which is the
   change cursor an agent wants. `.info` must NOT mark seen (`ls` polls every
   live daemon; a listing that cleared every unread flag would destroy the
   status column), and `history` is kept an export (transcript for a file, not
   an observation) — the line is: verbs that show you the *current screen*
   mark seen, verbs that report *about* the session don't.
2. **Geometry rides `info`, not the capture reply.** A `k\tv` header frame
   inside the capture stream would interleave with the screen bytes on stdout
   (`drainReplies` writes both). Capture stays "screen text only" (same UX as
   `history`); cursor/size/alt come from `info` — racy across two calls, which
   an agent handles by checking `outseq` didn't move between them.
3. **Control resize applies iff no attached sizer exists.** The abduco rule
   ("never fight the active user's size") extends, it doesn't bend: an attached
   sizer always wins; with none attached there is nobody to fight, and the
   detached session gets the size an agent asks for. Same-size is a no-op
   (`.done` without touching the emulator) for the same reason attach guards it:
   `Vt.resize` resets DECSTBM and the tab ruler unconditionally, and no SIGWINCH
   nudges the child to re-establish them at an unchanged winsize
   (restore-conformance Step 0 ledger 1).
4. **New one-shot verbs must own a reply deadline.** A pre-upgrade daemon —
   linger's whole point is that daemons outlive upgrades — drops tag 16 without
   a trace (§Frame) and replies nothing to a control `.resize`; `oneShot`'s
   `poll … (-1)` would hang forever. New verbs drain with a ~2 s *silence*
   timeout (the `queryInfo` pattern) and report "no reply (daemon predates this
   command?)". `wait` keeps the untimed path: waiting arbitrarily long is its
   job.
5. **Raw input is stdin (`send <name> -`), not named keys.** Named keys done
   right are mode-dependent (DECCKM decides `CSI A` vs `SS3 A`) and belong in
   the daemon next to the modes, if ever. Raw bytes are unambiguous, compose
   with `printf`, and cover Enter/^C/ESC/arrows today. `-` is the argv literal;
   `linger send foo - x` stays an error (usage), not a mixed mode.

## Definition of done

1. `Session.infoFields` additionally reports `cols`, `rows`, `cursorx`,
   `cursory`, `alt` (`true` iff the alt screen is live), `outseq`. They flow
   through `rowFields` into `ls --porcelain` unchanged (it only strips `name`),
   and the human listing ignores them (`humanRow` reads named keys only).
   `infoText_framing` / `infoText_records` hold as stated (they quantify over
   the field list — if either needs a new hypothesis, the change is wrong).
2. `linger info <name>` prints the raw `k\tv` records for one session (no
   30-daemon fan-out just to read one cursor), through the bounded drain.
3. New wire message `.screen`, tag 16, empty payload; `knownTag` becomes
   `t ≤ 16`; round-trip and payload-bound theorems extended (`ne 16` in the
   `unknown` case; a `t = 16` branch in `decodeMsg_payload_le`). Tags are
   frozen-append: 16 is `.screen` forever.
4. `Render.screenText v` — the grid only, `rowText`-per-row, LF-terminated,
   plain text (the exact shape of `history`'s plain branch minus the ring).
   Theorems `screenText_framing` and `screenText_lines` (every byte a line
   terminator or printable; newline count = grid row count — a cell cannot
   forge a line), and a `tests/coverage.py` EMITTERS entry naming them. The
   ANSI variant is deliberately NOT wired (scrollback-fidelity owns the colored
   ladder; plain text is what an agent parses).
5. `.screen` in `onMsg`: replies `outputMsgs (Render.screenText s.vt) ++
   [.done]` and sets `lookSeq := s.outSeq`. Theorems: the exact shape (`rfl`,
   which also claims `screenText` in a statement), `unseen` is false
   afterwards, and vt/labels untouched. `linger capture <name>` = send tag 16,
   bounded drain to stdout.
6. `send <name> -`: poll+read stdin until EOF, each chunk (≤ 64 KiB reads) one
   `.input` frame on a single connection. Binary-safe; empty stdin sends
   nothing and exits 0.
7. Control `.resize` (from a non-attached client): refused with `.err` while an
   attached sizer exists; `.done` (emulator untouched) at the current size;
   otherwise `Vt.resize` + `.resizePty` + `.done`. Attached-client semantics
   byte-identical to today. Theorem: a control resize never emits `.resizePty`
   while an attached sizer exists (the abduco rule as a statement, extended).
   `linger resize <name> <cols> <rows>` validates 1..1000 (`clampDim`'s range)
   client-side.
8. Usage text names the four verbs; README gains an "Agents" note (the loop
   above, and that capture marks the session seen).
9. Unit fixtures (`Tests/Wire.lean`, `Tests/Session.lean`, `Tests/Render.lean`)
   for the new tag, the new arms (capture reply shape, marks-seen, resize
   refusal/apply/same-size), and `screenText`. A new `tests/agent_test.py`
   e2e suite (12) covering: info fields present and sane; capture returns the
   screen and marks seen (porcelain `unseen` flips); `send -` delivers exact
   bytes (^C interrupts a child); resize applies detached, is refused while a
   sizer is attached, and `capture` reflects the new width; a stale-daemon
   *shape* check is impossible cheaply, so the bounded drain is at least
   exercised by the refusal path replying promptly.
10. Ratchets: `SHIM_CAP=27` unchanged (nothing here needs a syscall);
    `HEARTBEAT_CAP=1` unchanged; `RUNTIME_PARTIAL_CAP=2` unchanged (the new
    loops are `while` in `do`); `coverage.py` — new defs arrive claimed
    (`screenText` via its theorems; no other new Core def without a statement
    naming it), cap stays ≤ 19 or tightens.
11. Every new theorem and fixture break-verified once, breaks recorded in
    `SCRATCHPAD.md` (which claims catch a wrong `lookSeq`, a forged line, a
    sizer-overriding resize, a dropped `.done`).
12. `./lake build`, `./lake build Theorems Tests`, `./tests/e2e.sh` green and
    warning-free at every step's commit.

## Steps

### Step 1 — geometry + change cursor in `info`, and a per-session `info` verb

Status: pending.

`Session.infoFields`: append the six pairs after `behind`. `Cli`: `info`/`i`
verb through the bounded drain (introduced here, in `Client`); usage line.
Fixtures pin the new keys' presence and values against a hand-built `State`.
e2e: `tests/agent_test.py` asserts `cols`/`rows` match the spawn size and
`outseq` increases after output.

**Exit:** gates green; porcelain shows the new keys; `linger info` prints one
session's records; fixtures pin `alt` flipping with the alt screen and `outseq`
tracking `.ptyOut` count.

### Step 2 — `capture`

Status: pending (needs Step 1's bounded drain).

Wire tag 16 + theorem cases; `Render.screenText` + the two theorems +
coverage.py entry; the `onMsg` arm (reply + `lookSeq`); `capture`/`c` verb.
Break-verify: make `screenText` also paint the ring → `screenText_lines`'s
fixture and the e2e screen-only assertion fail; drop the `lookSeq` write → the
marks-seen theorem and the porcelain-flip e2e fail; reply without `.done` → the
bounded drain reports no-reply (e2e).

**Exit:** gates green; `linger capture` on a session whose scrollback differs
from its screen returns exactly the screen (`rows` lines); `unseen` flips to
`false` in the porcelain after a capture; old-daemon hang is impossible by
construction (silence deadline, exercised in unit form).

### Step 3 — `send -`

Status: pending.

`Cli`: the `["-"]` case of `send` reads stdin (poll 200 ms rounds so EOF and
would-block are distinguished — `read` returns `none` at EOF, `some #[]` when
it would block) and sends each chunk as one `.input`. No protocol change, no
daemon change.

**Exit:** gates green; e2e pipes `printf 'echo BOUND\n'` and sees `BOUND` in a
capture; pipes a lone `\x03` at a `sleep 100` child and observes the interrupt
(child exit surfaces via `wait`); `printf ''` exits 0 and delivers nothing.

### Step 4 — control `resize`

Status: pending.

`Session.onMsg` `.resize` arm restructured (attached path byte-identical;
control path per Decision 3, with `.err`/`.done` replies); theorem
`resize_control_never_overrides` (+ the exact-shape `rfl`s); `resize` verb with
1..1000 validation; fixtures for all three control branches.
Break-verify: drop the sizer guard → the theorem fails; drop the same-size
guard → the fixture pinning "emulator untouched at same size" fails (the
DECSTBM/tab-ruler wipe, caught structurally).

**Exit:** gates green; e2e: resize a detached session, capture shows the new
width (child redrew via SIGWINCH), `info` agrees; attach a pty client, control
resize is refused with a message and exit 1; detach, it applies again.

## Non-goals (this spec)

- **A persistent control stream / control mode.** One-shot verbs + `outseq`
  polling cover the loop; a long-lived stream adds an unbounded bidirectional
  surface for no capability an agent lacks.
- **Named keys.** Mode-dependent; revisit as a daemon-side `.key` tag only if
  raw bytes prove insufficient in practice.
- **Colored capture (`-e`).** `history`'s `withAnsi` branch exists but stays
  CLI-dead pending scrollback-fidelity; an agent parses plain text.
- **Atomic screen+geometry.** Two calls + `outseq` equality check; a combined
  reply tag can come later without breaking anything (frozen-append).
- **Auth beyond the socket.** Same-user processes already hold full authority
  over the socket dir; different-user access is out of scope.

## Interaction with live specs

`specs/scrollback-fidelity.md` Step 2 is pending and owns `Render`'s emitter
ladder. `screenText` is additive (a new named stage over `rowText`; zero bytes
change in `restore`/`history`), so the flagship screen statements must be
byte-identical before/after Step 2 here — same exit criterion the scrollback
spec used for its Step 1.
