# pin-the-gaps — close the nine holes the 2026-08-29 coverage audit found

Status: **complete (2026-08-29)** — archived record, do not edit
Predecessors: `specs/lean-modules.md` (Steps 0–2, 5 done; 3–4 optional),
`specs/scrollback-fidelity.md` (Step 1 done, Step 2 next). Neither was disturbed:
this spec added claims, tightened gates and fixed docs, and changed no emitter and
no proof already standing.

## Completion record

All nine items closed in one round. `./lake build`, `./lake build Theorems Tests`
and `./tests/e2e.sh` green and warning-free (`E2E OK — 10 live suites green`);
`coverage.py` at `core defs 259; named by no theorem STATEMENT: 16 (cap 16)`;
every ratchet now at **zero headroom** (`SHIM_CAP` 27/27, `HEARTBEAT_CAP` 1/1,
`RUNTIME_PARTIAL_CAP` 2/2, `STATEMENT_CAP` 16/16, and ten per-suite check floors
each exact). Every new claim and gate break-verified; the eight break records, the
measured facts and the negative results are in SCRATCHPAD 2026-08-29.

| # | Gap | Closed by |
|---|---|---|
| 1 | `linger watch` had zero coverage of any kind | `tests/watch_test.py` (17 checks) + 3 grep gates in `e2e.sh` |
| 2 | `.detachAll`'s effect list unpinned (only `.1 = s`) | `onMsg_detachAll` (`rfl`), `_vt` kept as its corollary |
| 3 | `.labelUnset` / `.labelClear` pinned nowhere | `onMsg_labelUnset{,_gone,_keeps}`, `onMsg_labelClear{,_empty}` + 5 fixtures |
| 4 | `isWide` / `isZeroWidth` named nowhere in the repo | 3 walls + 12 per-clause edge pins + `zeroWidth_not_wide` + `widthProbes` |
| 5 | `Vt.feedBytes` docstring claimed a runtime role it lacks | docstring corrected; the `Buf.lean` precedent citation with it |
| 6 | `STATEMENT_CAP` 19 against 18 actual — a free slot | 16, zero headroom |
| 7 | no check-count ratchet on the pty suites | `suite <name> <floor>` in `e2e.sh`, ten measured floors |
| 8 | emitter table listed 4 of the 5 streams `coverage.py` enforces | `Render.screenText` row added; `history_records` named |
| 9 | `THEOREMS.md` stated a `+6`→`+0` claim Step 1 had falsified | corrected, citing `rowAnsi_len_le_cost` |

**Three findings worth more than the fixes**, all in SCRATCHPAD:

1. **Read-only is enforced daemon-side.** Two of `Client.attach`'s three
   `!readOnly` guards are semantic no-ops — the daemon drops a non-sizer's input
   and resize regardless — so a pty test cannot see them and they got grep gates.
   Only the `0×0` attach (guard A) is observable. This redirected item 1 entirely.
2. **`charWidth`'s branch order cannot be pinned by anything**, and correctly so:
   `zeroWidth_not_wide` makes the tables disjoint, so at most one branch can fire.
   Two theorem shapes that *appear* to pin it were declined for that reason.
3. **Item 7's ratchet was demonstrated, not argued.** Wrapping one `status_test.py`
   assertion in `if False:` leaves the suite printing `FAILURES: 0` while running
   four checks instead of five — green under the old gate, red under the floor.

**One follow-up, deliberately not folded in:** the nine older pty suites still
carry their own copies of the helpers now in `tests/harness.py`. Porting them is a
ten-file diff across a green gate and belongs in its own commit (AGENTS.md, one
item in flight). The check-count floors make it safe — a port that silently drops
an assertion now fails the gate.

## Where this stood while active

An audit of the whole test+theorem surface (recorded in SCRATCHPAD 2026-08-29)
found nine gaps in a tree that is otherwise deep and honest: 1467 theorems, 262
fixtures, every rung of the Render ladder linked, and every theorem name
`THEOREMS.md` cites resolving except three that the ledger itself marks as not yet
existing. The nine are narrow and specific, and they are what this spec closed.
**Item numbering is the audit's and is used everywhere — SCRATCHPAD, the commit
messages, this file.**

The audit's own most important finding, because it redirected item 1: **read-only
is enforced daemon-side, not client-side.** `Client.attach`'s three `!readOnly`
guards look like the mechanism and are not. The mechanism is
`sizer := cols != 0 && rows != 0` (`Linger/Core/Session.lean`) plus
`onMsg .input`'s `if c.attached && !c.sizer then (s, [])` — already proved by
`onMsg_input_readonly`. Only guard A (sending `.attach 0 0`) has an observable
consequence; removing guard B (resize suppression) or C (keystroke suppression) is
a **semantic no-op**, because the daemon drops a non-sizer's `.resize` and
`.input` anyway. So a pty test can only bite guard A, and B and C need grep gates
— the `SHIM_CAP` idiom (AGENTS.md, "a proved pure value needs a grep gate to
bite"). Do not write a pty assertion claiming to catch B or C; it cannot, and
pretending otherwise is the decoration this repo rejects.

## Goal

Every verb the CLI dispatches, every wire message the daemon handles, and every
table the emulator consults is pinned by a theorem, a fixture, a pty assertion
or a declared limitation — and each gate is at zero headroom, so the next gap
fails a build instead of waiting for an audit.

## Decisions (made, with reasons)

1. **Width tables get closed `decide` propositions, not `∀`-shaped
   restatements.** `isWide`/`isZeroWidth` take `Nat`, so `isWide 0x10FF = false
   ∧ isWide 0x1100 = true` is a real theorem: kernel-decidable (so it honours
   "no `native_decide` in `Theorems/`"), reaching above the BMP where Lean's
   `\uXXXX` cannot, and naming the function so `coverage.py` counts it. A
   `∀ c, isWide c = true ↔ <the same disjunction>` is a verbatim second copy of
   the table whose repair after a regression is to edit the copy — not
   logically vacuous, but operationally worthless.
2. **Two seams inside the wide table stay unclaimed, on purpose.**
   `0x3041-0x33FF ∪ 0x3400-0x4DBF` and `0x4E00-0x9FFF ∪ 0xA000-0xA4CF` are each
   one contiguous run written as two clauses. Moving a split point in *both*
   clauses is invisible to every possible oracle — the two `Bool` functions
   agree on every `Nat`. A one-sided shrink is catchable and is pinned; an
   overlap is not, and is recorded rather than pretended.
   Likewise the `0x200B/0x200C/0x200D` singleton cluster: mutually adjacent, so
   no neighbour probe detects the loss of any one. Each is pinned individually.
3. **`charWidth_eq_zero_iff`-shaped theorems are declined.** They name all three
   functions and so would drop the ratchet by 2 while pinning no range content —
   they catch only a swap of `charWidth`'s two `if` branches. Taking them
   *instead of* the edge pins would be exactly the under-claimed-surface failure
   the gate cannot see. `zeroWidth_not_wide` is kept, because cross-table
   disjointness is content no per-table edge pin has.
4. **`Vt.feedBytes` is kept, its docstring corrected.** The repo's rule is about
   *unreachable* code; `feedBytes` is reached from five `Tests/` sites, so it is a
   legitimate convenience. What is false is its docstring ("The runtime hands us
   `ByteArray`s") — the daemon's path is `Terminal.feed` — and the `Buf.lean`
   comment citing it as precedent for a design decision. Fix the two sentences,
   not the code.
5. **`onMsg_detachAll_vt` is kept as a corollary, not deleted.** The new
   `onMsg_detachAll` subsumes it, but the `_vt` name is what §Detach's prose
   cites for "a client detaching cannot change the screen", and a corollary that
   names the weaker fact keeps that citation honest.
6. **The check-count ratchet is per-suite floors in `e2e.sh`, not a new line in
   ten suites.** One file changes, the numbers live next to `SHIM_CAP` and
   friends where the other ratchets are read, and no suite's output format moves.

## Definition of done

All nine audit items closed, `./lake build`, `./lake build Theorems Tests` and
`./tests/e2e.sh` green and warning-free, every new theorem and pty assertion
break-verified with the break recorded in `SCRATCHPAD.md`, and every ratchet at
zero headroom.

| # | Gap | Close |
|---|---|---|
| 1 | `linger watch` has zero coverage of any kind | `tests/watch_test.py` in the gate + two grep gates for guards B/C |
| 2 | `.detachAll`'s effect list unpinned (only `.1 = s`) | `onMsg_detachAll`, full-pair `rfl` |
| 3 | `.labelUnset` / `.labelClear` pinned nowhere | `onMsg_labelUnset`, `onMsg_labelClear` + fixtures |
| 4 | `isWide` / `isZeroWidth` named nowhere in the repo | low walls + per-clause edge pins + `zeroWidth_not_wide` + fixtures |
| 5 | `Vt.feedBytes` docstring claims a runtime role it lacks | correct it and the `Buf.lean` citation |
| 6 | `STATEMENT_CAP` 19 vs 18 actual — one free slot | tighten to the post-item-4 measured value |
| 7 | no check-count ratchet on the pty suites | per-suite floors in `e2e.sh` |
| 8 | `THEOREMS.md` emitter table lists 4 of 5 streams | add the `screenText` row; add `history_records` |
| 9 | `THEOREMS.md:666` states a `+6`→`+0` claim Step 1 falsified | correct it, citing `rowAnsi_len_le_cost` |

## Non-goals

- **Making guards B and C in `Client.lean` behaviourally observable.** That
  would mean removing the daemon-side drop so the client-side guard is the only
  thing standing — trading defence in depth for testability. The greps are the
  right oracle.
- **A `readOnly` bit on the wire.** The `0×0` geometry is the marker and
  `controlResize` already refuses a zero dimension for the same reason
  (`Session.lean:236`). Adding a redundant flag creates a second source of truth
  for one predicate.
- **Chasing width-table *accuracy* against Unicode.** This pins the table
  against *change*, not against UAX #11. A deliberate correction to a range is
  expected to update the matching pin; that is the pin working.
