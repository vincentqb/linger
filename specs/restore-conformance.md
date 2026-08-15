# restore-conformance — restore works into any client, and the proofs say so

Status: active
Updated: 2026-08-15
Predecessor: `specs/terminal-contract.md` (Steps 1–3 complete; its Step 4 is carried
here in a different shape, and its Step 5 archival gate is carried unchanged)

## Where this stands (2026-08-15)

The diagnosis this spec is built on: **every §Replay bug had the same shape, and the
shape was in the quantifier.** `Tests/Fuzz.lean`'s header calls it "an emitter stage
correct only under a precondition on the emulator state it is fed into" — and the
fidelity theorem quantifies over `Vt.init`, the one receiver state in which every
such precondition already holds. So the theorem was structurally blind to the class.

`87f64b3` fixed the live instance: `modesAnsi` was set-only for eight modes and the
repaint ran before any receiver state was established, so a real client's leftover
IRM, DECOM, mouse reporting, scroll region, charset or alt screen either corrupted
the repaint or survived it. `prologueAnsi` now establishes what the repaint needs and
every mode is emitted both ways.

What is *not* fixed is the theorem. `restore_grid` and the `Ends`/`Quiet`/`Keeps`
layers all still start from a pristine, ground receiver, so nothing above the tests
rules out the next instance of the same class.

## Goal

`restore` puts **any** conforming receiver of the right size into the session's
state, and the theorems quantify over that receiver rather than over one convenient
starting point.

Two things this deliberately does not claim. It is not conformance to xterm: the
model receiver is our own `Vt`, so these are emitter/parser self-consistency
theorems, and the pty and e2e suites remain the only evidence about real terminals.
And it is not scrollback: restore repaints the screen, not history.

## Definition of done

1. `Sets`, a predicate for "this chunk leaves property `P` at value `x` regardless of
   the receiver's incoming state", with `nil`/`append`/`ite` composition laws
   mirroring `Ends`/`Quiet`/`Keeps`.
2. `restore_modes_any`: for every `v` and every `w`, the modes after
   `w.feed (restore v)` are `v`'s — the theorem that certifies `87f64b3` instead of
   the tests carrying it alone. Likewise the charset flags, the scroll region, and
   the alt-screen flag.
3. `Ends`, `Quiet` and `Keeps` re-stated without the ground-parser assumption, which
   requires the prologue to lead with a sequence abort so a client caught
   mid-escape resynchronises.
4. `PaintState` — the painter's abstract state (`x`, `y`, `pen`, `pending`) as a
   named record, with `rowAnsi` threading it, and a `Matches` relation tying it to a
   `Vt` and a row prefix.
5. `restore_grid_any`: for every `v` and every `w` of the same dimensions, the grid
   after `w.feed (restore v)` is `v.grid`, with cell and pen equality. Then
   `restore_grid_reachable` from `LiveReachableVt`, and `resume_grid` composing with
   checkpoint exactness.
6. `./lake build Theorems Tests` and `./tests/e2e.sh` warning-free and green; every
   new theorem break-verified and recorded in `SCRATCHPAD.md`.

Review/revise cap: two fresh-review rounds, as before.

## Step 1 — `Sets`, and the modes the fix already establishes

Status: not started.

Purpose: make the bug fix a theorem rather than a test. This is the cheapest step and
the one that pays first, because it is a frame-shaped claim — the kind that has
caught every real bug in this project — with the quantifier corrected.

Reads: `Zmx/Core/Render.lean`, `Theorems/Render.lean`, `SCRATCHPAD.md`.
Writes: `Theorems/Render.lean`, `THEOREMS.md`, `SCRATCHPAD.md`.

Shape: `Sets (P : Vt → α) (x : α) (bs : Bytes) : Prop := ∀ w, (w.feed bs).P = x`.
The composition law that matters is *right*-absorbing: `Sets P x b → Sets P x (a ++ b)`
for any `a`, which is what lets a later chunk overwrite an earlier one and is why
both-ways emission is provable at all.

Exit: `restore_modes_any` holds for all ten `Modes` fields, plus `g0Line`, `g1Line`,
`shiftOut`, `top`, `bot`, and `altGrid.isNone` when the session is not in alt.
Deleting any one both-ways emit from `modesAnsi` breaks the corresponding claim.

## Step 2 — drop the ground-parser assumption

Status: **first half done** (2026-08-15). `restore_grounds (v w : Vt) :
(w.feed (restore v)).pstate = .ground` holds with no hypothesis on `w` — the first
receiver-quantified theorem in the file. Chain: `un_abortUtf8_esc`, `esc_lands` (one
case per `PState`), `st_finish`, `st_grounds`, `prologue_grounds`.

The abort turned out to be `ESC \` (ST) rather than `CAN`: our `stepOsc` treats a C0
byte as payload, so `CAN` would have needed a Core semantics change, while `ST` is
what both string states already listen for and `stepEsc` routes `0x5C` to its default
arm. No new parser surface.

Remaining: the `u8need` half, and the same treatment for `Quiet`'s origin half. Both
need each chunk to preserve its property from an arbitrary start — the per-chunk work
`Keeps` already does for the grid.

Purpose: a client cut off mid-escape is a real state, and every existing stream
theorem assumed it away.

Exit: the three predicates carry no hypothesis on the receiver's parser state.
`restore_quiesced` and `resume_quiesced` follow with their hypotheses removed.

## Step 3 — `PaintState`

Status: not started.

Purpose: replace the monolithic row induction with a named invariant, which is what
makes the exact claim affordable. `rowAnsi` already threads `(bytes, pen, x)`; the
missing piece is `pending`, which the 2026-08-15 negative result proved is
load-bearing rather than noise.

Shape: a `PaintState` record; `rowAnsi` refactored to carry it; `Matches w P g k`
meaning "`w`'s row agrees with `g` on columns `< k`, and `w`'s cursor and pen are
`P`"; one step lemma per cell shape (width 1, width 2 with room, width 0), with
`mend_of_pairOk` as the stability argument for the re-mend after each write.

Exit: `rowAnsi_writes_row` for any `RowOk` row, from any receiver matching the
claimed `PaintState`. A same-shape value mutation in `rowAnsi` breaks it.

## Step 4 — the grid, and the end-to-end claim

Status: not started. Depends on Steps 1–3.

Shape: `joinCRLF` row walk (including the argument that no line feed scrolls, which
needs Step 1's scroll-region claim), the alt switch, then composition through
`restore_grid_of_paint` — which already exists and already reduces `restore_grid` to
the paint prefix.

Exit: criteria 5 of Definition of done.

## Step 5 — review, document, archive

Status: not started.

Archive `specs/terminal-contract.md` and `specs/grid-fidelity.md` with completion
records once their carried obligations land here. Neither may be archived while its
exit criteria are unmet; that is why both are still in `specs/`.

## Carried decisions

Recorded so they are not relitigated:

- **Autowrap stays on across the repaint.** `Vt.printMark` reads wrap-pending to
  attach a combining mark to the margin cell it just wrote, and no absolute cursor
  move can express that position. Two fuzz seeds catch the alternative
  (SCRATCHPAD 2026-08-15).
- **`ED 2`'s cell-level blanking is not on the critical path.** The paint writes every
  column, so only `eraseScreen_two_frame` is needed, and it is proved.
- **The exact-cell claim is not to be weakened.** Choosing test coverage over proof
  for the anchor claim was considered and rejected: the fuzzer's exclusion list was
  historically non-empty, so cell bugs here are real and recurring.
- **Explicit private-mode sets, not DECSTR.** We already parse the former, so the
  prologue costs no new parser surface, and `CSI ! p`'s reset list varies by
  terminal.
