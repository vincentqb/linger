# grid-fidelity — the replayed screen equals the saved screen

**Goal.** Close anchor A1's last gap: prove that
`(Vt.init v.cols v.rows).feed (Render.restore v)` has the *same cells and
pens* as `v`, not merely the same cursor and a quiesced parser.

**Definition of done.** A green theorem `restore_grid` in
`Theorems/Render.lean` (no `sorry`, no `native_decide`), lifted to
`Theorems/Resume.lean`, break-verified with the break in `SCRATCHPAD.md`,
its row in `THEOREMS.md`, and `./tests/e2e.sh` green. At that point
`Tests/Render.lean`'s `replayEq` fixtures stop being the fidelity oracle
and become regression tests.

**Predecessor.** `specs/archive/bigger-theorems.md` (closed). It left the byte
layer *done*: `utf8_feed`, `utf8s_feed`, `cellText_feed` and `crlf_feed`
already reduce a repaint to a chain of `Vt.print`s, so nothing here needs
to reason about bytes. What remains is a statement about `print`.

## What is already in hand

| Rung | Theorem |
|---|---|
| bytes → prints | `utf8_feed`, `utf8s_feed`, `cellText_feed`, `crlf_feed` |
| bytes → pen set | *open* — see step 2 |
| parser stays ground | `Ends`, `restore_quiesced` |
| DECOM stays off | `Quiet`, `quiet_restoreBody` |
| cursor lands right | `cup_places_cursor`, `restore_cursor` |
| dimensions unchanged | `dims_feed` |
| SGRs under the cap | `penSgr_under_cap` |

## Steps

**Step 1 — the hypotheses, stated honestly.** The claim is false for an
arbitrary `Vt`, and the reasons are worth naming as a predicate rather than
discovered one at a time in the middle of a proof:

```lean
structure Renderable (v : Vt) : Prop where
  base   : ∀ c ∈ cells v, safeChar c.base = c.base   -- no C0/DEL in a cell
  width  : ∀ c ∈ cells v, charWidth c.base = c.width -- stored width agrees
  marks  : ∀ c ∈ cells v, c.marks.length ≤ 8 ∧ ∀ m ∈ c.marks, charWidth m = 0
  shadow : ∀ x y, (cell v x y).width = 2 → (cell v (x+1) y).width = 0
```
Every clause holds of a state reached from `Vt.init` by `feed` — `print`
stores `charWidth ch` as the width, `Cell.erased` stores a blank of width
1, and the mark branch caps at 8 — so `Renderable` is a §Bound-style
invariant, and proving it preserved by `step` is step 5. Do *not* weaken
the theorem to dodge these: they are facts about the emulator, and the
right move is to prove them.

**Step 2 — the pen round trip** (`penSgr_feed`), independent of the grid
and the larger half of the work:

1. the parser accumulates `joinSemi codes` into
   `params = codes.map (min · 65535, false)` — an induction threading the
   params array, with the ≤ 16 bound from `penSgr_under_cap` discharging
   the `ignore` branch;
2. `Vt.applySgr` over `penAttrCodes p ++ colorCodes p.fg ++ colorCodes p.bg`
   yields `p`. Note `applySgr` is a `let rec go` with fuel: prove
   `fuel ≥ length + 1 → go = <pure fold>` first, or the fuel bookkeeping
   will be threaded through every case.

The emitter was restructured for exactly this: `colorCodes`/`penAttrCodes`
produce parameter *numbers*, so half of this is about numbers, not bytes.

**Step 3 — one glyph group.** `print` writes a cell and advances; a
width-2 glyph writes its shadow cell too, and a mark lands on the cell
*before* the cursor (`§Replay` fix 1: on a wide char's shadow). So the
row induction steps by *glyph group*, not by cell — a width-1 cell, or a
width-2 cell plus its shadow. State that group step, with the pen fixed.

**Step 4 — row, then grid.** `rowAnsi` threads a pen and emits `penSgr`
only when it changes, so the row induction carries "the emulator's pen is
the last cell's pen". `gridAnsi` is `CSI H` then rows joined by CRLF, with
no trailing separator; at a row end the cursor sits at the last column with
wrap *pending*, which the CRLF clears — that is why `≃` excludes pending
flags. Also needed: `CSI 2 J` at the head of `restoreBody` blanks the grid
with the default pen, which is what makes the painted result independent of
the fresh emulator's contents.

**Step 5 — `Renderable` is preserved by `step`**, so the theorem's
hypothesis is discharged for every reachable session rather than assumed.
Same shape as `Good.step`; the frames layer covers the operations that do
not write cells.

## Risks, measured rather than guessed

* `print` is heavy for the kernel: `frame_print` as a single `rfl` times
  out at `whnf` (200000 heartbeats). The workaround is known — peel the
  stage frames inside a field projection (`ua_print` does) — but expect to
  name intermediate stages rather than reason about `print` monolithically.
* `applySgr`'s fold is the largest single unknown. If step 2 stalls, the
  grid claim can still land *conditioned* on the pen, by taking
  "the emulator's pen equals the cell's pen" as a hypothesis and closing it
  later; say so in the statement rather than quietly narrowing the claim.

## Open

* Whether `Renderable` should live in `Zmx/Core/Vt.lean` next to `Good` or
  in `Theorems/`. It is a proof-side notion, but so was `Good`.
