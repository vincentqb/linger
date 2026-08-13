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
| a pen replays exactly | `penSgr_feed` (**step 2, done**) |
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

**Step 2 — the pen round trip: DONE** (`penSgr_feed`). Feeding the sequences
`penSgr` emits to a quiet emulator sets its pen to `p` and changes nothing
else. Both halves landed:

1. *(done)* the parser accumulates `joinSemi codes` into
   `params = codes.map (min · 65535, false)` — an induction threading the
   params array, with the ≤ 16 bound from `penSgr_under_cap` discharging
   the `ignore` branch. State the run lemma with the *pushed* array
   (`(s'.params.push (min s'.cur 65535, s'.curSub)).toList = …`) rather than
   with `dropLast`/`getLast`: `csiFinish` performs exactly that push, and
   the induction then follows `joinSemi`'s own three-arm recursion. Kept
   separate from `csi_param_run_frame`, which says the run touches nothing
   but `pstate` — the two views are then identified through the injectivity
   of `PState.csi`.
2. *(done)* `Vt.applySgr` recovers the pen. The fuel turned out not to need
   a pure-fold detour: every sequence is called at `length + 1`, which is
   exactly what the fold consumes, so the concrete cases close directly.
   The attributes went as 128 branches over the seven `Bool`s (4.7 s) —
   cheaper than seven step lemmas plus a composition law; the 16-colour
   forms as 8 concrete codes each, which lets the fold's long `if`-chain
   decide by computation instead of needing a disequality per rung.

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
  — **Resolved.** The fold was not the problem: `pen_codes_recover` landed
  in ~120 lines with no fuel machinery, because every sequence is called at
  exactly `length + 1`. The risk was mis-estimated; the note stays as the
  record of that.

## Open

* Whether `Renderable` should live in `Zmx/Core/Vt.lean` next to `Good` or
  in `Theorems/`. It is a proof-side notion, but so was `Good`.
