import Theorems.Render.History
/-! # Step 3 — the row painter

`PaintState` and `Matches` (the row induction's invariant), one step lemma per cell
shape, the mark loop, and the fold that assembles them: `rowAnsi_writes_row`. Split
out of `Theorems/Render.lean`. -/

namespace Zmx.Core.Render

open Zmx.Core.Vt

/-! ## Step 3 — `PaintState` and `Matches`, the row induction's invariant

The monolithic row induction is replaced by a named invariant, which is what makes the
exact claim affordable. `rowAnsi` already threads `(bytes, pen, x)`; what the invariant
adds is the two things a receiver has that the emitter cannot see — wrap-`pending`, which
the 2026-08-15 negative result proved load-bearing, and the decoder triple.

Design constraints, all recorded in `specs/restore-conformance.md` before the proof and
each a way the obvious statement would be wrong:

* the parser component is a **triple** (`pstate`, `u8need`, `u8acc`), not a pair —
  `cellText_feed` needs the third, and inside a wide-with-marks cell the stream goes
  CSI → glyph, so it has to be re-established rather than assumed once;
* the frontier `k` must be a **glyph-group boundary**. If `k` ever sat between a width-2
  base and its shadow, `halfPair (k-1)` would be true at that moment and the re-mend
  would blank the base the previous rung had just painted. Hence `frontier`;
* `Matches` asserts **nothing** about columns `≥ k`. That is what lets the theorem
  quantify over an arbitrary client: every unpainted column still holds the previous
  occupant's junk, half pairs included.
-/

/-- Where the painter believes the receiver is. -/
structure PaintState where
  x : Nat
  y : Nat
  pen : Pen
  pending : Bool
  deriving DecidableEq, Repr

/-- `Matches w P g k` — the receiver agrees with row `g` on columns `< k`, its cursor and
pen are `P`, its decoder is quiet, and the receiver-side context every rung needs
(autowrap on, IRM off, ASCII charsets, a full-length row) holds. The context travels
inside the invariant rather than beside it so that one step lemma re-establishes
everything the next one needs. -/
structure Matches (w : Vt) (P : PaintState) (g : Row) (k : Nat) : Prop where
  curX : w.cursor.x = P.x
  curY : w.cursor.y = P.y
  pend : w.cursor.pending = P.pending
  pen : w.pen = P.pen
  ground : w.pstate = .ground
  u8need : w.u8need = 0
  u8acc : w.u8acc = 0
  ins : w.modes.insert = false
  wrap : w.modes.wrap = true
  ascii0 : w.g0Line = false
  ascii1 : w.g1Line = false
  rowLen : (w.getRow P.y).size = w.cols
  inGrid : P.y < w.grid.size
  /-- `k` is a glyph-group boundary: it never splits a wide pair. -/
  frontier : k = 0 ∨ (g.at (k - 1)).width ≠ 2
  cells : ∀ j, j < k → w.getCell j P.y = g.at j

/-- **The repair sweep keeps the painted prefix.**

Separating this from "the writes missed the prefix" is what lets one lemma serve every
cell shape: the narrow rung has one write, the wide rung two, the mark rung one at a
lower column. Each rung shows its own writes are invisible below the frontier (one
`at_putCell_ne` per write) and then applies this.

The case analysis is on the *source* row's shape at each column — which the induction
knows, because the prefix already equals the source there — and `RowOk.pairs` is what
turns "width 0 at `j`" into "a whole pair at `j-1`", so `mend_keeps_wide` applies to the
pair rather than to half of it. It cannot be done per *row*: `mend_of_pairOk` needs the
whole row pair-consistent, and mid-paint it is not — every column above the frontier
still holds the previous occupant's junk, half pairs included.

`hfront` rules out the one bad split. Without it `j = k-1` could be a width-2 base whose
shadow sits at `k`, unpainted, so the sweep would see a half pair and blank the base the
previous rung just painted. Verified load-bearing: replacing it with `True` collapses
exactly the width-2 case. -/
theorem mend_keeps_prefix {u : Vt} {g : Row} {y k : Nat}
    (hrow : RowOk u.cols g)
    (hcells : ∀ j, j < k → u.getCell j y = g.at j)
    (hfront : k = 0 ∨ (g.at (k - 1)).width ≠ 2)
    (hy : y < u.grid.size) :
    ∀ j, j < k → (u.mendRow y).getCell j y = g.at j := by
  intro j hj
  -- `getCell x y` *is* `(getRow y).at x`; ascribing once keeps every `rw` syntactic
  have hat : ∀ i, i < k → (u.getRow y).at i = g.at i := fun i hi => hcells i hi
  have hwj : (u.getRow y).at j = g.at j := hat j hj
  -- a stored width is 0, 1 or 2: `CellOk` ties a non-zero one to `charWidth`
  have hw3 : (g.at j).width = 0 ∨ (g.at j).width = 1 ∨ (g.at j).width = 2 := by
    by_cases hz : (g.at j).width = 0
    · exact Or.inl hz
    · rw [← (hrow.cells j).width hz]
      unfold charWidth
      split
      · exact Or.inl rfl
      · split
        · exact Or.inr (Or.inr rfl)
        · exact Or.inr (Or.inl rfl)
  rw [getCell_mendRow_same _ _ _ hy]
  rcases hw3 with hz | hz | hz
  · -- a shadow: `PairOk` puts its base at `j-1`, so the whole pair is in the prefix
    obtain ⟨hne0, hbase⟩ := (hrow.pairs j).2 hz
    have hj1eq : j - 1 + 1 = j := by omega
    have hj1 : j - 1 < k := by omega
    obtain ⟨-, h1⟩ := mend_keeps_wide (u.getRow y) (j - 1)
      (by rw [hat (j - 1) hj1]; exact hbase)
      (by
        rw [hj1eq, hat j hj, hat (j - 1) hj1, ← hj1eq]
        exact (hrow.pairs (j - 1)).1 hbase)
    rw [hj1eq] at h1
    rw [h1]; exact hwj
  · rw [mend_keeps_narrow _ j (by rw [hwj, hz])]; exact hwj
  · -- a base: `hfront` is what puts its shadow inside the prefix too
    have hshIn : j + 1 < k := by
      rcases hfront with h | h
      · omega
      · rcases Nat.lt_or_ge (j + 1) k with hh | hh
        · exact hh
        · exact absurd (by rw [show k - 1 = j from by omega]; exact hz) h
    obtain ⟨h0, -⟩ := mend_keeps_wide (u.getRow y) j (by rw [hwj, hz])
      (by rw [hat (j + 1) hshIn, hat j hj]; exact (hrow.pairs j).1 hz)
    rw [h0]; exact hwj

/-! ### The step lemmas

One per cell shape. Each takes `Matches … k` and returns `Matches … (k+1)` (or `(k+2)`
for a pair), so the row walk is a fold rather than a case analysis, and each
re-establishes every field of the invariant the next rung reads.

`hfit : k + 1 < w.cols` is the *interior* case. The final column is deliberately a
separate rung: there the advance clamps and arms wrap-pending, which is the state the
2026-08-15 negative result showed no absolute cursor move can express. -/

set_option maxHeartbeats 1000000 in
/-- **One narrow cell with no marks, in the interior of a row.** The first rung.

The heartbeat bump is the write term: `Matches`'s fifteen fields each mention the fed
state, and unifying `RowOk u.cols g` against the `putCell`/`mendRow` composite is a defeq
check per field. Cheaper than restructuring the invariant into a conjunction of smaller
records, which would move the cost to every call site instead. -/
theorem step_narrow {w : Vt} {P : PaintState} {g : Row} {k : Nat}
    (hrow : RowOk w.cols g) (hm : Matches w P g k)
    (hPx : P.x = k) (hpend : P.pending = false) (hfit : k + 1 < w.cols)
    (hwid : (g.at k).width = 1) (hmk : (g.at k).marks = [])
    (hpen : (g.at k).pen = P.pen) :
    Matches (w.feed (cellText (g.at k))) { P with x := k + 1, pending := false } g (k + 1) := by
  have hem : Emittable (g.at k).base := (hrow.cells k).base
  have hpc : w.printChar (g.at k).base = (g.at k).base :=
    printChar_id_of_ascii hm.ascii0 hm.ascii1 hem.1 hem.2
  have hcw : charWidth (g.at k).base = 1 := by
    rw [(hrow.cells k).width (by rw [hwid]; omega), hwid]
  have hpd : w.cursor.pending = false := by rw [hm.pend, hpend]
  -- the bytes of one cell are one `print`
  have hfeed : w.feed (cellText (g.at k)) = w.print (g.at k).base := by
    rw [cellText_feed (g.at k) hm.ground hm.u8need hm.u8acc, hmk, safeChar_of_emittable hem]
    rfl
  -- …and one `print` is one write plus an advance
  have hx : w.cursor.x = k := by rw [hm.curX, hPx]
  have hwrite := print_narrow_eq hpc hcw hm.ins hpd
  have hcur := cursor_print_narrow_fits hpc hcw hm.ins hpd (by rw [hx]; exact hfit)
  have hgs : w.cursor.y < w.clearPending.grid.size := by
    show w.cursor.y < w.grid.size
    rw [hm.curY]; exact hm.inGrid
  have hrl : w.cursor.x < (w.clearPending.getRow w.cursor.y).size := by
    show w.cursor.x < (w.getRow w.cursor.y).size
    rw [hm.curY, hm.rowLen, hx]; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfeed, hcur]; show w.cursor.x + 1 = k + 1; rw [hx]
  · rw [hfeed, hcur]; show w.cursor.y = P.y; exact hm.curY
  · rw [hfeed, hcur]
  · rw [hfeed, pen_print]; exact hm.pen
  · rw [hfeed, Zmx.Core.Vt.ps_print]; exact hm.ground
  · rw [hfeed, Zmx.Core.Vt.un_print]; exact hm.u8need
  · rw [hfeed, ua_print']; exact hm.u8acc
  · rw [hfeed, ins_print]; exact hm.ins
  · rw [hfeed, wrap_print]; exact hm.wrap
  · rw [hfeed, g0_print]; exact hm.ascii0
  · rw [hfeed, g1_print]; exact hm.ascii1
  · -- the painted row is still `cols` long: a write and a sweep resize nothing
    show ((w.feed (cellText (g.at k))).getRow P.y).size = (w.feed (cellText (g.at k))).cols
    rw [hfeed, hwrite]
    obtain ⟨hcl, -, hrw⟩ := write_shape w.clearPending w.cursor.x w.cursor.y
      { base := (g.at k).base, marks := [], width := 1, pen := w.pen } 1 hgs
    rw [hcl, hrw P.y]
    show (w.getRow P.y).size = w.cols
    exact hm.rowLen
  · show P.y < (w.feed (cellText (g.at k))).grid.size
    rw [hfeed, hwrite]
    obtain ⟨-, hgz, -⟩ := write_shape w.clearPending w.cursor.x w.cursor.y
      { base := (g.at k).base, marks := [], width := 1, pen := w.pen } 1 hgs
    rw [hgz]
    show P.y < w.grid.size
    exact hm.inGrid
  · exact Or.inr (by rw [show k + 1 - 1 = k from by omega, hwid]; decide)
  · -- the cells: the prefix by `prefix_kept`, column `k` by the write itself
    intro j hj
    show (w.feed (cellText (g.at k))).getCell j P.y = g.at j
    rw [hfeed, hwrite, getCell_printAdvance, show P.y = w.cursor.y from hm.curY.symm]
    rcases Nat.lt_or_ge j k with hjk | hjk
    · have hcellsW : ∀ i, i < k → (w.clearPending.putCell w.cursor.x w.cursor.y
          { base := (g.at k).base, marks := [], width := 1, pen := w.pen }).getCell i
          w.cursor.y = g.at i := by
        intro i hi
        show ((w.clearPending.putCell w.cursor.x w.cursor.y
          { base := (g.at k).base, marks := [], width := 1, pen := w.pen }).getRow
            w.cursor.y).at i = g.at i
        rw [at_putCell_ne _ _ _ _ i (by omega) hgs]
        show w.getCell i w.cursor.y = g.at i
        rw [hm.curY]
        exact hm.cells i hi
      have hgsW : w.cursor.y < (w.clearPending.putCell w.cursor.x w.cursor.y
          { base := (g.at k).base, marks := [], width := 1, pen := w.pen }).grid.size := by
        rw [grid_size_putCell]; exact hgs
      exact mend_keeps_prefix (u := w.clearPending.putCell w.cursor.x w.cursor.y
        { base := (g.at k).base, marks := [], width := 1, pen := w.pen })
        hrow hcellsW hm.frontier hgsW j hjk
    · have hje : j = k := by omega
      subst hje
      -- the write's index is the receiver's cursor; `hx` is what identifies it with `j`
      rw [hx] at hrl ⊢
      rw [getCell_write_mendRow_narrow _ _ _ _ rfl hgs hrl]
      exact Cell.ext' rfl hmk.symm hwid.symm (hm.pen.trans hpen.symm)

set_option maxHeartbeats 1000000 in
/-- **One narrow cell at the right margin.** The rung the interior case cannot cover: the
advance clamps the column and arms wrap-pending, which is the state the 2026-08-15
negative result showed no absolute cursor move can express. `x` does not move (it is
already `cols - 1`); what changes is `pending`, and the following `carriageReturn`
discards it — which is why the row-exit shape is `x = cols - 1` and not a claim about
`pending`. -/
theorem step_narrow_margin {w : Vt} {P : PaintState} {g : Row} {k : Nat}
    (hrow : RowOk w.cols g) (hm : Matches w P g k)
    (hPx : P.x = k) (hpend : P.pending = false)
    (hk : k < w.cols) (hmar : w.cols ≤ k + 1)
    (hwid : (g.at k).width = 1) (hmk : (g.at k).marks = [])
    (hpen : (g.at k).pen = P.pen) :
    Matches (w.feed (cellText (g.at k))) { P with pending := true } g (k + 1) := by
  have hem : Emittable (g.at k).base := (hrow.cells k).base
  have hpc : w.printChar (g.at k).base = (g.at k).base :=
    printChar_id_of_ascii hm.ascii0 hm.ascii1 hem.1 hem.2
  have hcw : charWidth (g.at k).base = 1 := by
    rw [(hrow.cells k).width (by rw [hwid]; omega), hwid]
  have hpd : w.cursor.pending = false := by rw [hm.pend, hpend]
  have hfeed : w.feed (cellText (g.at k)) = w.print (g.at k).base := by
    rw [cellText_feed (g.at k) hm.ground hm.u8need hm.u8acc, hmk, safeChar_of_emittable hem]
    rfl
  have hx : w.cursor.x = k := by rw [hm.curX, hPx]
  have hwrite := print_narrow_eq hpc hcw hm.ins hpd
  have hcur := cursor_print_narrow_margin hpc hcw hm.ins hpd (by rw [hx]; exact hmar)
  have hgs : w.cursor.y < w.clearPending.grid.size := by
    show w.cursor.y < w.grid.size
    rw [hm.curY]; exact hm.inGrid
  have hrl : w.cursor.x < (w.clearPending.getRow w.cursor.y).size := by
    show w.cursor.x < (w.getRow w.cursor.y).size
    rw [hm.curY, hm.rowLen, hx]; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfeed, hcur]; show w.cols - 1 = P.x; rw [hPx]; omega
  · rw [hfeed, hcur]; show w.cursor.y = P.y; exact hm.curY
  · rw [hfeed, hcur]; show w.modes.wrap = true; exact hm.wrap
  · rw [hfeed, pen_print]; exact hm.pen
  · rw [hfeed, Zmx.Core.Vt.ps_print]; exact hm.ground
  · rw [hfeed, Zmx.Core.Vt.un_print]; exact hm.u8need
  · rw [hfeed, ua_print']; exact hm.u8acc
  · rw [hfeed, ins_print]; exact hm.ins
  · rw [hfeed, wrap_print]; exact hm.wrap
  · rw [hfeed, g0_print]; exact hm.ascii0
  · rw [hfeed, g1_print]; exact hm.ascii1
  · show ((w.feed (cellText (g.at k))).getRow P.y).size = (w.feed (cellText (g.at k))).cols
    rw [hfeed, hwrite]
    obtain ⟨hcl, -, hrw⟩ := write_shape w.clearPending w.cursor.x w.cursor.y
      { base := (g.at k).base, marks := [], width := 1, pen := w.pen } 1 hgs
    rw [hcl, hrw P.y]
    show (w.getRow P.y).size = w.cols
    exact hm.rowLen
  · show P.y < (w.feed (cellText (g.at k))).grid.size
    rw [hfeed, hwrite]
    obtain ⟨-, hgz, -⟩ := write_shape w.clearPending w.cursor.x w.cursor.y
      { base := (g.at k).base, marks := [], width := 1, pen := w.pen } 1 hgs
    rw [hgz]
    show P.y < w.grid.size
    exact hm.inGrid
  · exact Or.inr (by rw [show k + 1 - 1 = k from by omega, hwid]; decide)
  · intro j hj
    show (w.feed (cellText (g.at k))).getCell j P.y = g.at j
    rw [hfeed, hwrite, getCell_printAdvance, show P.y = w.cursor.y from hm.curY.symm]
    rcases Nat.lt_or_ge j k with hjk | hjk
    · have hcellsW : ∀ i, i < k → (w.clearPending.putCell w.cursor.x w.cursor.y
          { base := (g.at k).base, marks := [], width := 1, pen := w.pen }).getCell i
          w.cursor.y = g.at i := by
        intro i hi
        show ((w.clearPending.putCell w.cursor.x w.cursor.y
          { base := (g.at k).base, marks := [], width := 1, pen := w.pen }).getRow
            w.cursor.y).at i = g.at i
        rw [at_putCell_ne _ _ _ _ i (by omega) hgs]
        show w.getCell i w.cursor.y = g.at i
        rw [hm.curY]
        exact hm.cells i hi
      have hgsW : w.cursor.y < (w.clearPending.putCell w.cursor.x w.cursor.y
          { base := (g.at k).base, marks := [], width := 1, pen := w.pen }).grid.size := by
        rw [grid_size_putCell]; exact hgs
      exact mend_keeps_prefix (u := w.clearPending.putCell w.cursor.x w.cursor.y
        { base := (g.at k).base, marks := [], width := 1, pen := w.pen })
        hrow hcellsW hm.frontier hgsW j hjk
    · have hje : j = k := by omega
      subst hje
      rw [hx] at hrl ⊢
      rw [getCell_write_mendRow_narrow _ _ _ _ rfl hgs hrl]
      exact Cell.ext' rfl hmk.symm hwid.symm (hm.pen.trans hpen.symm)


set_option maxHeartbeats 1000000 in
/-- **A wide glyph and its shadow — one rung, `k` to `k+2`.**

The pair is consumed together, and that is a correctness requirement rather than a
convenience: if the frontier ever sat between a base and its shadow, `halfPair (k-1)`
would be true at that moment and the repair sweep would blank the base the rung had just
painted. The shadow's own slot in `rowAnsi`'s fold emits nothing, so there is no second
rung to give it. -/
theorem step_wide {w : Vt} {P : PaintState} {g : Row} {k : Nat}
    (hrow : RowOk w.cols g) (hm : Matches w P g k)
    (hPx : P.x = k) (hpend : P.pending = false)
    (hfit : k + 1 < w.cols) (hfit2 : k + 2 < w.cols)
    (hwid : (g.at k).width = 2) (hmk : (g.at k).marks = [])
    (hpen : (g.at k).pen = P.pen) :
    Matches (w.feed (cellText (g.at k))) { P with x := k + 2, pending := false } g (k + 2) := by
  have hem : Emittable (g.at k).base := (hrow.cells k).base
  have hpc : w.printChar (g.at k).base = (g.at k).base :=
    printChar_id_of_ascii hm.ascii0 hm.ascii1 hem.1 hem.2
  have hcw : charWidth (g.at k).base = 2 := by
    rw [(hrow.cells k).width (by rw [hwid]; omega), hwid]
  have hpd : w.cursor.pending = false := by rw [hm.pend, hpend]
  have hsh : g.at (k + 1) = Cell.shadow (g.at k) := (hrow.pairs k).1 hwid
  have hfeed : w.feed (cellText (g.at k)) = w.print (g.at k).base := by
    rw [cellText_feed (g.at k) hm.ground hm.u8need hm.u8acc, hmk, safeChar_of_emittable hem]
    rfl
  have hx : w.cursor.x = k := by rw [hm.curX, hPx]
  have hfitc : w.cursor.x + 1 < w.cols := by rw [hx]; exact hfit
  have hwrite := print_wide_eq hpc hcw hm.ins hpd hfitc
  have hcur := cursor_print_wide_fits hpc hcw hm.ins hpd hfitc (by rw [hx]; exact hfit2)
  have hgs : w.cursor.y < w.clearPending.grid.size := by
    show w.cursor.y < w.grid.size
    rw [hm.curY]; exact hm.inGrid
  have hrl : w.cursor.x + 1 < (w.clearPending.getRow w.cursor.y).size := by
    show w.cursor.x + 1 < (w.getRow w.cursor.y).size
    rw [hm.curY, hm.rowLen, hx]; omega
  have hpenW : ({ base := (g.at k).base, marks := [], width := 2, pen := w.pen } : Cell).pen
      = (g.at k).pen := hm.pen.trans hpen.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfeed, hcur]; show w.cursor.x + 2 = k + 2; rw [hx]
  · rw [hfeed, hcur]; show w.cursor.y = P.y; exact hm.curY
  · rw [hfeed, hcur]
  · rw [hfeed, pen_print]; exact hm.pen
  · rw [hfeed, Zmx.Core.Vt.ps_print]; exact hm.ground
  · rw [hfeed, Zmx.Core.Vt.un_print]; exact hm.u8need
  · rw [hfeed, ua_print']; exact hm.u8acc
  · rw [hfeed, ins_print]; exact hm.ins
  · rw [hfeed, wrap_print]; exact hm.wrap
  · rw [hfeed, g0_print]; exact hm.ascii0
  · rw [hfeed, g1_print]; exact hm.ascii1
  · show ((w.feed (cellText (g.at k))).getRow P.y).size = (w.feed (cellText (g.at k))).cols
    rw [hfeed, hwrite]
    obtain ⟨hcl, -, hrw⟩ := write_shape2 w.clearPending w.cursor.x w.cursor.y
      { base := (g.at k).base, marks := [], width := 2, pen := w.pen }
      (Cell.shadow { base := (g.at k).base, marks := [], width := 2, pen := w.pen }) 2 hgs
    rw [hcl, hrw P.y]
    show (w.getRow P.y).size = w.cols
    exact hm.rowLen
  · show P.y < (w.feed (cellText (g.at k))).grid.size
    rw [hfeed, hwrite]
    obtain ⟨-, hgz, -⟩ := write_shape2 w.clearPending w.cursor.x w.cursor.y
      { base := (g.at k).base, marks := [], width := 2, pen := w.pen }
      (Cell.shadow { base := (g.at k).base, marks := [], width := 2, pen := w.pen }) 2 hgs
    rw [hgz]
    show P.y < w.grid.size
    exact hm.inGrid
  · -- the frontier moves past the shadow, whose width is 0
    refine Or.inr ?_
    rw [show k + 2 - 1 = k + 1 from by omega, hsh]
    show (0 : Nat) ≠ 2
    decide
  · intro j hj
    show (w.feed (cellText (g.at k))).getCell j P.y = g.at j
    rw [hfeed, hwrite, getCell_printAdvance, show P.y = w.cursor.y from hm.curY.symm]
    rcases Nat.lt_or_ge j k with hjk | hjk
    · -- the prefix: both writes are above it, then the sweep keeps it
      have hcellsW : ∀ i, i < k →
          ((w.clearPending.putCell w.cursor.x w.cursor.y { base := (g.at k).base, marks := [], width := 2, pen := w.pen }).putCell
            (w.cursor.x + 1) w.cursor.y (Cell.shadow { base := (g.at k).base, marks := [], width := 2, pen := w.pen })).getCell i w.cursor.y = g.at i := by
        intro i hi
        show (((w.clearPending.putCell w.cursor.x w.cursor.y { base := (g.at k).base, marks := [], width := 2, pen := w.pen }).putCell
          (w.cursor.x + 1) w.cursor.y (Cell.shadow { base := (g.at k).base, marks := [], width := 2, pen := w.pen })).getRow w.cursor.y).at i = g.at i
        rw [at_putCell_ne _ _ _ _ i (by omega) (by rw [grid_size_putCell]; exact hgs),
          at_putCell_ne _ _ _ _ i (by omega) hgs]
        show w.getCell i w.cursor.y = g.at i
        rw [hm.curY]
        exact hm.cells i hi
      have hgsW : w.cursor.y <
          ((w.clearPending.putCell w.cursor.x w.cursor.y { base := (g.at k).base, marks := [], width := 2, pen := w.pen }).putCell
            (w.cursor.x + 1) w.cursor.y (Cell.shadow { base := (g.at k).base, marks := [], width := 2, pen := w.pen })).grid.size := by
        rw [grid_size_putCell, grid_size_putCell]; exact hgs
      exact mend_keeps_prefix
        (u := (w.clearPending.putCell w.cursor.x w.cursor.y { base := (g.at k).base, marks := [], width := 2, pen := w.pen }).putCell
          (w.cursor.x + 1) w.cursor.y (Cell.shadow { base := (g.at k).base, marks := [], width := 2, pen := w.pen }))
        hrow hcellsW hm.frontier hgsW j hjk
    · -- the pair itself
      rw [hx] at hrl ⊢
      obtain ⟨h0, h1⟩ := getCell_write_mendRow_wide w.clearPending k w.cursor.y
        { base := (g.at k).base, marks := [], width := 2, pen := w.pen } rfl hgs hrl
      rcases Nat.lt_or_ge j (k + 1) with hj1 | hj1
      · have hjk0 : j = k := by omega
        subst hjk0
        rw [h0]
        exact Cell.ext' rfl hmk.symm hwid.symm (hm.pen.trans hpen.symm)
      · have hjk1 : j = k + 1 := by omega
        subst hjk1
        rw [h1]
        exact (shadow_congr hpenW).trans hsh.symm

/-- **A pen change.** `rowAnsi` emits `penSgr c.pen` before a cell whose pen differs from
the one it is carrying, and that is the whole of the SGR handling: the glyph bytes carry no
colour, so the cell the receiver *stores* takes the receiver's current pen
(`Vt.printPut`). This rung is what makes the cell rungs' `hpen` hypothesis discharegable,
and it is where the invariant's `pen` field earns its keep. -/
theorem step_pen {w : Vt} {P : PaintState} {g : Row} {k : Nat} (hm : Matches w P g k)
    (p : Pen) : Matches (w.feed (penSgr p)) { P with pen := p } g k := by
  have heq : w.feed (penSgr p) = { w with pen := p } := penSgr_feed p hm.ground hm.u8need
  -- the pen is in `getRow`'s *default* row, so a cell read only survives because the
  -- invariant says the row index is in the grid
  have hcell : ∀ j, ({ w with pen := p } : Vt).getCell j P.y = w.getCell j P.y := by
    intro j
    show (((({ w with pen := p } : Vt)).grid.getD P.y
        (blankRow ({ w with pen := p } : Vt).cols p)).getD j default)
      = ((w.grid.getD P.y (blankRow w.cols w.pen)).getD j default)
    rw [getD_of_lt w.grid P.y (blankRow w.cols p) (blankRow w.cols w.pen) hm.inGrid]
  have hrow : (({ w with pen := p } : Vt).getRow P.y) = w.getRow P.y := by
    show ((({ w with pen := p } : Vt)).grid.getD P.y
        (blankRow ({ w with pen := p } : Vt).cols p)) = w.grid.getD P.y (blankRow w.cols w.pen)
    rw [getD_of_lt w.grid P.y (blankRow w.cols p) (blankRow w.cols w.pen) hm.inGrid]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [heq]; exact hm.curX
  · rw [heq]; exact hm.curY
  · rw [heq]; exact hm.pend
  · rw [heq]
  · rw [heq]; exact hm.ground
  · rw [heq]; exact hm.u8need
  · rw [heq]; exact hm.u8acc
  · rw [heq]; exact hm.ins
  · rw [heq]; exact hm.wrap
  · rw [heq]; exact hm.ascii0
  · rw [heq]; exact hm.ascii1
  · rw [heq, hrow]; exact hm.rowLen
  · rw [heq]; exact hm.inGrid
  · exact hm.frontier
  · intro j hj
    rw [heq, hcell j]
    exact hm.cells j hj

/-- **The shadow slot emits nothing.** `rowAnsi`'s fold visits a width-0 cell and appends
`utf8s c.marks`, which for a shadow is empty — so the pair's second column needs no rung
of its own, which is exactly why `step_wide` had to advance the frontier by two. Stated
about the source row rather than assumed: `RowOk.pairs` is what makes a shadow's marks
empty, and `rowAnsi`'s width-0 branch is defensive code for a decoded checkpoint that has
no such guarantee. -/
theorem shadow_emits_nothing {g : Row} {k : Nat} (hrow : RowOk g.size g)
    (hwid : (g.at k).width = 2) : utf8s (g.at (k + 1)).marks = [] := by
  rw [(hrow.pairs k).1 hwid]
  rfl

/-! ### The mark loop

A cell's marks are printed one at a time *after* its base glyph, and each one lands on
a cell the previous rung already painted. So the loop does not move the frontier — it
refines what sits below it, and the honest way to say that is to move the **source
row**: after `n` marks the receiver agrees with `withMarks g k (ms.take n)`, and after
all of them with `g` itself. Reusing `Matches` this way is what keeps the fifteen-field
bookkeeping out of the loop; a bespoke mid-cell invariant would have restated it. -/

/-- The source row with column `k`'s marks replaced. -/
def withMarks (g : Row) (k : Nat) (ms : List Char) : Row :=
  g.setIfInBounds k { g.at k with marks := ms }

theorem size_withMarks (g : Row) (k : Nat) (ms : List Char) :
    (withMarks g k ms).size = g.size := by
  simp [withMarks]

/-- Out of range it is the identity, which is why no lemma here needs a column bound
except the one that reads column `k` back. -/
theorem withMarks_of_ge (g : Row) (k : Nat) (ms : List Char) (h : g.size ≤ k) :
    withMarks g k ms = g := by
  simp [withMarks, Array.setIfInBounds, Nat.not_lt.mpr h]

theorem at_withMarks_self (g : Row) (k : Nat) (ms : List Char) (hk : k < g.size) :
    (withMarks g k ms).at k = { g.at k with marks := ms } := by
  unfold withMarks Row.at
  exact getD_set_self g k _ default hk

theorem at_withMarks_ne (g : Row) (k : Nat) (ms : List Char) (j : Nat) (h : j ≠ k) :
    (withMarks g k ms).at j = g.at j := by
  unfold withMarks Row.at
  exact getD_set_ne g k j _ default h

/-- **`withMarks` rewrites nothing but a mark list.** Every column keeps its base, its
width and its pen — which is what makes the truncated row still pair-consistent, and
`Cell.shadow` (a blank carrying the base's pen) unchanged. -/
theorem withMarks_keeps (g : Row) (k : Nat) (ms : List Char) (x : Nat) :
    ((withMarks g k ms).at x).base = (g.at x).base
      ∧ ((withMarks g k ms).at x).width = (g.at x).width
      ∧ ((withMarks g k ms).at x).pen = (g.at x).pen := by
  by_cases hx : x = k
  · subst hx
    by_cases hk : x < g.size
    · rw [at_withMarks_self g x ms hk]
      exact ⟨rfl, rfl, rfl⟩
    · rw [withMarks_of_ge g x ms (by omega)]
      exact ⟨rfl, rfl, rfl⟩
  · rw [at_withMarks_ne g k ms x hx]
    exact ⟨rfl, rfl, rfl⟩

/-- The truncated row is still one a repaint can reproduce.

`hwid` is what the pair clause needs, and the spec named it before the proof: column
`k` is a glyph — never a shadow — so it is not the second half of anything, and the
only column whose *content* the pair rule constrains is a shadow. Its own shadow (if
it has one) is untouched and still canonical, because `Cell.shadow` reads the pen and
nothing else. -/
theorem rowOk_withMarks {cols : Nat} {g : Row} {k : Nat} {ms : List Char}
    (hrow : RowOk cols g) (hwid : (g.at k).width ≠ 0)
    (hlen : ms.length ≤ 8) (hmk : ∀ m ∈ ms, charWidth m = 0 ∧ Emittable m) :
    RowOk cols (withMarks g k ms) := by
  refine ⟨by rw [size_withMarks]; exact hrow.size, fun x => ?_, fun x => ?_⟩
  · by_cases hx : x = k
    · subst hx
      by_cases hk : x < g.size
      · rw [at_withMarks_self g x ms hk]
        exact ⟨(hrow.cells x).base, (hrow.cells x).width, hlen, hmk⟩
      · rw [withMarks_of_ge g x ms (by omega)]
        exact hrow.cells x
    · rw [at_withMarks_ne g k ms x hx]
      exact hrow.cells x
  · obtain ⟨-, hw, hp⟩ := withMarks_keeps g k ms x
    refine ⟨fun h2 => ?_, fun h0 => ?_⟩
    · have h2' : (g.at x).width = 2 := by rw [← hw]; exact h2
      have hsh : g.at (x + 1) = Cell.shadow (g.at x) := (hrow.pairs x).1 h2'
      -- column `k` is a glyph, so it is not this pair's shadow — hence untouched
      have hne : x + 1 ≠ k := by
        intro hc
        rw [← hc, hsh] at hwid
        exact hwid rfl
      rw [at_withMarks_ne g k ms (x + 1) hne, hsh]
      exact (shadow_congr hp).symm
    · have h0' : (g.at x).width = 0 := by rw [← hw]; exact h0
      obtain ⟨hne0, hpr⟩ := (hrow.pairs x).2 h0'
      exact ⟨hne0, by rw [(withMarks_keeps g k ms (x - 1)).2.1]; exact hpr⟩

/-- **`Matches … k` reads the source row only below `k`.** So a rung may swap the row
out from under it for any row that agrees there — which is how the mark loop enters
(against `withMarks g k []`, the cell as the base glyph alone leaves it) and how it
leaves (against `g`, once every mark is on). -/
theorem matches_below {w : Vt} {P : PaintState} {g g' : Row} {k : Nat}
    (h : ∀ j, j < k → g'.at j = g.at j) (hm : Matches w P g k) : Matches w P g' k := by
  refine ⟨hm.curX, hm.curY, hm.pend, hm.pen, hm.ground, hm.u8need, hm.u8acc, hm.ins,
    hm.wrap, hm.ascii0, hm.ascii1, hm.rowLen, hm.inGrid, ?_, ?_⟩
  · by_cases hk : k = 0
    · exact Or.inl hk
    · rcases hm.frontier with hz | hne
      · exact Or.inl hz
      · exact Or.inr (by rw [h (k - 1) (by omega)]; exact hne)
  · intro j hj
    rw [h j hj]
    exact hm.cells j hj

/-- Full pointwise agreement, for the loop's *exit*: after every mark is on, the
receiver matches `withMarks g k (g.at k).marks`, which reads back as `g` at every
column. -/
theorem matches_row_congr {w : Vt} {P : PaintState} {g g' : Row} {k : Nat}
    (h : ∀ j, g'.at j = g.at j) (hm : Matches w P g' k) : Matches w P g k := by
  refine ⟨hm.curX, hm.curY, hm.pend, hm.pen, hm.ground, hm.u8need, hm.u8acc, hm.ins,
    hm.wrap, hm.ascii0, hm.ascii1, hm.rowLen, hm.inGrid, ?_, ?_⟩
  · rcases hm.frontier with hz | hne
    · exact Or.inl hz
    · exact Or.inr (by rw [← h (k - 1)]; exact hne)
  · intro j hj
    rw [← h j]
    exact hm.cells j hj

/-- **`Matches` survives a `CHA`.** The receiver stays matched to the same row `g` at the
same frontier `kf`; only the paint state's column moves (clamped to the margin) and
wrap-pending clears. This is the cursor park the wide-with-marks branch does twice. -/
theorem cha_matches {w : Vt} {P : PaintState} {g : Row} {kf n : Nat}
    (hm : Matches w P g kf) (hn : 0 < n) (hlt : n < 65535) :
    Matches (w.feed (csiNum n 0x47))
      { P with x := min (n - 1) (w.cols - 1), pending := false } g kf := by
  rw [cha_feed_eq n hm.ground hm.u8need hn hlt]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (w.setCol (n - 1)).cursor.x = min (n - 1) (w.cols - 1)
    unfold Vt.setCol; rfl
  · show (w.setCol (n - 1)).cursor.y = P.y
    rw [show (w.setCol (n - 1)).cursor.y = w.cursor.y from rfl]; exact hm.curY
  · show (w.setCol (n - 1)).cursor.pending = false
    unfold Vt.setCol; rfl
  · show (w.setCol (n - 1)).pen = P.pen
    rw [show (w.setCol (n - 1)).pen = w.pen from by rw [frame_setCol]]; exact hm.pen
  · rw [Zmx.Core.Vt.ps_setCol]; exact hm.ground
  · rw [Zmx.Core.Vt.un_setCol]; exact hm.u8need
  · show (w.setCol (n - 1)).u8acc = 0
    rw [show (w.setCol (n - 1)).u8acc = w.u8acc from by rw [frame_setCol]]; exact hm.u8acc
  · show (w.setCol (n - 1)).modes.insert = false
    rw [show (w.setCol (n - 1)).modes = w.modes from by rw [frame_setCol]]; exact hm.ins
  · show (w.setCol (n - 1)).modes.wrap = true
    rw [show (w.setCol (n - 1)).modes = w.modes from by rw [frame_setCol]]; exact hm.wrap
  · show (w.setCol (n - 1)).g0Line = false
    rw [show (w.setCol (n - 1)).g0Line = w.g0Line from by rw [frame_setCol]]; exact hm.ascii0
  · show (w.setCol (n - 1)).g1Line = false
    rw [show (w.setCol (n - 1)).g1Line = w.g1Line from by rw [frame_setCol]]; exact hm.ascii1
  · show ((w.setCol (n - 1)).getRow P.y).size = (w.setCol (n - 1)).cols
    rw [show (w.setCol (n - 1)).getRow P.y = w.getRow P.y from by
        unfold Vt.getRow; rw [frame_setCol],
      show (w.setCol (n - 1)).cols = w.cols from by rw [frame_setCol]]
    exact hm.rowLen
  · show P.y < (w.setCol (n - 1)).grid.size
    rw [show (w.setCol (n - 1)).grid = w.grid from by rw [frame_setCol]]; exact hm.inGrid
  · exact hm.frontier
  · intro j hj
    show (w.setCol (n - 1)).getCell j P.y = g.at j
    rw [show (w.setCol (n - 1)).getCell j P.y = w.getCell j P.y from by
      unfold Vt.getCell Vt.getRow; rw [frame_setCol]]
    exact hm.cells j hj

/-- `CHA` to an **in-range** column: no clamp, so the paint state's column is exactly
`n - 1`. This is the form the wide-with-marks branch uses — both its jumps land inside the
row (`k + 1` for the mark, `k + 2` past the pair), which is what `k + 2 < cols` gives. -/
theorem cha_matches_lt {w : Vt} {P : PaintState} {g : Row} {kf n : Nat}
    (hm : Matches w P g kf) (hn : 0 < n) (hlt : n < 65535) (hin : n - 1 < w.cols) :
    Matches (w.feed (csiNum n 0x47)) { P with x := n - 1, pending := false } g kf := by
  have h := cha_matches hm hn hlt
  rwa [show min (n - 1) (w.cols - 1) = n - 1 from by omega] at h

/-- The marks fold preserves the column count — each `print` does (`cols_print`), so the
whole walk does. Needed to keep the `CHA` bounds in range across the mark run. -/
theorem foldl_print_cols (l : List Char) (u : Vt) :
    (l.foldl (fun w c => w.print (safeChar c)) u).cols = u.cols := by
  induction l generalizing u with
  | nil => rfl
  | cons a l ih => rw [List.foldl_cons, ih]; exact cols_print u (safeChar a)

/-- `CHA` moves only the cursor, so the column count is unchanged — the wide-with-marks
branch keeps its `CHA` bounds in range across the whole sequence. -/
theorem cha_cols {v : Vt} (n : Nat) (hg : v.pstate = .ground) (hu : v.u8need = 0)
    (hn : 0 < n) (hlt : n < 65535) : (v.feed (csiNum n 0x47)).cols = v.cols := by
  rw [cha_feed_eq n hg hu hn hlt, frame_setCol]

/-- `safeChar` is the identity on a list of emittable marks, so the marks the painter
re-emits are exactly the ones the cell stored. -/
theorem map_safeChar_id : ∀ (l : List Char), (∀ x ∈ l, Emittable x) → l.map safeChar = l
  | [], _ => rfl
  | a :: l, h => by
    rw [List.map_cons, safeChar_of_emittable (h a (List.mem_cons_self)),
      map_safeChar_id l (fun x hx => h x (List.mem_cons_of_mem a hx))]

set_option maxHeartbeats 1000000 in
/-- **One mark lands on column `wcol` and moves nothing.** The receiver's row already
agrees with `withMarks g wcol done` (the source cell with only the marks seen so far, at a
frontier `kf` already past it); one more `print (safeChar m)` extends that to
`withMarks g wcol (done ++ [safeChar m])`.

The write column `wcol` is separate from the frontier `kf` so that this one lemma serves
both the narrow cell (`wcol = k`, `kf = k + 1`) and the marks of a **wide** glyph
(`wcol = k`, `kf = k + 2`): there the first `CHA` parked the cursor at `k + 1`, one past
the base, so the mark still attaches to the base at `k` while the frontier already covers
the shadow.

`hdisj` is the one fact that distinguishes where the cursor sits: interior — one column
right of the write, wrap-pending clear (a narrow cell that advanced, or a `CHA` that
placed the cursor); at the margin — *on* the write column with wrap-pending, which is why
`print_mark_pending_eq` had to exist. Both write `wcol`, so the tail is shared. -/
theorem mark_step {cols : Nat} {w : Vt} {Q : PaintState} {g : Row} {wcol kf : Nat}
    {done : List Char}
    (hrow : RowOk cols g) (hcols : w.cols = cols) (hwid : (g.at wcol).width ≠ 0)
    (hwcol : wcol < cols) (hlt : wcol < kf)
    (hdisj : (Q.x = wcol + 1 ∧ Q.pending = false) ∨ (Q.x = wcol ∧ Q.pending = true))
    (hcap : done.length < 8) (hdone : ∀ x ∈ done, charWidth x = 0 ∧ Emittable x)
    (hm : Matches w Q (withMarks g wcol done) kf)
    (m : Char) (hmw : charWidth m = 0) (hme : Emittable m) :
    Matches (w.print (safeChar m)) Q (withMarks g wcol (done ++ [safeChar m])) kf := by
  have hsafe : safeChar m = m := safeChar_of_emittable hme
  have hcw : charWidth (safeChar m) = 0 := by rw [hsafe]; exact hmw
  have hpc : w.printChar (safeChar m) = safeChar m := printChar_id_of_ascii hm.ascii0 hm.ascii1
    (by rw [hsafe]; exact hme.1) (by rw [hsafe]; exact hme.2)
  have hkg : wcol < g.size := by rw [hrow.size]; exact hwcol
  have hgetk : w.getCell wcol Q.y = { g.at wcol with marks := done } := by
    rw [hm.cells wcol hlt, at_withMarks_self g wcol done hkg]
  have hyk : w.cursor.y = Q.y := hm.curY
  have hgs : Q.y < w.grid.size := hm.inGrid
  have hwk0 : (w.getCell wcol Q.y).width ≠ 0 := by rw [hgetk]; exact hwid
  have hcapk : (w.getCell wcol Q.y).marks.length < 8 := by
    rw [hgetk]; show done.length < 8; exact hcap
  have hcelleq : ({ w.getCell wcol Q.y with marks := (w.getCell wcol Q.y).marks ++ [safeChar m] }
      : Cell) = { g.at wcol with marks := done ++ [safeChar m] } := by rw [hgetk]
  -- the write, whichever branch: the source cell with one more mark
  obtain ⟨hpm, hcur⟩ :
      w.print (safeChar m)
          = (w.putCell wcol Q.y { g.at wcol with marks := done ++ [safeChar m] }).mendRow Q.y
        ∧ (w.print (safeChar m)).cursor = w.cursor := by
    rcases hdisj with ⟨hQx, hQp⟩ | ⟨hQx, hQp⟩
    · have hx : w.cursor.x = wcol + 1 := by rw [hm.curX, hQx]
      have hpd : w.cursor.pending = false := by rw [hm.pend, hQp]
      have hx1 : w.cursor.x - 1 = wcol := by omega
      have hnw : (w.getCell (w.cursor.x - 1) w.cursor.y).width ≠ 0 := by rw [hx1, hyk]; exact hwk0
      have hcapp : (w.getCell (w.cursor.x - 1) w.cursor.y).marks.length < 8 := by
        rw [hx1, hyk]; exact hcapk
      exact ⟨by rw [print_mark_eq hpc hcw hpd (by omega) hnw hcapp, hx1, hyk, hcelleq],
        cursor_print_mark hpc hcw hpd (by omega) hnw hcapp⟩
    · have hx : w.cursor.x = wcol := by rw [hm.curX, hQx]
      have hpd : w.cursor.pending = true := by rw [hm.pend, hQp]
      have hnw : (w.getCell w.cursor.x w.cursor.y).width ≠ 0 := by rw [hx, hyk]; exact hwk0
      have hcapp : (w.getCell w.cursor.x w.cursor.y).marks.length < 8 := by rw [hx, hyk]; exact hcapk
      exact ⟨by rw [print_mark_pending_eq hpc hcw hpd hnw hcapp, hx, hyk, hcelleq],
        cursor_print_mark_pending hpc hcw hpd hnw hcapp⟩
  -- the source row after this mark, and that it is still reproducible
  have hmv : ∀ x ∈ done ++ [safeChar m], charWidth x = 0 ∧ Emittable x := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact hdone x h
    · rw [List.mem_singleton.mp h, hsafe]; exact ⟨hmw, hme⟩
  have hrowW : RowOk w.cols (withMarks g wcol (done ++ [safeChar m])) := by
    rw [hcols]
    exact rowOk_withMarks hrow hwid
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hmv
  have hgsW : Q.y
      < (w.putCell wcol Q.y { g.at wcol with marks := done ++ [safeChar m] }).grid.size := by
    rw [grid_size_putCell]; exact hgs
  -- the frontier at `kf - 1` is a *width*, and `withMarks` never changes a width
  have hfront : kf = 0 ∨ ((withMarks g wcol (done ++ [safeChar m])).at (kf - 1)).width ≠ 2 := by
    rcases hm.frontier with hz | hne
    · exact Or.inl hz
    · refine Or.inr ?_
      rw [(withMarks_keeps g wcol (done ++ [safeChar m]) (kf - 1)).2.1]
      rw [(withMarks_keeps g wcol done (kf - 1)).2.1] at hne
      exact hne
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfront, ?_⟩
  · rw [hcur]; exact hm.curX
  · rw [hcur]; exact hm.curY
  · rw [hcur]; exact hm.pend
  · rw [pen_print]; exact hm.pen
  · rw [Zmx.Core.Vt.ps_print]; exact hm.ground
  · rw [Zmx.Core.Vt.un_print]; exact hm.u8need
  · rw [ua_print']; exact hm.u8acc
  · rw [ins_print]; exact hm.ins
  · rw [wrap_print]; exact hm.wrap
  · rw [g0_print]; exact hm.ascii0
  · rw [g1_print]; exact hm.ascii1
  · show ((w.print (safeChar m)).getRow Q.y).size = (w.print (safeChar m)).cols
    rw [hpm,
      show ((w.putCell wcol Q.y { g.at wcol with marks := done ++ [safeChar m] }).mendRow Q.y).cols
          = w.cols from by rw [frame_mendRow, frame_putCell],
      size_getRow_mendRow _ Q.y hgsW Q.y,
      size_getRow_putCell_any w wcol Q.y { g.at wcol with marks := done ++ [safeChar m] } hgs Q.y]
    exact hm.rowLen
  · show Q.y < (w.print (safeChar m)).grid.size
    rw [hpm, grid_size_mendRow, grid_size_putCell]; exact hgs
  · intro j hj
    show (w.print (safeChar m)).getCell j Q.y = (withMarks g wcol (done ++ [safeChar m])).at j
    rw [hpm]
    have hcellsW : ∀ i, i < kf →
        (w.putCell wcol Q.y { g.at wcol with marks := done ++ [safeChar m] }).getCell i Q.y
          = (withMarks g wcol (done ++ [safeChar m])).at i := by
      intro i hi
      show ((w.putCell wcol Q.y { g.at wcol with marks := done ++ [safeChar m] }).getRow Q.y).at i
        = (withMarks g wcol (done ++ [safeChar m])).at i
      by_cases hiw : i = wcol
      · rw [hiw, getRow_putCell_self w wcol Q.y { g.at wcol with marks := done ++ [safeChar m] } hgs
            (by rw [hm.rowLen, hcols]; exact hwcol),
          at_withMarks_self g wcol (done ++ [safeChar m]) hkg]
      · rw [at_putCell_ne w wcol Q.y { g.at wcol with marks := done ++ [safeChar m] } i hiw hgs]
        show w.getCell i Q.y = _
        rw [hm.cells i hi, at_withMarks_ne g wcol done i hiw,
          at_withMarks_ne g wcol (done ++ [safeChar m]) i hiw]
    exact mend_keeps_prefix
      (u := w.putCell wcol Q.y { g.at wcol with marks := done ++ [safeChar m] })
      hrowW hcellsW hfront hgsW j hj

set_option maxHeartbeats 1000000 in
/-- **The mark loop.** Fold `mark_step` over the marks not yet emitted: the receiver's
row grows from `withMarks g wcol acc` to `withMarks g wcol (acc ++ rest.map safeChar)`, and
the paint state `Q` never moves because a mark moves no cursor. `cols` is fixed once; each
step's receiver keeps it (`cols_print`), which is what lets the one `RowOk cols g` serve
the whole fold. -/
theorem marks_fold {cols : Nat} {Q : PaintState} {g : Row} {wcol kf : Nat}
    (hrow : RowOk cols g) (hwid : (g.at wcol).width ≠ 0) (hwcol : wcol < cols) (hlt : wcol < kf)
    (hdisj : (Q.x = wcol + 1 ∧ Q.pending = false) ∨ (Q.x = wcol ∧ Q.pending = true)) :
    ∀ (rest : List Char) (u : Vt) (acc : List Char),
      (∀ x ∈ acc, charWidth x = 0 ∧ Emittable x) →
      (∀ x ∈ rest, charWidth x = 0 ∧ Emittable x) →
      acc.length + rest.length ≤ 8 →
      u.cols = cols →
      Matches u Q (withMarks g wcol acc) kf →
      Matches (rest.foldl (fun w c => w.print (safeChar c)) u) Q
        (withMarks g wcol (acc ++ rest.map safeChar)) kf
  | [], u, acc, _, _, _, _, hu => by simpa using hu
  | m :: rest, u, acc, hacc, hrest, hlen, hucols, hu => by
    have hmm := hrest m (List.mem_cons_self)
    have hstep := mark_step (w := u) (cols := cols) hrow hucols hwid hwcol hlt hdisj
      (by simp only [List.length_cons] at hlen; omega) hacc hu m hmm.1 hmm.2
    have hacc' : ∀ x ∈ acc ++ [safeChar m], charWidth x = 0 ∧ Emittable x := by
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact hacc x h
      · rw [List.mem_singleton.mp h, safeChar_of_emittable hmm.2]; exact hmm
    have hucols' : (u.print (safeChar m)).cols = cols := by rw [cols_print]; exact hucols
    have hrec := marks_fold hrow hwid hwcol hlt hdisj rest (u.print (safeChar m))
      (acc ++ [safeChar m]) hacc' (fun x hx => hrest x (List.mem_cons_of_mem m hx))
      (by simp only [List.length_append, List.length_cons, List.length_nil] at hlen ⊢; omega)
      hucols' hstep
    simpa [List.foldl_cons, List.map_cons, List.append_assoc] using hrec

/-- **One narrow cell with its marks, in the interior.** `step_narrow` paints the base
glyph, leaving the receiver matching `withMarks g k []`; `marks_fold` then walks the
marks on. This is the rung `step_narrow` becomes once a cell may carry combining marks —
`step_narrow` is its `marks = []` special case, kept because the base step reuses it. -/
theorem step_narrow_marks {w : Vt} {P : PaintState} {g : Row} {k : Nat}
    (hrow : RowOk w.cols g) (hm : Matches w P g k)
    (hPx : P.x = k) (hpend : P.pending = false) (hfit : k + 1 < w.cols)
    (hwid : (g.at k).width = 1) (hpen : (g.at k).pen = P.pen) :
    Matches (w.feed (cellText (g.at k))) { P with x := k + 1, pending := false } g (k + 1) := by
  have hkg : k < g.size := by rw [hrow.size]; omega
  have hmks := (hrow.cells k).marks
  have hmle := (hrow.cells k).marksLe
  -- paint the base glyph on the row truncated to no marks at `k`
  have hrow0 : RowOk w.cols (withMarks g k []) :=
    rowOk_withMarks hrow (by rw [hwid]; decide) (by simp) (by simp)
  have hwid0 : ((withMarks g k []).at k).width = 1 := by rw [at_withMarks_self g k [] hkg]; exact hwid
  have hmk0 : ((withMarks g k []).at k).marks = [] := by rw [at_withMarks_self g k [] hkg]
  have hpen0 : ((withMarks g k []).at k).pen = P.pen := by
    rw [at_withMarks_self g k [] hkg]; exact hpen
  have hm0 : Matches w P (withMarks g k []) k :=
    matches_below (fun j hj => at_withMarks_ne g k [] j (by omega)) hm
  have hbase := step_narrow hrow0 hm0 hPx hpend hfit hwid0 hmk0 hpen0
  -- the base glyph of `g`'s cell is `cellText` of the truncated cell
  have hbtext : cellText ((withMarks g k []).at k) = utf8 (safeChar (g.at k).base) := by
    rw [at_withMarks_self g k [] hkg]
    show utf8 (safeChar (g.at k).base) ++ utf8s [] = utf8 (safeChar (g.at k).base)
    simp [utf8s]
  rw [hbtext] at hbase
  -- so the full cellText is the base glyph then the marks; feed splits there
  have hct : cellText (g.at k) = utf8 (safeChar (g.at k).base) ++ utf8s (g.at k).marks := rfl
  rw [hct, feed_append]
  have hucols : (w.feed (utf8 (safeChar (g.at k).base))).cols = w.cols := by
    rw [utf8_feed (safeChar (g.at k).base) (safeChar_ge (g.at k).base).1
      hm.ground hm.u8need hm.u8acc]
    exact cols_print w (safeChar (g.at k).base)
  rw [utf8s_feed (g.at k).marks hbase.ground hbase.u8need hbase.u8acc]
  have hfold := marks_fold (Q := { P with x := k + 1, pending := false }) hrow
    (by rw [hwid]; decide) (by omega : k < w.cols) (by omega : k < k + 1)
    (Or.inl ⟨rfl, rfl⟩) (g.at k).marks
    (w.feed (utf8 (safeChar (g.at k).base))) []
    (by simp) hmks (by simpa using hmle) hucols hbase
  rw [map_safeChar_id (g.at k).marks (fun x hx => (hmks x hx).2)] at hfold
  simp only [List.nil_append] at hfold
  -- exit: the fully-marked truncated row reads back as `g` at every column
  refine matches_row_congr (fun j => ?_) hfold
  by_cases hjk : j = k
  · subst hjk; rw [at_withMarks_self g j (g.at j).marks hkg]
  · exact at_withMarks_ne g k (g.at k).marks j hjk

set_option maxHeartbeats 1000000 in
/-- **A wide glyph carrying its own marks — the `CHA`/`CHA` dance.** `rowSlot`'s
marked-wide branch is `glyph · CHA(k+2) · marks · CHA(k+3)`: the wide base advances the
cursor two, the first `CHA` parks it at `k + 1` (between glyph and shadow) so the marks
attach to the base at `k` rather than the shadow, and the second `CHA` steps it past the
pair to `k + 2`. Interior form (`k + 2 < cols`); the pair cannot sit at the very margin
because a width-2 base with no room for its shadow is stored as a blank (`printPut`), so
`RowOk` never presents one. `hcb` bounds the emitted column so `CHA` addresses it exactly
rather than clamping to 65535 — the column analogue of `restore_sticky_any`'s `hfits`. -/
theorem step_wide_marks {w : Vt} {P : PaintState} {g : Row} {k : Nat}
    (hrow : RowOk w.cols g) (hm : Matches w P g k)
    (hPx : P.x = k) (hpend : P.pending = false)
    (hfit : k + 1 < w.cols) (hfit2 : k + 2 < w.cols) (hcb : k + 3 < 65535)
    (hwid : (g.at k).width = 2) (hpen : (g.at k).pen = P.pen) :
    Matches (w.feed (utf8 (safeChar (g.at k).base) ++ csiNum (k + 2) 0x47
        ++ utf8s (g.at k).marks ++ csiNum (k + 3) 0x47))
      { P with x := k + 2, pending := false } g (k + 2) := by
  have hkg : k < g.size := by rw [hrow.size]; omega
  have hmks := (hrow.cells k).marks
  have hmle := (hrow.cells k).marksLe
  -- the wide base, painted on the row with `k`'s marks stripped
  have hrow0 : RowOk w.cols (withMarks g k []) :=
    rowOk_withMarks hrow (by rw [hwid]; decide) (by simp) (by simp)
  have hwid0 : ((withMarks g k []).at k).width = 2 := by rw [at_withMarks_self g k [] hkg]; exact hwid
  have hmk0 : ((withMarks g k []).at k).marks = [] := by rw [at_withMarks_self g k [] hkg]
  have hpen0 : ((withMarks g k []).at k).pen = P.pen := by
    rw [at_withMarks_self g k [] hkg]; exact hpen
  have hm0 : Matches w P (withMarks g k []) k :=
    matches_below (fun j hj => at_withMarks_ne g k [] j (by omega)) hm
  have hbase := step_wide hrow0 hm0 hPx hpend hfit hfit2 hwid0 hmk0 hpen0
  have hbtext : cellText ((withMarks g k []).at k) = utf8 (safeChar (g.at k).base) := by
    rw [at_withMarks_self g k [] hkg]
    show utf8 (safeChar (g.at k).base) ++ utf8s [] = utf8 (safeChar (g.at k).base)
    simp [utf8s]
  rw [hbtext] at hbase
  -- split the emitted bytes into base · CHA · marks · CHA
  rw [feed_append, feed_append, feed_append]
  have hw1cols : (w.feed (utf8 (safeChar (g.at k).base))).cols = w.cols := by
    rw [utf8_feed (safeChar (g.at k).base) (safeChar_ge (g.at k).base).1
      hm.ground hm.u8need hm.u8acc]
    exact cols_print w (safeChar (g.at k).base)
  -- CHA(k+2): park the cursor at k+1, between glyph and shadow
  have hcha1 := cha_matches_lt (n := k + 2) hbase (by omega) (by omega)
    (by rw [hw1cols]; omega)
  rw [show k + 2 - 1 = k + 1 from by omega] at hcha1
  have hu2cols : ((w.feed (utf8 (safeChar (g.at k).base))).feed (csiNum (k + 2) 0x47)).cols
      = w.cols := by
    rw [cha_cols (k + 2) hbase.ground hbase.u8need (by omega) (by omega)]; exact hw1cols
  -- the marks land on the base
  rw [utf8s_feed (g.at k).marks hcha1.ground hcha1.u8need hcha1.u8acc]
  have hfold := marks_fold (Q := { { P with x := k + 2, pending := false } with
      x := k + 1, pending := false }) hrow (by rw [hwid]; decide)
    (by omega : k < w.cols) (by omega : k < k + 2) (Or.inl ⟨rfl, rfl⟩)
    (g.at k).marks ((w.feed (utf8 (safeChar (g.at k).base))).feed (csiNum (k + 2) 0x47)) []
    (by simp) hmks (by simpa using hmle) hu2cols hcha1
  rw [map_safeChar_id (g.at k).marks (fun x hx => (hmks x hx).2)] at hfold
  simp only [List.nil_append] at hfold
  -- exit the mark loop back to `g`
  have hmg := matches_row_congr (g := g)
    (fun j => by
      by_cases hjk : j = k
      · subst hjk; rw [at_withMarks_self g j (g.at j).marks hkg]
      · exact at_withMarks_ne g k (g.at k).marks j hjk) hfold
  -- CHA(k+3): step past the pair to k+2
  have hcha2 := cha_matches_lt (n := k + 3) hmg (by omega) (by omega)
    (by rw [foldl_print_cols, hu2cols]; omega)
  rw [show k + 3 - 1 = k + 2 from by omega] at hcha2
  exact hcha2

/-- **A marked narrow cell at the right margin.** Base via `step_narrow_margin` (which
clamps the column and arms wrap-pending), then the mark loop through `hdisj`'s pending
branch — the marks attach *on* the cursor rather than one left of it. Row-exit shape:
`x = P.x` (unchanged, already `cols - 1`) with `pending := true`, left for the following
`carriageReturn` to discard. -/
theorem step_narrow_margin_marks {w : Vt} {P : PaintState} {g : Row} {k : Nat}
    (hrow : RowOk w.cols g) (hm : Matches w P g k)
    (hPx : P.x = k) (hpend : P.pending = false)
    (hk : k < w.cols) (hmar : w.cols ≤ k + 1)
    (hwid : (g.at k).width = 1) (hpen : (g.at k).pen = P.pen) :
    Matches (w.feed (cellText (g.at k))) { P with pending := true } g (k + 1) := by
  have hkg : k < g.size := by rw [hrow.size]; omega
  have hmks := (hrow.cells k).marks
  have hmle := (hrow.cells k).marksLe
  have hrow0 : RowOk w.cols (withMarks g k []) :=
    rowOk_withMarks hrow (by rw [hwid]; decide) (by simp) (by simp)
  have hwid0 : ((withMarks g k []).at k).width = 1 := by rw [at_withMarks_self g k [] hkg]; exact hwid
  have hmk0 : ((withMarks g k []).at k).marks = [] := by rw [at_withMarks_self g k [] hkg]
  have hpen0 : ((withMarks g k []).at k).pen = P.pen := by
    rw [at_withMarks_self g k [] hkg]; exact hpen
  have hm0 : Matches w P (withMarks g k []) k :=
    matches_below (fun j hj => at_withMarks_ne g k [] j (by omega)) hm
  have hbase := step_narrow_margin hrow0 hm0 hPx hpend hk hmar hwid0 hmk0 hpen0
  have hbtext : cellText ((withMarks g k []).at k) = utf8 (safeChar (g.at k).base) := by
    rw [at_withMarks_self g k [] hkg]
    show utf8 (safeChar (g.at k).base) ++ utf8s [] = utf8 (safeChar (g.at k).base)
    simp [utf8s]
  rw [hbtext] at hbase
  have hct : cellText (g.at k) = utf8 (safeChar (g.at k).base) ++ utf8s (g.at k).marks := rfl
  rw [hct, feed_append]
  have hucols : (w.feed (utf8 (safeChar (g.at k).base))).cols = w.cols := by
    rw [utf8_feed (safeChar (g.at k).base) (safeChar_ge (g.at k).base).1
      hm.ground hm.u8need hm.u8acc]
    exact cols_print w (safeChar (g.at k).base)
  rw [utf8s_feed (g.at k).marks hbase.ground hbase.u8need hbase.u8acc]
  have hfold := marks_fold (Q := { P with pending := true }) hrow
    (by rw [hwid]; decide) hk (by omega : k < k + 1)
    (Or.inr ⟨hPx, rfl⟩) (g.at k).marks
    (w.feed (utf8 (safeChar (g.at k).base))) []
    (by simp) hmks (by simpa using hmle) hucols hbase
  rw [map_safeChar_id (g.at k).marks (fun x hx => (hmks x hx).2)] at hfold
  simp only [List.nil_append] at hfold
  refine matches_row_congr (fun j => ?_) hfold
  by_cases hjk : j = k
  · subst hjk; rw [at_withMarks_self g j (g.at j).marks hkg]
  · exact at_withMarks_ne g k (g.at k).marks j hjk
set_option maxHeartbeats 1000000 in
/-- **A wide glyph whose shadow is the final column.** The pair fits (`k + 1 < cols`) but
ends at the margin (`cols ≤ k + 2`), so the advance clamps to `cols - 1` and arms
wrap-pending. The write is the same base-and-shadow as `step_wide`; only the cursor lands
differently. -/
theorem step_wide_margin {w : Vt} {P : PaintState} {g : Row} {k : Nat}
    (hrow : RowOk w.cols g) (hm : Matches w P g k)
    (hPx : P.x = k) (hpend : P.pending = false)
    (hfit : k + 1 < w.cols) (hmar : w.cols ≤ k + 2)
    (hwid : (g.at k).width = 2) (hmk : (g.at k).marks = [])
    (hpen : (g.at k).pen = P.pen) :
    Matches (w.feed (cellText (g.at k))) { P with x := w.cols - 1, pending := true } g (k + 2) := by
  have hem : Emittable (g.at k).base := (hrow.cells k).base
  have hpc : w.printChar (g.at k).base = (g.at k).base :=
    printChar_id_of_ascii hm.ascii0 hm.ascii1 hem.1 hem.2
  have hcw : charWidth (g.at k).base = 2 := by
    rw [(hrow.cells k).width (by rw [hwid]; omega), hwid]
  have hpd : w.cursor.pending = false := by rw [hm.pend, hpend]
  have hsh : g.at (k + 1) = Cell.shadow (g.at k) := (hrow.pairs k).1 hwid
  have hfeed : w.feed (cellText (g.at k)) = w.print (g.at k).base := by
    rw [cellText_feed (g.at k) hm.ground hm.u8need hm.u8acc, hmk, safeChar_of_emittable hem]
    rfl
  have hx : w.cursor.x = k := by rw [hm.curX, hPx]
  have hfitc : w.cursor.x + 1 < w.cols := by rw [hx]; exact hfit
  have hwrite := print_wide_eq hpc hcw hm.ins hpd hfitc
  have hcur := cursor_print_wide_margin hpc hcw hm.ins hpd hfitc (by rw [hx]; exact hmar)
  have hgs : w.cursor.y < w.clearPending.grid.size := by
    show w.cursor.y < w.grid.size
    rw [hm.curY]; exact hm.inGrid
  have hrl : w.cursor.x + 1 < (w.clearPending.getRow w.cursor.y).size := by
    show w.cursor.x + 1 < (w.getRow w.cursor.y).size
    rw [hm.curY, hm.rowLen, hx]; omega
  have hpenW : ({ base := (g.at k).base, marks := [], width := 2, pen := w.pen } : Cell).pen
      = (g.at k).pen := hm.pen.trans hpen.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfeed, hcur]
  · rw [hfeed, hcur]; show w.cursor.y = P.y; exact hm.curY
  · rw [hfeed, hcur]; show w.modes.wrap = true; exact hm.wrap
  · rw [hfeed, pen_print]; exact hm.pen
  · rw [hfeed, Zmx.Core.Vt.ps_print]; exact hm.ground
  · rw [hfeed, Zmx.Core.Vt.un_print]; exact hm.u8need
  · rw [hfeed, ua_print']; exact hm.u8acc
  · rw [hfeed, ins_print]; exact hm.ins
  · rw [hfeed, wrap_print]; exact hm.wrap
  · rw [hfeed, g0_print]; exact hm.ascii0
  · rw [hfeed, g1_print]; exact hm.ascii1
  · show ((w.feed (cellText (g.at k))).getRow P.y).size = (w.feed (cellText (g.at k))).cols
    rw [hfeed, hwrite]
    obtain ⟨hcl, -, hrw⟩ := write_shape2 w.clearPending w.cursor.x w.cursor.y
      { base := (g.at k).base, marks := [], width := 2, pen := w.pen }
      (Cell.shadow { base := (g.at k).base, marks := [], width := 2, pen := w.pen }) 2 hgs
    rw [hcl, hrw P.y]
    show (w.getRow P.y).size = w.cols
    exact hm.rowLen
  · show P.y < (w.feed (cellText (g.at k))).grid.size
    rw [hfeed, hwrite]
    obtain ⟨-, hgz, -⟩ := write_shape2 w.clearPending w.cursor.x w.cursor.y
      { base := (g.at k).base, marks := [], width := 2, pen := w.pen }
      (Cell.shadow { base := (g.at k).base, marks := [], width := 2, pen := w.pen }) 2 hgs
    rw [hgz]
    show P.y < w.grid.size
    exact hm.inGrid
  · refine Or.inr ?_
    rw [show k + 2 - 1 = k + 1 from by omega, hsh]
    show (0 : Nat) ≠ 2
    decide
  · intro j hj
    show (w.feed (cellText (g.at k))).getCell j P.y = g.at j
    rw [hfeed, hwrite, getCell_printAdvance, show P.y = w.cursor.y from hm.curY.symm]
    rcases Nat.lt_or_ge j k with hjk | hjk
    · have hcellsW : ∀ i, i < k →
          ((w.clearPending.putCell w.cursor.x w.cursor.y { base := (g.at k).base, marks := [], width := 2, pen := w.pen }).putCell
            (w.cursor.x + 1) w.cursor.y (Cell.shadow { base := (g.at k).base, marks := [], width := 2, pen := w.pen })).getCell i w.cursor.y = g.at i := by
        intro i hi
        show (((w.clearPending.putCell w.cursor.x w.cursor.y { base := (g.at k).base, marks := [], width := 2, pen := w.pen }).putCell
          (w.cursor.x + 1) w.cursor.y (Cell.shadow { base := (g.at k).base, marks := [], width := 2, pen := w.pen })).getRow w.cursor.y).at i = g.at i
        rw [at_putCell_ne _ _ _ _ i (by omega) (by rw [grid_size_putCell]; exact hgs),
          at_putCell_ne _ _ _ _ i (by omega) hgs]
        show w.getCell i w.cursor.y = g.at i
        rw [hm.curY]
        exact hm.cells i hi
      have hgsW : w.cursor.y <
          ((w.clearPending.putCell w.cursor.x w.cursor.y { base := (g.at k).base, marks := [], width := 2, pen := w.pen }).putCell
            (w.cursor.x + 1) w.cursor.y (Cell.shadow { base := (g.at k).base, marks := [], width := 2, pen := w.pen })).grid.size := by
        rw [grid_size_putCell, grid_size_putCell]; exact hgs
      exact mend_keeps_prefix
        (u := (w.clearPending.putCell w.cursor.x w.cursor.y { base := (g.at k).base, marks := [], width := 2, pen := w.pen }).putCell
          (w.cursor.x + 1) w.cursor.y (Cell.shadow { base := (g.at k).base, marks := [], width := 2, pen := w.pen }))
        hrow hcellsW hm.frontier hgsW j hjk
    · rw [hx] at hrl ⊢
      obtain ⟨h0, h1⟩ := getCell_write_mendRow_wide w.clearPending k w.cursor.y
        { base := (g.at k).base, marks := [], width := 2, pen := w.pen } rfl hgs hrl
      rcases Nat.lt_or_ge j (k + 1) with hj1 | hj1
      · have hjk0 : j = k := by omega
        subst hjk0
        rw [h0]
        exact Cell.ext' rfl hmk.symm hwid.symm (hm.pen.trans hpen.symm)
      · have hjk1 : j = k + 1 := by omega
        subst hjk1
        rw [h1]
        exact (shadow_congr hpenW).trans hsh.symm

set_option maxHeartbeats 1000000 in
/-- **A wide glyph carrying marks, whose shadow is the final column.** As `step_wide_marks`,
but the pair ends at the margin (`cols ≤ k + 2`): the base clamps (via `step_wide_margin`),
the first `CHA(k+2)` still parks in range at `k + 1 = cols - 1`, and the trailing `CHA(k+3)`
addresses `cols` and so **clamps** to `cols - 1` rather than reaching `k + 2`. Row-exit:
`x = cols - 1`, `pending := false` (the trailing `CHA` cleared it). -/
theorem step_wide_margin_marks {w : Vt} {P : PaintState} {g : Row} {k : Nat}
    (hrow : RowOk w.cols g) (hm : Matches w P g k)
    (hPx : P.x = k) (hpend : P.pending = false)
    (hfit : k + 1 < w.cols) (hmar : w.cols ≤ k + 2) (hcb : k + 3 < 65535)
    (hwid : (g.at k).width = 2) (hpen : (g.at k).pen = P.pen) :
    Matches (w.feed (utf8 (safeChar (g.at k).base) ++ csiNum (k + 2) 0x47
        ++ utf8s (g.at k).marks ++ csiNum (k + 3) 0x47))
      { P with x := w.cols - 1, pending := false } g (k + 2) := by
  have hkg : k < g.size := by rw [hrow.size]; omega
  have hmks := (hrow.cells k).marks
  have hmle := (hrow.cells k).marksLe
  have hrow0 : RowOk w.cols (withMarks g k []) :=
    rowOk_withMarks hrow (by rw [hwid]; decide) (by simp) (by simp)
  have hwid0 : ((withMarks g k []).at k).width = 2 := by rw [at_withMarks_self g k [] hkg]; exact hwid
  have hmk0 : ((withMarks g k []).at k).marks = [] := by rw [at_withMarks_self g k [] hkg]
  have hpen0 : ((withMarks g k []).at k).pen = P.pen := by
    rw [at_withMarks_self g k [] hkg]; exact hpen
  have hm0 : Matches w P (withMarks g k []) k :=
    matches_below (fun j hj => at_withMarks_ne g k [] j (by omega)) hm
  have hbase := step_wide_margin hrow0 hm0 hPx hpend hfit hmar hwid0 hmk0 hpen0
  have hbtext : cellText ((withMarks g k []).at k) = utf8 (safeChar (g.at k).base) := by
    rw [at_withMarks_self g k [] hkg]
    show utf8 (safeChar (g.at k).base) ++ utf8s [] = utf8 (safeChar (g.at k).base)
    simp [utf8s]
  rw [hbtext] at hbase
  rw [feed_append, feed_append, feed_append]
  have hw1cols : (w.feed (utf8 (safeChar (g.at k).base))).cols = w.cols := by
    rw [utf8_feed (safeChar (g.at k).base) (safeChar_ge (g.at k).base).1
      hm.ground hm.u8need hm.u8acc]
    exact cols_print w (safeChar (g.at k).base)
  -- CHA(k+2) still lands in range: k+1 = cols-1 < cols
  have hcha1 := cha_matches_lt (n := k + 2) hbase (by omega) (by omega)
    (by rw [hw1cols]; omega)
  rw [show k + 2 - 1 = k + 1 from by omega] at hcha1
  have hu2cols : ((w.feed (utf8 (safeChar (g.at k).base))).feed (csiNum (k + 2) 0x47)).cols
      = w.cols := by
    rw [cha_cols (k + 2) hbase.ground hbase.u8need (by omega) (by omega)]; exact hw1cols
  rw [utf8s_feed (g.at k).marks hcha1.ground hcha1.u8need hcha1.u8acc]
  have hfold := marks_fold (Q := { { P with x := w.cols - 1, pending := true } with
      x := k + 1, pending := false }) hrow (by rw [hwid]; decide)
    (by omega : k < w.cols) (by omega : k < k + 2) (Or.inl ⟨rfl, rfl⟩)
    (g.at k).marks ((w.feed (utf8 (safeChar (g.at k).base))).feed (csiNum (k + 2) 0x47)) []
    (by simp) hmks (by simpa using hmle) hu2cols hcha1
  rw [map_safeChar_id (g.at k).marks (fun x hx => (hmks x hx).2)] at hfold
  simp only [List.nil_append] at hfold
  have hmg := matches_row_congr (g := g)
    (fun j => by
      by_cases hjk : j = k
      · subst hjk; rw [at_withMarks_self g j (g.at j).marks hkg]
      · exact at_withMarks_ne g k (g.at k).marks j hjk) hfold
  have hu3cols : ((g.at k).marks.foldl (fun w c => w.print (safeChar c))
      ((w.feed (utf8 (safeChar (g.at k).base))).feed (csiNum (k + 2) 0x47))).cols = w.cols := by
    rw [foldl_print_cols]; exact hu2cols
  -- CHA(k+3) addresses `cols`, so it clamps to cols-1
  have hcha2 := cha_matches (n := k + 3) hmg (by omega) (by omega)
  rw [hu3cols, show min (k + 3 - 1) (w.cols - 1) = w.cols - 1 from by omega] at hcha2
  exact hcha2

/-! ### The row fold assembled — `rowAnsi_writes_row`

The rungs above are one cell (or one pair) each; this folds them over the row. Two
structural facts about `rowSlot` come first: it only ever *appends* to the byte
accumulator, and its pen/index evolution ignores the bytes already there. That lets the
fold be peeled a cell at a time (or a pair at a time for a wide glyph) with the receiver
threaded through. -/

/-- `rowSlot` appends to the byte accumulator and its `(pen, index)` output ignores the
bytes already accumulated. -/
theorem rowSlot_split (B : Bytes) (p : Pen) (x : Nat) (c : Cell) :
    (rowSlot (B, p, x) c).1 = B ++ (rowSlot ([], p, x) c).1
      ∧ (rowSlot (B, p, x) c).2 = (rowSlot ([], p, x) c).2 := by
  unfold rowSlot
  dsimp only
  by_cases hw : c.width == 0
  · rw [if_pos hw, if_pos hw]; exact ⟨rfl, rfl⟩
  · rw [if_neg hw, if_neg hw]
    dsimp only
    by_cases hp : c.pen == p
    · rw [if_pos hp, if_pos hp]; exact ⟨by simp, rfl⟩
    · rw [if_neg hp, if_neg hp]; exact ⟨by simp [List.append_assoc], rfl⟩

/-- …and therefore so does the whole fold. -/
theorem rowSlot_fold_split : ∀ (cs : List Cell) (B : Bytes) (p : Pen) (x : Nat),
    (cs.foldl rowSlot (B, p, x)).1 = B ++ (cs.foldl rowSlot ([], p, x)).1
      ∧ (cs.foldl rowSlot (B, p, x)).2 = (cs.foldl rowSlot ([], p, x)).2
  | [], B, p, x => ⟨by simp, rfl⟩
  | c :: cs, B, p, x => by
    rw [List.foldl_cons, List.foldl_cons]
    obtain ⟨hb, hpx⟩ := rowSlot_split B p x c
    have h0 := rowSlot_fold_split cs (rowSlot (B, p, x) c).1 (rowSlot (B, p, x) c).2.1
      (rowSlot (B, p, x) c).2.2
    have h1 := rowSlot_fold_split cs (rowSlot ([], p, x) c).1 (rowSlot ([], p, x) c).2.1
      (rowSlot ([], p, x) c).2.2
    -- the one-step output is its own components (product eta), so `h0`/`h1` are about the
    -- same accumulators the goal folds over
    rw [show ((rowSlot (B, p, x) c).1, (rowSlot (B, p, x) c).2.1, (rowSlot (B, p, x) c).2.2)
        = rowSlot (B, p, x) c from rfl] at h0
    rw [show ((rowSlot ([], p, x) c).1, (rowSlot ([], p, x) c).2.1, (rowSlot ([], p, x) c).2.2)
        = rowSlot ([], p, x) c from rfl] at h1
    -- the (pen, index) after one step agree, so the two tails fold the same
    rw [congrArg Prod.fst hpx, congrArg Prod.snd hpx] at h0
    refine ⟨?_, ?_⟩
    · rw [h0.1, h1.1, hb, List.append_assoc]
    · rw [h0.2, h1.2]

/-- Peel the head of a `range`-indexed cell list: `g.at n` followed by the same shape at
`n + 1`. This is how the row walk advances one column without ever materializing
`g.toList`. -/
theorem range_map_cons (g : Row) (n m : Nat) (hm : 0 < m) :
    (List.range m).map (fun i => g.at (n + i))
      = g.at n :: (List.range (m - 1)).map (fun i => g.at (n + 1 + i)) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  simp only [Nat.add_zero, Nat.add_sub_cancel]
  congr 1
  apply List.map_congr_left
  intro i _
  show g.at (n + (i + 1)) = g.at (n + 1 + i)
  rw [show n + (i + 1) = n + 1 + i from by omega]

/-- The array fold `rowAnsi` runs is the fold over `g`'s cells read positionally, which is
the shape `paint_range` inducts on. -/
theorem foldl_rowSlot_range (g : Row) (acc : Bytes × Pen × Nat) :
    g.foldl rowSlot acc = ((List.range g.size).map (fun i => g.at i)).foldl rowSlot acc := by
  rw [← Array.foldl_toList]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hi : i < g.size := by simpa using h1
    rw [List.getElem_map, List.getElem_range]
    show g.toList[i] = g.at i
    unfold Row.at
    rw [Array.getElem_toList, Array.getD, dif_pos hi]
    rfl

/-- The optional `SGR` `rowSlot` emits before a cell whose pen differs from the one in
effect: either empty (pens match) or `penSgr`, and in both cases the receiver's pen ends at
the cell's. Wraps `step_pen` so the row walk need not case on the pen at every cell. -/
theorem pen_prefix_matches {w : Vt} {P : PaintState} {g : Row} {k : Nat}
    (hm : Matches w P g k) (c : Cell) :
    Matches (w.feed (if c.pen == P.pen then ([] : Bytes) else penSgr c.pen))
      { P with pen := c.pen } g k := by
  by_cases hpe : c.pen == P.pen
  · rw [if_pos hpe]
    rw [show (w.feed ([] : Bytes)) = w from rfl]
    rw [show ({ P with pen := c.pen } : PaintState) = P from by
      rw [beq_iff_eq] at hpe; rw [hpe]]
    exact hm
  · rw [if_neg hpe]
    exact step_pen hm c.pen

/-! ### `rowSlot`'s output per cell shape, folding from empty bytes. -/

theorem rowSlot_eq_narrow (c : Cell) (p : Pen) (x : Nat) (hw : c.width = 1) :
    rowSlot ([], p, x) c
      = ((if c.pen == p then [] else penSgr c.pen) ++ cellText c, c.pen, x + 1) := by
  unfold rowSlot
  dsimp only
  rw [if_neg (show ¬(c.width == 0) = true from by simp [hw]),
    if_neg (show ¬(c.width == 2 && !c.marks.isEmpty) = true from by simp [hw])]
  by_cases hpe : c.pen == p
  · rw [if_pos hpe, if_pos hpe]
  · rw [if_neg hpe, if_neg hpe]; simp

theorem rowSlot_eq_wide_nomarks (c : Cell) (p : Pen) (x : Nat)
    (hw : c.width = 2) (hmk : c.marks = []) :
    rowSlot ([], p, x) c
      = ((if c.pen == p then [] else penSgr c.pen) ++ cellText c, c.pen, x + 1) := by
  unfold rowSlot
  dsimp only
  rw [if_neg (show ¬(c.width == 0) = true from by simp [hw]),
    if_neg (show ¬(c.width == 2 && !c.marks.isEmpty) = true from by simp [hmk])]
  by_cases hpe : c.pen == p
  · rw [if_pos hpe, if_pos hpe]
  · rw [if_neg hpe, if_neg hpe]; simp

theorem rowSlot_eq_wide_marks (c : Cell) (p : Pen) (x : Nat)
    (hw : c.width = 2) (hmk : c.marks ≠ []) :
    rowSlot ([], p, x) c
      = ((if c.pen == p then [] else penSgr c.pen)
          ++ (utf8 (safeChar c.base) ++ csiNum (x + 2) 0x47 ++ utf8s c.marks
            ++ csiNum (x + 3) 0x47), c.pen, x + 1) := by
  unfold rowSlot
  dsimp only
  rw [if_neg (show ¬(c.width == 0) = true from by simp [hw]),
    if_pos (show (c.width == 2 && !c.marks.isEmpty) = true from by
      rcases List.exists_cons_of_ne_nil hmk with ⟨a, t, hcm⟩
      rw [hw, hcm]; rfl)]
  by_cases hpe : c.pen == p
  · rw [if_pos hpe, if_pos hpe]
  · rw [if_neg hpe, if_neg hpe]; simp

theorem rowSlot_eq_shadow (c : Cell) (B : Bytes) (p : Pen) (x : Nat) (hw : c.width = 0) :
    rowSlot (B, p, x) c = (B ++ utf8s c.marks, p, x + 1) := by
  unfold rowSlot
  dsimp only
  rw [if_pos (show (c.width == 0) = true from by simp [hw])]

/-! ### Column count is preserved across a cell's bytes (for the row walk's recursion). -/

theorem penSgr_cols {w : Vt} (p : Pen) (hg : w.pstate = .ground) (hu : w.u8need = 0) :
    (w.feed (penSgr p)).cols = w.cols := by rw [penSgr_feed p hg hu]

theorem pen_prefix_cols {w : Vt} (c : Cell) (p : Pen) (hg : w.pstate = .ground)
    (hu : w.u8need = 0) :
    (w.feed (if c.pen == p then ([] : Bytes) else penSgr c.pen)).cols = w.cols := by
  by_cases hpe : c.pen == p
  · rw [if_pos hpe]; rfl
  · rw [if_neg hpe]; exact penSgr_cols c.pen hg hu

theorem cellText_cols {w : Vt} (c : Cell) (hg : w.pstate = .ground) (hu : w.u8need = 0)
    (ha : w.u8acc = 0) : (w.feed (cellText c)).cols = w.cols := by
  rw [cellText_feed c hg hu ha, foldl_print_cols]
  exact cols_print w (safeChar c.base)

theorem utf8s_cols {w : Vt} (ms : List Char) (hg : w.pstate = .ground) (hu : w.u8need = 0)
    (ha : w.u8acc = 0) : (w.feed (utf8s ms)).cols = w.cols := by
  rw [utf8s_feed ms hg hu ha, foldl_print_cols]

theorem foldl_print_quiet : ∀ (l : List Char) (w : Vt),
    w.pstate = .ground → w.u8need = 0 → w.u8acc = 0 →
    (l.foldl (fun w c => w.print (safeChar c)) w).pstate = .ground
      ∧ (l.foldl (fun w c => w.print (safeChar c)) w).u8need = 0
      ∧ (l.foldl (fun w c => w.print (safeChar c)) w).u8acc = 0
  | [], w, hg, hu, ha => ⟨hg, hu, ha⟩
  | a :: l, w, hg, hu, ha => by
    rw [List.foldl_cons]
    obtain ⟨h1, h2, h3⟩ := print_quiet (safeChar a) hg hu ha
    exact foldl_print_quiet l (w.print (safeChar a)) h1 h2 h3

theorem utf8s_quiet (ms : List Char) {w : Vt} (hg : w.pstate = .ground) (hu : w.u8need = 0)
    (ha : w.u8acc = 0) :
    (w.feed (utf8s ms)).pstate = .ground ∧ (w.feed (utf8s ms)).u8need = 0
      ∧ (w.feed (utf8s ms)).u8acc = 0 := by
  rw [utf8s_feed ms hg hu ha]; exact foldl_print_quiet ms w hg hu ha

/-- The wide-with-marks branch's bytes preserve the column count. Each piece — the glyph, the
two `CHA`s, the marks — does; threaded through the intermediate quiescent states. -/
theorem dance_cols {w : Vt} (b : Char) (ms : List Char) (a a' : Nat)
    (hg : w.pstate = .ground) (hu : w.u8need = 0) (ha : w.u8acc = 0)
    (ha1 : 0 < a) (ha1' : a < 65535) (ha2 : 0 < a') (ha2' : a' < 65535) :
    (w.feed (utf8 (safeChar b) ++ csiNum a 0x47 ++ utf8s ms ++ csiNum a' 0x47)).cols = w.cols := by
  have hb := (safeChar_ge b).1
  -- after the glyph
  have e1 : w.feed (utf8 (safeChar b)) = w.print (safeChar b) := utf8_feed (safeChar b) hb hg hu ha
  obtain ⟨hg1, hu1, ha1q⟩ := print_quiet (safeChar b) hg hu ha
  have hgw1 : (w.feed (utf8 (safeChar b))).pstate = .ground := by rw [e1]; exact hg1
  have huw1 : (w.feed (utf8 (safeChar b))).u8need = 0 := by rw [e1]; exact hu1
  have hc1 : (w.feed (utf8 (safeChar b))).cols = w.cols := by rw [e1]; exact cols_print w (safeChar b)
  -- after the first CHA
  have e2 : (w.feed (utf8 (safeChar b))).feed (csiNum a 0x47)
      = (w.feed (utf8 (safeChar b))).setCol (a - 1) := by
    rw [e1]; exact cha_feed_eq a hg1 hu1 ha1 ha1'
  have hg2 : ((w.feed (utf8 (safeChar b))).feed (csiNum a 0x47)).pstate = .ground := by
    rw [e2, Zmx.Core.Vt.ps_setCol, e1]; exact hg1
  have hu2 : ((w.feed (utf8 (safeChar b))).feed (csiNum a 0x47)).u8need = 0 := by
    rw [e2, Zmx.Core.Vt.un_setCol, e1]; exact hu1
  have ha2q : ((w.feed (utf8 (safeChar b))).feed (csiNum a 0x47)).u8acc = 0 := by
    rw [e2, show ((w.feed (utf8 (safeChar b))).setCol (a - 1)).u8acc
        = (w.feed (utf8 (safeChar b))).u8acc from by rw [frame_setCol], e1]; exact ha1q
  have hc2 : ((w.feed (utf8 (safeChar b))).feed (csiNum a 0x47)).cols = w.cols := by
    rw [cha_cols a hgw1 huw1 ha1 ha1', hc1]
  -- after the marks
  have hg3 : (((w.feed (utf8 (safeChar b))).feed (csiNum a 0x47)).feed (utf8s ms)).pstate = .ground
      ∧ (((w.feed (utf8 (safeChar b))).feed (csiNum a 0x47)).feed (utf8s ms)).u8need = 0
      ∧ (((w.feed (utf8 (safeChar b))).feed (csiNum a 0x47)).feed (utf8s ms)).u8acc = 0 :=
    utf8s_quiet ms hg2 hu2 ha2q
  have hc3 : (((w.feed (utf8 (safeChar b))).feed (csiNum a 0x47)).feed (utf8s ms)).cols = w.cols := by
    rw [utf8s_cols ms hg2 hu2 ha2q, hc2]
  -- after the last CHA
  rw [feed_append, feed_append, feed_append,
    cha_cols a' hg3.1 hg3.2.1 ha2 ha2', hc3]


end Zmx.Core.Render
