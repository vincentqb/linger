module

import all Linger.Core.Render
import all Linger.Core.Vt
import all Theorems.Render.Row
import all Theorems.Render.PendingWrap

-- Module-private by default: `Vt`'s fields are sealed (see `Theorems/Vt/State.lean`).

/-! # Step 4 — the grid

`OffRow` (a row's paint leaves the other rows alone), the `joinCRLF` row walk
(`Walking`, `paint_rows`), `gridAnsi_writes_grid`, the prologue's canonical entry
state, and the composition to `restore_grid_any` on both screens. Split out of
`Theorems/Render.lean`. -/

namespace Linger.Core.Render

open Linger.Core.Vt

/-! ## Step 4 — the grid

Step 3 proved a row. A grid is not a list of independent rows: the walk's invariant is
"the rows below `y` are already painted", so each later row's paint must leave them
alone — and `Matches`, a statement about **one** row, cannot say that. `OffRow` is the
missing half, and it is the cross-row catastrophe `RowOk` was guarding against stated
positively. -/

/-- **What a row's paint owes the grid walk**: it changes no cell outside row `y`, resizes
no row, and changes neither dimension. Composable by `trans`, which is the whole point —
the row's bytes arrive in pieces (a pen prefix, a glyph, a `CHA`, marks) and each piece
must be transparent off row `y`. -/
structure OffRow (y : Nat) (u u' : Vt) : Prop where
  /-- Bounded to rows the grid actually has, and that bound is load-bearing: out of range
  `getRow` returns `blankRow cols pen`, so a **pen change** alters it. The grid walk only
  ever reads rows in the grid. -/
  cells : ∀ i y', y' ≠ y → y' < u.grid.size → u'.getCell i y' = u.getCell i y'
  sizes : ∀ y', (u'.getRow y').size = (u.getRow y').size
  gridSize : u'.grid.size = u.grid.size
  cols : u'.cols = u.cols
  /-- A row's paint pushes nothing to scrollback. `cells` cannot supply this: at
  `rows = 1` a scroll rewrites only row `y`, so `cells` is vacuous while the ring grows —
  which is exactly the confusion this field exists to make impossible. -/
  sb : u'.sb = u.sb

theorem OffRow.refl (y : Nat) (u : Vt) : OffRow y u u :=
  ⟨fun _ _ _ _ => rfl, fun _ => rfl, rfl, rfl, rfl⟩

theorem OffRow.trans {y : Nat} {u u' u'' : Vt} (h1 : OffRow y u u') (h2 : OffRow y u' u'') :
    OffRow y u u'' :=
  ⟨fun i y' hne hlt =>
    (h2.cells i y' hne
          (by
            rw [h1.gridSize]; exact hlt)).trans
      (h1.cells i y' hne hlt),
    fun y' => (h2.sizes y').trans (h1.sizes y'), h2.gridSize.trans h1.gridSize,
    h2.cols.trans h1.cols, h2.sb.trans h1.sb⟩

/-- A stream that writes no cell at all is transparent off every row. Covers the pen
prefix and both `CHA`s. -/
theorem OffRow.of_grid_eq {y : Nat} {u u' : Vt} (hg : u'.grid = u.grid) (hc : u'.cols = u.cols)
    (hsb : u'.sb = u.sb) : OffRow y u u' := by
  refine ⟨fun i y' _ hlt => ?_, fun y' => ?_, by rw [hg], hc, hsb⟩
  · show
      Array.getD (u'.grid.getD y' (blankRow u'.cols u'.pen)) i default =
        Array.getD (u.grid.getD y' (blankRow u.cols u.pen)) i default
    rw [hg, getD_of_lt u.grid y' (blankRow u'.cols u'.pen) (blankRow u.cols u.pen) hlt]
  · show
      (u'.grid.getD y' (blankRow u'.cols u'.pen)).size =
        (u.grid.getD y' (blankRow u.cols u.pen)).size
    rw [hg]
    by_cases hlt : y' < u.grid.size
    · rw [getD_of_lt u.grid y' (blankRow u'.cols u'.pen) (blankRow u.cols u.pen) hlt]
    · rw [Array.getD, dite_eq_right hlt, Array.getD, dite_eq_right hlt]
      show (blankRow u'.cols u'.pen).size = (blankRow u.cols u.pen).size
      simp [blankRow, hc]

theorem offRow_penSgr {w : Vt} (y : Nat) (p : Pen) (hg : w.pstate = .ground) (hu : w.u8need = 0) :
    OffRow y w (w.feed (penSgr p)) :=
  OffRow.of_grid_eq (by rw [penSgr_feed p hg hu]) (by rw [penSgr_feed p hg hu])
    (by rw [penSgr_feed p hg hu])

theorem offRow_pen_prefix {w : Vt} (y : Nat) (c : Cell) (p : Pen) (hg : w.pstate = .ground)
    (hu : w.u8need = 0) :
    OffRow y w (w.feed (if c.pen == p then ([] : Bytes) else penSgr c.pen)) := by
  by_cases hpe : c.pen == p
  · rw [ite_eq_left hpe]; exact OffRow.refl y w
  · rw [ite_eq_right hpe]; exact offRow_penSgr y c.pen hg hu

theorem offRow_cha {w : Vt} (y n : Nat) (hg : w.pstate = .ground) (hu : w.u8need = 0) (hn : 0 < n)
    (hlt : n < 65535) : OffRow y w (w.feed (csiNum n 0x47)) :=
  OffRow.of_grid_eq (by rw [cha_feed_eq n hg hu hn hlt, frame_setCol])
    (by rw [cha_feed_eq n hg hu hn hlt, frame_setCol])
    (by rw [cha_feed_eq n hg hu hn hlt, frame_setCol])

/-! ### `OffRow` for the cell rungs

Each mirrors a rung's hypotheses, because each needs the same reduction of the print to
its write — the general statement for `print` would have to reason through `printWrap`'s
scroll, which is precisely the cross-row catastrophe these hypotheses rule out. -/

/-- **A narrow cell's bytes touch no other row.** Serves both the interior and the margin
rung: the advance differs, `getCell_printAdvance` does not care. -/
theorem offRow_narrow {w : Vt} {P : PaintState} {g : Row} {k : Nat} (hrow : RowOk w.cols g)
    (hm : Matches w P g k) (hpend : P.pending = false) (hwid : (g.at k).width = 1)
    (hmk : (g.at k).marks = []) : OffRow P.y w (w.feed (cellText (g.at k))) := by
  have hem : Emittable (g.at k).base := (hrow.cells k).base
  have hpc : w.printChar (g.at k).base = (g.at k).base :=
    printChar_id_of_ascii hm.ascii0 hm.ascii1 hem.1 hem.2
  have hcw : charWidth (g.at k).base = 1 := by
    rw [(hrow.cells k).width
        (by
          rw [hwid]; omega),
      hwid]
  have hpd : w.cursor.pending = false := by rw [hm.pend, hpend]
  have hfeed : w.feed (cellText (g.at k)) = w.print (g.at k).base := by
    rw [cellText_feed (g.at k) hm.ground hm.u8need hm.u8acc, hmk, safeChar_of_emittable hem]
    rfl
  have hgs : w.cursor.y < w.clearPending.grid.size := by
    show w.cursor.y < w.grid.size
    rw [hm.curY]; exact hm.inGrid
  rw [hfeed, print_narrow_eq hpc hcw hm.ins hpd]
  obtain ⟨hc, hgz, hr⟩ :=
    write_shape w.clearPending w.cursor.x w.cursor.y
      { base := (g.at k).base, marks := [], width := 1, pen := w.pen } 1 hgs
  refine ⟨fun i y' hne _ => ?_, fun y' => ?_, ?_, ?_, ?_⟩
  · rw [getCell_write_off w.clearPending w.cursor.x w.cursor.y _ 1 i y'
        (by
          rw [hm.curY]; exact hne)]
    exact getCell_clearPending w i y'
  · rw [hr y']
    show (w.clearPending.getRow y').size = (w.getRow y').size
    unfold Vt.getRow; rw [frame_clearPending]
  · rw [hgz]; exact congrArg Array.size (grid_clearPending w)
  · rw [hc]; rw [frame_clearPending]
  · rw [frame_printAdvance, frame_mendRow, frame_putCell, frame_clearPending]

/-- **A wide glyph's bytes touch no other row**, base and shadow together. -/
theorem offRow_wide {w : Vt} {P : PaintState} {g : Row} {k : Nat} (hrow : RowOk w.cols g)
    (hm : Matches w P g k) (hPx : P.x = k) (hpend : P.pending = false) (hfit : k + 1 < w.cols)
    (hwid : (g.at k).width = 2) (hmk : (g.at k).marks = []) :
    OffRow P.y w (w.feed (cellText (g.at k))) := by
  have hem : Emittable (g.at k).base := (hrow.cells k).base
  have hpc : w.printChar (g.at k).base = (g.at k).base :=
    printChar_id_of_ascii hm.ascii0 hm.ascii1 hem.1 hem.2
  have hcw : charWidth (g.at k).base = 2 := by
    rw [(hrow.cells k).width
        (by
          rw [hwid]; omega),
      hwid]
  have hpd : w.cursor.pending = false := by rw [hm.pend, hpend]
  have hx : w.cursor.x = k := by rw [hm.curX, hPx]
  have hfitc : w.cursor.x + 1 < w.cols := by
    rw [hx]; exact hfit
  have hfeed : w.feed (cellText (g.at k)) = w.print (g.at k).base := by
    rw [cellText_feed (g.at k) hm.ground hm.u8need hm.u8acc, hmk, safeChar_of_emittable hem]
    rfl
  have hgs : w.cursor.y < w.clearPending.grid.size := by
    show w.cursor.y < w.grid.size
    rw [hm.curY]; exact hm.inGrid
  rw [hfeed, print_wide_eq hpc hcw hm.ins hpd hfitc]
  obtain ⟨hc, hgz, hr⟩ :=
    write_shape2 w.clearPending w.cursor.x w.cursor.y
      { base := (g.at k).base, marks := [], width := 2, pen := w.pen }
      (Cell.shadow { base := (g.at k).base, marks := [], width := 2, pen := w.pen }) 2 hgs
  refine ⟨fun i y' hne _ => ?_, fun y' => ?_, ?_, ?_, ?_⟩
  · rw [getCell_write2_off w.clearPending w.cursor.x w.cursor.y _ _ 2 i y'
        (by
          rw [hm.curY]; exact hne)]
    exact getCell_clearPending w i y'
  · rw [hr y']
    show (w.clearPending.getRow y').size = (w.getRow y').size
    unfold Vt.getRow; rw [frame_clearPending]
  · rw [hgz]; exact congrArg Array.size (grid_clearPending w)
  · rw [hc]; rw [frame_clearPending]
  · rw [frame_printAdvance]; dsimp only; rw [frame_mendRow]; dsimp only
    rw [frame_putCell]; dsimp only; rw [frame_putCell]; dsimp only; rw [frame_clearPending]

/-- **A combining mark's bytes touch no other row.** Mirrors `mark_step`, including its
interior/margin disjunction, since the two use different `printMark` equations. -/
theorem offRow_mark {cols : Nat} {w : Vt} {Q : PaintState} {g : Row} {wcol kf : Nat}
    {done : List Char} (hrow : RowOk cols g) (hwid : (g.at wcol).width ≠ 0) (hwcol : wcol < cols)
    (hlt : wcol < kf)
    (hdisj : (Q.x = wcol + 1 ∧ Q.pending = false) ∨ (Q.x = wcol ∧ Q.pending = true))
    (hcap : done.length < 8) (hm : Matches w Q (withMarks g wcol done) kf) (m : Char)
    (hmw : charWidth m = 0) (hme : Emittable m) : OffRow Q.y w (w.print (safeChar m)) := by
  have hsafe : safeChar m = m := safeChar_of_emittable hme
  have hcw : charWidth (safeChar m) = 0 := by
    rw [hsafe]; exact hmw
  have hpc : w.printChar (safeChar m) = safeChar m :=
    printChar_id_of_ascii hm.ascii0 hm.ascii1
      (by
        rw [hsafe]; exact hme.1)
      (by
        rw [hsafe]; exact hme.2)
  have hkg : wcol < g.size := by
    rw [hrow.size]; exact hwcol
  have hgetk : w.getCell wcol Q.y = { g.at wcol with marks := done } := by
    rw [hm.cells wcol hlt, at_withMarks_self g wcol done hkg]
  have hyk : w.cursor.y = Q.y := hm.curY
  have hgs : Q.y < w.grid.size := hm.inGrid
  have hwk0 : (w.getCell wcol Q.y).width ≠ 0 := by
    rw [hgetk]; exact hwid
  have hcapk : (w.getCell wcol Q.y).marks.length < 8 := by
    rw [hgetk]; show done.length < 8; exact hcap
  have hpm :
    w.print (safeChar m) =
      (w.putCell wcol Q.y
            { w.getCell wcol Q.y with marks := (w.getCell wcol Q.y).marks ++ [safeChar m] }).mendRow
        Q.y := by
    rcases hdisj with ⟨hQx, hQp⟩ | ⟨hQx, hQp⟩
    · have hx : w.cursor.x = wcol + 1 := by rw [hm.curX, hQx]
      have hpd : w.cursor.pending = false := by rw [hm.pend, hQp]
      have hx1 : w.cursor.x - 1 = wcol := by omega
      have hnw : (w.getCell (w.cursor.x - 1) w.cursor.y).width ≠ 0 := by
        rw [hx1, hyk]; exact hwk0
      have hcapp : (w.getCell (w.cursor.x - 1) w.cursor.y).marks.length < 8 := by
        rw [hx1, hyk]; exact hcapk
      rw [print_mark_eq hpc hcw hpd hnw hcapp, hx1, hyk]
    · have hx : w.cursor.x = wcol := by rw [hm.curX, hQx]
      have hpd : w.cursor.pending = true := by rw [hm.pend, hQp]
      have hnw : (w.getCell w.cursor.x w.cursor.y).width ≠ 0 := by
        rw [hx, hyk]; exact hwk0
      have hcapp : (w.getCell w.cursor.x w.cursor.y).marks.length < 8 := by
        rw [hx, hyk]; exact hcapk
      rw [print_mark_pending_eq hpc hcw hpd hnw hcapp, hx, hyk]
  rw [hpm]
  refine ⟨fun i y' hne _ => getCell_mark_off w wcol Q.y _ i y' hne, fun y' => ?_, ?_, ?_, ?_⟩
  · rw [size_getRow_mendRow _ Q.y
        (by
          rw [grid_size_putCell]; exact hgs)
        y',
      size_getRow_putCell_any w wcol Q.y _ hgs y']
  · rw [grid_size_mendRow, grid_size_putCell]
  · rw [frame_mendRow, frame_putCell]
  · rw [frame_mendRow, frame_putCell]

/-- **The mark loop is transparent off its row.** Runs the same recursion as `marks_fold`,
carrying `Matches` alongside so each step's `offRow_mark` has its hypotheses. -/
theorem offRow_marks_fold {cols : Nat} {Q : PaintState} {g : Row} {wcol kf : Nat}
    (hrow : RowOk cols g) (hwid : (g.at wcol).width ≠ 0) (hwcol : wcol < cols) (hlt : wcol < kf)
    (hdisj : (Q.x = wcol + 1 ∧ Q.pending = false) ∨ (Q.x = wcol ∧ Q.pending = true)) :
    ∀ (rest : List Char) (u : Vt) (acc : List Char),
      (∀ x ∈ acc, charWidth x = 0 ∧ Emittable x) →
        (∀ x ∈ rest, charWidth x = 0 ∧ Emittable x) →
        acc.length + rest.length ≤ 8 →
        u.cols = cols →
        Matches u Q (withMarks g wcol acc) kf →
        OffRow Q.y u (rest.foldl (fun w c => w.print (safeChar c)) u)
  | [], u, _, _, _, _, _, _ => OffRow.refl Q.y u
  | m :: rest, u, acc, hacc, hrest, hlen, hucols, hu => by
    have hmm := hrest m (List.mem_cons_self)
    have hoff :=
      offRow_mark (cols := cols) hrow hwid hwcol hlt hdisj
        (by
          simp only [List.length_cons] at hlen; omega)
        hu m hmm.1 hmm.2
    have hstep :=
      mark_step (w := u) (cols := cols) hrow hucols hwid hwcol hlt hdisj
        (by
          simp only [List.length_cons] at hlen; omega)
        hacc hu m hmm.1 hmm.2
    have hacc' : ∀ x ∈ acc ++ [safeChar m], charWidth x = 0 ∧ Emittable x := by
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact hacc x h
      · rw [List.mem_singleton.mp h, safeChar_of_emittable hmm.2]; exact hmm
    have hucols' : (u.print (safeChar m)).cols = cols := by
      rw [cols_print]; exact hucols
    have hrec :=
      offRow_marks_fold hrow hwid hwcol hlt hdisj rest (u.print (safeChar m)) (acc ++ [safeChar m])
        hacc' (fun x hx => hrest x (List.mem_cons_of_mem m hx))
        (by
          simp only [List.length_append, List.length_cons, List.length_nil] at hlen ⊢; omega)
        hucols' hstep
    rw [List.foldl_cons]
    exact hoff.trans hrec

/-- **A narrow cell with its marks is transparent off its row**, for either base step:
the base glyph (`offRow_narrow`) then the loop (`offRow_marks_fold`), composed by
`trans`. `hdisj` is the interior/margin split the mark loop reads. -/
theorem offRow_narrow_marks_of {w : Vt} {P : PaintState} {g : Row} {k : Nat} (xb : Nat) (pb : Bool)
    (hrow : RowOk w.cols g) (hm : Matches w P g k) (hpend : P.pending = false) (hk : k < w.cols)
    (hwid : (g.at k).width = 1) (hpen : (g.at k).pen = P.pen)
    (hdisj : (xb = k + 1 ∧ pb = false) ∨ (xb = k ∧ pb = true))
    (hstep :
      ∀ {g' : Row},
        RowOk w.cols g' →
          Matches w P g' k →
          (g'.at k).width = 1 →
          (g'.at k).marks = [] →
          (g'.at k).pen = P.pen →
          Matches (w.feed (cellText (g'.at k)))
            { P with
              x := xb, pending := pb }
            g' (k + 1)) :
    OffRow P.y w (w.feed (cellText (g.at k))) := by
  have hkg : k < g.size := by
    rw [hrow.size]; omega
  have hmks := (hrow.cells k).marks
  have hmle := (hrow.cells k).marksLe
  have hrow0 : RowOk w.cols (withMarks g k []) :=
    rowOk_withMarks hrow
      (by
        rw [hwid]; decide)
      (by simp) (by simp)
  have hwid0 : ((withMarks g k []).at k).width = 1 := by
    rw [at_withMarks_self g k [] hkg]; exact hwid
  have hmk0 : ((withMarks g k []).at k).marks = [] := by rw [at_withMarks_self g k [] hkg]
  have hpen0 : ((withMarks g k []).at k).pen = P.pen := by
    rw [at_withMarks_self g k [] hkg]; exact hpen
  have hm0 : Matches w P (withMarks g k []) k :=
    matches_below (fun j hj => at_withMarks_ne g k [] j (by omega)) hm
  have hoffbase : OffRow P.y w (w.feed (cellText ((withMarks g k []).at k))) :=
    offRow_narrow hrow0 hm0 hpend hwid0 hmk0
  have hbase := hstep hrow0 hm0 hwid0 hmk0 hpen0
  have hbtext : cellText ((withMarks g k []).at k) = utf8 (safeChar (g.at k).base) := by
    rw [at_withMarks_self g k [] hkg]
    show utf8 (safeChar (g.at k).base) ++ utf8s [] = utf8 (safeChar (g.at k).base)
    simp [utf8s]
  rw [hbtext] at hoffbase hbase
  have hucols : (w.feed (utf8 (safeChar (g.at k).base))).cols = w.cols := by
    rw [utf8_feed (safeChar (g.at k).base) (safeChar_ge (g.at k).base) hm.ground hm.u8need hm.u8acc]
    exact cols_print w (safeChar (g.at k).base)
  have hoffmarks :=
    offRow_marks_fold (Q :=
      { P with
        x := xb, pending := pb })
      hrow
      (by
        rw [hwid]; decide)
      hk (by omega : k < k + 1) hdisj (g.at k).marks (w.feed (utf8 (safeChar (g.at k).base))) []
      (by simp) hmks (by simpa using hmle) hucols hbase
  rw [show cellText (g.at k) = utf8 (safeChar (g.at k).base) ++ utf8s (g.at k).marks from rfl,
    feed_append, utf8s_feed (g.at k).marks hbase.ground hbase.u8need hbase.u8acc]
  exact hoffbase.trans hoffmarks

theorem offRow_narrow_marks {w : Vt} {P : PaintState} {g : Row} {k : Nat} (hrow : RowOk w.cols g)
    (hm : Matches w P g k) (hPx : P.x = k) (hpend : P.pending = false) (hfit : k + 1 < w.cols)
    (hwid : (g.at k).width = 1) (hpen : (g.at k).pen = P.pen) :
    OffRow P.y w (w.feed (cellText (g.at k))) :=
  offRow_narrow_marks_of (k + 1) false hrow hm hpend (by omega) hwid hpen (Or.inl ⟨rfl, rfl⟩)
    (fun hr hm' hw hmk hp => step_narrow hr hm' hPx hpend hfit hw hmk hp)

/-- At the right margin the base print clamps and arms wrap-pending. -/
theorem offRow_narrow_margin_marks {w : Vt} {P : PaintState} {g : Row} {k : Nat}
    (hrow : RowOk w.cols g) (hm : Matches w P g k) (hPx : P.x = k) (hpend : P.pending = false)
    (hk : k < w.cols) (hmar : w.cols ≤ k + 1) (hwid : (g.at k).width = 1)
    (hpen : (g.at k).pen = P.pen) : OffRow P.y w (w.feed (cellText (g.at k))) :=
  offRow_narrow_marks_of P.x true hrow hm hpend hk hwid hpen (Or.inr ⟨hPx, rfl⟩)
    (fun hr hm' hw hmk hp => step_narrow_margin hr hm' hPx hpend hk hmar hw hmk hp)

/-- **A wide glyph carrying marks is transparent off its row**, for either base step.
Four pieces — glyph, `CHA`, marks, `CHA` — composed by `trans`. The two `CHA`s write no
cell at all, so they cost `OffRow.of_grid_eq`; the base print and the mark loop are the
real work. -/
theorem offRow_wide_marks_of {w : Vt} {P : PaintState} {g : Row} {k : Nat} (xb : Nat) (pb : Bool)
    (hrow : RowOk w.cols g) (hm : Matches w P g k) (hPx : P.x = k) (hpend : P.pending = false)
    (hfit : k + 1 < w.cols) (hcb : k + 3 < 65535) (hwid : (g.at k).width = 2)
    (hpen : (g.at k).pen = P.pen)
    (hstep :
      ∀ {g' : Row},
        RowOk w.cols g' →
          Matches w P g' k →
          (g'.at k).width = 2 →
          (g'.at k).marks = [] →
          (g'.at k).pen = P.pen →
          Matches (w.feed (cellText (g'.at k)))
            { P with
              x := xb, pending := pb }
            g' (k + 2)) :
    OffRow P.y w
      (w.feed
        (utf8 (safeChar (g.at k).base) ++ csiNum (k + 2) 0x47 ++ utf8s (g.at k).marks ++
          csiNum (k + 3) 0x47)) := by
  have hkg : k < g.size := by
    rw [hrow.size]; omega
  have hmks := (hrow.cells k).marks
  have hmle := (hrow.cells k).marksLe
  have hrow0 : RowOk w.cols (withMarks g k []) :=
    rowOk_withMarks hrow
      (by
        rw [hwid]; decide)
      (by simp) (by simp)
  have hwid0 : ((withMarks g k []).at k).width = 2 := by
    rw [at_withMarks_self g k [] hkg]; exact hwid
  have hmk0 : ((withMarks g k []).at k).marks = [] := by rw [at_withMarks_self g k [] hkg]
  have hpen0 : ((withMarks g k []).at k).pen = P.pen := by
    rw [at_withMarks_self g k [] hkg]; exact hpen
  have hm0 : Matches w P (withMarks g k []) k :=
    matches_below (fun j hj => at_withMarks_ne g k [] j (by omega)) hm
  have hbtext : cellText ((withMarks g k []).at k) = utf8 (safeChar (g.at k).base) := by
    rw [at_withMarks_self g k [] hkg]
    show utf8 (safeChar (g.at k).base) ++ utf8s [] = utf8 (safeChar (g.at k).base)
    simp [utf8s]
  have hoffbase : OffRow P.y w (w.feed (utf8 (safeChar (g.at k).base))) := by
    have := offRow_wide hrow0 hm0 hPx hpend hfit hwid0 hmk0
    rwa [hbtext] at this
  have hbase := hstep hrow0 hm0 hwid0 hmk0 hpen0
  rw [hbtext] at hbase
  have hw1cols : (w.feed (utf8 (safeChar (g.at k).base))).cols = w.cols := by
    rw [utf8_feed (safeChar (g.at k).base) (safeChar_ge (g.at k).base) hm.ground hm.u8need hm.u8acc]
    exact cols_print w (safeChar (g.at k).base)
  have hoffcha1 :
    OffRow P.y (w.feed (utf8 (safeChar (g.at k).base)))
      ((w.feed (utf8 (safeChar (g.at k).base))).feed (csiNum (k + 2) 0x47)) :=
    offRow_cha P.y (k + 2) hbase.ground hbase.u8need (by omega) (by omega)
  have hcha1 :=
    cha_matches_lt (n := k + 2) hbase (by omega) (by omega)
      (by
        rw [hw1cols]; omega)
  rw [show k + 2 - 1 = k + 1 from by omega] at hcha1
  have hu2cols :
    ((w.feed (utf8 (safeChar (g.at k).base))).feed (csiNum (k + 2) 0x47)).cols = w.cols := by
    rw [cha_cols (k + 2) hbase.ground hbase.u8need (by omega) (by omega)]; exact hw1cols
  have hoffmarks :=
    offRow_marks_fold (Q :=
      {
        { P with
          x := xb, pending := pb } with
        x := k + 1, pending := false })
      hrow
      (by
        rw [hwid]; decide)
      (by omega : k < w.cols) (by omega : k < k + 2) (Or.inl ⟨rfl, rfl⟩) (g.at k).marks
      ((w.feed (utf8 (safeChar (g.at k).base))).feed (csiNum (k + 2) 0x47)) [] (by simp) hmks
      (by simpa using hmle) hu2cols hcha1
  have hmg :=
    matches_row_congr (g := g)
      (fun j => by
        by_cases hjk : j = k
        · subst hjk; rw [at_withMarks_self g j (g.at j).marks hkg]
        · exact at_withMarks_ne g k (g.at k).marks j hjk)
      (by
        have h :=
          marks_fold (Q :=
            {
              { P with
                x := xb, pending := pb } with
              x := k + 1, pending := false })
            hrow
            (by
              rw [hwid]; decide)
            (by omega : k < w.cols) (by omega : k < k + 2) (Or.inl ⟨rfl, rfl⟩) (g.at k).marks
            ((w.feed (utf8 (safeChar (g.at k).base))).feed (csiNum (k + 2) 0x47)) [] (by simp) hmks
            (by simpa using hmle) hu2cols hcha1
        rw [map_safeChar_id (g.at k).marks (fun x hx => (hmks x hx).2)] at h
        simpa using h)
  have hoffcha2 :
    OffRow P.y
      ((g.at k).marks.foldl (fun w c => w.print (safeChar c))
        ((w.feed (utf8 (safeChar (g.at k).base))).feed (csiNum (k + 2) 0x47)))
      (((g.at k).marks.foldl (fun w c => w.print (safeChar c))
            ((w.feed (utf8 (safeChar (g.at k).base))).feed (csiNum (k + 2) 0x47))).feed
        (csiNum (k + 3) 0x47)) :=
    offRow_cha P.y (k + 3) hmg.ground hmg.u8need (by omega) (by omega)
  rw [feed_append, feed_append, feed_append,
    utf8s_feed (g.at k).marks hcha1.ground hcha1.u8need hcha1.u8acc]
  exact ((hoffbase.trans hoffcha1).trans hoffmarks).trans hoffcha2

theorem offRow_wide_marks {w : Vt} {P : PaintState} {g : Row} {k : Nat} (hrow : RowOk w.cols g)
    (hm : Matches w P g k) (hPx : P.x = k) (hpend : P.pending = false) (hfit : k + 1 < w.cols)
    (hfit2 : k + 2 < w.cols) (hcb : k + 3 < 65535) (hwid : (g.at k).width = 2)
    (hpen : (g.at k).pen = P.pen) :
    OffRow P.y w
      (w.feed
        (utf8 (safeChar (g.at k).base) ++ csiNum (k + 2) 0x47 ++ utf8s (g.at k).marks ++
          csiNum (k + 3) 0x47)) :=
  offRow_wide_marks_of (k + 2) false hrow hm hPx hpend hfit hcb hwid hpen
    (fun hr hm' hw hmk hp => step_wide hr hm' hPx hpend hfit hfit2 hw hmk hp)

theorem offRow_wide_margin_marks {w : Vt} {P : PaintState} {g : Row} {k : Nat}
    (hrow : RowOk w.cols g) (hm : Matches w P g k) (hPx : P.x = k) (hpend : P.pending = false)
    (hfit : k + 1 < w.cols) (hmar : w.cols ≤ k + 2) (hcb : k + 3 < 65535)
    (hwid : (g.at k).width = 2) (hpen : (g.at k).pen = P.pen) :
    OffRow P.y w
      (w.feed
        (utf8 (safeChar (g.at k).base) ++ csiNum (k + 2) 0x47 ++ utf8s (g.at k).marks ++
          csiNum (k + 3) 0x47)) :=
  offRow_wide_marks_of (w.cols - 1) true hrow hm hPx hpend hfit hcb hwid hpen
    (fun hr hm' hw hmk hp => step_wide_margin hr hm' hPx hpend hfit hmar hw hmk hp)

/-- **The row walk.** Feeding `rowSlot` folded over the cells from column `n` onward carries
the receiver from frontier `n` to the full row. Peels a narrow cell (advance one) or a wide
pair (advance two) each step; `Matches.frontier` rules out ever landing on a shadow. The
final pen is `rowAnsi`'s returned pen, so a grid can thread it into the next row. -/
theorem paint_range {cols : Nat} {g : Row} {Y : Nat} (hrow : RowOk cols g) (hcb : cols < 65533) :
    ∀ (m n : Nat) (w : Vt) (pen : Pen),
      w.cols = cols →
        n + m = cols →
        0 < m →
        Matches w { x := n, y := Y, pen := pen, pending := false } g n →
        ∃ pd : Bool,
          Matches
              (w.feed (((List.range m).map (fun i => g.at (n + i))).foldl rowSlot ([], pen, n)).1)
              { x := cols - 1, y := Y,
                pen :=
                  (((List.range m).map (fun i => g.at (n + i))).foldl rowSlot ([], pen, n)).2.1,
                pending := pd }
              g cols ∧
            OffRow Y w
              (w.feed
                (((List.range m).map (fun i => g.at (n + i))).foldl rowSlot ([], pen, n)).1) := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro n w pen hcols hsum hm0 hmatch
    have hncols : n < cols := by omega
    have hwle : (g.at n).width ≤ 2 := by
      by_cases hz : (g.at n).width = 0
      · omega
      · have := (hrow.cells n).width hz
        rw [← this]; unfold charWidth; split
        · omega
        · split <;> omega
    rw [range_map_cons g n m hm0, List.foldl_cons]
    by_cases hw0 : (g.at n).width = 0
    · exfalso
      obtain ⟨hne0, hprev⟩ := (hrow.pairs n).2 hw0
      rcases hmatch.frontier with hz | hne
      · exact hne0 hz
      · exact hne hprev
    · by_cases hw1 : (g.at n).width = 1
      · -- NARROW
        rw [rowSlot_eq_narrow (g.at n) pen n hw1]
        have hm1 := pen_prefix_matches hmatch (g.at n)
        have hw1c :
          (w.feed (if (g.at n).pen == pen then ([] : Bytes) else penSgr (g.at n).pen)).cols =
            cols := by
          rw [pen_prefix_cols (g.at n) pen hmatch.ground hmatch.u8need]; exact hcols
        by_cases hmar : n + 1 < cols
        · -- interior narrow
          obtain ⟨hs1, hs2⟩ :=
            rowSlot_fold_split ((List.range (m - 1)).map (fun i => g.at (n + 1 + i)))
              ((if (g.at n).pen == pen then [] else penSgr (g.at n).pen) ++ cellText (g.at n))
              (g.at n).pen (n + 1)
          rw [hs1, hs2, feed_append, feed_append]
          have hstep :=
            step_narrow_marks (hw1c ▸ hrow) hm1 rfl rfl
              (by
                rw [hw1c]; exact hmar)
              hw1 rfl
          obtain ⟨pd, hM, hO⟩ :=
            ih (m - 1) (by omega) (n + 1) _ (g.at n).pen
              (by
                rw [cellText_cols (g.at n) hm1.ground hm1.u8need hm1.u8acc]; exact hw1c)
              (by omega) (by omega) hstep
          exact
            ⟨pd, hM,
              ((offRow_pen_prefix Y (g.at n) pen hmatch.ground hmatch.u8need).trans
                    (offRow_narrow_marks (hw1c ▸ hrow) hm1 rfl rfl
                      (by
                        rw [hw1c]; exact hmar)
                      hw1 rfl)).trans
                hO⟩
        · -- margin narrow (n + 1 = cols)
          have hmeq : n + 1 = cols := by omega
          have hm2 : m = 1 := by omega
          subst hm2
          simp only [Nat.sub_self, List.range_zero, List.map_nil, List.foldl_nil]
          rw [feed_append]
          have hcell :
            OffRow Y w
              ((w.feed (if (g.at n).pen == pen then ([] : Bytes) else penSgr (g.at n).pen)).feed
                (cellText (g.at n))) :=
            (offRow_pen_prefix Y (g.at n) pen hmatch.ground hmatch.u8need).trans
              (offRow_narrow_margin_marks (hw1c ▸ hrow) hm1 rfl rfl
                (by
                  rw [hw1c]; exact hncols)
                (by
                  rw [hw1c]; omega)
                hw1 rfl)
          refine ⟨true, ?_, hcell⟩
          have hstep :=
            step_narrow_margin_marks (hw1c ▸ hrow) hm1 rfl rfl
              (by
                rw [hw1c]; exact hncols)
              (by
                rw [hw1c]; omega)
              hw1 rfl
          rw [show cols - 1 = n from by omega, ← hmeq]
          exact hstep
      · -- WIDE: (g.at n).width = 2
        have hw2 : (g.at n).width = 2 := by omega
        have hshadow : g.at (n + 1) = Cell.shadow (g.at n) := (hrow.pairs n).1 hw2
        have hn1 : n + 1 < cols := by
          rcases Nat.lt_or_ge (n + 1) cols with h | h
          · exact h
          · exfalso
            have hd : g.at (n + 1) = default :=
              at_of_size_le g (n + 1)
                (by
                  rw [hrow.size]; omega)
            rw [hd] at hshadow
            have hcw := congrArg Cell.width hshadow
            rw [show (default : Cell).width = 1 from rfl,
              show (Cell.shadow (g.at n)).width = 0 from rfl] at hcw
            exact absurd hcw (by decide)
        have hrs : RowOk g.size g := by
          rw [hrow.size]; exact hrow
        have hsm : utf8s (g.at (n + 1)).marks = [] := shadow_emits_nothing hrs hw2
        have hshw0 : (g.at (n + 1)).width = 0 := by
          rw [hshadow]; rfl
        have hm1 := pen_prefix_matches hmatch (g.at n)
        have hw1c :
          (w.feed (if (g.at n).pen == pen then ([] : Bytes) else penSgr (g.at n).pen)).cols =
            cols := by
          rw [pen_prefix_cols (g.at n) pen hmatch.ground hmatch.u8need]; exact hcols
        -- peel the shadow cell too
        rw [range_map_cons g (n + 1) (m - 1) (by omega), List.foldl_cons]
        by_cases hmk : (g.at n).marks = []
        · -- wide, no marks: base body is `cellText`
          rw [rowSlot_eq_wide_nomarks (g.at n) pen n hw2 hmk,
            rowSlot_eq_shadow (g.at (n + 1)) _ (g.at n).pen (n + 1) hshw0, hsm, List.append_nil]
          obtain ⟨hs1, hs2⟩ :=
            rowSlot_fold_split ((List.range (m - 1 - 1)).map (fun i => g.at (n + 1 + 1 + i)))
              ((if (g.at n).pen == pen then [] else penSgr (g.at n).pen) ++ cellText (g.at n))
              (g.at n).pen (n + 2)
          rw [hs1, hs2, feed_append, feed_append]
          by_cases hmar2 : n + 2 < cols
          · -- interior wide
            have hstep :=
              step_wide (hw1c ▸ hrow) hm1 rfl rfl
                (by
                  rw [hw1c]; exact hn1)
                (by
                  rw [hw1c]; exact hmar2)
                hw2 hmk rfl
            obtain ⟨pd, hM, hO⟩ :=
              ih (m - 2) (by omega) (n + 2) _ (g.at n).pen
                (by
                  rw [cellText_cols (g.at n) hm1.ground hm1.u8need hm1.u8acc]; exact hw1c)
                (by omega) (by omega) hstep
            exact
              ⟨pd, hM,
                ((offRow_pen_prefix Y (g.at n) pen hmatch.ground hmatch.u8need).trans
                      (offRow_wide (hw1c ▸ hrow) hm1 rfl rfl
                        (by
                          rw [hw1c]; exact hn1)
                        hw2 hmk)).trans
                  hO⟩
          · -- margin wide (n + 2 = cols)
            have hmeq2 : n + 2 = cols := by omega
            rw [show m - 1 - 1 = 0 from by omega]
            simp only [List.range_zero, List.map_nil, List.foldl_nil, feed_nil]
            have hcell :
              OffRow Y w
                ((w.feed (if (g.at n).pen == pen then ([] : Bytes) else penSgr (g.at n).pen)).feed
                  (cellText (g.at n))) :=
              (offRow_pen_prefix Y (g.at n) pen hmatch.ground hmatch.u8need).trans
                (offRow_wide (hw1c ▸ hrow) hm1 rfl rfl
                  (by
                    rw [hw1c]; exact hn1)
                  hw2 hmk)
            refine ⟨true, ?_, hcell⟩
            have hstep :=
              step_wide_margin (hw1c ▸ hrow) hm1 rfl rfl
                (by
                  rw [hw1c]; exact hn1)
                (by
                  rw [hw1c]; omega)
                hw2 hmk rfl
            rw [hw1c] at hstep
            rw [← hmeq2, show n + 2 - 1 = cols - 1 from by omega]
            exact hstep
        · -- wide, marks: base body is the CHA dance
          rw [rowSlot_eq_wide_marks (g.at n) pen n hw2 hmk,
            rowSlot_eq_shadow (g.at (n + 1)) _ (g.at n).pen (n + 1) hshw0, hsm, List.append_nil]
          obtain ⟨hs1, hs2⟩ :=
            rowSlot_fold_split ((List.range (m - 1 - 1)).map (fun i => g.at (n + 1 + 1 + i)))
              ((if (g.at n).pen == pen then [] else penSgr (g.at n).pen) ++
                (utf8 (safeChar (g.at n).base) ++ csiNum (n + 2) 0x47 ++ utf8s (g.at n).marks ++
                  csiNum (n + 3) 0x47))
              (g.at n).pen (n + 2)
          rw [hs1, hs2, feed_append, feed_append]
          by_cases hmar2 : n + 2 < cols
          · -- interior wide with marks
            have hstep :=
              step_wide_marks (hw1c ▸ hrow) hm1 rfl rfl
                (by
                  rw [hw1c]; exact hn1)
                (by
                  rw [hw1c]; exact hmar2)
                (by omega) hw2 rfl
            obtain ⟨pd, hM, hO⟩ :=
              ih (m - 2) (by omega) (n + 2) _ (g.at n).pen
                (by
                  rw [dance_cols (g.at n).base (g.at n).marks (n + 2) (n + 3) hm1.ground hm1.u8need
                      hm1.u8acc (by omega) (by omega) (by omega) (by omega)]
                  exact hw1c)
                (by omega) (by omega) hstep
            exact
              ⟨pd, hM,
                ((offRow_pen_prefix Y (g.at n) pen hmatch.ground hmatch.u8need).trans
                      (offRow_wide_marks (hw1c ▸ hrow) hm1 rfl rfl
                        (by
                          rw [hw1c]; exact hn1)
                        (by
                          rw [hw1c]; exact hmar2)
                        (by omega) hw2 rfl)).trans
                  hO⟩
          · -- margin wide with marks (n + 2 = cols)
            have hmeq2 : n + 2 = cols := by omega
            rw [show m - 1 - 1 = 0 from by omega]
            simp only [List.range_zero, List.map_nil, List.foldl_nil, feed_nil]
            have hcell :
              OffRow Y w
                ((w.feed (if (g.at n).pen == pen then ([] : Bytes) else penSgr (g.at n).pen)).feed
                  (utf8 (safeChar (g.at n).base) ++ csiNum (n + 2) 0x47 ++ utf8s (g.at n).marks ++
                    csiNum (n + 3) 0x47)) :=
              (offRow_pen_prefix Y (g.at n) pen hmatch.ground hmatch.u8need).trans
                (offRow_wide_margin_marks (hw1c ▸ hrow) hm1 rfl rfl
                  (by
                    rw [hw1c]; exact hn1)
                  (by
                    rw [hw1c]; omega)
                  (by omega) hw2 rfl)
            refine ⟨false, ?_, hcell⟩
            have hstep :=
              step_wide_margin_marks (hw1c ▸ hrow) hm1 rfl rfl
                (by
                  rw [hw1c]; exact hn1)
                (by
                  rw [hw1c]; omega)
                (by omega) hw2 rfl
            rw [hw1c] at hstep
            rw [← hmeq2, show n + 2 - 1 = cols - 1 from by omega]
            exact hstep

/-- **A painted row lands, for any receiver.** Feeding `rowAnsi g startPen` into a receiver
that matches `g` on nothing yet (frontier 0), with `startPen` in effect, paints the whole
row: the receiver ends matching `g` at every column, with `rowAnsi`'s returned pen in
effect so a grid can thread it into the next row. `pending` is left existential — it depends
on the last cell's shape (§ Step 3 constraint 3) and the joining `CR` discards it. -/
theorem rowAnsi_writes_row {w : Vt} {g : Row} {startPen : Pen} {Y : Nat} (hrow : RowOk w.cols g)
    (hcb : w.cols < 65533) (hpos : 0 < w.cols)
    (hm : Matches w { x := 0, y := Y, pen := startPen, pending := false } g 0) :
    ∃ pd : Bool,
      Matches (w.feed (rowAnsi g startPen).1)
          { x := w.cols - 1, y := Y, pen := (rowAnsi g startPen).2, pending := pd } g w.cols ∧
        OffRow Y w (w.feed (rowAnsi g startPen).1) := by
  have key := paint_range (cols := w.cols) hrow hcb w.cols 0 w startPen rfl (by omega) hpos hm
  have hlist :
    ((List.range w.cols).map (fun i => g.at (0 + i))).foldl rowSlot ([], startPen, 0) =
      g.foldl rowSlot ([], startPen, 0) := by
    rw [foldl_rowSlot_range g ([], startPen, 0), hrow.size]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [Nat.zero_add]
  rw [hlist] at key
  rw [show (rowAnsi g startPen).1 = (g.foldl rowSlot ([], startPen, 0)).1 from rfl,
    show (rowAnsi g startPen).2 = (g.foldl rowSlot ([], startPen, 0)).2.1 from rfl]
  exact key

/-! ### The grid walk — `joinCRLF` over the rows

`rowAnsi_writes_row` paints one row; `OffRow` says it leaves the others alone. The grid
walk threads them with `CRLF` separators, and the whole no-scroll argument is one fact:
between rows the cursor sits at `y < bot`, so the `LF` moves down rather than scrolling
(`lineFeed_interior`). `joinCRLF` emits no *trailing* separator, so the last row's `LF`
— the only one that could scroll — never happens. -/

/-- **`CRLF` between rows: cursor to the next row's start, every cell untouched.** The `CR`
discards any wrap-`pending` the row's last cell armed, and the `LF` (below `bot`) does not
scroll — so the whole `CRLF` is one clean cursor move on `v`, leaving grid, dims and modes. -/
theorem crlf_step {v : Vt} (hg : v.pstate = .ground) (hu : v.u8need = 0) (hy : v.cursor.y < v.bot)
    (hlt : v.bot < v.rows) :
    v.feed [0x0D, 0x0A] =
      { v with cursor := { x := 0, y := v.cursor.y + 1, pending := false } } := by
  rw [crlf_feed hg hu, lineFeed_interior v.carriageReturn (by exact hy) (by exact hlt)]
  rfl

/-- The per-row byte list `gridAnsi` builds, with the pen threaded — head-first, so the row
walk can peel it. Reversing `gridAnsi`'s accumulated rows produces this same list. -/
def rowsAnsi : List Row → Pen → List Bytes
  | [], _ => []
  | r :: rs, p => (rowAnsi r p).1 :: rowsAnsi rs (rowAnsi r p).2

/-- The reference left-appending fold produces exactly `rowsAnsi`. -/
theorem gridFold_eq_rowsAnsi :
    ∀ (rs : List Row) (pre : List Bytes) (p : Pen),
      (rs.foldl
            (fun (acc : List Bytes × Pen) row =>
              ((acc.1 ++ [(rowAnsi row acc.2).1]), (rowAnsi row acc.2).2))
            (pre, p)).1 =
        pre ++ rowsAnsi rs p
  | [], pre, p => by simp [rowsAnsi]
  | r :: rs, pre, p => by
    rw [List.foldl_cons, gridFold_eq_rowsAnsi rs (pre ++ [(rowAnsi r p).1]) (rowAnsi r p).2]
    rw [List.append_assoc]
    rfl

theorem gridAnsi_eq (grid : Array Row) :
    gridAnsi grid = csiNum 0 0x6D ++ (csiB ++ [0x48] ++ joinCRLF (rowsAnsi grid.toList {})) := by
  let rev := fun (acc : List Bytes × Pen) => (acc.1.reverse, acc.2)
  have h :=
    Array.foldl_hom rev (g₁ := fun acc row =>
      (acc.1 ++ [(rowAnsi row acc.2).1], (rowAnsi row acc.2).2)) (g₂ := fun acc row =>
      ((rowAnsi row acc.2).1 :: acc.1, (rowAnsi row acc.2).2)) (xs := grid) (init :=
      ([], ({} : Pen)))
      (by
        rintro ⟨bs, p⟩ row; simp [rev, List.reverse_append])
  have hr := congrArg (fun acc : List Bytes × Pen => acc.1.reverse) h
  simp only [rev, List.reverse_nil, List.reverse_reverse] at hr
  unfold gridAnsi
  dsimp only
  rw [hr]
  rw [show
      (grid.foldl
            (fun (acc : List Bytes × Pen) row =>
              ((acc.1 ++ [(rowAnsi row acc.2).1]), (rowAnsi row acc.2).2))
            ([], ({} : Pen))).1 =
        rowsAnsi grid.toList {}
      from by
      rw [← Array.foldl_toList, gridFold_eq_rowsAnsi grid.toList [] {}]; rfl]

/-- In range, `getD` returns the element whatever the default is. -/
theorem getD_lt' {α} (a : Array α) (i : Nat) (d : α) (h : i < a.size) : a.getD i d = a[i] := by
  rw [Array.getD, dite_eq_left h]; rfl

/-- Row length depends only on the grid and the column count, not the pen (which sets the
out-of-range default's *content*, never its size). -/
theorem size_getRow_congr {v w : Vt} (hg : v.grid = w.grid) (hc : v.cols = w.cols) (y : Nat) :
    (v.getRow y).size = (w.getRow y).size := by
  unfold Vt.getRow
  rw [hg]
  by_cases h : y < w.grid.size
  · rw [getD_lt' w.grid y (blankRow v.cols v.pen) h, getD_lt' w.grid y (blankRow w.cols w.pen) h]
  · rw [Array.getD, dite_eq_right h, Array.getD, dite_eq_right h]; simp [blankRow, hc]

/-- **A grid equals its target when every in-range cell agrees and the rows are the right
length.** The array-`ext` plumbing the grid claim needs, done once: grid `ext` over rows,
then row `ext` over columns, both bounded to what's actually there. -/
theorem grid_eq_of_cells {w : Vt} {tg : Array Row} {cols rows : Nat} (hwsz : w.grid.size = rows)
    (htgsz : tg.size = rows)
    (hcell :
      ∀ y', y' < rows → ∀ x, x < cols → w.getCell x y' = (tg.getD y' (blankRow cols {})).at x)
    (hwlen : ∀ y', y' < rows → (w.getRow y').size = cols)
    (htglen : ∀ y', y' < rows → (tg.getD y' (blankRow cols {})).size = cols) : w.grid = tg := by
  apply Array.ext
  · rw [hwsz, htgsz]
  · intro y' hy _
    have hyr : y' < rows := by
      rw [hwsz] at hy; exact hy
    have hrow : w.getRow y' = tg.getD y' (blankRow cols {}) := by
      apply Array.ext
      · rw [hwlen y' hyr, htglen y' hyr]
      · intro x hx _
        have hxc : x < cols := by
          rw [hwlen y' hyr] at hx; exact hx
        have := hcell y' hyr x hxc
        rw [show w.getCell x y' = (w.getRow y')[x] from by
            unfold Vt.getCell;
            rw [getD_lt' _ x default
                (by
                  rw [hwlen y' hyr]; exact hxc)],
          show (tg.getD y' (blankRow cols {})).at x = (tg.getD y' (blankRow cols {}))[x] from by
            unfold Row.at;
            rw [getD_lt' _ x default
                (by
                  rw [htglen y' hyr]; exact hxc)]] at this
        exact this
    rw [show w.grid[y'] = w.getRow y' from by
        unfold Vt.getRow;
        rw [getD_lt' _ y' _
            (by
              rw [hwsz]; exact hyr)],
      show tg[y'] = tg.getD y' (blankRow cols {}) from
        (getD_lt' tg y' (blankRow cols {})
            (by
              rw [htgsz]; exact hyr)).symm]
    exact hrow

/-- Build the frontier-0 `Matches` a row's paint starts from, out of the receiver's plain
state. Every field is a hypothesis the grid walk already carries; the `cells` obligation is
vacuous at frontier 0. -/
theorem matches_zero {w : Vt} {g : Row} {Y : Nat} {p : Pen} (hx : w.cursor.x = 0)
    (hy : w.cursor.y = Y) (hpd : w.cursor.pending = false) (hpen : w.pen = p)
    (hg : w.pstate = .ground) (hu : w.u8need = 0) (ha : w.u8acc = 0) (hins : w.modes.insert = false)
    (hwrap : w.modes.wrap = true) (h0 : w.g0Line = false) (h1 : w.g1Line = false)
    (hrl : (w.getRow Y).size = w.cols) (hin : Y < w.grid.size) :
    Matches w { x := 0, y := Y, pen := p, pending := false } g 0 :=
  ⟨hx, hy, hpd, hpen, hg, hu, ha, hins, hwrap, h0, h1, hrl, hin, Or.inl rfl, fun j hj =>
    absurd hj (by omega)⟩

/-- A painted row *is* the source row, as arrays: `Matches` at the full width plus both
being `cols` long makes them equal cell for cell and length for length. -/
theorem row_eq_of_paint {w : Vt} {g : Row} {Y cols : Nat} {pp : Pen} {pd : Bool}
    (hcols : w.cols = cols) (hrok : RowOk cols g)
    (hm : Matches w { x := cols - 1, y := Y, pen := pp, pending := pd } g cols) :
    w.getRow Y = g := by
  have hsz : (w.getRow Y).size = cols := by
    have := hm.rowLen; rw [hcols] at this; exact this
  apply Array.ext
  · rw [hsz, hrok.size]
  · intro j hj1 hj2
    have hjc : j < cols := by
      rw [hsz] at hj1; exact hj1
    have hjr : j < (w.getRow Y).size := by
      rw [hsz]; exact hjc
    have hjg : j < g.size := by
      rw [hrok.size]; exact hjc
    have hc : (w.getRow Y).getD j default = g.getD j default := hm.cells j hjc
    rw [getD_lt' (w.getRow Y) j default hjr, getD_lt' g j default hjg] at hc
    exact hc

/-- The receiver, poised to paint row `Y` of a `rows × cols` grid onto the target `tg`.
Bundled so the row walk's twenty-odd invariants read as one hypothesis and re-establish as
one. `done` is the running invariant: rows below `Y` already match `tg`. -/
structure Walking (cols rows : Nat) (tg : Array Row) (w : Vt) (Y : Nat) (p : Pen) : Prop where
  colsEq : w.cols = cols
  rowsEq : w.rows = rows
  top : w.top = 0
  bot : w.bot = rows - 1
  ground : w.pstate = .ground
  u8need : w.u8need = 0
  u8acc : w.u8acc = 0
  ins : w.modes.insert = false
  wrap : w.modes.wrap = true
  g0 : w.g0Line = false
  g1 : w.g1Line = false
  curx : w.cursor.x = 0
  cury : w.cursor.y = Y
  cpend : w.cursor.pending = false
  pen : w.pen = p
  gsz : w.grid.size = rows
  rlens : ∀ y', (w.getRow y').size = cols
  done : ∀ y' x, y' < Y → w.getCell x y' = (tg.getD y' (blankRow cols {})).at x

/-- **The grid walk.** Painting the source rows `rs` from row `Y` onward carries the
receiver to a grid that matches `tg` on every row: rows below `Y` were already right and are
left alone (`OffRow`), row `Y` is painted (`rowAnsi_writes_row`), and the `CRLF` between rows
moves down without scrolling (`crlf_step`, since `Y < bot`). `joinCRLF`'s missing trailing
separator is why the last row's line feed — the only one that could scroll — never fires. -/
theorem paint_rows {cols rows : Nat} {tg : Array Row} (hcb : cols < 65533) (hpos : 0 < cols) :
    ∀ (rs : List Row) (Y : Nat) (w : Vt) (p : Pen),
      Walking cols rows tg w Y p →
        Y + rs.length = rows →
        (∀ i (hi : i < rs.length), RowOk cols rs[i]) →
        (∀ i (hi : i < rs.length), rs[i] = tg.getD (Y + i) (blankRow cols {})) →
        (∀ y' x,
            y' < rows →
              (w.feed (joinCRLF (rowsAnsi rs p))).getCell x y' =
                (tg.getD y' (blankRow cols {})).at x) ∧
          (w.feed (joinCRLF (rowsAnsi rs p))).grid.size = rows ∧
          (∀ y', ((w.feed (joinCRLF (rowsAnsi rs p))).getRow y').size = cols) ∧
          (w.feed (joinCRLF (rowsAnsi rs p))).pstate = .ground ∧
          (w.feed (joinCRLF (rowsAnsi rs p))).u8need = 0 ∧
          (w.feed (joinCRLF (rowsAnsi rs p))).u8acc = 0 ∧
          (w.feed (joinCRLF (rowsAnsi rs p))).modes.insert = false ∧
          (w.feed (joinCRLF (rowsAnsi rs p))).modes.wrap = true ∧
          (w.feed (joinCRLF (rowsAnsi rs p))).sb = w.sb
  | [], Y, w, p, hw, hsum, _, _ => by
    have hYrows : Y = rows := by simpa using hsum
    subst hYrows
    show
      (∀ y' x,
          y' < Y →
            (w.feed (joinCRLF (rowsAnsi [] p))).getCell x y' =
              (tg.getD y' (blankRow cols {})).at x) ∧
        _ ∧ _
    rw [show rowsAnsi ([] : List Row) p = [] from rfl,
      show joinCRLF ([] : List Bytes) = [] from rfl, feed_nil]
    exact
      ⟨fun y' x h => hw.done y' x h, hw.gsz, hw.rlens, hw.ground, hw.u8need, hw.u8acc, hw.ins,
        hw.wrap, rfl⟩
  | r :: rest, Y, w, p, hw, hsum, hrsok, hrstg => by
    have hYrows : Y < rows := by
      simp only [List.length_cons] at hsum; omega
    have hr0 : r = tg.getD Y (blankRow cols {}) := by
      have := hrstg 0 (by simp); simpa using this
    have hrok0 : RowOk cols r := by
      have := hrsok 0 (by simp); simpa using this
    -- paint row Y
    have hgsY : Y < w.grid.size := by
      rw [hw.gsz]; exact hYrows
    have hm0 : Matches w { x := 0, y := Y, pen := p, pending := false } r 0 :=
      matches_zero hw.curx hw.cury hw.cpend hw.pen hw.ground hw.u8need hw.u8acc hw.ins hw.wrap hw.g0
        hw.g1 (by rw [hw.rlens Y, hw.colsEq]) hgsY
    have hrow_w : RowOk w.cols r := by
      rw [hw.colsEq]; exact hrok0
    obtain ⟨pd, hM, hO⟩ :=
      rowAnsi_writes_row hrow_w
        (by
          rw [hw.colsEq]; exact hcb)
        (by
          rw [hw.colsEq]; exact hpos)
        hm0
    -- the painted row equals the source, hence the target
    have hrowY : (w.feed (rowAnsi r p).1).getRow Y = r :=
      row_eq_of_paint (cols := w.cols) hO.cols hrow_w hM
    cases rest with
    | nil =>
      -- last row: no trailing CRLF
      have hYlast : Y + 1 = rows := by simpa using hsum
      rw [show rowsAnsi [r] p = [(rowAnsi r p).1] from rfl,
        show joinCRLF [(rowAnsi r p).1] = (rowAnsi r p).1 from rfl]
      refine ⟨fun y' x hy' => ?_, ?_, ?_, hM.ground, hM.u8need, hM.u8acc, hM.ins, hM.wrap, hO.sb⟩
      · by_cases hyY : y' = Y
        · subst hyY
          rw [show (w.feed (rowAnsi r p).1).getCell x y' = ((w.feed (rowAnsi r p).1).getRow y').at x
              from rfl,
            hrowY, hr0]
        · rw [hO.cells x y' hyY
              (by
                rw [hw.gsz]; omega)]
          exact hw.done y' x (by omega)
      · rw [hO.gridSize, hw.gsz]
      · intro y'; rw [hO.sizes y', hw.rlens y']
    | cons r' rest' =>
      -- an interior row: paint, then CRLF, then recurse
      have hstick : stick (w.feed (rowAnsi r p).1) = stick w := (smap_id_rowAnsi r p w hw.ground).2
      have hbot1 : (w.feed (rowAnsi r p).1).bot = rows - 1 := by
        have := congrArg Sticky.bot hstick; rw [stick_bot, stick_bot] at this; rw [this];
        exact hw.bot
      have hrows1 : (w.feed (rowAnsi r p).1).rows = rows := by
        have := congrArg Sticky.rows hstick; rw [stick_rows, stick_rows] at this
        rw [this]; exact hw.rowsEq
      have htop1 : (w.feed (rowAnsi r p).1).top = 0 := by
        have := congrArg Sticky.top hstick; rw [stick_top, stick_top] at this; rw [this];
        exact hw.top
      have hg01 : (w.feed (rowAnsi r p).1).g0Line = false := by
        have := congrArg Sticky.g0 hstick; rw [stick_g0, stick_g0] at this; rw [this]; exact hw.g0
      have hg11 : (w.feed (rowAnsi r p).1).g1Line = false := by
        have := congrArg Sticky.g1 hstick; rw [stick_g1, stick_g1] at this; rw [this]; exact hw.g1
      have hcuryY : (w.feed (rowAnsi r p).1).cursor.y = Y := hM.curY
      have hcrlfy : (w.feed (rowAnsi r p).1).cursor.y < (w.feed (rowAnsi r p).1).bot := by
        rw [hcuryY, hbot1]; simp only [List.length_cons] at hsum; omega
      have hcrlf :=
        crlf_step hM.ground hM.u8need hcrlfy
          (by
            rw [hbot1]; omega)
      rw [show
          joinCRLF (rowsAnsi (r :: r' :: rest') p) =
            (rowAnsi r p).1 ++ [0x0D, 0x0A] ++ joinCRLF (rowsAnsi (r' :: rest') (rowAnsi r p).2)
          from rfl,
        feed_append, feed_append, hcrlf, hcuryY]
      have hwalk :
        Walking cols rows tg
          { (w.feed (rowAnsi r p).1) with cursor := { x := 0, y := Y + 1, pending := false } }
          (Y + 1) (rowAnsi r p).2 := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
        · show (w.feed (rowAnsi r p).1).cols = cols
          rw [hO.cols, hw.colsEq]
        · exact hrows1
        · exact htop1
        · exact hbot1
        · exact hM.ground
        · exact hM.u8need
        · exact hM.u8acc
        · exact hM.ins
        · exact hM.wrap
        · exact hg01
        · exact hg11
        · exact hM.pen
        · show (w.feed (rowAnsi r p).1).grid.size = rows
          rw [hO.gridSize, hw.gsz]
        · intro y'
          show ((w.feed (rowAnsi r p).1).getRow y').size = cols
          rw [hO.sizes y', hw.rlens y']
        · intro y' x hy'
          show ((w.feed (rowAnsi r p).1).getCell x y') = (tg.getD y' (blankRow cols {})).at x
          by_cases hyY : y' = Y
          · subst hyY
            rw [show
                (w.feed (rowAnsi r p).1).getCell x y' = ((w.feed (rowAnsi r p).1).getRow y').at x
                from rfl,
              hrowY, hr0]
          · rw [hO.cells x y' hyY
                (by
                  rw [hw.gsz]; omega)]
            exact hw.done y' x (by omega)
      obtain ⟨hcellR, hgszR, hrlR, hgrR, hunR, huaR, hinsR, hwrapR, hsbR⟩ :=
        paint_rows hcb hpos (r' :: rest') (Y + 1)
          { (w.feed (rowAnsi r p).1) with cursor := { x := 0, y := Y + 1, pending := false } }
          (rowAnsi r p).2 hwalk
          (by
            simp only [List.length_cons] at hsum ⊢; omega)
          (fun i hi => by
            have :=
              hrsok (i + 1)
                (by
                  simp only [List.length_cons] at hi ⊢; omega)
            simpa using this)
          (fun i hi => by
            have :=
              hrstg (i + 1)
                (by
                  simp only [List.length_cons] at hi ⊢; omega)
            rw [show Y + (i + 1) = Y + 1 + i from by omega] at this
            simpa using this)
      exact ⟨hcellR, hgszR, hrlR, hgrR, hunR, huaR, hinsR, hwrapR, hsbR.trans hO.sb⟩

/-! ### `gridAnsi`, painted into a receiver — the grid claim's core

`gridAnsi` is `SGR 0 · CSI H · joinCRLF (rows)`: reset the pen to default, home the cursor,
paint. The `SGR 0` and the home are what let the walk start from a *known* `(0, 0, {})`
whatever the receiver's cursor and pen were; `paint_rows` does the rest. -/

/-- **A bare `CSI H` is `moveTo 0 0`**, as a state equation. With no parameters both
arguments fall back to `1`, and with DECOM off `moveTo 0 0` is the true origin rather than
the scroll region's top, which is why `prologueAnsi` resets `?6l` before the paint.
`csiFinish` returns to ground and `moveTo` keeps it, so every non-cursor field frames
through at once. -/
theorem home_feed_eq {v : Vt} (hg : v.pstate = .ground) (hu : v.u8need = 0) :
    v.feed (csiB ++ [0x48]) = v.moveTo 0 0 := by
  rw [show (csiB ++ [0x48] : Bytes) = [0x1B, 0x5B] ++ [(0x48 : UInt8)] from by simp [csiB]]
  rw [feed_append, keeps_csi_open hg hu,
    show ∀ (u : Vt), u.feed [(0x48 : UInt8)] = u.step 0x48 from fun _ => rfl]
  rw [csi_final_step_eq 0x48 (v := { v with pstate := .csi ({} : CsiState) }) (s := ({} : CsiState))
      rfl (by simpa using hu) rfl (by decide) (by decide)]
  unfold Vt.csiFinish
  rw [ite_eq_right (by decide)]
  dsimp only
  rw [show
      ({ v with pstate := .csi ({} : CsiState) } : Vt).csiDispatch ({} : CsiState) 0x48 =
        ({ v with pstate := .csi ({} : CsiState) } : Vt).moveTo 0 0
      from by
      unfold Vt.csiDispatch; rw [ite_eq_right (by decide)]; rfl]
  show
    ({ ({ v with pstate := .csi ({} : CsiState) } : Vt).moveTo 0 0 with pstate := .ground } : Vt) =
      v.moveTo 0 0
  unfold Vt.moveTo
  rw [hg]

/-- **The grid, painted.** From a receiver established by the prologue (ground, the right
modes, `top = 0`, `bot = rows - 1`, no alt screen) and of matching dimensions with
reproducible rows, `gridAnsi v.grid` reproduces `v.grid` exactly — array for array, cell for
cell. This is the heart of the grid claim; `restore_grid_of_paint` bolts the clear and the
tail onto it.

The seventh conjunct is the **history**, and it is here rather than in a `Fixes (·.sb)` lemma
because `gridAnsi` cannot have one: the stage ends in `joinCRLF`, and a `CRLF` with the cursor
at the region bottom scrolls with `allowSb := true` and pushes the evicted row. Invariance is
therefore conditional on the row count, which this hypothesis list already carries — `hvsz` is
the load-bearing one, and the claim is false without it (a target taller than the receiver
pushes exactly `v.grid.size - v.rows` rows). -/
theorem gridAnsi_writes_grid {u v : Vt} (hcols : u.cols = v.cols) (hrows : u.rows = v.rows)
    (hpos : 0 < v.cols) (hub : v.cols < 65533) (htop : u.top = 0) (hbot : u.bot = v.rows - 1)
    (hg : u.pstate = .ground) (hun : u.u8need = 0) (hua : u.u8acc = 0)
    (hins : u.modes.insert = false) (hwrap : u.modes.wrap = true) (horg : u.modes.origin = false)
    (hg0 : u.g0Line = false) (hg1 : u.g1Line = false) (hgsz : u.grid.size = v.rows)
    (hrlens : ∀ y', (u.getRow y').size = v.cols)
    (hvok : ∀ y', RowOk v.cols (v.grid.getD y' (blankRow v.cols {})))
    (hvsz : v.grid.size = v.rows) :
    (u.feed (gridAnsi v.grid)).grid = v.grid ∧
      (u.feed (gridAnsi v.grid)).pstate = .ground ∧
      (u.feed (gridAnsi v.grid)).u8need = 0 ∧
      (u.feed (gridAnsi v.grid)).u8acc = 0 ∧
      (u.feed (gridAnsi v.grid)).modes.insert = false ∧
      (u.feed (gridAnsi v.grid)).modes.wrap = true ∧ (u.feed (gridAnsi v.grid)).sb = u.sb := by
  -- `insert`/`wrap` are `Walking` invariants the walk re-establishes, surfaced by
  -- `paint_rows`. (origin rides the `Quiet` family instead — `quiet_gridAnsi` — since it is
  -- about the whole `gridAnsi` term and would not survive `gridAnsi_eq`'s rewrite here.)
  rw [gridAnsi_eq]
  -- reset the pen, then home the cursor: a known (0, 0, {}) entry state
  have hsgr : u.feed (csiNum 0 0x6D) = { u with pen := {} } := by
    rw [show csiNum 0 0x6D = sgrOf [0] from by simp [csiNum, sgrOf, joinSemi],
      sgrOf_feed [0] (by decide) (by decide) (by decide) hg hun,
      show penAfter u.pen [0] = ({} : Pen) from by
        simp [penAfter, sgrParamsOf, Vt.applySgr.go, Vt.sgrAttr]]
  rw [feed_append, feed_append, hsgr, home_feed_eq (v := { u with pen := ({} : Pen) }) hg hun]
  have hu2cursor :
    (({ u with pen := ({} : Pen) }).moveTo 0 0).cursor.x = 0 ∧
      (({ u with pen := ({} : Pen) }).moveTo 0 0).cursor.y = 0 ∧
      (({ u with pen := ({} : Pen) }).moveTo 0 0).cursor.pending = false := by
    simp [Vt.moveTo, horg]
  have hwalk : Walking v.cols v.rows v.grid (({ u with pen := ({} : Pen) }).moveTo 0 0) 0 {} := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [frame_moveTo]; exact hcols
    · rw [frame_moveTo]; exact hrows
    · rw [frame_moveTo]; exact htop
    · rw [frame_moveTo]; exact hbot
    · rw [frame_moveTo]; exact hg
    · rw [frame_moveTo]; exact hun
    · rw [frame_moveTo]; exact hua
    · rw [frame_moveTo]; exact hins
    · rw [frame_moveTo]; exact hwrap
    · rw [frame_moveTo]; exact hg0
    · rw [frame_moveTo]; exact hg1
    · exact hu2cursor.1
    · exact hu2cursor.2.1
    · exact hu2cursor.2.2
    · rw [frame_moveTo]
    · rw [frame_moveTo]; exact hgsz
    · intro y'
      exact
        (size_getRow_congr (v := ({ u with pen := ({} : Pen) }).moveTo 0 0) (w := u)
              (by rw [frame_moveTo]) (by rw [frame_moveTo]) y').trans
          (hrlens y')
    · intro y' x h; exact absurd h (by omega)
  have hrs_len : v.grid.toList.length = v.rows := by
    rw [← hvsz]; simp
  have htlist :
    ∀ i (hi : i < v.grid.toList.length), v.grid.toList[i] = v.grid.getD i (blankRow v.cols {}) :=
    fun i hi => by
    rw [Array.getElem_toList, getD_lt' v.grid i (blankRow v.cols {}) (by simpa using hi)]
  obtain ⟨hcell, hgsz', hrl', hpg', hpu', hpa', hpi', hpw', hpsb⟩ :=
    paint_rows hub hpos v.grid.toList 0 (({ u with pen := ({} : Pen) }).moveTo 0 0) {} hwalk
      (by
        rw [Nat.zero_add]; exact hrs_len)
      (fun i hi => by
        rw [htlist i hi]; exact hvok i)
      (fun i hi => by rw [htlist i hi, Nat.zero_add])
  refine
    ⟨grid_eq_of_cells (cols := v.cols) (rows := v.rows) hgsz' hvsz ?_ (fun y' _ => hrl' y') ?_,
      hpg', hpu', hpa', hpi', hpw', hpsb.trans (by rw [frame_moveTo])⟩
  · intro y' hyr x _; exact hcell y' x hyr
  · intro y' _; exact (hvok y').size

/-- **`gridAnsi_writes_grid` with the target grid as a bare `Array Row`.** The stashed main
grid in `screensAnsi`'s alt branch is not any `Vt`'s `.grid`, so the paint theorem is restated
over an explicit `tg : Array Row` and its `cols`/`rows`. Threading them through a receiver
record whose own dimensions are set to `cols`/`rows` makes every hypothesis line up
definitionally. -/
theorem gridAnsi_writes_rows {u : Vt} {tg : Array Row} {cols rows : Nat} (hcols : u.cols = cols)
    (hrows : u.rows = rows) (hpos : 0 < cols) (hub : cols < 65533) (htop : u.top = 0)
    (hbot : u.bot = rows - 1) (hg : u.pstate = .ground) (hun : u.u8need = 0) (hua : u.u8acc = 0)
    (hins : u.modes.insert = false) (hwrap : u.modes.wrap = true) (horg : u.modes.origin = false)
    (hg0 : u.g0Line = false) (hg1 : u.g1Line = false) (hgsz : u.grid.size = rows)
    (hrlens : ∀ y', (u.getRow y').size = cols)
    (hvok : ∀ y', RowOk cols (tg.getD y' (blankRow cols {}))) (hvsz : tg.size = rows) :
    (u.feed (gridAnsi tg)).grid = tg ∧
      (u.feed (gridAnsi tg)).pstate = .ground ∧
      (u.feed (gridAnsi tg)).u8need = 0 ∧
      (u.feed (gridAnsi tg)).u8acc = 0 ∧
      (u.feed (gridAnsi tg)).modes.insert = false ∧
      (u.feed (gridAnsi tg)).modes.wrap = true ∧ (u.feed (gridAnsi tg)).sb = u.sb :=
  gridAnsi_writes_grid (u := u) (v :=
    { u with
      grid := tg, cols := cols, rows := rows })
    hcols hrows hpos hub htop hbot hg hun hua hins hwrap horg hg0 hg1 hgsz hrlens hvok hvsz

/-! ### The prologue's canonical mid-stream state — the entry `gridAnsi_writes_grid` assumes

`restore_sticky_any` computes the sticky bundle at the *end* of the stream (the session's
values, set by the tail). The grid walk needs it *after the prologue* — canonical: region
whole, no alt screen, ASCII charsets — which is the same chain stopped early. `rows ≥ 2` is
`DECSTBM`'s own constraint (a one-row region is degenerate); the one-row grid is handled
without it, since a single row cannot scroll. `DECSTBM`'s *parameter* cap
(`v.rows < 65535`) is not a hypothesis: this is the only place in the chain that consumes it,
and `Good w`'s `rowsLe` plus `hrows` supply it, so it is derived rather than stated. -/

theorem prologue_sticky (v w : Vt) (hgood : Good w) (hrows : w.rows = v.rows) :
    (w.feed (prologueAnsi v)).pstate = .ground ∧
      stick (w.feed (prologueAnsi v)) = ⟨v.rows, 0, v.rows - 1, false, false, false, false⟩ := by
  have hfits : v.rows < 65535 := by
    have := hgood.rowsLe; rw [hrows] at this; omega
  have hpos1 : 1 ≤ v.rows := hrows ▸ hgood.rowsPos
  rw [show
      prologueAnsi v =
        escSeq 0x5C ++ modeSet 1049 false ++ csiNum 4 0x6C ++ modeSet 6 false ++ modeSet 7 true ++
          csiNum2 1 v.rows 0x72 ++
          escCharset 0x28 0x42 ++
          escCharset 0x29 0x42 ++
          [0x0F]
      from by simp only [prologueAnsi]]
  obtain ⟨A, hA⟩ : ∃ y : Sticky, stAlt false (stick (w.feed (escSeq 0x5C))) = y := ⟨_, rfl⟩
  have hArows : A.rows = v.rows := by
    rw [← hA, stAlt_rows]; exact (rows_st_lead w).trans hrows
  have hAalt : A.alt = false := by
    rw [← hA]; exact stAlt_alt false _
  obtain ⟨Ar, At, Ab, Ag0, Ag1, Aso, Aal⟩ := A
  simp only at hArows hAalt
  subst hArows hAalt
  -- For a one-row screen `DECSTBM 1;1r` is a no-op, so the region it leaves is whatever the
  -- lead-in left — which `Good w` forces to be whole (`bot < rows = 1` ⟹ `bot = 0`, `top ≤ bot`).
  have hAtb : v.rows = 1 → At = 0 ∧ Ab = 0 := by
    intro hr1
    have hgoodE : Good (w.feed (escSeq 0x5C)) := Good.feed _ hgood
    have hrE : (w.feed (escSeq 0x5C)).rows = 1 := by
      rw [rows_st_lead, hrows]; exact hr1
    have key :
      (stAlt false (stick (w.feed (escSeq 0x5C)))).top = 0 ∧
        (stAlt false (stick (w.feed (escSeq 0x5C)))).bot = 0 := by
      unfold stAlt; dsimp only
      by_cases ha : (stick (w.feed (escSeq 0x5C))).alt = true
      · rw [ite_eq_left ha]
        exact
          ⟨rfl, by
            show (stick (w.feed (escSeq 0x5C))).rows - 1 = 0; rw [stick_rows, hrE]⟩
      · rw [ite_eq_right ha]
        have hb0 : (w.feed (escSeq 0x5C)).bot = 0 := by
          have := hgoodE.botLt; rw [hrE] at this; omega
        have ht0 : (w.feed (escSeq 0x5C)).top = 0 := by
          have := hgoodE.topLe; omega
        exact
          ⟨by
            show (stick (w.feed (escSeq 0x5C))).top = 0; rw [stick_top]; exact ht0, by
            show (stick (w.feed (escSeq 0x5C))).bot = 0; rw [stick_bot]; exact hb0⟩
    rw [hA] at key; exact key
  have h0 :
    (w.feed (escSeq 0x5C)).pstate = .ground ∧
      stick (w.feed (escSeq 0x5C)) = stick (w.feed (escSeq 0x5C)) :=
    ⟨(st_grounds w).1, rfl⟩
  have h1 := sput_congr (sput_step h0 (smap_modeSet 1049 false (by decide) (by decide))) hA
  have h2s := sput_congr (sput_step h1 smap_id_irm_reset) (id_eq _)
  have h3 :=
    sput_congr (sput_step h2s (smap_modeSet 6 false (by decide) (by decide)))
      (stSetMode_of_not_screen false _)
  have h4 :=
    sput_congr (sput_step h3 (smap_modeSet 7 true (by decide) (by decide)))
      (stSetMode_of_not_screen true _)
  have h5 :=
    sput_congr (sput_step h4 (smap_stbm 1 v.rows (by decide) (by omega) (by decide) (by omega)))
      (show
        stStbm (1 - 1) (v.rows - 1) (⟨v.rows, At, Ab, Ag0, Ag1, Aso, false⟩ : Sticky) =
          ⟨v.rows, 0, v.rows - 1, Ag0, Ag1, Aso, false⟩
        from by
        by_cases hrge : 0 < v.rows - 1
        · rw [stStbm_of (by omega)
              (show v.rows - 1 < (⟨v.rows, At, Ab, Ag0, Ag1, Aso, false⟩ : Sticky).rows from by
                simp only; omega)]
        · have hr1 : v.rows = 1 := by omega
          obtain ⟨hat0, hab0⟩ := hAtb hr1
          rw [hr1, hat0, hab0]; rfl)
  have h6 :=
    sput_congr (sput_step h5 (smap_charset 0x28 0x42 (Or.inl rfl) (by decide) (by decide)))
      (show
        stCharset 0x28 0x42 (⟨v.rows, 0, v.rows - 1, Ag0, Ag1, Aso, false⟩ : Sticky) =
          ⟨v.rows, 0, v.rows - 1, false, Ag1, Aso, false⟩
        from by
        unfold stCharset; rw [ite_eq_left (by decide)]; rfl)
  have h7 :=
    sput_congr (sput_step h6 (smap_charset 0x29 0x42 (Or.inr rfl) (by decide) (by decide)))
      (show
        stCharset 0x29 0x42 (⟨v.rows, 0, v.rows - 1, false, Ag1, Aso, false⟩ : Sticky) =
          ⟨v.rows, 0, v.rows - 1, false, false, Aso, false⟩
        from by
        unfold stCharset; rw [ite_eq_right (by decide), ite_eq_left (by decide)]; rfl)
  have h8 :=
    sput_congr (sput_step h7 smap_si)
      (show
        ({ (⟨v.rows, 0, v.rows - 1, false, false, Aso, false⟩ : Sticky) with so := false }) =
          ⟨v.rows, 0, v.rows - 1, false, false, false, false⟩
        from rfl)
  exact h8

/-- The prologue's `DECSTBM` (`CSI 1 ; rows r`) writes no `Modes` field — it moves the
region and homes the cursor, both outside `Modes`. -/
theorem mmap_id_stbm2 (a b : Nat) : MMap id (csiNum2 a b 0x72) := by
  rw [show csiNum2 a b 0x72 = csiB ++ (digits a ++ [0x3B] ++ digits b) ++ [0x72] from by
      simp [csiNum2, csiB, List.append_assoc]]
  exact
    mmap_id_csi_seq _ 0x72 (paramBytes_digits2 a b) (by decide) (by decide)
      (fun w t => modes_csiDispatch_stbm w t)

/-- `DECAWM`/`DECOM` on the abstract modes: each sets exactly its field. `DECOM` goes
through `moveTo`, which frames away. -/
theorem smMod_daw7 (X : Modes) (on : Bool) : smMod 7 on X = { X with wrap := on } := by rfl

theorem smMod_dom6 (X : Modes) (on : Bool) : smMod 6 on X = { X with origin := on } := by
  show
    (({ Vt.init 1 1 with modes := { X with origin := on } }).moveTo 0 0).modes =
      { X with origin := on }
  rw [frame_moveTo]

/-- **The prologue leaves insert off, wrap on, origin off** — the three `Modes` facts the
grid walk needs, established absolutely by `IRM 4l`, `DECAWM ?7h`, `DECOM ?6l`, and untouched
by the region set, the charsets and the shift state that follow. -/
theorem prologue_modes (v w : Vt) :
    (w.feed (prologueAnsi v)).modes.insert = false ∧
      (w.feed (prologueAnsi v)).modes.wrap = true ∧
      (w.feed (prologueAnsi v)).modes.origin = false := by
  rw [show
      prologueAnsi v =
        escSeq 0x5C ++
          (modeSet 1049 false ++ csiNum 4 0x6C ++ modeSet 6 false ++ modeSet 7 true ++
            csiNum2 1 v.rows 0x72 ++
            escCharset 0x28 0x42 ++
            escCharset 0x29 0x42 ++
            [0x0F])
      from by simp only [prologueAnsi, List.append_assoc],
    feed_append]
  obtain ⟨hlg, hlu⟩ := st_grounds w
  -- the mode-affecting chain, after the lead-in has grounded the receiver
  have hmm :
    MMap (fun m => smMod 7 true (smMod 6 false ({ (smMod 1049 false m) with insert := false })))
      (modeSet 1049 false ++ csiNum 4 0x6C ++ modeSet 6 false ++ modeSet 7 true ++
        csiNum2 1 v.rows 0x72 ++
        escCharset 0x28 0x42 ++
        escCharset 0x29 0x42 ++
        [0x0F]) := by
    have :=
      (((((((mmap_modeSet 1049 false (by decide) (by decide)).comp (mmap_irm false)).comp
                            (mmap_modeSet 6 false (by decide) (by decide))).comp
                        (mmap_modeSet 7 true (by decide) (by decide))).comp
                    (mmap_id_stbm2 1 v.rows)).comp
                (mmap_id_charset 0x28 0x42 (Or.inl rfl) (by decide) (by decide))).comp
            (mmap_id_charset 0x29 0x42 (Or.inr rfl) (by decide) (by decide))).comp
        mmap_id_si
    refine this.congr (fun m => ?_)
    simp only [id_eq]
  obtain ⟨-, -, hmodes⟩ := hmm (w.feed (escSeq 0x5C)) hlg hlu
  rw [hmodes]
  dsimp only
  rw [smMod_daw7, smMod_dom6]
  exact ⟨rfl, rfl, rfl⟩

/-! ### The paint's entry state, assembled

`gridAnsi_writes_grid` asks for a receiver already established. `restore` establishes it with
`prologueAnsi ++ SGR 0 ++ ED 2`, and every fact it needs is now available: the sticky bundle
and the modes from the prologue, the dimensions from `dims_feed`, the reproducible rows from
`renderable_feed`, and the decoder from `uaz_feed` — the last being the one that needed its
own argument, since a CSI final byte zeroes `u8need` but not `u8acc`. -/

/-- **All bytes ASCII** — the side condition `uaz_feed` reads. Composable like `Ends`,
`Quiet` and `ParamBytes`, so each emitter stage discharges it once. -/
def Ascii (bs : Bytes) : Prop := ∀ b ∈ bs, b < 0x80

theorem Ascii.nil : Ascii [] := fun _ h => absurd h (by simp)

theorem Ascii.append {a b : Bytes} (ha : Ascii a) (hb : Ascii b) : Ascii (a ++ b) := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact ha x h
  · exact hb x h

theorem Ascii.cons {x : UInt8} {l : Bytes} (hx : x < 0x80) (hl : Ascii l) : Ascii (x :: l) := by
  intro y hy
  rcases List.mem_cons.mp hy with h | h
  · subst h; exact hx
  · exact hl y h

theorem ascii_digits (n : Nat) : Ascii (digits n) := by
  intro b hb; have := digits_range n b hb; grind

theorem ascii_csiB : Ascii csiB := Ascii.cons (by decide) (Ascii.cons (by decide) Ascii.nil)

theorem ascii_escB : Ascii escB := Ascii.cons (by decide) Ascii.nil

theorem ascii_csiNum (n : Nat) (f : UInt8) (hf : f < 0x80) : Ascii (csiNum n f) := by
  rw [show csiNum n f = csiB ++ digits n ++ [f] from rfl]
  exact (ascii_csiB.append (ascii_digits n)).append (Ascii.cons hf Ascii.nil)

theorem ascii_csiNum2 (a b : Nat) (f : UInt8) (hf : f < 0x80) : Ascii (csiNum2 a b f) := by
  rw [show csiNum2 a b f = csiB ++ digits a ++ [0x3B] ++ digits b ++ [f] from rfl]
  exact
    (((ascii_csiB.append (ascii_digits a)).append (Ascii.cons (by decide) Ascii.nil)).append
          (ascii_digits b)).append
      (Ascii.cons hf Ascii.nil)

theorem ascii_csiPriv (n : Nat) (f : UInt8) (hf : f < 0x80) : Ascii (csiPriv n f) := by
  rw [show csiPriv n f = csiB ++ [0x3F] ++ digits n ++ [f] from rfl]
  exact
    ((ascii_csiB.append (Ascii.cons (by decide) Ascii.nil)).append (ascii_digits n)).append
      (Ascii.cons hf Ascii.nil)

theorem ascii_modeSet (n : Nat) (on : Bool) : Ascii (modeSet n on) := by
  unfold modeSet
  exact ascii_csiPriv n _ (by cases on <;> decide)

theorem ascii_escSeq (f : UInt8) (hf : f < 0x80) : Ascii (escSeq f) := by
  rw [show escSeq f = escB ++ [f] from rfl]
  exact ascii_escB.append (Ascii.cons hf Ascii.nil)

theorem ascii_escCharset (i x : UInt8) (hi : i < 0x80) (hx : x < 0x80) :
    Ascii (escCharset i x) := by
  rw [show escCharset i x = escB ++ [i, x] from rfl]
  exact ascii_escB.append (Ascii.cons hi (Ascii.cons hx Ascii.nil))

theorem ascii_joinSemi : ∀ (l : List Nat), Ascii (joinSemi l)
  | [] => Ascii.nil
  | [n] => by
    rw [show joinSemi [n] = digits n from rfl]; exact ascii_digits n
  | n :: m :: l => by
    rw [show joinSemi (n :: m :: l) = digits n ++ [0x3B] ++ joinSemi (m :: l) from rfl]
    exact
      (ascii_digits n |>.append (Ascii.cons (by decide) Ascii.nil)).append (ascii_joinSemi (m :: l))

theorem ascii_sgrOf (codes : List Nat) : Ascii (sgrOf codes) := by
  rw [show sgrOf codes = csiB ++ joinSemi codes ++ [0x6D] from rfl]
  exact (ascii_csiB.append (ascii_joinSemi codes)).append (Ascii.cons (by decide) Ascii.nil)

theorem ascii_sgrColorSeq (c : Color) (isFg : Bool) : Ascii (sgrColorSeq c isFg) := by
  unfold sgrColorSeq
  split
  · exact Ascii.nil
  · exact ascii_sgrOf _

theorem ascii_penSgr (p : Pen) : Ascii (penSgr p) := by
  unfold penSgr
  exact ((ascii_sgrOf _).append (ascii_sgrColorSeq _ _)).append (ascii_sgrColorSeq _ _)

/-- The establishing prefix — prologue, SGR reset, clear — is all ASCII. -/
theorem ascii_paint_prefix (v : Vt) : Ascii (prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A) := by
  refine
    (Ascii.append ?_ (ascii_csiNum 0 0x6D (by decide))).append (ascii_csiNum 2 0x4A (by decide))
  unfold prologueAnsi
  exact
    ((((((((ascii_escSeq 0x5C (by decide)).append (ascii_modeSet 1049 false)).append
                              (ascii_csiNum 4 0x6C (by decide))).append
                          (ascii_modeSet 6 false)).append
                      (ascii_modeSet 7 true)).append
                  (ascii_csiNum2 1 v.rows 0x72 (by decide))).append
              (ascii_escCharset 0x28 0x42 (by decide) (by decide))).append
          (ascii_escCharset 0x29 0x42 (by decide) (by decide))).append
      (Ascii.cons (by decide) Ascii.nil)

/-- **The paint's entry state.** After the establishing prefix, a `Good`/`Renderable` receiver
of the session's dimensions — whose decoder is quiesced, which is the `u8acc` precondition —
satisfies every hypothesis `gridAnsi_writes_grid` asks for. -/
theorem paint_entry (v w : Vt) (hgood : Good w) (hren : Renderable w) (hcols : w.cols = v.cols)
    (hrows : w.rows = v.rows) (hua : w.u8acc = 0) (hun : w.u8need = 0) :
    let u := w.feed (prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A)
    u.cols = v.cols ∧
      u.rows = v.rows ∧
      u.top = 0 ∧
      u.bot = v.rows - 1 ∧
      u.pstate = .ground ∧
      u.u8need = 0 ∧
      u.u8acc = 0 ∧
      u.modes.insert = false ∧
      u.modes.wrap = true ∧
      u.modes.origin = false ∧
      u.g0Line = false ∧
      u.g1Line = false ∧
      u.grid.size = v.rows ∧
      (∀ y', (u.getRow y').size = v.cols) ∧
      u.altGrid = none ∧ stick u = ⟨v.rows, 0, v.rows - 1, false, false, false, false⟩ := by
  intro u
  -- dimensions: no linger stream emits RIS, but `Good` is what `dims_feed` needs anyway
  have hd : dims u = dims w := dims_feed _ hgood
  have hucols : u.cols = v.cols := by
    rw [← dims_fst u, hd, dims_fst]; exact hcols
  have hurows : u.rows = v.rows := by
    rw [← dims_snd u, hd, dims_snd]; exact hrows
  -- reproducible rows survive any stream
  have hurend : Renderable u := renderable_feed hren _
  obtain ⟨hgsz, hrok⟩ := hurend.main
  -- the sticky bundle and the modes, from the prologue, then through `SGR 0` and `ED 2`
  have hpro := prologue_sticky v w hgood hrows
  have hst :
    (u.pstate = .ground ∧ stick u = ⟨v.rows, 0, v.rows - 1, false, false, false, false⟩) := by
    have e1 := sput_congr (sput_step hpro (smap_id_sgrNum 0)) (id_eq _)
    have e2 := sput_congr (sput_step e1 (smap_id_ed 2)) (id_eq _)
    exact e2
  have hmod : u.modes.insert = false ∧ u.modes.wrap = true ∧ u.modes.origin = false := by
    obtain ⟨hi, hw, ho⟩ := prologue_modes v w
    have hm : MMap id (csiNum 0 0x6D ++ csiNum 2 0x4A) := mmap_id_append mmap_id_sgr (mmap_id_ed 2)
    have hpg : (w.feed (prologueAnsi v)).pstate = .ground := prologue_grounds v w
    have hpu : (w.feed (prologueAnsi v)).u8need = 0 :=
      (uaz_feed (prologueAnsi v)
          (fun b hb =>
            ascii_paint_prefix v b (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hb)))))
          hun hua).1
    obtain ⟨-, -, hmm⟩ := hm (w.feed (prologueAnsi v)) hpg hpu
    have : u.modes = (w.feed (prologueAnsi v)).modes := by
      show (w.feed (prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A)).modes = _
      rw [show
          prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A =
            prologueAnsi v ++ (csiNum 0 0x6D ++ csiNum 2 0x4A)
          from by simp only [List.append_assoc],
        feed_append, hmm, id_eq]
    rw [this]
    exact ⟨hi, hw, ho⟩
  -- the decoder: the whole prefix is ASCII, so nothing is half-decoded
  obtain ⟨huun, huua⟩ := uaz_feed _ (ascii_paint_prefix v) hun hua
  refine
    ⟨hucols, hurows, ?_, ?_, hst.1, huun, huua, hmod.1, hmod.2.1, hmod.2.2, ?_, ?_, by
      rw [hgsz, hurows], fun y' => ?_, ?_, hst.2⟩
  case refine_6 =>
    have : u.altGrid.isSome = false := by rw [← stick_alt u, hst.2]
    exact
      Option.not_isSome_iff_eq_none.mp
        (by
          rw [this]; simp)
  · rw [← stick_top u, hst.2]
  · rw [← stick_bot u, hst.2]
  · rw [← stick_g0 u, hst.2]
  · rw [← stick_g1 u, hst.2]
  · have := (hrok y').size
    rw [show u.getRow y' = u.grid.getD y' (blankRow u.cols u.pen) from rfl]
    by_cases hy : y' < u.grid.size
    · rw [getD_lt' u.grid y' _ hy, ← getD_lt' u.grid y' (blankRow u.cols {}) hy, hucols] at *
      exact this
    · rw [Array.getD, dite_eq_right hy]
      show (blankRow u.cols u.pen).size = v.cols
      rw [show (blankRow u.cols u.pen).size = u.cols from by simp [blankRow]]; exact hucols

/-! ### The history stage, between the prefix and the paint

`screensAnsi` now leads with `scrollbackAnsi v`, so the paint's entry state has to
survive it. It does, and — the point of the whole staged design —
**with no hypothesis about the ring**: none of `paint_entry`'s sixteen conjuncts is
about cells, and `Good`/`Renderable` are preserved by feeding *any* bytes. A
`RowOk`/`fitRow`/`v.sb` hypothesis in a *screen* proof would mean the staging broke. -/

/-- **The bridge.** Feeding the history stage after `paint_entry`'s prefix
re-establishes all sixteen of `paint_entry`'s conjuncts, so
`gridAnsi_writes_grid` can be applied at the later state unchanged.

Where each comes from: dims by `dims_feed`; the region, charsets, shift state and
which-screen from `smap_id_scrollbackAnsi` (`SMap` carries no `u8need` side
condition, which is what makes those one line each); `grid.size`/row lengths from
`renderable_feed`; and `u8need` plus the three modes from `sbTail_modes`, i.e. from
the stage's ESC-leading mode tail — **not** from "the stage ends in ASCII", which
is not a route: `uaz_feed` needs every byte below 0x80 and the ring paint emits
glyphs. `u8acc` then follows from `u8Ok_feed`. -/
theorem scrollback_entry {u v : Vt} (hgood : Good u) (hren : Renderable u) (hcols : u.cols = v.cols)
    (hrows : u.rows = v.rows) (hg : u.pstate = .ground) (hua : u.u8acc = 0)
    (hst : stick u = ⟨v.rows, 0, v.rows - 1, false, false, false, false⟩) :
    let z := u.feed (scrollbackAnsi v)
    z.cols = v.cols ∧
      z.rows = v.rows ∧
      z.top = 0 ∧
      z.bot = v.rows - 1 ∧
      z.pstate = .ground ∧
      z.u8need = 0 ∧
      z.u8acc = 0 ∧
      z.modes.insert = false ∧
      z.modes.wrap = true ∧
      z.modes.origin = false ∧
      z.g0Line = false ∧
      z.g1Line = false ∧
      z.grid.size = v.rows ∧
      (∀ y', (z.getRow y').size = v.cols) ∧
      z.altGrid = none ∧ stick z = ⟨v.rows, 0, v.rows - 1, false, false, false, false⟩ := by
  intro z
  -- the sticky bundle, straight through
  obtain ⟨hzg, hzst⟩ := smap_id_scrollbackAnsi v u hg
  have hstz : stick z = ⟨v.rows, 0, v.rows - 1, false, false, false, false⟩ := by
    show stick (u.feed (scrollbackAnsi v)) = _
    rw [hzst, id_eq, hst]
  -- dimensions
  have hd : dims z = dims u := dims_feed _ hgood
  have hzcols : z.cols = v.cols := by
    rw [← dims_fst z, hd, dims_fst]; exact hcols
  have hzrows : z.rows = v.rows := by
    rw [← dims_snd z, hd, dims_snd]; exact hrows
  -- reproducible rows survive any stream
  obtain ⟨hgsz, hrok⟩ := (renderable_feed hren (scrollbackAnsi v)).main
  -- the decoder and the three modes, through the ESC-leading mode tail
  have hsplit :
    scrollbackAnsi v =
      (if (sbRows v).isEmpty then []
        else csiNum 3 0x4A ++ gridAnsi (sbRows v) ++ (List.replicate v.rows crlfB).flatten) ++
        (csiNum 4 0x6C ++ modeSet 6 false ++ modeSet 7 true) := by
    unfold scrollbackAnsi; simp only [List.append_assoc]
  obtain ⟨-, hzun, hzins, hzwrap, hzorg⟩ := sbTail_modes (smap_id_sbPush v u hg).1
  have hzun' : z.u8need = 0 := by
    show (u.feed (scrollbackAnsi v)).u8need = 0
    rw [hsplit, feed_append]
    exact hzun
  have hzua : z.u8acc = 0 := u8Ok_feed (scrollbackAnsi v) (fun _ => hua) hzun'
  refine
    ⟨hzcols, hzrows, ?_, ?_, hzg, hzun', hzua, ?_, ?_, ?_, ?_, ?_, by rw [hgsz, hzrows], fun y' =>
      ?_, ?_, hstz⟩
  · rw [← stick_top z, hstz]
  · rw [← stick_bot z, hstz]
  · show (u.feed (scrollbackAnsi v)).modes.insert = false
    rw [hsplit, feed_append]; exact hzins
  · show (u.feed (scrollbackAnsi v)).modes.wrap = true
    rw [hsplit, feed_append]; exact hzwrap
  · show (u.feed (scrollbackAnsi v)).modes.origin = false
    rw [hsplit, feed_append]; exact hzorg
  · rw [← stick_g0 z, hstz]
  · rw [← stick_g1 z, hstz]
  · have := (hrok y').size
    rw [show z.getRow y' = z.grid.getD y' (blankRow z.cols z.pen) from rfl]
    by_cases hy : y' < z.grid.size
    · rw [getD_lt' z.grid y' _ hy, ← getD_lt' z.grid y' (blankRow z.cols {}) hy, hzcols] at *
      exact this
    · rw [Array.getD, dite_eq_right hy]
      show (blankRow z.cols z.pen).size = v.cols
      rw [show (blankRow z.cols z.pen).size = z.cols from by simp [blankRow]]; exact hzcols
  · have hns : z.altGrid.isSome = false := by rw [← stick_alt z, hstz]
    exact
      Option.not_isSome_iff_eq_none.mp
        (by
          rw [hns]; simp)

/-- The post-paint receiver retains the prologue's geometry, region and ASCII
translation. The alt branch resets the same full-screen region at its switch. -/
theorem restore_paint_canonical (v w : Vt) (hgood : Good w) (hren : Renderable w)
    (hcols : w.cols = v.cols) (hrows : w.rows = v.rows) (hua : w.u8acc = 0) (hun : w.u8need = 0) :
    let u := w.feed (prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v)
    u.cols = v.cols ∧
      u.rows = v.rows ∧
      u.top = 0 ∧
      u.bot = v.rows - 1 ∧ u.g0Line = false ∧ u.g1Line = false ∧ u.modes.origin = false := by
  intro u
  obtain ⟨-, -, -, -, ep, -, -, -, -, eo, -, -, -, -, -, es⟩ :=
    paint_entry v w hgood hren hcols hrows hua hun
  have hs := (smap_screensAnsi v _ ep).2
  rw [es] at hs
  have hf :
    (if v.altGrid.isSome then stAlt true else id)
        ⟨v.rows, 0, v.rows - 1, false, false, false, false⟩ =
      ⟨v.rows, 0, v.rows - 1, false, false, false, v.altGrid.isSome⟩ := by
    split <;> simp_all only [stAlt, Bool.false_eq_true, ↓reduceIte, id_eq]
  rw [hf] at hs
  have hsu : stick u = ⟨v.rows, 0, v.rows - 1, false, false, false, v.altGrid.isSome⟩ := by
    simpa only [u, feed_append] using hs
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← dims_fst, dims_feed _ hgood, dims_fst]; exact hcols
  · rw [← dims_snd, dims_feed _ hgood, dims_snd]; exact hrows
  · rw [← stick_top, hsu]
  · rw [← stick_bot, hsu]
  · rw [← stick_g0, hsu]
  · rw [← stick_g1, hsu]
  · dsimp only [u]
    rw [feed_append]
    exact (quiet_screensAnsi v _ ep eo).2

/-- Existing-cell replay replaces the metadata-only grid frame for the full
tail. All receiver facts are supplied by the original paint proof. -/
theorem restore_grid_of_paint (v w : Vt) (hgood : Good w) (hren : Renderable w)
    (hcols : w.cols = v.cols) (hrows : w.rows = v.rows) (hua : w.u8acc = 0) (hun : w.u8need = 0)
    (hps :
      (w.feed (prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v)).pstate = .ground)
    (hn : (w.feed (prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v)).u8need = 0)
    (hgrid :
      (w.feed (prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v)).grid = v.grid)
    (hins :
      (w.feed (prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v)).modes.insert =
        false)
    (hwrap :
      (w.feed (prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v)).modes.wrap =
        true) :
    (w.feed (restore v)).grid = v.grid := by
  let u := w.feed (prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v)
  obtain ⟨uc, ur, ut, ub, u0, u1, uo⟩ := restore_paint_canonical v w hgood hren hcols hrows hua hun
  have ua : u.u8acc = 0 := u8Ok_feed _ (fun _ => hua) hn
  have hf :=
    pending_tail_frames v u (Good.feed _ hgood) (renderable_feed hren _) uc ur hgrid ut ub u0 u1
      hwrap hins uo hps hn ua
  let a := u.feed (regionAnsi v ++ tabsAnsi v ++ savedAnsi v)
  let b := a.feed (savedPendingAnsi v)
  let c := b.feed (titleAnsi v ++ modesAnsi v ++ charsetAnsi v ++ penSgr v.pen ++ cursorAnsi v)
  have ha := (((keeps_regionAnsi v).append (keeps_tabsAnsi v)).append (keeps_savedAnsi v)) u hps hn
  have hc :=
    (((((keeps_titleAnsi v).append (keeps_modesAnsi v)).append (keeps_charsetAnsi v)).append
            (keeps_penSgr v.pen)).append
        (keeps_cursorAnsi v))
      b hf.1 hf.2.1
  have he : (c.feed (cursorPendingAnsi v)).grid = v.grid :=
    hf.2.2.2.2.2.2.1.trans (hc.2.2.trans (hf.2.2.1.trans (ha.2.2.trans hgrid)))
  simpa only [restore_split, u, a, b, c, feed_append] using he

/-! ### `restore_grid_any` — Definition-of-done item 5

The composition. `screensAnsi` has two branches; on the main screen it is exactly
`gridAnsi v.grid`, so `paint_entry` + `gridAnsi_writes_grid` + `restore_grid_of_paint` close
it. `hua`/`hun` are the decoder precondition — real here, and **not** hypotheses of
`restore_grid_reachable`: reachability supplies `hua` via `U8Ok`, and `hun` is discharged by
the stream itself (`feed_restore_zeroed`, since `restore` opens with `ESC`). -/

/-- **The grid, restored into any client — main screen.** For a session not on the alt
screen, feeding `restore v` to any `Good`/`Renderable` receiver of the session's dimensions
and with a quiesced decoder leaves the receiver's grid equal to `v.grid`, cell for cell and
pen for pen.

`Renderable v` carries the row count the last `CRLF` of the paint needs — `hvren.main.1` *is*
`v.grid.size = v.rows`, so a separate binder for it would be the same fact stated twice. The
two column bounds stay, and are the honest ones: `gridAnsi_writes_grid` takes no `Good`, so
they are its hypotheses rather than this one's, and `restore_grid_any` derives them once for
both branches. -/
theorem restore_grid_any_main (v w : Vt) (hgood : Good w) (hren : Renderable w)
    (hcols : w.cols = v.cols) (hrows : w.rows = v.rows) (hua : w.u8acc = 0) (hun : w.u8need = 0)
    (halt : v.altGrid = none) (hpos : 0 < v.cols) (hub : v.cols < 65533) (hvren : Renderable v) :
    (w.feed (restore v)).grid = v.grid := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, -, est⟩ :=
    paint_entry v w hgood hren hcols hrows hua hun
  -- the history stage sits between the prefix and the paint, and hands the paint
  -- back the same sixteen conjuncts (`scrollback_entry`)
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, -, -⟩ :=
    scrollback_entry (u := w.feed (prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A)) (v := v)
      (Good.feed _ hgood) (renderable_feed hren _) e1 e2 e5 e7 est
  have hscreens : screensAnsi v = scrollbackAnsi v ++ gridAnsi v.grid := by
    unfold screensAnsi; rw [halt]
  have hpaint :=
    gridAnsi_writes_grid f1 f2 hpos hub f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 (by rw [f13]) f14
      hvren.main.2 hvren.main.1
  have hpeel :
    w.feed (prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v) =
      ((w.feed (prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A)).feed (scrollbackAnsi v)).feed
        (gridAnsi v.grid) := by
    rw [hscreens]; simp only [feed_append]
  refine restore_grid_of_paint v w hgood hren hcols hrows hua hun ?_ ?_ ?_ ?_ ?_
  · rw [hpeel]; exact hpaint.2.1
  · rw [hpeel]; exact hpaint.2.2.1
  · rw [hpeel]; exact hpaint.1
  · rw [hpeel]; exact hpaint.2.2.2.2.1
  · rw [hpeel]; exact hpaint.2.2.2.2.2.1

/-! ### The alt screen — `restore_grid_any`'s other branch

On the alt screen `screensAnsi` paints main, parks the stashed cursor/pen, switches with
`?1049h`, then paints the alt grid. The switch is the useful part: `Vt.enterAlt` *replaces*
the client's grid with a fresh blank of the right shape and resets the region, so the second
paint's entry state is established by the switch itself rather than inherited — which makes
this branch cleaner than the main one, not harder. What it needs is the switch as a **state**
equation, which the modes-only `modeSet_modes` did not give. -/

/-- **The alt switch establishes the second paint's entry state by itself.** `enterAlt`
replaces the grid with a fresh blank of the receiver's shape, homes the cursor and resets the
region — so nothing has to be inherited across the main paint. The `altGrid = none`
hypothesis is what makes the switch fire, and the prologue's `?1049l` is what supplies it. -/
theorem alt_switch_entry {u : Vt} (halt : u.altGrid = none) (hg : u.pstate = .ground)
    (hun : u.u8need = 0) :
    let z := u.feed (csiPriv 1049 0x68)
    z.cols = u.cols ∧
      z.rows = u.rows ∧
      z.top = 0 ∧
      z.bot = u.rows - 1 ∧
      z.pstate = .ground ∧
      z.u8need = u.u8need ∧
      z.u8acc = u.u8acc ∧
      z.modes = u.modes ∧
      z.g0Line = u.g0Line ∧
      z.g1Line = u.g1Line ∧
      z.grid = Array.replicate u.rows (blankRow u.cols {}) ∧
      z.cursor.x = 0 ∧ z.cursor.y = 0 ∧ z.cursor.pending = false := by
  intro z
  have heq : z = { u.enterAlt true with pstate := .ground } := by
    show u.feed (csiPriv 1049 0x68) = _
    rw [show csiPriv 1049 0x68 = modeSet 1049 true from rfl,
      modeSet_feed_eq 1049 true (by decide) (by decide) hg hun,
      show u.setMode true 1049 true = u.enterAlt true from rfl]
  have hent :
    u.enterAlt true =
      { u with
        altGrid := some (u.grid, u.cursor, u.pen),
        grid := Array.replicate u.rows (blankRow u.cols {}), cursor := {},
        saved := { cur := u.cursor, pen := u.pen }, top := 0, bot := u.rows - 1 } := by
    unfold Vt.enterAlt
    dsimp only
    rw [ite_eq_right
        (show ¬(u.altGrid.isSome = true) from by
          rw [halt]; simp),
      ite_eq_left rfl]
  rw [heq, hent]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Every row of a freshly-blanked grid (what `enterAlt` installs) is `cols` cells long,
whatever the default the `getRow` lookup would fall back to. -/
theorem getRow_size_replicate {u : Vt} {n c : Nat} (hg : u.grid = Array.replicate n (blankRow c {}))
    (hc : u.cols = c) (y' : Nat) : (u.getRow y').size = c := by
  show (u.grid.getD y' (blankRow u.cols u.pen)).size = c
  rw [hg]
  by_cases hy : y' < n
  · rw [show (Array.replicate n (blankRow c {})).getD y' (blankRow u.cols u.pen) = blankRow c {}
        from by simp [Array.getD, Array.size_replicate, Array.getElem_replicate, hy]]
    simp [blankRow, Array.size_replicate]
  · rw [show
        (Array.replicate n (blankRow c {})).getD y' (blankRow u.cols u.pen) = blankRow u.cols u.pen
        from by simp [Array.getD, Array.size_replicate, hy]]
    simp only [blankRow, Array.size_replicate]; exact hc

/-- **The state just before the alt switch is fully re-established.** Feed a receiver `z` (in
the prologue's canonical entry state) the discarded main paint `gridAnsi mg` and then the park
(`penSgr`/`CUP`); every field the second paint's entry state reads is left intact — dimensions,
region top, no alt screen, the decoder quiesced, the three paint modes and the ASCII charsets.
The main paint's *cells* are thrown away by the switch, so only these framed invariants matter:
`insert`/`wrap` from `gridAnsi_writes_rows`'s exposed output, `origin` from the `Quiet` frame,
the sticky fields from `SMap`, the dimensions from `dims_feed`; the park preserves all of them
(`MMap`/`SMap`/`uaz_feed`). This is what carries the modes to the switch without an `origin`
field on `Matches`. -/
theorem alt_pre_switch {z : Vt} {mg : Array Row} {mc : Cursor} {mp : Pen} {cols rows : Nat}
    (hcols : z.cols = cols) (hrows : z.rows = rows) (htop : z.top = 0) (hbot : z.bot = rows - 1)
    (hg : z.pstate = .ground) (hun : z.u8need = 0) (hua : z.u8acc = 0)
    (hins : z.modes.insert = false) (hwrap : z.modes.wrap = true) (horg : z.modes.origin = false)
    (hg0 : z.g0Line = false) (hg1 : z.g1Line = false) (hgsz : z.grid.size = rows)
    (hrlens : ∀ y', (z.getRow y').size = cols) (halt : z.altGrid = none) (hgood : Good z)
    (hpos : 0 < cols) (hub : cols < 65533) (hmok : ∀ y', RowOk cols (mg.getD y' (blankRow cols {})))
    (hmsz : mg.size = rows) :
    ((z.feed (gridAnsi mg)).feed (penSgr mp ++ csiNum2 (mc.y + 1) (mc.x + 1) 0x48)).cols = cols ∧
      ((z.feed (gridAnsi mg)).feed (penSgr mp ++ csiNum2 (mc.y + 1) (mc.x + 1) 0x48)).rows = rows ∧
      ((z.feed (gridAnsi mg)).feed (penSgr mp ++ csiNum2 (mc.y + 1) (mc.x + 1) 0x48)).top = 0 ∧
      ((z.feed (gridAnsi mg)).feed (penSgr mp ++ csiNum2 (mc.y + 1) (mc.x + 1) 0x48)).altGrid =
        none ∧
      ((z.feed (gridAnsi mg)).feed (penSgr mp ++ csiNum2 (mc.y + 1) (mc.x + 1) 0x48)).pstate =
        .ground ∧
      ((z.feed (gridAnsi mg)).feed (penSgr mp ++ csiNum2 (mc.y + 1) (mc.x + 1) 0x48)).u8need = 0 ∧
      ((z.feed (gridAnsi mg)).feed (penSgr mp ++ csiNum2 (mc.y + 1) (mc.x + 1) 0x48)).u8acc = 0 ∧
      ((z.feed (gridAnsi mg)).feed (penSgr mp ++ csiNum2 (mc.y + 1) (mc.x + 1) 0x48)).modes.insert =
        false ∧
      ((z.feed (gridAnsi mg)).feed (penSgr mp ++ csiNum2 (mc.y + 1) (mc.x + 1) 0x48)).modes.wrap =
        true ∧
      ((z.feed (gridAnsi mg)).feed (penSgr mp ++ csiNum2 (mc.y + 1) (mc.x + 1) 0x48)).modes.origin =
        false ∧
      ((z.feed (gridAnsi mg)).feed (penSgr mp ++ csiNum2 (mc.y + 1) (mc.x + 1) 0x48)).g0Line =
        false ∧
      ((z.feed (gridAnsi mg)).feed (penSgr mp ++ csiNum2 (mc.y + 1) (mc.x + 1) 0x48)).g1Line =
        false := by
  -- A: the main paint. Its result is discarded; only these framed facts survive.
  obtain ⟨-, -, hAun, hAua, hAins, hAwrap, -⟩ :=
    gridAnsi_writes_rows (u := z) (tg := mg) hcols hrows hpos hub htop hbot hg hun hua hins hwrap
      horg hg0 hg1 hgsz hrlens hmok hmsz
  have hAg : (z.feed (gridAnsi mg)).pstate = .ground := (quiet_gridAnsi mg z hg horg).1
  have hAorg : (z.feed (gridAnsi mg)).modes.origin = false := (quiet_gridAnsi mg z hg horg).2
  have hAstick : stick (z.feed (gridAnsi mg)) = stick z := (smap_id_gridAnsi mg z hg).2
  have hAdims : dims (z.feed (gridAnsi mg)) = dims z := dims_feed _ hgood
  have hgoodA : Good (z.feed (gridAnsi mg)) := Good.feed _ hgood
  -- the park: `penSgr ++ CUP`. Modes / sticky bundle / decoder / dims all preserved.
  have hMpark := mmap_id_append (mmap_id_penSgr mp) (mmap_id_cup (mc.y + 1) (mc.x + 1))
  have hSpark := SMap.append (smap_id_penSgr mp) (smap_id_cup (mc.y + 1) (mc.x + 1))
  have hAscii := (ascii_penSgr mp).append (ascii_csiNum2 (mc.y + 1) (mc.x + 1) 0x48 (by decide))
  obtain ⟨hPg, hPn, hPmodes⟩ := hMpark _ hAg hAun
  obtain ⟨-, hPstick⟩ := hSpark _ hAg
  obtain ⟨-, hPua⟩ := uaz_feed _ hAscii hAun hAua
  have hPdims :
    dims ((z.feed (gridAnsi mg)).feed (penSgr mp ++ csiNum2 (mc.y + 1) (mc.x + 1) 0x48)) =
      dims (z.feed (gridAnsi mg)) :=
    dims_feed _ hgoodA
  refine ⟨?_, ?_, ?_, ?_, hPg, hPn, hPua, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← dims_fst, hPdims, hAdims, dims_fst, hcols]
  · rw [← dims_snd, hPdims, hAdims, dims_snd, hrows]
  · rw [← stick_top, hPstick, id_eq, hAstick, stick_top, htop]
  · have hnone :
      ((z.feed (gridAnsi mg)).feed
            (penSgr mp ++ csiNum2 (mc.y + 1) (mc.x + 1) 0x48)).altGrid.isSome =
        false := by
      rw [← stick_alt, hPstick, id_eq, hAstick, stick_alt, halt]; rfl
    exact
      Option.not_isSome_iff_eq_none.mp
        (by
          rw [hnone]; simp)
  · rw [hPmodes, id_eq, hAins]
  · rw [hPmodes, id_eq, hAwrap]
  · rw [hPmodes, id_eq, hAorg]
  · rw [← stick_g0, hPstick, id_eq, hAstick, stick_g0, hg0]
  · rw [← stick_g1, hPstick, id_eq, hAstick, stick_g1, hg1]

/-- Reprinting the stashed margin cell preserves the complete paint entry
context, including the ring that the following switch must retain. -/
theorem pending_park_frame (s : Vt) (cols : Nat) (mg : Array Row) (mc : Cursor) (mp : Pen)
    (hg : Good s) (hr : Renderable s) (hc : s.cols = cols) (hgrid : s.grid = mg)
    (h0 : s.g0Line = false) (h1 : s.g1Line = false) (hw : s.modes.wrap = true)
    (hi : s.modes.insert = false) (ho : s.modes.origin = false) (hp : s.pstate = .ground)
    (hn : s.u8need = 0) (ha : s.u8acc = 0) :
    let t := s.feed (pendingAnsi cols mg mc (mc.y + 1) mp)
    t.cols = s.cols ∧
      t.rows = s.rows ∧
      t.top = s.top ∧
      t.altGrid = s.altGrid ∧
      t.pstate = .ground ∧
      t.u8need = 0 ∧
      t.u8acc = 0 ∧
      t.modes = s.modes ∧
      t.g0Line = s.g0Line ∧ t.g1Line = s.g1Line ∧ t.grid = s.grid ∧ t.sb = s.sb := by
  have he :=
    pendingAnsi_feed_eq s mc (mc.y + 1) mp hg hr h0 h1 hw hi
      (fun hy => pending_row_absolute s mc hg ho hy) hp hn ha
  dsimp only
  rw [← hc, ← hgrid, he]
  split <;> exact ⟨rfl, rfl, rfl, rfl, hp, hn, ha, rfl, rfl, rfl, rfl, rfl⟩

/-- **The grid, restored into any client — alt screen.** With the session on the alt screen,
`screensAnsi` paints the stashed main grid, parks its cursor/pen, switches with `?1049h`, then
paints the visible (alt) grid. `alt_pre_switch` carries the entry state across the discarded
main paint and the park; `alt_switch_entry` hands the second paint a blank grid of the
receiver's shape with its region reset and cursor homed; `gridAnsi_writes_rows` then
reproduces `v.grid`. -/
theorem restore_grid_any_alt (v w : Vt) (hgood : Good w) (hren : Renderable w)
    (hcols : w.cols = v.cols) (hrows : w.rows = v.rows) (hua : w.u8acc = 0) (hun : w.u8need = 0)
    {mainGrid : Array Row} {mcur : Cursor} {mpen : Pen}
    (halt : v.altGrid = some (mainGrid, mcur, mpen)) (hpos : 0 < v.cols) (hub : v.cols < 65533)
    (hvren : Renderable v) : (w.feed (restore v)).grid = v.grid := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, -, est⟩ :=
    paint_entry v w hgood hren hcols hrows hua hun
  obtain ⟨hmsz, hmok⟩ := hvren.alt mainGrid mcur mpen halt
  -- the history stage precedes the discarded main paint on both screens:
  -- `scrollback_entry` re-establishes `paint_entry`'s conjuncts for `alt_pre_switch`
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, falt, -⟩ :=
    scrollback_entry (u := w.feed (prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A)) (v := v)
      (Good.feed _ hgood) (renderable_feed hren _) e1 e2 e5 e7 est
  -- across the discarded main paint and the park, the entry state is preserved
  obtain
    ⟨hs2cols, hs2rows, hs2top, hs2alt, hs2g, hs2n, hs2ua, hs2ins, hs2wrap, hs2org, hs2g0, hs2g1⟩ :=
    alt_pre_switch (z :=
      (w.feed (prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A)).feed (scrollbackAnsi v)) (mg :=
      mainGrid) (mc := mcur) (mp := mpen) (cols := v.cols) (rows := v.rows) f1 f2 f3 f4 f5 f6 f7 f8
      f9 f10 f11 f12 f13 f14 falt (Good.feed _ (Good.feed _ hgood)) hpos hub hmok hmsz
  have hmain :=
    gridAnsi_writes_rows f1 f2 hpos hub f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 hmok hmsz
  have hsg :
    ((((w.feed (prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A)).feed (scrollbackAnsi v)).feed
              (gridAnsi mainGrid)).feed
          (penSgr mpen ++ csiNum2 (mcur.y + 1) (mcur.x + 1) 0x48)).grid =
      mainGrid :=
    (keeps_park (mcur.y + 1) (mcur.x + 1) mpen _ hmain.2.1 hmain.2.2.1).2.2.trans hmain.1
  obtain ⟨pc, pr, pt, pa, pg, pn, pua, pm, p0, p1, -, -⟩ :=
    pending_park_frame _ v.cols mainGrid mcur mpen
      (Good.feed _ (Good.feed _ (Good.feed _ (Good.feed _ hgood))))
      (renderable_feed (renderable_feed (renderable_feed (renderable_feed hren _) _) _) _) hs2cols
      hsg hs2g0 hs2g1 hs2wrap hs2ins hs2org hs2g hs2n hs2ua
  -- the switch establishes the second paint's entry state
  obtain ⟨hZcols, hZrows, hZtop, hZbot, hZg, hZun, hZua, hZmodes, hZg0, hZg1, hZgrid, -, -, -⟩ :=
    alt_switch_entry (u :=
      ((((w.feed (prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A)).feed (scrollbackAnsi v)).feed
                (gridAnsi mainGrid)).feed
            (penSgr mpen ++ csiNum2 (mcur.y + 1) (mcur.x + 1) 0x48)).feed
        (pendingAnsi v.cols mainGrid mcur (mcur.y + 1) mpen))
      (pa.trans hs2alt) pg pn
  -- the final paint reproduces the visible (alt) grid, over a post-switch blank of
  -- the receiver's shape
  have hfin :=
    gridAnsi_writes_rows (u :=
      (((((w.feed (prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A)).feed (scrollbackAnsi v)).feed
                    (gridAnsi mainGrid)).feed
                (penSgr mpen ++ csiNum2 (mcur.y + 1) (mcur.x + 1) 0x48)).feed
            (pendingAnsi v.cols mainGrid mcur (mcur.y + 1) mpen)).feed
        (csiPriv 1049 0x68))
      (tg := v.grid) (cols := v.cols) (rows := v.rows) (hZcols.trans (pc.trans hs2cols))
      (hZrows.trans (pr.trans hs2rows)) hpos hub hZtop (by rw [hZbot, pr, hs2rows]) hZg
      (hZun.trans pn) (hZua.trans pua)
      (by
        rw [hZmodes, pm]; exact hs2ins)
      (by
        rw [hZmodes, pm]; exact hs2wrap)
      (by
        rw [hZmodes, pm]; exact hs2org)
      (hZg0.trans (p0.trans hs2g0)) (hZg1.trans (p1.trans hs2g1))
      (by
        rw [hZgrid, Array.size_replicate]; exact pr.trans hs2rows)
      (fun y' => (getRow_size_replicate hZgrid hZcols y').trans (pc.trans hs2cols)) hvren.main.2
      hvren.main.1
  -- assemble via `restore_grid_of_paint`
  have hscreens :
    screensAnsi v =
      scrollbackAnsi v ++ gridAnsi mainGrid ++
        (penSgr mpen ++ csiNum2 (mcur.y + 1) (mcur.x + 1) 0x48) ++
        pendingAnsi v.cols mainGrid mcur (mcur.y + 1) mpen ++
        csiPriv 1049 0x68 ++
        gridAnsi v.grid := by
    unfold screensAnsi; rw [halt]; simp only [List.append_assoc]
  -- peel the stream to the shape the chain above is stated over. `simp only
  -- [feed_append]` on both sides rather than a hand-counted `rw` chain: the peels
  -- are order-sensitive, since `++` is left-associative and a `rw` takes the
  -- outermost append first — which with the history stage in front splits the
  -- pen/cursor park before it reaches the stage, and then nothing matches.
  have hpeel :
    w.feed (prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v) =
      ((((((w.feed (prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A)).feed (scrollbackAnsi v)).feed
                        (gridAnsi mainGrid)).feed
                    (penSgr mpen ++ csiNum2 (mcur.y + 1) (mcur.x + 1) 0x48)).feed
                (pendingAnsi v.cols mainGrid mcur (mcur.y + 1) mpen)).feed
            (csiPriv 1049 0x68)).feed
        (gridAnsi v.grid) := by
    rw [hscreens]; simp only [feed_append]
  refine restore_grid_of_paint v w hgood hren hcols hrows hua hun ?_ ?_ ?_ ?_ ?_
  · rw [hpeel]; exact hfin.2.1
  · rw [hpeel]; exact hfin.2.2.1
  · rw [hpeel]; exact hfin.1
  · rw [hpeel]; exact hfin.2.2.2.2.1
  · rw [hpeel]; exact hfin.2.2.2.2.2.1

/-- **The grid, restored into any client — both screens (Definition-of-done item 5).** The one
theorem that dispatches on whether the session is on the alt screen; each branch is proved
above.

Every hypothesis here is one the claim genuinely needs: the paint's column bounds are derived
once from `Good w` and handed to both branches, and the row count rides `Renderable v`. Same
signature as `restore_sb_of_stage`, and for the same reason. -/
theorem restore_grid_any (v w : Vt) (hgood : Good w) (hren : Renderable w) (hcols : w.cols = v.cols)
    (hrows : w.rows = v.rows) (hua : w.u8acc = 0) (hun : w.u8need = 0) (hvren : Renderable v) :
    (w.feed (restore v)).grid = v.grid := by
  have hpos : 0 < v.cols := by
    rw [← hcols]; exact hgood.colsPos
  have hub : v.cols < 65533 := by
    have := hgood.colsLe; rw [hcols] at this; omega
  match halt : v.altGrid with
  | none => exact restore_grid_any_main v w hgood hren hcols hrows hua hun halt hpos hub hvren
  | some (mainGrid, mcur, mpen) =>
    exact restore_grid_any_alt v w hgood hren hcols hrows hua hun halt hpos hub hvren

/-! ### The receiver's decoder is not a hypothesis — the stream's own first byte resets it

Reachability does **not** supply `u8need = 0`: `((Vt.init 80 24).feed [0xC3]).u8need = 1`.
`restore` begins with `ESC`, and `abortUtf8` discards a pending sequence on a stray `ESC`,
so the receiver may be mid-character and the repaint still lands.

`U8Ok` is still load-bearing and cannot be dropped: `abortUtf8` zeroes `u8need` but leaves a
stale `u8acc` alone, so without `U8Ok` the normalised state is not the zeroed one. It comes
free from reachability (`u8Ok_of_liveReachable`), which is the difference between an
assumption about a cooperative client and a fact about every client there is. -/

theorem restore_cons (v : Vt) : restore v = 0x1B :: (restore v).tail := by
  simp only [restore, restoreBody, prologueAnsi, escSeq, escB, List.cons_append, List.nil_append,
    List.tail_cons]

/-- **A `restore` replay does not care what the receiver's decoder was holding.** -/
theorem feed_restore_zeroed (v w : Vt) (hok : U8Ok w) :
    w.feed (restore v) =
      ({ w with
            u8need := 0, u8acc := 0 }).feed
        (restore v) := by
  rw [restore_cons v, feed_cons, feed_cons, step_esc_eq hok]

/-- **The grid claim with every hypothesis discharged from reachability.** The receiver's
`Good`, `Renderable` and decoder invariants are not assumptions about a *cooperative* client —
they hold of every state a terminal can reach by being fed bytes, which is every client there
is (`good_of_liveReachable`, `renderable_of_liveReachable`, `u8Ok_of_liveReachable`). What is
left in the statement is matching dimensions, on **both** screens, main and alt. The receiver's
`u8need` is not a hypothesis (section above). -/
theorem restore_grid_reachable (v w : Vt) (hw : LiveReachableVt w) (hv : LiveReachableVt v)
    (hcols : w.cols = v.cols) (hrows : w.rows = v.rows) : (w.feed (restore v)).grid = v.grid := by
  rw [feed_restore_zeroed v w (u8Ok_of_liveReachable hw)]
  exact
    restore_grid_any v _ (Good.set_u8 0 0 (by omega) (good_of_liveReachable hw))
      (renderable_congr (renderable_of_liveReachable hw) rfl rfl rfl rfl) hcols hrows rfl rfl
      (renderable_of_liveReachable hv)

end Linger.Core.Render
