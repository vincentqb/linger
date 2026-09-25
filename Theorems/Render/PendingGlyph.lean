module

public import Theorems.Vt
import all Linger.Core.Vt
import all Theorems.Vt

/-! Reprinting a canonical margin glyph restores its complete state while arming
pending wrap. This layer works on characters and is independent of the byte emitter. -/

namespace Linger.Core.Render

open Linger.Core.Vt

namespace PendingGlyph

theorem set_read {α : Type} (r : Array α) (x : Nat) (d : α) :
    r.setIfInBounds x (r.getD x d) = r := by
  by_cases h : x < r.size <;> simp [Array.setIfInBounds, Array.getD, h]

theorem mendAt_fixed {row : Row} {x : Nat} (h : ∀ j, PairOk row j) : row.mendAt x = row := by
  have hhp : row.halfPair x = false :=
    (halfPair_eq_false_iff row x).mpr
      ⟨fun h2 => by
        rw [(h x).1 h2]; rfl, (h x).2⟩
  unfold Row.mendAt
  rw [hhp, ite_eq_right (by decide)]
  split
  · rename_i h0
    have hw0 : (row.at x).width = 0 := by simpa only [beq_iff_eq] using h0
    obtain ⟨hne, hbase⟩ := (h x).2 hw0
    have hcan : row.at x = Cell.shadow (row.at (x - 1)) := by
      have hp := (h (x - 1)).1 hbase
      rw [show x - 1 + 1 = x from by omega] at hp
      exact hp
    rw [← hcan]
    exact set_read row x default
  · rfl

theorem mend_fixed {row : Row} (h : ∀ j, PairOk row j) : row.mend = row := by
  unfold Row.mend
  have key : ∀ l : List Nat, l.foldl (fun (r : Row) x => r.mendAt x) row = row := by
    intro l
    induction l with
    | nil => rfl
    | cons x xs ih =>
      rw [List.foldl_cons, mendAt_fixed h]; exact ih
  exact key _

theorem pairs_congr {r s : Row} (h : ∀ j, PairOk r j) (hw : ∀ j, (s.at j).width = (r.at j).width)
    (hp : ∀ j, (s.at j).pen = (r.at j).pen) (hz : ∀ j, (r.at j).width = 0 → s.at j = r.at j) :
    ∀ j, PairOk s j := by
  intro j
  refine ⟨fun h2 => ?_, fun h0 => ?_⟩
  · have hcan := (h j).1 ((hw j) ▸ h2)
    have hnext : (r.at (j + 1)).width = 0 := by
      rw [hcan]; rfl
    rw [hz (j + 1) hnext, hcan]
    simp only [Cell.shadow, hp]
  · obtain ⟨hne, hbase⟩ := (h j).2 ((hw j) ▸ h0)
    exact ⟨hne, (hw (j - 1)).trans hbase⟩

/-- A base cell may change its text without changing the canonical pair layout,
provided its width and pen stay the same. Shadows cannot be edited this way. -/
theorem pairs_set {row : Row} (h : ∀ j, PairOk row j) (x : Nat) (c : Cell) (hx : x < row.size)
    (hw : c.width = (row.at x).width) (hp : c.pen = (row.at x).pen) (hn : c.width ≠ 0) :
    ∀ j, PairOk (row.setIfInBounds x c) j := by
  have hat : (Row.at (row.setIfInBounds x c) x) = c := getD_set_self row x c default hx
  have hne : ∀ j, j ≠ x → Row.at (row.setIfInBounds x c) j = row.at j := by
    intro j hj
    exact getD_set_ne row x j c default hj
  apply pairs_congr h
  · intro j
    by_cases hj : j = x
    · subst j; rw [hat]; exact hw
    · rw [hne j hj]
  · intro j
    by_cases hj : j = x
    · subst j; rw [hat]; exact hp
    · rw [hne j hj]
  · intro j h0
    apply hne j
    intro hj
    subst j
    exact hn (hw.trans h0)

theorem put_self (v : Vt) (x y : Nat) : v.putCell x y (v.getCell x y) = v := by
  unfold Vt.putCell Vt.getCell
  rw [set_read]
  unfold Vt.getRow
  dsimp only
  rw [set_read]

theorem put_twice (v : Vt) (x y : Nat) (a b : Cell) (hy : y < v.grid.size) :
    (v.putCell x y a).putCell x y b = v.putCell x y b := by
  simp only [Vt.putCell, Vt.getRow]
  rw [getD_set_self _ _ _ _ hy]
  simp only [Array.setIfInBounds_setIfInBounds]

theorem mendRow_fixed {v : Vt} {y : Nat} (h : ∀ j, PairOk (v.getRow y) j) : v.mendRow y = v := by
  unfold Vt.mendRow
  rw [mend_fixed h]
  unfold Vt.getRow
  rw [set_read]

def markState (v : Vt) (x y : Nat) (ms : List Char) : Vt :=
  v.putCell x y { v.getCell x y with marks := ms }

theorem markState_self (v : Vt) (x y : Nat) : markState v x y (v.getCell x y).marks = v := by
  unfold markState
  rw [show { v.getCell x y with marks := (v.getCell x y).marks } = v.getCell x y from rfl, put_self]

theorem markState_at (v : Vt) (x y : Nat) (ms : List Char) (hy : y < v.grid.size)
    (hx : x < (v.getRow y).size) :
    (markState v x y ms).getCell x y = { v.getCell x y with marks := ms } :=
  getRow_putCell_self v x y _ hy hx

theorem markState_ne (v : Vt) (x y j : Nat) (ms : List Char) (hy : y < v.grid.size) (hj : j ≠ x) :
    (markState v x y ms).getCell j y = v.getCell j y := by
  change Row.at ((v.putCell x y _).getRow y) j = _
  rw [getRow_putCell_same _ _ _ _ hy]
  exact getD_set_ne _ x j _ default hj

theorem markState_width (v : Vt) (x y j : Nat) (ms : List Char) (hy : y < v.grid.size)
    (hx : x < (v.getRow y).size) :
    ((markState v x y ms).getCell j y).width = (v.getCell j y).width := by
  by_cases hj : j = x
  · subst j; rw [markState_at v x y ms hy hx]
  · rw [markState_ne v x y j ms hy hj]

theorem markState_mend {v : Vt} {x y : Nat} (ms : List Char) (hy : y < v.grid.size)
    (hx : x < (v.getRow y).size) (hpair : ∀ j, PairOk (v.getRow y) j)
    (hn : (v.getCell x y).width ≠ 0) : (markState v x y ms).mendRow y = markState v x y ms := by
  apply mendRow_fixed
  unfold markState
  rw [getRow_putCell_same _ _ _ _ hy]
  exact pairs_set hpair x _ hx rfl rfl hn

theorem print_mark (v : Vt) (x : Nat) (ms : List Char) (m : Char) (hy : v.cursor.y < v.grid.size)
    (hx : x < (v.getRow v.cursor.y).size) (hpair : ∀ j, PairOk (v.getRow v.cursor.y) j)
    (hn : (v.getCell x v.cursor.y).width ≠ 0) (h0 : v.g0Line = false) (h1 : v.g1Line = false)
    (hpend : v.cursor.pending = true)
    (htarget :
      (if (v.getCell v.cursor.x v.cursor.y).width == 0 && v.cursor.x != 0 then v.cursor.x - 1
        else v.cursor.x) =
        x)
    (hw : charWidth m = 0) (hem : Emittable m) (hcap : ms.length < 8) :
    (markState v x v.cursor.y ms).print m = markState v x v.cursor.y (ms ++ [m]) := by
  have hpc : (markState v x v.cursor.y ms).printChar m = m :=
    printChar_id_of_ascii h0 h1 hem.1 hem.2
  have hcur : (markState v x v.cursor.y ms).cursor = v.cursor := rfl
  unfold Vt.print
  simp only [hpc, hw]
  rw [ite_eq_left (by decide)]
  unfold Vt.printMark
  have htarget' :
    (if
          ((markState v x v.cursor.y ms).getCell v.cursor.x v.cursor.y).width == 0 &&
            v.cursor.x != 0 then
        v.cursor.x - 1
      else v.cursor.x) =
      x := by
    rw [markState_width v x v.cursor.y v.cursor.x ms hy hx]
    exact htarget
  simp only [hcur, hpend, ite_true, htarget']
  rw [markState_at v x v.cursor.y ms hy hx]
  rw [ite_eq_right (by simpa using Nat.not_le.mpr hcap)]
  change
    ((v.putCell x v.cursor.y { v.getCell x v.cursor.y with marks := ms }).putCell x v.cursor.y
            { v.getCell x v.cursor.y with marks := ms ++ [m] }).mendRow
        v.cursor.y =
      _
  rw [put_twice v x v.cursor.y _ _ hy]
  exact markState_mend _ hy hx hpair hn

theorem print_marks (v : Vt) (x : Nat) (hy : v.cursor.y < v.grid.size)
    (hx : x < (v.getRow v.cursor.y).size) (hpair : ∀ j, PairOk (v.getRow v.cursor.y) j)
    (hn : (v.getCell x v.cursor.y).width ≠ 0) (h0 : v.g0Line = false) (h1 : v.g1Line = false)
    (hpend : v.cursor.pending = true)
    (htarget :
      (if (v.getCell v.cursor.x v.cursor.y).width == 0 && v.cursor.x != 0 then v.cursor.x - 1
        else v.cursor.x) =
        x) :
    ∀ (rest ms : List Char),
      (ms ++ rest).length ≤ 8 →
        (∀ m ∈ rest, charWidth m = 0 ∧ Emittable m) →
        rest.foldl (fun u m => u.print m) (markState v x v.cursor.y ms) =
          markState v x v.cursor.y (ms ++ rest) := by
  intro rest
  induction rest with
  | nil =>
    intro ms _ _; simp
  | cons m rest ih =>
    intro ms hcap hmarks
    have hm := hmarks m (by simp)
    rw [List.foldl_cons,
      print_mark v x ms m hy hx hpair hn h0 h1 hpend htarget hm.1 hm.2
        (by
          simp only [List.length_append, List.length_cons] at hcap; omega)]
    rw [ih (ms ++ [m]) (by simpa [List.append_assoc] using hcap)
        (fun c hc => hmarks c (by simp [hc]))]
    simp only [List.append_assoc, List.cons_append, List.nil_append]

theorem base_width {c : Cell} (hc : CellOk c) (hn : c.width ≠ 0) : c.width = 1 ∨ c.width = 2 := by
  have hw := hc.width hn
  unfold charWidth at hw
  split at hw
  · exact False.elim (hn hw.symm)
  · split at hw
    · exact Or.inr hw.symm
    · exact Or.inl hw.symm

theorem print_base (w : Vt) (hg : Good w) (hr : Renderable w) (h0 : w.g0Line = false)
    (h1 : w.g1Line = false) (hwrap : w.modes.wrap = true) (hins : w.modes.insert = false)
    (hpend : w.cursor.pending = false) (hp : (w.getCell w.cursor.x w.cursor.y).pen = w.pen)
    (hwidth : (w.getCell w.cursor.x w.cursor.y).width ≠ 0)
    (hmargin : w.cursor.x + charWidth (w.getCell w.cursor.x w.cursor.y).base = w.cols) :
    w.print (w.getCell w.cursor.x w.cursor.y).base =
      markState
        { w with
          cursor :=
            { w.cursor with
              x := w.cols - 1, pending := true } }
        w.cursor.x w.cursor.y [] := by
  let c := w.getCell w.cursor.x w.cursor.y
  have hc := cellOk_getCell hr w.cursor.x w.cursor.y
  have hcw : charWidth c.base = c.width := hc.width hwidth
  have hpc : w.printChar c.base = c.base := printChar_id_of_ascii h0 h1 hc.base.1 hc.base.2
  have hy : w.cursor.y < w.grid.size := by
    rw [hr.main.1]; exact hg.curY
  have hx : w.cursor.x < (w.getRow w.cursor.y).size := by
    rw [(rowOk_getRow hr w.cursor.y).size]
    exact hg.curX
  have hpair := (rowOk_getRow hr w.cursor.y).pairs
  have hclear : w.clearPending = w := by
    unfold Vt.clearPending
    rw [← hpend]
  have hmar : w.cols ≤ w.cursor.x + c.width := by
    rw [← hcw]
    exact Nat.le_of_eq hmargin.symm
  have hadv :
    (markState w w.cursor.x w.cursor.y []).printAdvance c.width =
      markState
        { w with
          cursor :=
            { w.cursor with
              x := w.cols - 1, pending := true } }
        w.cursor.x w.cursor.y [] := by
    simp [Vt.printAdvance, markState, Vt.putCell, Vt.getCell, Vt.getRow, hwrap, hmar]
  rcases base_width hc hwidth with hw | hw
  · have hcell :
      ({ base := c.base, marks := [], width := 1, pen := w.pen } : Cell) = { c with marks := [] } :=
      Cell.ext' rfl rfl hw.symm hp.symm
    rw [print_narrow_eq hpc (hcw.trans hw) hins hpend, hclear, hcell]
    change ((markState w w.cursor.x w.cursor.y []).mendRow w.cursor.y).printAdvance 1 = _
    rw [markState_mend [] hy hx hpair hwidth]
    simpa only [c, hw] using hadv
  · have hfit : w.cursor.x + 1 < w.cols := by
      rw [hcw, hw] at hmargin
      omega
    have hcell :
      ({ base := c.base, marks := [], width := 2, pen := w.pen } : Cell) = { c with marks := [] } :=
      Cell.ext' rfl rfl hw.symm hp.symm
    have hshadow :
      (markState w w.cursor.x w.cursor.y []).getCell (w.cursor.x + 1) w.cursor.y =
        Cell.shadow c := by
      rw [markState_ne w w.cursor.x w.cursor.y (w.cursor.x + 1) [] hy (by omega)]
      exact (hpair w.cursor.x).1 hw
    rw [print_wide_eq hpc (hcw.trans hw) hins hpend hfit, hclear, hcell]
    change
      (((markState w w.cursor.x w.cursor.y []).putCell (w.cursor.x + 1) w.cursor.y
                  (Cell.shadow c)).mendRow
              w.cursor.y).printAdvance
          2 =
        _
    rw [← hshadow, put_self, markState_mend [] hy hx hpair hwidth]
    simpa only [c, hw] using hadv

end PendingGlyph

/-- Replaying the base and all stored marks of a canonical margin glyph changes
only the cursor to the margin with wrap pending. The equation preserves every
other field, including both grids, saved state, parser state and scrollback. -/
theorem reprint_margin (w : Vt) (hg : Good w) (hr : Renderable w) (h0 : w.g0Line = false)
    (h1 : w.g1Line = false) (hwrap : w.modes.wrap = true) (hins : w.modes.insert = false)
    (hpend : w.cursor.pending = false) (hp : (w.getCell w.cursor.x w.cursor.y).pen = w.pen)
    (hwidth : (w.getCell w.cursor.x w.cursor.y).width ≠ 0)
    (hmargin : w.cursor.x + charWidth (w.getCell w.cursor.x w.cursor.y).base = w.cols) :
    ((w.getCell w.cursor.x w.cursor.y).marks.foldl (fun v m => v.print m)
        (w.print (w.getCell w.cursor.x w.cursor.y).base)) =
      { w with
        cursor :=
          { w.cursor with
            x := w.cols - 1, pending := true } } := by
  let t :=
    { w with
      cursor :=
        { w.cursor with
          x := w.cols - 1, pending := true } }
  have hc := cellOk_getCell hr w.cursor.x w.cursor.y
  have hy : t.cursor.y < t.grid.size := by
    change w.cursor.y < w.grid.size
    rw [hr.main.1]
    exact hg.curY
  have hx : w.cursor.x < (t.getRow t.cursor.y).size := by
    change w.cursor.x < (w.getRow w.cursor.y).size
    rw [(rowOk_getRow hr w.cursor.y).size]
    exact hg.curX
  have hpair : ∀ j, PairOk (t.getRow t.cursor.y) j := (rowOk_getRow hr w.cursor.y).pairs
  have hmar : w.cursor.x + (w.getCell w.cursor.x w.cursor.y).width = w.cols := by
    rw [← hc.width hwidth]
    exact hmargin
  have htarget :
    (if (t.getCell t.cursor.x t.cursor.y).width == 0 && t.cursor.x != 0 then t.cursor.x - 1
      else t.cursor.x) =
      w.cursor.x := by
    change
      (if (w.getCell (w.cols - 1) w.cursor.y).width == 0 && w.cols - 1 != 0 then w.cols - 1 - 1
        else w.cols - 1) =
        w.cursor.x
    rcases PendingGlyph.base_width hc hwidth with hw | hw
    · have hm : w.cols - 1 = w.cursor.x := by omega
      rw [hm, hw]
      simp
    · have hm : w.cols - 1 = w.cursor.x + 1 := by omega
      have hshadow :
        w.getCell (w.cursor.x + 1) w.cursor.y = Cell.shadow (w.getCell w.cursor.x w.cursor.y) :=
        ((rowOk_getRow hr w.cursor.y).pairs w.cursor.x).1 hw
      rw [hm, hshadow]
      simp [Cell.shadow]
  rw [PendingGlyph.print_base w hg hr h0 h1 hwrap hins hpend hp hwidth hmargin]
  have hmarks :=
    PendingGlyph.print_marks t w.cursor.x hy hx hpair hwidth h0 h1 rfl htarget
      (w.getCell w.cursor.x w.cursor.y).marks [] (by simpa using hc.marksLe) hc.marks
  simp only [List.nil_append] at hmarks
  rw [hmarks]
  exact PendingGlyph.markState_self t w.cursor.x t.cursor.y

end Linger.Core.Render
