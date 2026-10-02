module

public import Theorems.Vt.State
import all Theorems.Vt.State

namespace Linger.Core.Vt

/-! ## Wide pairs: the repair's postcondition

`Render.rowAnsi` can express a row only if every wide glyph in it is whole: a
width-2 base immediately followed by its width-0 shadow, that shadow carrying
nothing of its own (the painter emits the base and nothing else), and no shadow
without a base. Half a pair is not displayable either — a lone base re-wraps on
replay, a lone shadow paints nothing while still occupying a column — so rather
than adding side conditions to the replay theorem, the emulator does not reach
those shapes. Every cell-writing operation ends in `Row.mend`.

This section proves the postcondition that makes those calls worth anything:
after `Row.mend`, **every column satisfies `PairOk`**. It is what `Renderable`
rests on, and proving it once here is what keeps the pair invariant out of every
individual mutation's proof.
-/

/-- Reading back the cell a `setIfInBounds` wrote. -/
theorem getD_set_self {α} [Inhabited α] (r : Array α) (x : Nat) (c d : α) (h : x < r.size) :
    (r.setIfInBounds x c).getD x d = c := by simp [Array.getD, Array.setIfInBounds, h]

/-- …and reading back any other cell. -/
theorem getD_set_ne {α} [Inhabited α] (r : Array α) (x j : Nat) (c d : α) (h : j ≠ x) :
    (r.setIfInBounds x c).getD j d = r.getD j d := by
  simp only [Array.getD, Array.setIfInBounds]
  split
  · simp only [Array.size_set]
    split
    · simp [Array.getElem_set, Ne.symm h]
    · rfl
  · rfl

/-- Out of range reads a default (width-1) cell, which is what lets the pair
rules treat "no neighbour" and "a narrow neighbour" alike. -/
theorem at_of_size_le (row : Row) (x : Nat) (h : row.size ≤ x) : row.at x = default := by
  unfold Row.at
  simp [Array.getD, Nat.not_lt.mpr h]

/-- **The pair rule for one column**, in `Prop`: a base keeps its shadow (and
that shadow is exactly what repainting the base re-creates), and a shadow keeps
its base. -/
def PairOk (row : Row) (x : Nat) : Prop :=
  ((row.at x).width = 2 → row.at (x + 1) = Cell.shadow (row.at x)) ∧
    ((row.at x).width = 0 → x ≠ 0 ∧ (row.at (x - 1)).width = 2)

/-- `halfPair` reads nothing but the three neighbouring widths. -/
theorem halfPair_congr {row row' : Row} (x : Nat)
    (h0 : (row'.at (x - 1)).width = (row.at (x - 1)).width)
    (h1 : (row'.at x).width = (row.at x).width)
    (h2 : (row'.at (x + 1)).width = (row.at (x + 1)).width) : row'.halfPair x = row.halfPair x := by
  simp only [Row.halfPair]
  rw [h0, h1, h2]

/-- `halfPair` in `Prop` — the width half of `PairOk`. -/
theorem halfPair_eq_false_iff (row : Row) (x : Nat) :
    row.halfPair x = false ↔
      ((row.at x).width = 2 → (row.at (x + 1)).width = 0) ∧
        ((row.at x).width = 0 → x ≠ 0 ∧ (row.at (x - 1)).width = 2) := by
  unfold Row.halfPair
  simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, beq_eq_false_iff_ne, bne_eq_false_iff_eq,
    ne_eq]
  constructor
  · intro h
    refine ⟨fun h2 => ?_, fun h0 => ?_⟩
    · rcases h.1 with hc | hs
      · exact absurd h2 hc
      · exact hs
    · rcases h.2 with hc | hs
      · exact absurd h0 hc
      · exact ⟨hs.1, hs.2⟩
  · intro h
    refine ⟨?_, ?_⟩
    · by_cases h2 : (row.at x).width = 2
      · exact Or.inr (h.1 h2)
      · exact Or.inl h2
    · by_cases h0 : (row.at x).width = 0
      · exact Or.inr ⟨(h.2 h0).1, (h.2 h0).2⟩
      · exact Or.inl h0

/-- A width-1 cell is not half of anything, so a blanked column is repaired. -/
theorem halfPair_of_width_one (row : Row) (x : Nat) (h : (row.at x).width = 1) :
    row.halfPair x = false := by
  rw [halfPair_eq_false_iff]
  exact
    ⟨fun h2 => absurd (h.symm.trans h2) (by decide), fun h0 => absurd (h.symm.trans h0) (by decide)⟩

/-! ### One repair step -/

theorem size_mendAt (row : Row) (x : Nat) : (Row.mendAt row x).size = row.size := by
  unfold Row.mendAt
  repeat' split
  all_goals
    first
    | simp
    | rfl

theorem mendAt_ne (row : Row) (x j : Nat) (h : j ≠ x) : (Row.mendAt row x).at j = row.at j := by
  unfold Row.mendAt Row.at
  repeat' split
  all_goals
    first
    | exact getD_set_ne _ _ _ _ _ h
    | rfl

/-- A half pair becomes a blank. -/
theorem mendAt_self_blank (row : Row) (x : Nat) (hx : x < row.size) (h : row.halfPair x = true) :
    (Row.mendAt row x).at x = Cell.erased (row.at x).pen := by
  unfold Row.mendAt Row.at
  rw [ite_eq_left h]
  exact getD_set_self _ _ _ _ hx

/-- A whole pair's shadow becomes canonical. -/
theorem mendAt_self_shadow (row : Row) (x : Nat) (hx : x < row.size) (h : row.halfPair x = false)
    (hw : (row.at x).width = 0) : (Row.mendAt row x).at x = Cell.shadow (row.at (x - 1)) := by
  unfold Row.mendAt Row.at
  rw [ite_eq_right (by simp [h]),
    ite_eq_left
      (by
        simp [Row.at] at hw ⊢; exact hw)]
  exact getD_set_self _ _ _ _ hx

/-- Anything else is left alone. -/
theorem mendAt_self_id (row : Row) (x : Nat) (h : row.halfPair x = false)
    (hw : (row.at x).width ≠ 0) : (Row.mendAt row x).at x = row.at x := by
  unfold Row.mendAt Row.at
  rw [ite_eq_right (by simp [h]),
    ite_eq_right
      (by
        simp only [Row.at] at hw ⊢; simpa using hw)]

/-- A repair that does not blank preserves every width, since a canonical
shadow is still a shadow. -/
theorem width_mendAt_of_whole (row : Row) (x j : Nat) (h : row.halfPair x = false) :
    ((Row.mendAt row x).at j).width = (row.at j).width := by
  by_cases hj : j = x
  · subst hj
    by_cases hw : (row.at j).width = 0
    · by_cases hb : j < row.size
      · rw [mendAt_self_shadow row j hb h hw]; rw [hw]; rfl
      · rw [at_of_size_le row j (by omega)] at hw
        exact absurd hw (by decide)
    · rw [mendAt_self_id row j h hw]
  · rw [mendAt_ne row x j hj]

/-! ### The sweep -/

/-- The repaired column comes out repaired. -/
theorem halfPair_mendAt_self (row : Row) (n : Nat) (hn : n < row.size) :
    (Row.mendAt row n).halfPair n = false := by
  by_cases h : row.halfPair n = true
  · refine halfPair_of_width_one _ _ ?_
    rw [mendAt_self_blank row n hn h]
    rfl
  · have h' : row.halfPair n = false := by simpa using h
    rw [halfPair_congr n (width_mendAt_of_whole row n _ h') (width_mendAt_of_whole row n _ h')
        (width_mendAt_of_whole row n _ h')]
    exact h'

/-- …and so does its shadow clause. -/
theorem shadow_mendAt_self (row : Row) (n : Nat) (hn : n < row.size)
    (hw : ((Row.mendAt row n).at n).width = 0) :
    n ≠ 0 ∧ (Row.mendAt row n).at n = Cell.shadow ((Row.mendAt row n).at (n - 1)) := by
  by_cases h : row.halfPair n = true
  · rw [mendAt_self_blank row n hn h] at hw
    simp [Cell.erased] at hw
  · have h' : row.halfPair n = false := by simpa using h
    have hw0 : (row.at n).width = 0 := by
      rw [width_mendAt_of_whole row n n h'] at hw; exact hw
    have hne : n ≠ 0 := ((halfPair_eq_false_iff row n).mp h').2 hw0 |>.1
    refine ⟨hne, ?_⟩
    rw [mendAt_self_shadow row n hn h' hw0, mendAt_ne row n (n - 1) (by omega)]

/-- A repair step leaves every column below it repaired.

The content is that a *whole* pair is never touched: blanking column `n` could
only orphan a base at `n - 1` if `n` were that base's shadow, and such a shadow
is exactly what `mendAt`'s guard protects. That argument is direction-free,
which is why the sweep's order does not matter (see `Row.mend`); the `j < n`
form is what the sweep induction consumes. -/
theorem halfPair_mendAt_lt (row : Row) (n j : Nat) (hj : j < n) (h : row.halfPair j = false) :
    (Row.mendAt row n).halfPair j = false := by
  rw [halfPair_eq_false_iff] at h ⊢
  have hj0 : (Row.mendAt row n).at j = row.at j := mendAt_ne row n j (by omega)
  have hjm : (Row.mendAt row n).at (j - 1) = row.at (j - 1) := mendAt_ne row n (j - 1) (by omega)
  refine ⟨fun h2 => ?_, fun h0 => ?_⟩
  · rw [hj0] at h2
    by_cases hn : j + 1 = n
    · -- the column being repaired is this base's shadow, so it is not blanked
      subst hn
      have hshadow : row.halfPair (j + 1) = false := by
        rw [halfPair_eq_false_iff]
        have hw : (row.at (j + 1)).width = 0 := h.1 h2
        exact ⟨fun hc => absurd (hw.symm.trans hc) (by decide), fun _ => ⟨by omega, h2⟩⟩
      rw [width_mendAt_of_whole row (j + 1) (j + 1) hshadow]
      exact h.1 h2
    · rw [mendAt_ne row n (j + 1) (by omega)]
      exact h.1 h2
  · rw [hj0] at h0
    exact
      ⟨(h.2 h0).1, by
        rw [hjm]; exact (h.2 h0).2⟩

/-- …including their shadow clause, which reads only columns at or below `j`. -/
theorem shadow_mendAt_lt (row : Row) (n j : Nat) (hj : j < n)
    (h : (row.at j).width = 0 → j ≠ 0 ∧ row.at j = Cell.shadow (row.at (j - 1))) :
    ((Row.mendAt row n).at j).width = 0 →
      j ≠ 0 ∧ (Row.mendAt row n).at j = Cell.shadow ((Row.mendAt row n).at (j - 1)) := by
  intro hw
  have hj0 : (Row.mendAt row n).at j = row.at j := mendAt_ne row n j (by omega)
  have hjm : (Row.mendAt row n).at (j - 1) = row.at (j - 1) := mendAt_ne row n (j - 1) (by omega)
  rw [hj0] at hw
  exact
    ⟨(h hw).1, by
      rw [hj0, hjm]; exact (h hw).2⟩

/-- The sweep, up to a bound: every column below `n` is repaired — both the
width rule and the canonical-shadow rule — and the row keeps its size. -/
theorem mendUpto_spec (row : Row) :
    ∀ n,
      ((List.range n).foldl (fun r x => Row.mendAt r x) row).size = row.size ∧
        ∀ j,
          j < n →
            n ≤ row.size →
            (((List.range n).foldl (fun r x => Row.mendAt r x) row).halfPair j = false ∧
              ((((List.range n).foldl (fun r x => Row.mendAt r x) row).at j).width = 0 →
                j ≠ 0 ∧
                  ((List.range n).foldl (fun r x => Row.mendAt r x) row).at j =
                    Cell.shadow
                      (((List.range n).foldl (fun r x => Row.mendAt r x) row).at (j - 1))))
  | 0 => ⟨rfl, fun _ hj => absurd hj (by omega)⟩
  | n + 1 => by
    have ih := mendUpto_spec row n
    have hstep :
      (List.range (n + 1)).foldl (fun r x => Row.mendAt r x) row =
        Row.mendAt ((List.range n).foldl (fun r x => Row.mendAt r x) row) n := by
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine
      ⟨by
        rw [hstep, size_mendAt]; exact ih.1, fun j hj hn => ?_⟩
    rw [hstep]
    by_cases hje : j = n
    · subst hje
      have hlt : j < ((List.range j).foldl (fun r x => Row.mendAt r x) row).size := by
        rw [ih.1]; omega
      exact ⟨halfPair_mendAt_self _ _ hlt, fun hw => shadow_mendAt_self _ _ hlt hw⟩
    · have hprev := ih.2 j (by omega) (by omega)
      exact ⟨halfPair_mendAt_lt _ _ _ (by omega) hprev.1, shadow_mendAt_lt _ _ _ (by omega) hprev.2⟩

theorem size_mend (row : Row) : (Row.mend row).size = row.size := by
  unfold Row.mend
  exact (mendUpto_spec row row.size).1

theorem mend_halfPair (row : Row) (x : Nat) (hx : x < row.size) :
    (Row.mend row).halfPair x = false := by
  unfold Row.mend
  exact ((mendUpto_spec row row.size).2 x hx (by omega)).1

theorem mend_shadow (row : Row) (x : Nat) (hx : x < row.size)
    (hw : ((Row.mend row).at x).width = 0) :
    x ≠ 0 ∧ (Row.mend row).at x = Cell.shadow ((Row.mend row).at (x - 1)) := by
  unfold Row.mend at hw ⊢
  exact ((mendUpto_spec row row.size).2 x hx (by omega)).2 hw

/-- **The repair's postcondition.** Every column of a mended row satisfies the
pair rule — for any input row at all, which is what lets every mutation end in
`Row.mend` and lets `Renderable` be an invariant rather than a hypothesis. -/
theorem mend_pairOk (row : Row) (x : Nat) (hx : x < row.size) : PairOk (Row.mend row) x := by
  have hsz : (Row.mend row).size = row.size := size_mend row
  refine ⟨fun h2 => ?_, fun h0 => ?_⟩
  · -- a base keeps its shadow, and that shadow is canonical
    have hhp := (halfPair_eq_false_iff (Row.mend row) x).mp (mend_halfPair row x hx)
    have hw : ((Row.mend row).at (x + 1)).width = 0 := hhp.1 h2
    have hb : x + 1 < (Row.mend row).size := by
      rcases Nat.lt_or_ge (x + 1) (Row.mend row).size with h | h
      · exact h
      · rw [at_of_size_le _ _ h] at hw
        exact absurd hw (by decide)
    have hsh :=
      mend_shadow row (x + 1)
        (by
          rw [hsz] at hb; exact hb)
        hw
    have hx1 : x + 1 - 1 = x := by omega
    rw [hx1] at hsh
    exact hsh.2
  · have hhp := (halfPair_eq_false_iff (Row.mend row) x).mp (mend_halfPair row x hx)
    exact hhp.2 h0

/-! ### What the sweep leaves alone

A repaint reads back the cell it just wrote, so the sweep must be the identity
on a cell that is already well formed. Two cases cover every write: a narrow
glyph, and a wide glyph together with its canonical shadow. -/

private theorem mendUpto_keeps_narrow (row : Row) (x : Nat) (h : (row.at x).width = 1) :
    ∀ n, ((List.range n).foldl (fun r y => Row.mendAt r y) row).at x = row.at x
  | 0 => rfl
  | n + 1 => by
    have ih := mendUpto_keeps_narrow row x h n
    have hstep :
      (List.range (n + 1)).foldl (fun r y => Row.mendAt r y) row =
        Row.mendAt ((List.range n).foldl (fun r y => Row.mendAt r y) row) n := by
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hstep]
    by_cases hn : n = x
    · subst hn
      have hw1 : (((List.range n).foldl (fun r y => Row.mendAt r y) row).at n).width = 1 := by
        rw [ih]; exact h
      rw [mendAt_self_id _ _ (halfPair_of_width_one _ _ hw1)
          (by
            rw [hw1]; decide)]
      exact ih
    · rw [mendAt_ne _ _ _ (fun hc => hn hc.symm)]
      exact ih

/-- The sweep is the identity on a narrow cell. -/
theorem mend_keeps_narrow (row : Row) (x : Nat) (h : (row.at x).width = 1) :
    (Row.mend row).at x = row.at x := mendUpto_keeps_narrow row x h row.size

private theorem mendUpto_keeps_wide (row : Row) (x : Nat) (h2 : (row.at x).width = 2)
    (hs : row.at (x + 1) = Cell.shadow (row.at x)) :
    ∀ n,
      ((List.range n).foldl (fun r y => Row.mendAt r y) row).at x = row.at x ∧
        ((List.range n).foldl (fun r y => Row.mendAt r y) row).at (x + 1) = row.at (x + 1)
  | 0 => ⟨rfl, rfl⟩
  | n + 1 => by
    have ih := mendUpto_keeps_wide row x h2 hs n
    have hstep :
      (List.range (n + 1)).foldl (fun r y => Row.mendAt r y) row =
        Row.mendAt ((List.range n).foldl (fun r y => Row.mendAt r y) row) n := by
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    -- the two columns still hold a whole pair, so neither repair branch moves them
    have hb : (((List.range n).foldl (fun r y => Row.mendAt r y) row).at x).width = 2 := by
      rw [ih.1]; exact h2
    have hsh : (((List.range n).foldl (fun r y => Row.mendAt r y) row).at (x + 1)).width = 0 := by
      rw [ih.2, hs]; rfl
    have hwhole : ((List.range n).foldl (fun r y => Row.mendAt r y) row).halfPair x = false := by
      rw [halfPair_eq_false_iff]
      exact ⟨fun _ => hsh, fun h0 => absurd (hb.symm.trans h0) (by decide)⟩
    have hwhole1 :
      ((List.range n).foldl (fun r y => Row.mendAt r y) row).halfPair (x + 1) = false := by
      rw [halfPair_eq_false_iff]
      refine ⟨fun hc => absurd (hsh.symm.trans hc) (by decide), fun _ => ⟨by omega, ?_⟩⟩
      simpa using hb
    rw [hstep]
    refine ⟨?_, ?_⟩
    · by_cases hn : n = x
      · subst hn
        rw [mendAt_self_id _ _ hwhole
            (by
              rw [hb]; decide)]
        exact ih.1
      · rw [mendAt_ne _ _ _ (fun hc => hn hc.symm)]
        exact ih.1
    · by_cases hn : n = x + 1
      · subst hn
        rw [mendAt_self_shadow _ _ ?_ hwhole1 hsh]
        · rw [show x + 1 - 1 = x from by omega, ih.1, hs]
        · -- the column is in range, or its cell would read as a width-1 default
          rcases
            Nat.lt_or_ge (x + 1)
              ((List.range (x + 1)).foldl (fun r y => Row.mendAt r y) row).size with
            hlt | hge
          · exact hlt
          · rw [at_of_size_le _ _ hge] at hsh
            exact absurd hsh (by decide)
      · rw [mendAt_ne _ _ _ (fun hc => hn hc.symm)]
        exact ih.2

/-- The sweep is the identity on a wide glyph and its canonical shadow. -/
theorem mend_keeps_wide (row : Row) (x : Nat) (h2 : (row.at x).width = 2)
    (hs : row.at (x + 1) = Cell.shadow (row.at x)) :
    (Row.mend row).at x = row.at x ∧ (Row.mend row).at (x + 1) = row.at (x + 1) :=
  mendUpto_keeps_wide row x h2 hs row.size

/-! ### Reading a mended row back out of the grid -/

theorem getCell_mendRow_same (v : Vt) (y x : Nat) (hy : y < v.grid.size) :
    (v.mendRow y).getCell x y = (v.getRow y).mend.at x := by
  unfold Vt.mendRow Vt.getCell Vt.getRow Row.at
  dsimp only
  rw [getD_set_self _ _ _ _ hy]

theorem getCell_mendRow_other (v : Vt) (y y' x : Nat) (h : y' ≠ y) :
    (v.mendRow y).getCell x y' = v.getCell x y' := by
  unfold Vt.mendRow Vt.getCell Vt.getRow
  dsimp only
  rw [getD_set_ne _ _ _ _ _ h]

/-! ### Write a cell, mend the row, read it back

What a repaint needs at every glyph. The write survives the sweep exactly when
it did not leave a half pair, and the two shapes a print produces are a narrow
cell and a wide base whose shadow the same print already wrote. -/

theorem grid_size_putCell (u : Vt) (x y : Nat) (c : Cell) :
    (u.putCell x y c).grid.size = u.grid.size := by
  unfold Vt.putCell
  simp

theorem getRow_putCell_same (u : Vt) (x y : Nat) (c : Cell) (hy : y < u.grid.size) :
    (u.putCell x y c).getRow y = (u.getRow y).setIfInBounds x c := by
  unfold Vt.putCell Vt.getRow
  dsimp only
  rw [getD_set_self _ _ _ _ hy]

theorem size_getRow_putCell (u : Vt) (x y : Nat) (c : Cell) (hy : y < u.grid.size) :
    ((u.putCell x y c).getRow y).size = (u.getRow y).size := by
  rw [getRow_putCell_same u x y c hy]
  simp

theorem getRow_putCell_self (u : Vt) (x y : Nat) (c : Cell) (hy : y < u.grid.size)
    (hx : x < (u.getRow y).size) : ((u.putCell x y c).getRow y).at x = c := by
  rw [getRow_putCell_same u x y c hy]
  unfold Row.at
  exact getD_set_self _ _ _ _ hx

/-- One narrow write survives the repair sweep. -/
theorem getCell_write_mendRow_narrow (u : Vt) (x y : Nat) (c : Cell) (hc : c.width = 1)
    (hy : y < u.grid.size) (hx : x < (u.getRow y).size) :
    ((u.putCell x y c).mendRow y).getCell x y = c := by
  have hcell := getRow_putCell_self u x y c hy hx
  rw [getCell_mendRow_same _ _ _
      (by
        rw [grid_size_putCell]; exact hy)]
  rw [mend_keeps_narrow _ _
      (by
        rw [hcell]; exact hc)]
  exact hcell

/-- A wide write and its shadow survive together. -/
theorem getCell_write_mendRow_wide (u : Vt) (x y : Nat) (cb : Cell) (h2 : cb.width = 2)
    (hy : y < u.grid.size) (hx : x + 1 < (u.getRow y).size) :
    (((u.putCell x y cb).putCell (x + 1) y (Cell.shadow cb)).mendRow y).getCell x y = cb ∧
      (((u.putCell x y cb).putCell (x + 1) y (Cell.shadow cb)).mendRow y).getCell (x + 1) y =
        Cell.shadow cb := by
  have hy' : y < (u.putCell x y cb).grid.size := by
    rw [grid_size_putCell]; exact hy
  have hrow' : ((u.putCell x y cb).getRow y).size = (u.getRow y).size :=
    size_getRow_putCell u x y cb hy
  have hshadow :=
    getRow_putCell_self (u.putCell x y cb) (x + 1) y (Cell.shadow cb) hy'
      (by
        rw [hrow']; exact hx)
  have hbase : (((u.putCell x y cb).putCell (x + 1) y (Cell.shadow cb)).getRow y).at x = cb := by
    rw [getRow_putCell_same _ (x + 1) y _ hy']
    unfold Row.at
    rw [getD_set_ne _ _ _ _ _ (by omega)]
    have := getRow_putCell_self u x y cb hy (by omega)
    unfold Row.at at this
    exact this
  have hkeep :=
    mend_keeps_wide (((u.putCell x y cb).putCell (x + 1) y (Cell.shadow cb)).getRow y) x
      (by
        rw [hbase]; exact h2)
      (by rw [hbase, hshadow])
  have hgs : y < ((u.putCell x y cb).putCell (x + 1) y (Cell.shadow cb)).grid.size := by
    rw [grid_size_putCell]; exact hy'
  rw [getCell_mendRow_same _ _ _ hgs, getCell_mendRow_same _ _ _ hgs]
  exact
    ⟨by
      rw [hkeep.1]; exact hbase, by
      rw [hkeep.2]; exact hshadow⟩

/-! #### Shapes: the repair sweep resizes nothing

`Matches` carries two shape facts — the painted row is `cols` long and its index is in
the grid — and no frame covers them, because both are about the grid a write *does*
touch. `mendAt` and `putCell` both go through `setIfInBounds`, so both are preserved
(`size_mendAt`/`size_mend` above); these lift that to the `Vt` level. -/

theorem size_getRow_putCell_any (u : Vt) (x y : Nat) (c : Cell) (hy : y < u.grid.size) (y' : Nat) :
    ((u.putCell x y c).getRow y').size = (u.getRow y').size := by
  by_cases h : y' = y
  · subst h; exact size_getRow_putCell _ _ _ _ hy
  · unfold Vt.putCell Vt.getRow
    dsimp only
    rw [getD_set_ne _ _ _ _ _ h]

/-- Structure equality by fields; there is no `ext` without Mathlib. -/
theorem Cell.ext' {a b : Cell} (hb : a.base = b.base) (hm : a.marks = b.marks)
    (hw : a.width = b.width) (hp : a.pen = b.pen) : a = b := by
  cases a; cases b; simp_all

theorem grid_size_mendRow (u : Vt) (y : Nat) : (u.mendRow y).grid.size = u.grid.size := by
  unfold Vt.mendRow
  simp

theorem size_getRow_mendRow (u : Vt) (y : Nat) (hy : y < u.grid.size) (y' : Nat) :
    ((u.mendRow y).getRow y').size = (u.getRow y').size := by
  by_cases h : y' = y
  · subst h
    unfold Vt.mendRow Vt.getRow
    dsimp only
    rw [getD_set_self _ _ _ _ hy, size_mend]
  · unfold Vt.mendRow Vt.getRow
    dsimp only
    rw [getD_set_ne _ _ _ _ _ h]

/-- **The write term's shape**, as the row induction needs it: a cell write, its repair
sweep and the cursor advance change no dimension, no row length and no row count. Stated
about the composite rather than about `print`, because under `print_narrow_eq`'s
hypotheses that composite *is* the print — and the general statement for `print` would
have to reason through `printWrap`'s scroll, which these hypotheses rule out. -/
theorem write_shape (u : Vt) (x y : Nat) (c : Cell) (n : Nat) (hy : y < u.grid.size) :
    (((u.putCell x y c).mendRow y).printAdvance n).cols = u.cols ∧
      (((u.putCell x y c).mendRow y).printAdvance n).grid.size = u.grid.size ∧
      ∀ y',
        ((((u.putCell x y c).mendRow y).printAdvance n).getRow y').size = (u.getRow y').size := by
  have hgs : y < (u.putCell x y c).grid.size := by
    rw [grid_size_putCell]; exact hy
  refine ⟨?_, ?_, ?_⟩
  · rw [frame_printAdvance, frame_mendRow, frame_putCell]
  · rw [frame_printAdvance, grid_size_mendRow, grid_size_putCell]
  · intro y'
    rw [show
        (((u.putCell x y c).mendRow y).printAdvance n).getRow y' =
          ((u.putCell x y c).mendRow y).getRow y'
        from by
        unfold Vt.getRow
        rw [frame_printAdvance]]
    rw [size_getRow_mendRow _ y hgs y', size_getRow_putCell_any u x y c hy y']

/-- The same for a wide glyph, which writes its base and its shadow before the sweep. -/
theorem write_shape2 (u : Vt) (x y : Nat) (c1 c2 : Cell) (n : Nat) (hy : y < u.grid.size) :
    ((((u.putCell x y c1).putCell (x + 1) y c2).mendRow y).printAdvance n).cols = u.cols ∧
      ((((u.putCell x y c1).putCell (x + 1) y c2).mendRow y).printAdvance n).grid.size =
        u.grid.size ∧
      ∀ y',
        (((((u.putCell x y c1).putCell (x + 1) y c2).mendRow y).printAdvance n).getRow y').size =
          (u.getRow y').size := by
  have h1 : y < (u.putCell x y c1).grid.size := by
    rw [grid_size_putCell]; exact hy
  obtain ⟨hc, hg, hr⟩ := write_shape (u.putCell x y c1) (x + 1) y c2 n h1
  refine ⟨?_, ?_, ?_⟩
  · rw [hc, frame_putCell]
  · rw [hg, grid_size_putCell]
  · intro y'
    rw [hr y', size_getRow_putCell_any u x y c1 hy y']

/-- `Cell.shadow` reads only the pen, so two cells with the same pen have the same
shadow — which is what identifies the shadow a wide print writes with the one the source
row holds. -/
theorem shadow_congr {a b : Cell} (h : a.pen = b.pen) : Cell.shadow a = Cell.shadow b := by
  unfold Cell.shadow
  rw [h]

/-! #### The within-row frame — the k-th write does not disturb columns already painted

The frames above cover the columns a write *touches* and every other *row*. The row
induction needs the third case and it is the delicate one: another column of the **same**
row. `Vt.mendRow` sweeps the whole row, and on a row whose pairs are broken `mendAt` may
rewrite any column — which is exactly the situation mid-paint, because every column the
paint has not reached still holds the previous occupant's junk.

So these are stated **per column, with that column's own shape** rather than with a
hypothesis about the row. `mend_keeps_narrow`/`mend_keeps_wide` need no global
pair-consistency, which is what makes that possible: a narrow cell, or a whole pair,
survives the sweep whatever surrounds it. Carrying the shape is the price of quantifying
over an arbitrary receiver, and it is a price the induction can pay — it painted those
columns and knows what it put there. -/

/-- Reading back another column of the written row: the write is invisible there. -/
theorem at_putCell_ne (u : Vt) (x y : Nat) (c : Cell) (x' : Nat) (hne : x' ≠ x)
    (hy : y < u.grid.size) : ((u.putCell x y c).getRow y).at x' = (u.getRow y).at x' := by
  rw [getRow_putCell_same u x y c hy]
  unfold Row.at
  exact getD_set_ne _ _ _ _ _ hne

/-- **A narrow cell at another column survives the write and the sweep.** -/
theorem getCell_write_mendRow_keep_narrow (u : Vt) (x y : Nat) (c : Cell) (x' : Nat) (hne : x' ≠ x)
    (hy : y < u.grid.size) (hnarrow : (u.getCell x' y).width = 1) :
    ((u.putCell x y c).mendRow y).getCell x' y = u.getCell x' y := by
  have hat : ((u.putCell x y c).getRow y).at x' = (u.getRow y).at x' :=
    at_putCell_ne u x y c x' hne hy
  rw [getCell_mendRow_same _ _ _
      (by
        rw [grid_size_putCell]; exact hy)]
  rw [mend_keeps_narrow _ x'
      (by
        rw [hat]; exact hnarrow),
    hat]
  rfl

/-- **…and so does a whole pair**, which is the case a painted wide glyph below `k`
lands in. Both halves are named because `mend` only leaves them alone together. -/
theorem getCell_write_mendRow_keep_wide (u : Vt) (x y : Nat) (c : Cell) (x' : Nat) (hne : x' ≠ x)
    (hne1 : x' + 1 ≠ x) (hy : y < u.grid.size) (hwide : (u.getCell x' y).width = 2)
    (hshadow : (u.getRow y).at (x' + 1) = Cell.shadow ((u.getRow y).at x')) :
    ((u.putCell x y c).mendRow y).getCell x' y = u.getCell x' y ∧
      ((u.putCell x y c).mendRow y).getCell (x' + 1) y = u.getCell (x' + 1) y := by
  have hat : ((u.putCell x y c).getRow y).at x' = (u.getRow y).at x' :=
    at_putCell_ne u x y c x' hne hy
  have hat1 : ((u.putCell x y c).getRow y).at (x' + 1) = (u.getRow y).at (x' + 1) :=
    at_putCell_ne u x y c (x' + 1) hne1 hy
  have hgs : y < (u.putCell x y c).grid.size := by
    rw [grid_size_putCell]; exact hy
  obtain ⟨h0, h1⟩ :=
    mend_keeps_wide ((u.putCell x y c).getRow y) x'
      (by
        rw [hat]; exact hwide)
      (by
        rw [hat, hat1]; exact hshadow)
  rw [getCell_mendRow_same _ _ _ hgs, getCell_mendRow_same _ _ _ hgs, h0, h1, hat, hat1]
  exact ⟨rfl, rfl⟩

/-- A write plus repair on one row leaves every other row alone. -/
theorem getCell_write_mendRow_other (u : Vt) (x y : Nat) (c : Cell) (x' y' : Nat) (h : y' ≠ y) :
    ((u.putCell x y c).mendRow y).getCell x' y' = u.getCell x' y' := by
  rw [getCell_mendRow_other _ _ _ _ h]
  unfold Vt.putCell Vt.getCell Vt.getRow
  dsimp only
  exact congrArg (fun r => Array.getD r x' default) (getD_set_ne _ _ _ _ _ h)

/-! ### `print`, reduced to its write

Three shape lemmas so the per-glyph fidelity theorems never have to walk
`print`'s five stages. Each is stated with `v.cursor` and `v.pen` rather than
`v.clearPending`'s, which are definitionally the same — `clearPending` writes
only the wrap flag. -/

theorem getCell_printAdvance (v : Vt) (n x y : Nat) :
    (v.printAdvance n).getCell x y = v.getCell x y := by
  unfold Vt.getCell Vt.getRow
  rw [frame_printAdvance]

/-! #### Off the written row — what the *grid* walk needs and the row walk did not

`Matches` is a statement about **one** row, so it cannot say that painting row `y` leaves
row `y'` alone. The grid walk needs exactly that: its invariant is "rows below `y` are
already painted", and each later row's paint must not disturb them. Every clause here is
about the composite a print reduces to (`print_narrow_eq` and friends), for the same
reason `write_shape` is — the general statement for `print` would have to reason through
`printWrap`'s scroll, which is the cross-row catastrophe those hypotheses rule out. -/

theorem grid_clearPending (u : Vt) : u.clearPending.grid = u.grid := by rw [frame_clearPending]

theorem getCell_clearPending (u : Vt) (x y : Nat) : u.clearPending.getCell x y = u.getCell x y := by
  unfold Vt.getCell Vt.getRow
  rw [frame_clearPending]

/-- **One narrow write touches no other row.** -/
theorem getCell_write_off (u : Vt) (x y : Nat) (c : Cell) (n : Nat) (x' y' : Nat) (hne : y' ≠ y) :
    ((((u.putCell x y c).mendRow y).printAdvance n).getCell x' y') = u.getCell x' y' := by
  rw [getCell_printAdvance]
  exact getCell_write_mendRow_other u x y c x' y' hne

/-- …and neither does a wide one, which writes its base and its shadow. -/
theorem getCell_write2_off (u : Vt) (x y : Nat) (c1 c2 : Cell) (n : Nat) (x' y' : Nat)
    (hne : y' ≠ y) :
    (((((u.putCell x y c1).putCell (x + 1) y c2).mendRow y).printAdvance n).getCell x' y') =
      u.getCell x' y' := by
  rw [getCell_printAdvance, getCell_write_mendRow_other (u.putCell x y c1) (x + 1) y c2 x' y' hne]
  unfold Vt.putCell Vt.getCell Vt.getRow
  dsimp only
  exact congrArg (fun r => Array.getD r x' default) (getD_set_ne _ _ _ _ _ hne)

/-- …nor a combining mark, whose write has no advance after it. -/
theorem getCell_mark_off (u : Vt) (x y : Nat) (c : Cell) (x' y' : Nat) (hne : y' ≠ y) :
    (((u.putCell x y c).mendRow y).getCell x' y') = u.getCell x' y' :=
  getCell_write_mendRow_other u x y c x' y' hne

theorem print_narrow_eq {v : Vt} {ch : Char} (hpc : v.printChar ch = ch) (hw : charWidth ch = 1)
    (hins : v.modes.insert = false) (hpend : v.cursor.pending = false) :
    v.print ch =
      ((v.clearPending.putCell v.cursor.x v.cursor.y
                { base := ch, marks := [], width := 1, pen := v.pen }).mendRow
            v.cursor.y).printAdvance
        1 := by
  unfold Vt.print
  simp only [hpc, hw]
  rw [ite_eq_right (by decide)]
  have h1 : v.printWrap = v.clearPending := by
    unfold Vt.printWrap; rw [ite_eq_right (by simp [hpend])]
  have h2 : ∀ (w : Vt), w.printWideWrap 1 = w := by
    intro w; unfold Vt.printWideWrap; rw [ite_eq_right (by simp)]
  have h3 : ∀ (w : Vt), w.modes.insert = false → w.printShift 1 = w := by
    intro w hw'; unfold Vt.printShift; rw [ite_eq_right (by simp [hw'])]
  have h4 :
    ∀ (w : Vt) (c : Char),
      w.printPut c 1 =
        (w.putCell w.cursor.x w.cursor.y
              { base := c, marks := [], width := 1, pen := w.pen }).mendRow
          w.cursor.y := by
    intro w c
    unfold Vt.printPut
    dsimp only
    rw [ite_eq_right (by simp), ite_eq_right (by decide)]
  rw [h1, h2,
    h3 _
      (by
        rw [frame_clearPending]; exact hins),
    h4]
  rfl

theorem print_wide_eq {v : Vt} {ch : Char} (hpc : v.printChar ch = ch) (hw : charWidth ch = 2)
    (hins : v.modes.insert = false) (hpend : v.cursor.pending = false)
    (hfit : v.cursor.x + 1 < v.cols) :
    v.print ch =
      (((v.clearPending.putCell v.cursor.x v.cursor.y
                    { base := ch, marks := [], width := 2, pen := v.pen }).putCell
                (v.cursor.x + 1) v.cursor.y
                (Cell.shadow { base := ch, marks := [], width := 2, pen := v.pen })).mendRow
            v.cursor.y).printAdvance
        2 := by
  unfold Vt.print
  simp only [hpc, hw]
  rw [ite_eq_right (by decide)]
  have hcp : v.clearPending = { v with cursor := { v.cursor with pending := false } } := by rfl
  have h1 : v.printWrap = v.clearPending := by
    unfold Vt.printWrap; rw [ite_eq_right (by simp [hpend])]
  have h2 : v.clearPending.printWideWrap 2 = v.clearPending := by
    unfold Vt.printWideWrap
    rw [ite_eq_right
        (by
          first
          | (simp [hcp]; done)
          | (simp [hcp]; omega))]
  have h3 : ∀ (w : Vt), w.modes.insert = false → w.printShift 2 = w := by
    intro w hw'; unfold Vt.printShift; rw [ite_eq_right (by simp [hw'])]
  have h4 :
    ∀ (w : Vt) (c : Char),
      w.cursor.x + 1 < w.cols →
        w.printPut c 2 =
          ((w.putCell w.cursor.x w.cursor.y
                    { base := c, marks := [], width := 2, pen := w.pen }).putCell
                (w.cursor.x + 1) w.cursor.y
                (Cell.shadow { base := c, marks := [], width := 2, pen := w.pen })).mendRow
            w.cursor.y := by
    intro w c hf
    unfold Vt.printPut
    dsimp only
    rw [ite_eq_right
        (by
          first
          | (simp; done)
          | (simp; omega)),
      ite_eq_left (by decide)]
    rfl
  rw [h1, h2,
    h3 _
      (by
        rw [frame_clearPending]; exact hins),
    h4 _ ch
      (by
        first
        | (simp [hcp]; done)
        | (simp [hcp]; omega))]
  rfl

theorem print_mark_eq {v : Vt} {m : Char} (hpc : v.printChar m = m) (hw : charWidth m = 0)
    (hpend : v.cursor.pending = false) (hnw : (v.getCell (v.cursor.x - 1) v.cursor.y).width ≠ 0)
    (hcap : (v.getCell (v.cursor.x - 1) v.cursor.y).marks.length < 8) :
    v.print m =
      (v.putCell (v.cursor.x - 1) v.cursor.y
            { v.getCell (v.cursor.x - 1) v.cursor.y with
              marks := (v.getCell (v.cursor.x - 1) v.cursor.y).marks ++ [m] }).mendRow
        v.cursor.y := by
  unfold Vt.print
  simp only [hpc, hw]
  rw [ite_eq_left (by decide)]
  unfold Vt.printMark
  simp only [hpend, ite_false, Bool.false_eq_true]
  rw [ite_eq_right
      (show ¬(((v.getCell (v.cursor.x - 1) v.cursor.y).width == 0 && v.cursor.x - 1 != 0) = true)
        from by
        simp only [Bool.and_eq_true, beq_iff_eq]
        exact fun h => hnw h.1)]
  rw [ite_eq_right (show ¬((v.getCell (v.cursor.x - 1) v.cursor.y).marks.length ≥ 8) from by omega)]

/-- The same, for a receiver with **wrap pending**. Not a variation for its own sake:
the row painter reaches this state on every marked cell in the final column. There the
advance clamped the column and armed wrap-pending instead of moving, so the glyph the
mark belongs to sits *at* the cursor rather than one to its left — which is precisely
the position `printMark`'s `pending` branch exists to name, and the one no absolute
cursor move can address. -/
theorem print_mark_pending_eq {v : Vt} {m : Char} (hpc : v.printChar m = m) (hw : charWidth m = 0)
    (hpend : v.cursor.pending = true) (hnw : (v.getCell v.cursor.x v.cursor.y).width ≠ 0)
    (hcap : (v.getCell v.cursor.x v.cursor.y).marks.length < 8) :
    v.print m =
      (v.putCell v.cursor.x v.cursor.y
            { v.getCell v.cursor.x v.cursor.y with
              marks := (v.getCell v.cursor.x v.cursor.y).marks ++ [m] }).mendRow
        v.cursor.y := by
  unfold Vt.print
  simp only [hpc, hw]
  rw [ite_eq_left (by decide)]
  unfold Vt.printMark
  simp only [hpend, ite_true]
  rw [ite_eq_right
      (show ¬(((v.getCell v.cursor.x v.cursor.y).width == 0 && v.cursor.x != 0) = true) from by
        simp only [Bool.and_eq_true, beq_iff_eq]
        exact fun h => hnw h.1)]
  rw [ite_eq_right (show ¬((v.getCell v.cursor.x v.cursor.y).marks.length ≥ 8) from by omega)]

end Linger.Core.Vt

namespace Linger.Core.Vt

/-! ## §Renderable — the emulator only reaches grids a repaint can reproduce

`Good` bounds the emulator; this bounds what it *stores*. `Render.restore`
paints a grid by emitting one glyph per cell, so a cell it can reproduce must
hold a printable base of the width it claims, at most eight zero-width marks,
and — for a wide glyph — its shadow, carrying nothing of its own.

The point of proving this is negative: it means the replay theorem needs no side
conditions. Every clause is established at the write, not assumed: controls are
neutralized on store (`printableChar`), marks are capped and land on a base
(`printMark`), and pairs are repaired at every row mutation (`Row.mend`), so
`mend_pairOk` discharges the pair clause uniformly.

The predicate is stated over the grid *array* with a fixed default row, not over
`Vt.getRow` (whose default carries the current pen). That is what lets every
operation which does not touch `grid`/`cols`/`rows`/`altGrid` be discharged by
its frame — most of `csiDispatch` — instead of by its own lemma.
-/

/-- A codepoint the emitter reproduces as itself: not a C0 control and not DEL.

Stated concretely rather than as `printableChar c = c`, which would be a
tautology against the very function that establishes it — mutating
`printableChar` would weaken the predicate and the storer together and
`renderable_print` would still prove. This way such a mutation has to break
`printableChar_emittable`, which is a claim about `printableChar`'s *range*. -/
def Emittable (c : Char) : Prop := 0x20 ≤ c.toNat ∧ c.toNat ≠ 0x7F

theorem printableChar_emittable (c : Char) : Emittable (printableChar c) := by
  unfold Emittable printableChar
  split
  · exact ⟨by decide, by decide⟩
  · rename_i h
    simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, not_or, Nat.not_lt] at h
    exact ⟨h.1, h.2⟩

theorem emittable_space : Emittable ' ' := ⟨by decide, by decide⟩

/-! ### The width tables (pin-the-gaps item 4)

`isZeroWidth` and `isWide` decide how many columns a glyph owns, and until this
section they were named **nowhere in the repo** outside their own definitions and
`charWidth` — 50 theorem statements mention `charWidth`, every one generic over
the tables, so a shifted range was invisible to the entire proof tree and to every
fixture. `CellOk.width` above is what makes them load-bearing: it ties a stored
cell's `width` field to `charWidth c.base`, so a table edit silently redefines
which grids are well-formed.

Both take `Nat`, not `Char`, so the pins are **closed propositions** decided by
the kernel — no `Char` literal (Lean's `\uXXXX` cannot reach plane 2), and no
compiled evaluation, which `tests/gates.sh` bans in `Theorems/` (and which greps
prose as well as code, so this sentence may not name the tactic). Each edge is
pinned on **both
sides** (`lo-1 = false, lo = true`), so shifting a bound either way falsifies a
conjunct. Deliberately *not* stated as `∀ c, isWide c = true ↔ <the disjunction>`:
that is a verbatim second copy of the table whose repair after a regression is to
edit the copy — the same anti-tautology argument as `Emittable` above.

**Two seams are unobservable, and are recorded rather than pretended.**
`0x3041-0x33FF ∪ 0x3400-0x4DBF` and `0x4E00-0x9FFF ∪ 0xA000-0xA4CF` are each one
contiguous run written as two clauses; moving a split point in *both* clauses
changes no value of the function, so no oracle can see it. The unions' outer edges
carry the content and are pinned; the seam interiors are pinned as `true` on both
sides, which catches a one-sided shrink (it opens a gap) but not an overlap.

**And a third thing nothing here can catch, found by break-verifying this
section:** `charWidth`'s *branch order*. Swapping its two `if`s is a semantic
no-op — and `zeroWidth_not_wide` below is exactly why, since disjoint tables mean
at most one branch can ever fire. So the order is a readability choice, not a
decision, and a theorem shaped `charWidth c = 2 ↔ (isZeroWidth … = false ∧ isWide
… = true)` would look like it pinned the order while pinning nothing. Those were
weighed and declined for that reason; the disjointness claim is what carries the
content they appeared to. -/

/-- **The low wall: nothing below U+1100 is wide.** One claim covering 4352
codepoints, and the property the grid actually rests on — every ASCII, Latin-1
and box-drawing glyph owns exactly one column, so a clause whose lower bound
slipped into the low plane mis-aligns every row of every restore. Tight: the
minimum `lo` in the table *is* `0x1100`, so lowering any of them breaks this. -/
theorem isWide_low (n : Nat) (h : n < 0x1100) : isWide n = false := by
  unfold isWide
  simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not, Nat.not_le]
  omega

/-- The same wall for the zero-width table, at U+0300. -/
theorem isZeroWidth_low (n : Nat) (h : n < 0x0300) : isZeroWidth n = false := by
  unfold isZeroWidth
  simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not, Nat.not_le,
    beq_eq_false_iff_ne, ne_eq]
  omega

/-- The consequence the row painter consumes: ASCII and Latin-1 are one column
wide. Composes the two walls through `charWidth`'s branch order. -/
theorem charWidth_low (c : Char) (h : c.toNat < 0x0300) : charWidth c = 1 := by
  unfold charWidth
  simp only [isZeroWidth_low _ h, isWide_low _ (by omega : c.toNat < 0x1100), Bool.false_eq_true,
    ite_false]

/-- Hangul Jamo leads (U+1100–U+115F), both edges. -/
theorem isWide_hangulJamo :
    isWide 0x10FF = false ∧
      isWide 0x1100 = true ∧ isWide 0x115F = true ∧ isWide 0x1160 = false := by
  decide

/-- CJK radicals through punctuation (U+2E80–U+303E). `0x303F` is the ideographic
half-fill space, narrow — and the gap to the next clause is two codepoints, the
tightest in the table. -/
theorem isWide_cjkRadicals :
    isWide 0x2E7F = false ∧
      isWide 0x2E80 = true ∧ isWide 0x303E = true ∧ isWide 0x303F = false := by
  decide

/-- Kana and CJK misc, the U+3041–U+4DBF run written as two clauses. The outer
edges carry the content; `0x33FF`/`0x3400` is the unobservable seam. -/
theorem isWide_kanaCjk :
    isWide 0x3040 = false ∧
      isWide 0x3041 = true ∧
      isWide 0x33FF = true ∧
      isWide 0x3400 = true ∧ isWide 0x4DBF = true ∧ isWide 0x4DC0 = false := by
  decide

/-- CJK unified through Yi, the U+4E00–U+A4CF run written as two clauses.
`0x9FFF`/`0xA000` is the second unobservable seam. -/
theorem isWide_cjkUnified :
    isWide 0x4DFF = false ∧
      isWide 0x4E00 = true ∧
      isWide 0x9FFF = true ∧
      isWide 0xA000 = true ∧ isWide 0xA4CF = true ∧ isWide 0xA4D0 = false := by
  decide

/-- Hangul syllables (U+AC00–U+D7A3). Both probes sit below the surrogate block,
so neither is an invalid scalar. -/
theorem isWide_hangulSyllables :
    isWide 0xABFF = false ∧
      isWide 0xAC00 = true ∧ isWide 0xD7A3 = true ∧ isWide 0xD7A4 = false := by
  decide

/-- CJK compatibility ideographs (U+F900–U+FAFF). -/
theorem isWide_cjkCompat :
    isWide 0xF8FF = false ∧
      isWide 0xF900 = true ∧ isWide 0xFAFF = true ∧ isWide 0xFB00 = false := by
  decide

/-- CJK compatibility forms (U+FE30–U+FE4F). Its `lo-1` is U+FE2F, the last
variation selector supplement — **zero-width**, not narrow: this edge is where
the two tables touch, and `zeroWidth_not_wide` below is what keeps them apart. -/
theorem isWide_cjkForms :
    isWide 0xFE2F = false ∧
      isWide 0xFE30 = true ∧ isWide 0xFE4F = true ∧ isWide 0xFE50 = false := by
  decide

/-- Fullwidth forms (U+FF00–U+FF60) and fullwidth signs (U+FFE0–U+FFE6). The
first `lo-1` is U+FEFF, the BOM — the second place the tables touch. -/
theorem isWide_fullwidth :
    isWide 0xFEFF = false ∧
      isWide 0xFF00 = true ∧
      isWide 0xFF60 = true ∧
      isWide 0xFF61 = false ∧
      isWide 0xFFDF = false ∧
      isWide 0xFFE0 = true ∧ isWide 0xFFE6 = true ∧ isWide 0xFFE7 = false := by
  decide

/-- Emoji (U+1F300–U+1F64F) and supplemental symbols (U+1F900–U+1F9FF), above
the BMP — reachable here only because `isWide` takes a `Nat`. -/
theorem isWide_emoji :
    isWide 0x1F2FF = false ∧
      isWide 0x1F300 = true ∧
      isWide 0x1F64F = true ∧
      isWide 0x1F650 = false ∧
      isWide 0x1F8FF = false ∧
      isWide 0x1F900 = true ∧ isWide 0x1F9FF = true ∧ isWide 0x1FA00 = false := by
  decide

/-- Planes 2 and 3 (U+20000–U+2FFFD, U+30000–U+3FFFD). Both `hi+1` probes are
noncharacters; Lean validates scalar-value-ness, not assignment. -/
theorem isWide_planes23 :
    isWide 0x1FFFF = false ∧
      isWide 0x20000 = true ∧
      isWide 0x2FFFD = true ∧
      isWide 0x2FFFE = false ∧
      isWide 0x2FFFF = false ∧
      isWide 0x30000 = true ∧ isWide 0x3FFFD = true ∧ isWide 0x3FFFE = false := by
  decide

/-- Combining diacritics (U+0300–U+036F). -/
theorem isZeroWidth_combining :
    isZeroWidth 0x02FF = false ∧
      isZeroWidth 0x0300 = true ∧ isZeroWidth 0x036F = true ∧ isZeroWidth 0x0370 = false := by
  decide

/-- Vedic extensions and combining marks (U+1AB0–U+1AFF, U+20D0–U+20FF). -/
theorem isZeroWidth_marks :
    isZeroWidth 0x1AAF = false ∧
      isZeroWidth 0x1AB0 = true ∧
      isZeroWidth 0x1AFF = true ∧
      isZeroWidth 0x1B00 = false ∧
      isZeroWidth 0x20CF = false ∧
      isZeroWidth 0x20D0 = true ∧ isZeroWidth 0x20FF = true ∧ isZeroWidth 0x2100 = false := by
  decide

/-- The zero-width joiner cluster (U+200B, U+200C, U+200D) — three **mutually
adjacent singletons**, so no neighbour probe can detect the loss of any one of
them. Each is pinned individually; U+200A and U+200E are the only outside probes
the cluster has. -/
theorem isZeroWidth_joiners :
    isZeroWidth 0x200A = false ∧
      isZeroWidth 0x200B = true ∧
      isZeroWidth 0x200C = true ∧ isZeroWidth 0x200D = true ∧ isZeroWidth 0x200E = false := by
  decide

/-- Variation selectors (U+FE00–U+FE0F) and their supplement (U+FE20–U+FE2F).
`0xFE30` is `false` here because it belongs to the *wide* table. -/
theorem isZeroWidth_varSel :
    isZeroWidth 0xFDFF = false ∧
      isZeroWidth 0xFE00 = true ∧
      isZeroWidth 0xFE0F = true ∧
      isZeroWidth 0xFE10 = false ∧
      isZeroWidth 0xFE1F = false ∧
      isZeroWidth 0xFE20 = true ∧ isZeroWidth 0xFE2F = true ∧ isZeroWidth 0xFE30 = false := by
  decide

/-- The BOM (U+FEFF), a singleton whose `hi+1` is the fullwidth block's `lo`. -/
theorem isZeroWidth_bom :
    isZeroWidth 0xFEFE = false ∧ isZeroWidth 0xFEFF = true ∧ isZeroWidth 0xFF00 = false := by decide

/-- **The tables never overlap.** They are adjacent at exactly two places, gap
one — U+FE2F/U+FE30 and U+FEFF/U+FF00 — and a one-codepoint slip in *either*
table at *either* place would make a codepoint both zero-width and wide, which
`charWidth`'s branch order then resolves silently. No per-table edge pin sees
that; this is false the moment it happens. -/
theorem zeroWidth_not_wide (n : Nat) (h : isZeroWidth n = true) : isWide n = false := by
  unfold isZeroWidth at h
  unfold isWide
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not, Nat.not_le]
  omega

/-- A cell a repaint can reproduce. -/
structure CellOk (c : Cell) : Prop where
  base : Emittable c.base
  width : c.width ≠ 0 → charWidth c.base = c.width
  marksLe : c.marks.length ≤ 8
  marks : ∀ m ∈ c.marks, charWidth m = 0 ∧ Emittable m

theorem cellOk_erased (p : Pen) : CellOk (Cell.erased p) :=
  ⟨emittable_space, fun _ => rfl, Nat.zero_le _, fun _ hm => nomatch hm⟩

theorem cellOk_shadow (c : Cell) : CellOk (Cell.shadow c) :=
  ⟨emittable_space, fun h => absurd rfl h, Nat.zero_le _, fun _ hm => nomatch hm⟩

theorem cellOk_default : CellOk (default : Cell) :=
  ⟨emittable_space, fun _ => rfl, Nat.zero_le _, fun _ hm => nomatch hm⟩

/-- A row a repaint can reproduce: exact width, reproducible cells, whole
pairs. Cells are quantified over *all* indices — an out-of-range read is a
default cell, which is fine — so no proof has to carry column bounds. -/
structure RowOk (cols : Nat) (row : Row) : Prop where
  size : row.size = cols
  cells : ∀ x, CellOk (row.at x)
  pairs : ∀ x, PairOk row x

/-- A width-1 row is trivially paired. -/
theorem pairOk_of_width_one {row : Row} (h : ∀ x, (row.at x).width = 1) (x : Nat) : PairOk row x :=
  ⟨fun h2 => absurd ((h x).symm.trans h2) (by decide), fun h0 =>
    absurd ((h x).symm.trans h0) (by decide)⟩

theorem at_blankRow (cols : Nat) (p : Pen) (x : Nat) :
    (blankRow cols p).at x = if x < cols then Cell.erased p else default := by
  unfold Row.at blankRow
  by_cases h : x < cols
  · rw [ite_eq_left h]
    simp [Array.getD, h]
  · rw [ite_eq_right h]
    simp [Array.getD, h]

theorem rowOk_blankRow (cols : Nat) (p : Pen) : RowOk cols (blankRow cols p) := by
  refine ⟨by simp [blankRow], fun x => ?_, pairOk_of_width_one (fun x => ?_)⟩
  · rw [at_blankRow]
    split
    · exact cellOk_erased p
    · exact cellOk_default
  · rw [at_blankRow]
    split <;> rfl

/-- A grid a repaint can reproduce. -/
def GridOk (cols rows : Nat) (g : Array Row) : Prop :=
  g.size = rows ∧ ∀ y, RowOk cols (g.getD y (blankRow cols {}))

structure Renderable (v : Vt) : Prop where
  main : GridOk v.cols v.rows v.grid
  alt : ∀ g c p, v.altGrid = some (g, c, p) → GridOk v.cols v.rows g

theorem gridOk_replicate (cols rows : Nat) (p : Pen) :
    GridOk cols rows (Array.replicate rows (blankRow cols p)) := by
  refine ⟨by simp, fun y => ?_⟩
  by_cases h : y < rows
  · rw [show (Array.replicate rows (blankRow cols p)).getD y (blankRow cols {}) = blankRow cols p
        from by simp [Array.getD, h]]
    exact rowOk_blankRow cols p
  · rw [show (Array.replicate rows (blankRow cols p)).getD y (blankRow cols {}) = blankRow cols {}
        from by simp [Array.getD, h]]
    exact rowOk_blankRow cols {}

theorem renderable_init (cols rows : Nat) : Renderable (Vt.init cols rows) :=
  ⟨gridOk_replicate _ _ _, fun _ _ _ h => nomatch h⟩

/-! ### The decoder's door, part two — the shape half (finding R2)

`decodedOk_iff` above decides `Good`'s content, and `Good` says nothing about the grid.
The audit recorded in SCRATCHPAD.md reached a `Good ∧ ¬Renderable` state **from disk**
with one flipped byte of a real checkpoint and refuted `resume_grid`'s conclusion at it,
which makes this an observable defect rather than a missing hypothesis. `Vt.decodedRenderable`
(`Linger/Core/Vt.lean`) is the second half of the door's check; these are its claims.

They live here, four thousand lines below the door's other claims, for one reason:
`Renderable` and its `GridOk`/`RowOk`/`CellOk`/`PairOk` ladder are defined just above, and
nothing earlier in this file can name them. One `iff` per rung, so the `Bool` and the
`Prop` cannot drift apart at any level — the same discipline as `decodedOk_iff`, five
times.

**The mirror lands here too.** `ofDecoded_of_good` is the same predicate seen from the
other side — the door's *non-rejection* — so it now asks for `Renderable` and `TabsOk`,
and everything above it inherits them: `Checkpoint.rt_vt` → `load_save` →
`load_save_exact` → the five `resume_*` claims that never read the grid. Every claim that
gained one says so in its own docstring, `renderable_of_liveReachable` and
`tabsOk_of_liveReachable` discharge them for any live session, and for the three claims
that *do* read the grid (`resume_grid`, `resume_sb`, `resume_tabs`) the new hypothesis was
already there. That trade was declined once, on the ground that a hypothesis a proof does
not use makes a theorem weaker than it is; the override is that the old unconditional
statements were also true of a screen the emitter cannot reproduce, which is a defect and
not a strength. -/

/-- Past its width a row reads default (width-1) cells, so no column out there is half of
a wide pair. With `cellOk_default` this is what makes `decodedRowOk`'s finite scan decide
`RowOk`'s two unbounded quantifiers. -/
theorem pairOk_of_size_le {row : Row} {x : Nat} (h : row.size ≤ x) : PairOk row x := by
  unfold PairOk
  rw [at_of_size_le row x h]
  exact ⟨fun h2 => absurd h2 (by decide), fun h0 => absurd h0 (by decide)⟩

/-- What the door decides about one codepoint, in `Emittable`'s vocabulary. -/
theorem decodedCharOk_iff {c : Char} : Vt.decodedCharOk c = true ↔ Emittable c := by
  unfold Vt.decodedCharOk Emittable
  simp

/-- …about one cell, in `CellOk`'s. The `width = 0` disjunct is `CellOk.width`'s
implication: a shadow's blank base is not the width it claims, and must not be. -/
theorem decodedCellOk_iff {c : Cell} : Vt.decodedCellOk c = true ↔ CellOk c := by
  unfold Vt.decodedCellOk
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    decodedCharOk_iff]
  constructor
  · rintro ⟨⟨⟨hb, hw⟩, hml⟩, hm⟩
    exact ⟨hb, fun hne => hw.resolve_left hne, hml, fun m hmem => hm m hmem⟩
  · rintro ⟨hb, hw, hml, hm⟩
    refine ⟨⟨⟨hb, ?_⟩, hml⟩, fun m hmem => hm m hmem⟩
    by_cases h0 : c.width = 0
    · exact Or.inl h0
    · exact Or.inr (hw h0)

/-- …and about one column pair, in `PairOk`'s. -/
theorem decodedPairOk_iff {row : Row} {x : Nat} : Vt.decodedPairOk row x = true ↔ PairOk row x := by
  unfold Vt.decodedPairOk PairOk
  simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
  constructor
  · rintro ⟨h2, h0⟩
    exact ⟨fun hw => h2.resolve_left (by omega), fun hw => h0.resolve_left (by omega)⟩
  · rintro ⟨h2, h0⟩
    constructor
    · by_cases hw : (row.at x).width = 2
      · exact Or.inr (h2 hw)
      · exact Or.inl hw
    · by_cases hw : (row.at x).width = 0
      · exact Or.inr (h0 hw)
      · exact Or.inl hw

/-- **A finite scan decides an unbounded quantifier.** `RowOk` quantifies over every `x`,
not over `x < cols`; the door checks `[0, cols)` and the two agree, because a read past
the width is the default cell — `cellOk_default` for the cells and `pairOk_of_size_le` for
the pairs. That is what made the per-cell half affordable at all. -/
theorem decodedRowOk_iff {cols : Nat} {row : Row} :
    Vt.decodedRowOk cols row = true ↔ RowOk cols row := by
  unfold Vt.decodedRowOk
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, decodedCellOk_iff,
    decodedPairOk_iff]
  constructor
  · rintro ⟨hsz, hall⟩
    refine ⟨hsz, fun x => ?_, fun x => ?_⟩
    · by_cases hx : x < cols
      · exact (hall x hx).1
      · rw [at_of_size_le row x (by omega)]
        exact cellOk_default
    · by_cases hx : x < cols
      · exact (hall x hx).2
      · exact pairOk_of_size_le (by omega)
  · rintro ⟨hsz, hc, hp⟩
    exact ⟨hsz, fun x _ => ⟨hc x, hp x⟩⟩

/-- …and one row per row decides the grid. Indexed with `GridOk`'s own
`getD … (blankRow cols {})`, so the two cannot disagree past the last row: there both read
a blank row of the right width, which `rowOk_blankRow` accepts. -/
theorem decodedGridOk_iff {cols rows : Nat} {g : Array Row} :
    Vt.decodedGridOk cols rows g = true ↔ GridOk cols rows g := by
  unfold Vt.decodedGridOk GridOk
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, decodedRowOk_iff]
  constructor
  · rintro ⟨hsz, hall⟩
    refine ⟨hsz, fun y => ?_⟩
    by_cases hy : y < rows
    · exact hall y hy
    · rw [show g.getD y (blankRow cols {}) = blankRow cols {} from by simp [Array.getD, hsz, hy]]
      exact rowOk_blankRow cols {}
  · rintro ⟨hsz, hall⟩
    exact ⟨hsz, fun y _ => hall y⟩

/-- **What the second stage decides, in `Renderable`'s vocabulary plus the ruler's.** The
alt clause is the sub-clause that was checked *nowhere* before: `decodedOk` looks at the
stashed cursor and never at the stashed grid. -/
theorem decodedRenderable_iff {cols rows : Nat} {grid : Array Row} {tabs : Array Bool}
    {altGrid : Option (Array Row × Cursor × Pen)} :
    Vt.decodedRenderable cols rows grid tabs altGrid = true ↔
      GridOk cols rows grid ∧
        tabs.size = cols ∧ ∀ g c p, altGrid = some (g, c, p) → GridOk cols rows g := by
  unfold Vt.decodedRenderable
  cases altGrid with
  | none =>
    simp only [Bool.and_eq_true, beq_iff_eq, decodedGridOk_iff, and_true]
    simp
  | some x =>
    obtain ⟨g₀, c₀, p₀⟩ := x
    simp only [Bool.and_eq_true, beq_iff_eq, decodedGridOk_iff, Option.some.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hg, ht⟩, ha⟩
      refine ⟨hg, ht, ?_⟩
      rintro g c p ⟨rfl, rfl, rfl⟩
      exact ha
    · rintro ⟨hg, ht, ha⟩
      exact ⟨⟨hg, ht⟩, ha g₀ c₀ p₀ ⟨rfl, rfl, rfl⟩⟩

/-- **Nothing the emitter cannot reproduce comes out of the decoder's door.** Whatever a
checkpoint file says, if `Vt.ofDecoded` returns a `Vt` at all then that `Vt` is
`Renderable`: the grid has exactly `rows` rows, each exactly `cols` wide, every cell holds
an emittable base of the width it claims with at most eight zero-width marks, every wide
glyph keeps its shadow — and the same of the stashed alt screen.

This is the claim finding R2 exists for. Before it, the door never saw the grid, so a
record whose `rows` byte disagreed with its grid's length decoded happily into a screen
`Render.restore` cannot repaint. `Checkpoint.load_renderable` is the same claim on the
real path, for *arbitrary bytes*. -/
theorem ofDecoded_renderable {cols rows : Nat} {grid : Array Row} {cursor : Cursor} {pen : Pen}
    {modes : Modes} {top bot : Nat} {tabs : Array Bool} {sb : Ring}
    {altGrid : Option (Array Row × Cursor × Pen)} {saved : Saved} {title : String}
    {g0Line g1Line shiftOut bell : Bool} {v : Vt}
    (h :
      Vt.ofDecoded cols rows grid cursor pen modes top bot tabs sb altGrid saved title g0Line g1Line
          shiftOut bell =
        some v) :
    Renderable v := by
  unfold Vt.ofDecoded at h
  split at h
  · rename_i hg
    simp only [Bool.and_eq_true] at hg
    obtain ⟨hgrid, -, halt⟩ := decodedRenderable_iff.mp hg.2
    cases h
    exact ⟨hgrid, halt⟩
  · exact absurd h (by simp)

/-- …and the tab ruler is the width of the screen. Split from `ofDecoded_renderable`
because `TabsOk` is not one of `Renderable`'s clauses and the claims that consume it
(`Render.restore_tabs_any`, `Resume.resume_tabs`) ask for it separately. -/
theorem ofDecoded_tabsOk {cols rows : Nat} {grid : Array Row} {cursor : Cursor} {pen : Pen}
    {modes : Modes} {top bot : Nat} {tabs : Array Bool} {sb : Ring}
    {altGrid : Option (Array Row × Cursor × Pen)} {saved : Saved} {title : String}
    {g0Line g1Line shiftOut bell : Bool} {v : Vt}
    (h :
      Vt.ofDecoded cols rows grid cursor pen modes top bot tabs sb altGrid saved title g0Line g1Line
          shiftOut bell =
        some v) :
    TabsOk v := by
  unfold Vt.ofDecoded at h
  split at h
  · rename_i hg
    simp only [Bool.and_eq_true] at hg
    obtain ⟨-, htabs, -⟩ := decodedRenderable_iff.mp hg.2
    cases h
    exact htabs
  · exact absurd h (by simp)

/-- **Nothing good is rejected.** The other half of the door: a `Vt` that is `Good`,
`Renderable` and ruler-consistent — which every live session's is, by `good_init`,
`renderable_init` and the `Pres`/frame machinery, and uniformly by
`good_of_liveReachable`/`renderable_of_liveReachable`/`tabsOk_of_liveReachable` — survives
the door unchanged, modulo the parser state a checkpoint deliberately forgets.

Without this, `ofDecoded_good` and `ofDecoded_renderable` would both be satisfied by a
constructor that returned `none` always, and §Restore would be a claim about a codec that
never restores anything. It is also exactly what `Checkpoint.rt_vt` needs, which is why
the round-trip theorem carries the same three hypotheses.

**This is the mirror**, and the two added hypotheses are its whole cost: `hren` and
`htabs` propagate from here to `rt_vt`, `load_save`, `load_save_exact` and five
`resume_*` claims. They cannot be dropped in favour of deriving them at the door — that
is what "validate, not clamp" means, and establishing `Renderable` from a bad record
would mean rebuilding the grid, which is `Vt.resize`, which the resume path refuses. -/
theorem ofDecoded_of_good {v : Vt} (h : Good v) (hren : Renderable v) (htabs : TabsOk v) :
    Vt.ofDecoded v.cols v.rows v.grid v.cursor v.pen v.modes v.top v.bot v.tabs v.sb v.altGrid
        v.saved v.title v.g0Line v.g1Line v.shiftOut v.bell =
      some v.quiesce := by
  unfold Vt.ofDecoded
  rw [ite_eq_left
      (by
        simp only [Bool.and_eq_true]
        exact
          ⟨decodedOk_iff.mpr
              ⟨h.colsPos, h.colsLe, h.rowsPos, h.rowsLe, h.curX, h.curY, h.savX, h.savY, h.topLe,
                h.botLt, h.sbLe, h.altCur⟩,
            decodedRenderable_iff.mpr ⟨hren.main, htabs, hren.alt⟩⟩)]
  cases v
  rfl

/-- **The exhibited attack, refused.** A record whose row count disagrees with its grid's
length is exactly finding R2's one-flipped-byte checkpoint — the `rows` byte of a real 4×2
record changed 2 → 3 — and it is `Good` for every clause `decodedOk` checks, which is why
it used to load. Now it does not.

The twin of `ofDecoded_none_of_cols_zero`, and the more instructive of the two: `cols = 0`
is refused by a dimension check anyone would think to write, and this one needed the
decoder to be handed the grid. `Tests/Checkpoint.lean` pins the byte-level version. -/
theorem ofDecoded_none_of_rows_mismatch {cols rows : Nat} {grid : Array Row} {cursor : Cursor}
    {pen : Pen} {modes : Modes} {top bot : Nat} {tabs : Array Bool} {sb : Ring}
    {altGrid : Option (Array Row × Cursor × Pen)} {saved : Saved} {title : String}
    {g0Line g1Line shiftOut bell : Bool} (hne : grid.size ≠ rows) :
    Vt.ofDecoded cols rows grid cursor pen modes top bot tabs sb altGrid saved title g0Line g1Line
        shiftOut bell =
      none := by
  have hno :
    (Vt.decodedOk cols rows cursor top bot sb altGrid saved &&
        Vt.decodedRenderable cols rows grid tabs altGrid) ≠
      true := by
    intro hg
    simp only [Bool.and_eq_true] at hg
    exact absurd (decodedRenderable_iff.mp hg.2).1.1 hne
  unfold Vt.ofDecoded
  rw [ite_eq_right hno]

/-! ### Frames discharge everything that does not write the grid -/

/-- An operation that leaves `grid`, `cols`, `rows` and `altGrid` alone
preserves `Renderable`. Most of `csiDispatch` is this. -/
theorem renderable_congr {v w : Vt} (h : Renderable v) (hg : w.grid = v.grid) (hc : w.cols = v.cols)
    (hr : w.rows = v.rows) (ha : w.altGrid = v.altGrid) : Renderable w := by
  refine
    ⟨by
      rw [hg, hc, hr]; exact h.main, fun g c p hs => ?_⟩
  rw [hc, hr]
  exact
    h.alt g c p
      (by
        rw [← ha]; exact hs)

/-! ### Writing cells -/

theorem cells_set {row : Row} (i : Nat) (c : Cell) (hrow : ∀ x, CellOk (row.at x)) (hc : CellOk c) :
    ∀ x, CellOk (Row.at (row.setIfInBounds i c) x) := by
  intro x
  unfold Row.at
  unfold Row.at at hrow
  by_cases hx : x = i
  · subst hx
    by_cases hb : x < row.size
    · rw [getD_set_self _ _ _ _ hb]; exact hc
    · rw [show row.setIfInBounds x c = row from by
          simp only [Array.setIfInBounds]; rw [dite_eq_right hb]]
      exact hrow x
  · rw [getD_set_ne _ _ _ _ _ hx]; exact hrow x

theorem cells_foldl {β : Type} {f : Row → β → Row}
    (hf : ∀ (r : Row) (b : β), (∀ x, CellOk (r.at x)) → ∀ x, CellOk ((f r b).at x)) :
    ∀ (l : List β) (row : Row),
      (∀ x, CellOk (row.at x)) →
        ∀ x, CellOk ((l.foldl f row).at x) := invariant_foldl (fun r => ∀ x, CellOk (r.at x)) f hf

theorem cells_mendAt {row : Row} (i : Nat) (hrow : ∀ x, CellOk (row.at x)) :
    ∀ x, CellOk ((Row.mendAt row i).at x) := by
  unfold Row.mendAt
  repeat' split
  all_goals
    first
    | exact cells_set _ _ hrow (cellOk_erased _)
    | exact cells_set _ _ hrow (cellOk_shadow _)
    | exact hrow

theorem cells_mend {row : Row} (hrow : ∀ x, CellOk (row.at x)) :
    ∀ x, CellOk ((Row.mend row).at x) := by
  unfold Row.mend
  exact cells_foldl (fun r b h => cells_mendAt b h) _ row hrow

/-- **The row-mutation workhorse.** A row whose cells are reproducible becomes a
reproducible row once mended — pairs included, by `mend_pairOk`. Every row
mutation ends in `Row.mend`, so every row mutation ends here. -/
theorem rowOk_mend {cols : Nat} {row : Row} (hsize : row.size = cols)
    (hcells : ∀ x, CellOk (row.at x)) : RowOk cols (Row.mend row) := by
  refine
    ⟨by
      rw [size_mend]; exact hsize, cells_mend hcells, fun x => ?_⟩
  by_cases hx : x < row.size
  · exact mend_pairOk row x hx
  · -- past the end every read is a default width-1 cell
    have hz : ∀ j, row.size ≤ j → (Row.mend row).at j = default := by
      intro j hj
      exact
        at_of_size_le _ _
          (by
            rw [size_mend]; exact hj)
    refine
      ⟨fun h2 =>
        absurd ((by rw [hz x (by omega)] : (Row.mend row).at x = default) ▸ h2) (by decide),
        fun h0 => ?_⟩
    exact absurd ((by rw [hz x (by omega)] : (Row.mend row).at x = default) ▸ h0) (by decide)

end Linger.Core.Vt

namespace Linger.Core.Vt

/-! ### One row at a time

Every cell-writing operation has the same shape: write into one row, then mend
it. `GridOkExcept y` is the state in between — every row reproducible except
row `y`, which has the right width and reproducible cells but no pair claim yet.
`mendRow` closes it. -/

theorem getD_of_lt {α} (g : Array α) (y : Nat) (d d' : α) (h : y < g.size) :
    g.getD y d = g.getD y d' := by simp [Array.getD, h]

def GridOkExcept (cols rows y : Nat) (g : Array Row) : Prop :=
  g.size = rows ∧
    (∀ y', y' ≠ y → RowOk cols (g.getD y' (blankRow cols {}))) ∧
    (g.getD y (blankRow cols {})).size = cols ∧ (∀ x, CellOk ((g.getD y (blankRow cols {})).at x))

theorem gridOkExcept_of_gridOk {cols rows : Nat} {g : Array Row} (y : Nat)
    (h : GridOk cols rows g) : GridOkExcept cols rows y g :=
  ⟨h.1, fun y' _ => h.2 y', (h.2 y).size, (h.2 y).cells⟩

/-- Writing one reproducible cell into the excepted row keeps the shape. -/
theorem gridOkExcept_set {cols rows y : Nat} {g : Array Row} (h : GridOkExcept cols rows y g)
    (x : Nat) (c : Cell) (hc : CellOk c) (d : Row)
    (hd : y < g.size → g.getD y d = g.getD y (blankRow cols {})) :
    GridOkExcept cols rows y (g.setIfInBounds y ((g.getD y d).setIfInBounds x c)) := by
  obtain ⟨hsz, hother, hrsz, hcells⟩ := h
  refine ⟨by simp [hsz], fun y' hy' => ?_, ?_, ?_⟩
  · rw [getD_set_ne _ _ _ _ _ hy']; exact hother y' hy'
  · by_cases hb : y < g.size
    · rw [getD_set_self _ _ _ _ hb, Array.size_setIfInBounds, hd hb]; exact hrsz
    · rw [show g.setIfInBounds y ((g.getD y d).setIfInBounds x c) = g from by
          simp only [Array.setIfInBounds]; rw [dite_eq_right hb]]
      exact hrsz
  · by_cases hb : y < g.size
    · rw [getD_set_self _ _ _ _ hb, hd hb]
      exact cells_set _ _ hcells hc
    · rw [show g.setIfInBounds y ((g.getD y d).setIfInBounds x c) = g from by
          simp only [Array.setIfInBounds]; rw [dite_eq_right hb]]
      exact hcells

/-- Replacing the excepted row wholesale, with a row built from it. -/
theorem gridOkExcept_replace {cols rows y : Nat} {g : Array Row} (h : GridOkExcept cols rows y g)
    (r : Row) (hsz : r.size = cols) (hcells : ∀ x, CellOk (r.at x)) :
    GridOkExcept cols rows y (g.setIfInBounds y r) := by
  obtain ⟨hgsz, hother, hrsz, hocells⟩ := h
  refine ⟨by simp [hgsz], fun y' hy' => ?_, ?_, ?_⟩
  · rw [getD_set_ne _ _ _ _ _ hy']; exact hother y' hy'
  · by_cases hb : y < g.size
    · rw [getD_set_self _ _ _ _ hb]; exact hsz
    · rw [show g.setIfInBounds y r = g from by
          simp only [Array.setIfInBounds]; rw [dite_eq_right hb]]
      exact hrsz
  · by_cases hb : y < g.size
    · rw [getD_set_self _ _ _ _ hb]; exact hcells
    · rw [show g.setIfInBounds y r = g from by
          simp only [Array.setIfInBounds]; rw [dite_eq_right hb]]
      exact hocells

/-- …and the repair closes it. -/
theorem gridOk_of_except {cols rows y : Nat} {g : Array Row} (h : GridOkExcept cols rows y g) :
    GridOk cols rows (g.setIfInBounds y (Row.mend (g.getD y (blankRow cols {})))) := by
  obtain ⟨hsz, hother, hrsz, hcells⟩ := h
  refine ⟨by simp [hsz], fun y' => ?_⟩
  by_cases hy' : y' = y
  · subst hy'
    by_cases hb : y' < g.size
    · rw [getD_set_self _ _ _ _ hb]
      exact rowOk_mend hrsz hcells
    · rw [show g.setIfInBounds y' (Row.mend (g.getD y' (blankRow cols {}))) = g from by
          simp only [Array.setIfInBounds]; rw [dite_eq_right hb]]
      -- out of range: the read is the default row, which is reproducible
      rw [show g.getD y' (blankRow cols {}) = blankRow cols {} from by simp [Array.getD, hb]]
      exact rowOk_blankRow cols {}
  · rw [getD_set_ne _ _ _ _ _ hy']
    exact hother y' hy'

/-! ### Folds that build a row -/

theorem size_foldl {β : Type} {f : Row → β → Row}
    (hf : ∀ (r : Row) (b : β), (f r b).size = r.size) :
    ∀ (l : List β) (row : Row), (l.foldl f row).size = row.size
  | [], _ => rfl
  | b :: l, row => by rw [List.foldl_cons, size_foldl hf l (f row b), hf row b]

end Linger.Core.Vt

namespace Linger.Core.Vt

/-! ### Renderable is preserved by every operation

Two shapes cover the emulator. An operation that leaves `grid`, `cols`, `rows`
and `altGrid` alone is discharged by its frame (`renderable_congr`) — that is
most of `csiDispatch`. An operation that writes cells goes
`GridOk → GridOkExcept y → write → mendRow`, which is why every row mutation
ends in `Row.mend`. -/

/-- Same grid, dimensions and stash ⇒ same verdict, whatever else moved. -/
theorem renderable_of_gridOk {v w : Vt} (h : Renderable v)
    (hc : w.cols = v.cols) (hr : w.rows = v.rows) (ha : w.altGrid = v.altGrid)
    (hg : GridOk w.cols w.rows w.grid) : Renderable w :=
  ⟨hg, fun g c p hs => by rw [hc, hr]; exact h.alt g c p (by rw [← ha]; exact hs)⟩

theorem gridOkExcept_putCell {v : Vt} {y : Nat}
    (h : GridOkExcept v.cols v.rows y v.grid) (x : Nat) (c : Cell) (hc : CellOk c) :
    GridOkExcept v.cols v.rows y (v.putCell x y c).grid := by
  unfold Vt.putCell Vt.getRow
  dsimp only
  exact gridOkExcept_set h x c hc _ (fun hb => getD_of_lt _ _ _ _ hb)

theorem gridOk_mendRow {v : Vt} {y : Nat}
    (h : GridOkExcept v.cols v.rows y v.grid) :
    GridOk v.cols v.rows (v.mendRow y).grid := by
  have hkey : (v.mendRow y).grid
      = v.grid.setIfInBounds y (Row.mend (v.grid.getD y (blankRow v.cols {}))) := by
    unfold Vt.mendRow Vt.getRow
    dsimp only
    by_cases hb : y < v.grid.size
    · rw [getD_of_lt v.grid y (blankRow v.cols v.pen) (blankRow v.cols {}) hb]
    · simp only [Array.setIfInBounds]
      rw [dite_eq_right hb, dite_eq_right hb]
  rw [hkey]
  exact gridOk_of_except h

/-- The write-then-repair sandwich, as one step. -/
theorem renderable_write_mend {v : Vt} (h : Renderable v) (y : Nat)
    (f : Vt → Vt) (hf : GridOkExcept v.cols v.rows y (f v).grid)
    (hc : (f v).cols = v.cols) (hr : (f v).rows = v.rows)
    (ha : (f v).altGrid = v.altGrid) :
    Renderable ((f v).mendRow y) := by
  refine renderable_of_gridOk h (by rw [Vt.mendRow]; exact hc) (by rw [Vt.mendRow]; exact hr)
    (by rw [Vt.mendRow]; exact ha) ?_
  have := gridOk_mendRow (v := f v) (y := y) (by rw [hc, hr]; exact hf)
  rw [hc, hr] at this
  show GridOk ((f v).mendRow y).cols ((f v).mendRow y).rows ((f v).mendRow y).grid
  rw [show ((f v).mendRow y).cols = v.cols from by rw [Vt.mendRow]; exact hc,
    show ((f v).mendRow y).rows = v.rows from by rw [Vt.mendRow]; exact hr]
  exact this

/-! #### Printing -/

theorem renderable_printPut {v : Vt} (h : Renderable v) (ch : Char) (w : Nat)
    (hpc : Emittable ch) (hw : charWidth ch = w) :
    Renderable (v.printPut ch w) := by
  have hbase : CellOk { base := ch, marks := [], width := w, pen := v.pen } :=
    ⟨hpc, fun _ => hw, Nat.zero_le _, fun _ hm => nomatch hm⟩
  have hblank : CellOk { base := ' ', marks := [], width := 1, pen := v.pen } :=
    ⟨emittable_space, fun _ => rfl, Nat.zero_le _, fun _ hm => nomatch hm⟩
  have hshadow : CellOk { base := ' ', marks := [], width := 0, pen := v.pen } :=
    ⟨emittable_space, fun hz => absurd rfl hz, Nat.zero_le _,
      fun _ hm => nomatch hm⟩
  unfold Vt.printPut
  dsimp only
  split
  · exact renderable_write_mend h _ (fun u => u.putCell v.cursor.x v.cursor.y _)
      (gridOkExcept_putCell (gridOkExcept_of_gridOk _ h.main) _ _ hblank) rfl rfl rfl
  · split
    · exact renderable_write_mend h _
        (fun u => (u.putCell v.cursor.x v.cursor.y _).putCell (v.cursor.x + 1) v.cursor.y _)
        (gridOkExcept_putCell (gridOkExcept_putCell
          (gridOkExcept_of_gridOk _ h.main) _ _ hbase) _ _ hshadow) rfl rfl rfl
    · exact renderable_write_mend h _ (fun u => u.putCell v.cursor.x v.cursor.y _)
        (gridOkExcept_putCell (gridOkExcept_of_gridOk _ h.main) _ _ hbase) rfl rfl rfl

/-- Every cell of a renderable emulator is reproducible, including the
out-of-range reads that `getCell` answers with a default. -/
theorem cellOk_getCell {v : Vt} (h : Renderable v) (x y : Nat) : CellOk (v.getCell x y) := by
  unfold Vt.getCell Vt.getRow
  by_cases hb : y < v.grid.size
  · rw [getD_of_lt v.grid y (blankRow v.cols v.pen) (blankRow v.cols {}) hb]
    exact (h.main.2 y).cells _
  · rw [show v.grid.getD y (blankRow v.cols v.pen) = blankRow v.cols v.pen from by
      simp [Array.getD, hb]]
    exact (rowOk_blankRow v.cols v.pen).cells _

/-- Appending one legal mark to a cell, then repairing the row. Stated over an
arbitrary column so `printMark`'s shadow redirect does not have to be unfolded
inside the proof. -/
theorem renderable_addMark {v : Vt} (h : Renderable v) (cx y : Nat) (ch : Char)
    (hpc : Emittable ch) (hw : charWidth ch = 0)
    (hcap : (v.getCell cx y).marks.length < 8) :
    Renderable ((v.putCell cx y { v.getCell cx y with
      marks := (v.getCell cx y).marks ++ [ch] }).mendRow y) := by
  have hold := cellOk_getCell h cx y
  refine renderable_write_mend h y (fun u => u.putCell cx y _)
    (gridOkExcept_putCell (gridOkExcept_of_gridOk y h.main) cx _ ?_) rfl rfl rfl
  refine ⟨hold.base, hold.width, ?_, ?_⟩
  · simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · intro m hm
    rcases List.mem_append.mp hm with hm' | hm'
    · exact hold.marks m hm'
    · rw [show m = ch from by simpa using hm']
      exact ⟨hw, hpc⟩

theorem renderable_printMark {v : Vt} (h : Renderable v) (ch : Char)
    (hpc : Emittable ch) (hw : charWidth ch = 0) :
    Renderable (v.printMark ch) := by
  unfold Vt.printMark
  dsimp only
  repeat' split
  all_goals first
    | exact h
    | exact renderable_addMark h _ _ _ hpc hw (by omega)

end Linger.Core.Vt

namespace Linger.Core.Vt

/-! #### Whole-row moves, and the stages around a write -/

theorem rowOk_getRow {v : Vt} (h : Renderable v) (y : Nat) : RowOk v.cols (v.getRow y) := by
  unfold Vt.getRow
  by_cases hb : y < v.grid.size
  · rw [getD_of_lt v.grid y (blankRow v.cols v.pen) (blankRow v.cols {}) hb]
    exact h.main.2 y
  · rw [show v.grid.getD y (blankRow v.cols v.pen) = blankRow v.cols v.pen from by
      simp [Array.getD, hb]]
    exact rowOk_blankRow v.cols v.pen

theorem gridOk_set_row {cols rows : Nat} {g : Array Row} (h : GridOk cols rows g)
    (y : Nat) (r : Row) (hr : RowOk cols r) : GridOk cols rows (g.setIfInBounds y r) := by
  refine ⟨by simp [h.1], fun y' => ?_⟩
  by_cases hy' : y' = y
  · subst hy'
    by_cases hb : y' < g.size
    · rw [getD_set_self _ _ _ _ hb]; exact hr
    · rw [show g.setIfInBounds y' r = g from by
        simp only [Array.setIfInBounds]; rw [dite_eq_right hb]]
      exact h.2 y'
  · rw [getD_set_ne _ _ _ _ _ hy']; exact h.2 y'

theorem gridOk_foldl {cols rows : Nat} {β : Type} {f : Array Row → β → Array Row}
    (hf : ∀ (g : Array Row) (b : β), GridOk cols rows g → GridOk cols rows (f g b)) :
    ∀ (l : List β) (g : Array Row), GridOk cols rows g → GridOk cols rows (l.foldl f g) :=
  invariant_foldl (GridOk cols rows) f hf

/-- Scrolling moves whole rows and blanks one, so it never breaks a pair. The
scrollback push is outside `Renderable`'s scope (a repaint paints the screen). -/
theorem renderable_scrollUpIn {v : Vt} (h : Renderable v) (t b : Nat) (a : Bool) :
    Renderable (v.scrollUpIn t b a) := by
  have hgrid : GridOk v.cols v.rows (v.scrollUpIn t b a).grid := by
    have hstep : GridOk v.cols v.rows
        ((List.range (b - t)).foldl
          (fun g i => g.setIfInBounds (t + i) (v.getRow (t + i + 1))) v.grid) :=
      gridOk_foldl (fun g i hg => gridOk_set_row hg _ _ (rowOk_getRow h _)) _ _ h.main
    have hblank := gridOk_set_row hstep b (blankRow v.cols v.pen) (rowOk_blankRow _ _)
    unfold Vt.scrollUpIn
    dsimp only
    split <;> exact hblank
  refine renderable_of_gridOk h ?_ ?_ ?_ ?_
  · rw [frame_scrollUpIn]
  · rw [frame_scrollUpIn]
  · rw [frame_scrollUpIn]
  · rw [show (v.scrollUpIn t b a).cols = v.cols from by rw [frame_scrollUpIn],
      show (v.scrollUpIn t b a).rows = v.rows from by rw [frame_scrollUpIn]]
    exact hgrid

theorem renderable_scrollDownIn {v : Vt} (h : Renderable v) (t b : Nat) :
    Renderable (v.scrollDownIn t b) := by
  have hgrid : GridOk v.cols v.rows (v.scrollDownIn t b).grid := by
    have hstep : GridOk v.cols v.rows
        ((List.range (b - t)).foldl
          (fun g i => g.setIfInBounds (b - i) (v.getRow (b - i - 1))) v.grid) :=
      gridOk_foldl (fun g i hg => gridOk_set_row hg _ _ (rowOk_getRow h _)) _ _ h.main
    exact gridOk_set_row hstep t (blankRow v.cols v.pen) (rowOk_blankRow _ _)
  refine renderable_of_gridOk h ?_ ?_ ?_ ?_
  · rw [frame_scrollDownIn]
  · rw [frame_scrollDownIn]
  · rw [frame_scrollDownIn]
  · rw [show (v.scrollDownIn t b).cols = v.cols from by rw [frame_scrollDownIn],
      show (v.scrollDownIn t b).rows = v.rows from by rw [frame_scrollDownIn]]
    exact hgrid

theorem renderable_scrollUp {v : Vt} (h : Renderable v) : Renderable v.scrollUp :=
  renderable_scrollUpIn h _ _ _

theorem renderable_scrollDown {v : Vt} (h : Renderable v) : Renderable v.scrollDown :=
  renderable_scrollDownIn h _ _

/-- Cursor-only motion: the frame says the grid, dimensions and stash are
untouched, so the verdict carries. -/
theorem renderable_clearPending {v : Vt} (h : Renderable v) : Renderable v.clearPending :=
  renderable_congr h rfl rfl rfl rfl

theorem renderable_carriageReturn {v : Vt} (h : Renderable v) : Renderable v.carriageReturn :=
  renderable_congr h rfl rfl rfl rfl

theorem renderable_printAdvance {v : Vt} (h : Renderable v) (w : Nat) :
    Renderable (v.printAdvance w) := by
  refine renderable_congr h ?_ ?_ ?_ ?_ <;> rw [frame_printAdvance]

theorem renderable_lineFeed {v : Vt} (h : Renderable v) : Renderable v.lineFeed := by
  have h' := renderable_clearPending h
  unfold Vt.lineFeed
  dsimp only
  split
  · exact renderable_scrollUp h'
  · split
    · exact renderable_congr h' rfl rfl rfl rfl
    · exact h'

theorem renderable_reverseIndex {v : Vt} (h : Renderable v) : Renderable v.reverseIndex := by
  have h' := renderable_clearPending h
  unfold Vt.reverseIndex
  dsimp only
  split
  · exact renderable_scrollDown h'
  · exact renderable_congr h' rfl rfl rfl rfl

theorem renderable_printWrap {v : Vt} (h : Renderable v) : Renderable v.printWrap := by
  unfold Vt.printWrap
  split
  · exact renderable_lineFeed (renderable_carriageReturn h)
  · exact renderable_clearPending h

theorem renderable_printWideWrap {v : Vt} (h : Renderable v) (w : Nat) :
    Renderable (v.printWideWrap w) := by
  unfold Vt.printWideWrap
  split
  · exact renderable_lineFeed (renderable_carriageReturn h)
  · exact h

/-- Insert mode shifts cells within a row and then repairs it. Every cell it
writes came from the same row, so `CellOk` carries; the width bookkeeping is
`Row.mend`'s. -/
theorem renderable_printShift {v : Vt} (h : Renderable v) (w : Nat) :
    Renderable (v.printShift w) := by
  unfold Vt.printShift
  dsimp only
  split
  · rename_i hins
    refine renderable_of_gridOk h rfl rfl rfl ?_
    show GridOk v.cols v.rows (v.grid.setIfInBounds v.cursor.y (Row.mend _))
    refine gridOk_set_row h.main _ _ (rowOk_mend ?_ ?_)
    · exact size_foldl (fun r b => by simp) _ _ |>.trans (rowOk_getRow h v.cursor.y).size
    · exact cells_foldl (fun r b hr =>
        cells_set _ _ hr ((rowOk_getRow h v.cursor.y).cells _)) _ _
        (rowOk_getRow h v.cursor.y).cells
  · exact h

/-- **Printing preserves `Renderable`.** The stored codepoint is
`printableChar`-stable by construction, which is what `CellOk.base` needs, and
its width is `charWidth` of exactly that codepoint. -/
theorem renderable_print {v : Vt} (h : Renderable v) (ch : Char) :
    Renderable (v.print ch) := by
  have hpc' : ∀ (u : Vt) (c : Char), Emittable (u.printChar c) := by
    intro u c
    unfold Vt.printChar
    exact printableChar_emittable _
  unfold Vt.print
  dsimp only
  split
  · rename_i h0
    exact renderable_printMark h _ (hpc' v ch) (by simpa using h0)
  · exact renderable_printAdvance (renderable_printPut
      (renderable_printShift (renderable_printWideWrap (renderable_printWrap h) _) _) _ _
        (hpc' v ch) rfl) _

end Linger.Core.Vt

namespace Linger.Core.Vt

/-! #### Erase, insert, delete -/

/-- Every row mutation has the same skeleton: fold writes over the row, mend it,
put it back. Only the written cells differ, and each is either copied from the
same row or an erased blank. -/
theorem renderable_row_mutation {v : Vt} (h : Renderable v) {β : Type}
    (y : Nat) (f : Row → β → Row) (l : List β)
    (hsz : ∀ (r : Row) (b : β), (f r b).size = r.size)
    (hc : ∀ (r : Row) (b : β), (∀ x, CellOk (r.at x)) → ∀ x, CellOk ((f r b).at x)) :
    GridOk v.cols v.rows
      (v.grid.setIfInBounds y (Row.mend (l.foldl f (v.getRow y)))) := by
  refine gridOk_set_row h.main _ _ (rowOk_mend ?_ ?_)
  · exact (size_foldl hsz l (v.getRow y)).trans (rowOk_getRow h y).size
  · exact cells_foldl hc l (v.getRow y) (rowOk_getRow h y).cells

theorem renderable_eraseRowSpan {v : Vt} (h : Renderable v) (y a b : Nat) :
    Renderable (v.eraseRowSpan y a b) := by
  refine renderable_of_gridOk h rfl rfl rfl ?_
  exact renderable_row_mutation h y _ _ (fun r b => by simp)
    (fun r b hr => cells_set _ _ hr (cellOk_erased _))

theorem renderable_eraseChars {v : Vt} (h : Renderable v) (n : Nat) :
    Renderable (v.eraseChars n) := renderable_eraseRowSpan h _ _ _

theorem renderable_eraseLine {v : Vt} (h : Renderable v) (m : Nat) :
    Renderable (v.eraseLine m) := by
  unfold Vt.eraseLine
  split <;> exact renderable_eraseRowSpan h _ _ _

theorem renderable_foldl {β : Type} {f : Vt → β → Vt}
    (hf : ∀ (u : Vt) (b : β), Renderable u → Renderable (f u b)) :
    ∀ (l : List β) (v : Vt), Renderable v → Renderable (l.foldl f v) :=
  invariant_foldl Renderable f hf

theorem renderable_eraseScreen {v : Vt} (h : Renderable v) (m : Nat) :
    Renderable (v.eraseScreen m) := by
  unfold Vt.eraseScreen
  split
  · exact renderable_foldl (fun u i hu => renderable_eraseRowSpan hu _ _ _) _ _
      (renderable_eraseLine h _)
  · exact renderable_foldl (fun u i hu => renderable_eraseRowSpan hu _ _ _) _ _
      (renderable_eraseLine h _)
  · -- ED 3 also drops scrollback, which `Renderable` does not watch
    exact renderable_congr
      (renderable_foldl (fun u i hu => renderable_eraseRowSpan hu _ _ _) _ _ h)
      rfl rfl rfl rfl
  · exact renderable_foldl (fun u i hu => renderable_eraseRowSpan hu _ _ _) _ _ h

theorem renderable_deleteChars {v : Vt} (h : Renderable v) (n : Nat) :
    Renderable (v.deleteChars n) := by
  refine renderable_of_gridOk h rfl rfl rfl ?_
  exact renderable_row_mutation h _ _ _ (fun r b => by simp)
    (fun r b hr => cells_set _ _ hr (by
      split
      · exact (rowOk_getRow h v.cursor.y).cells _
      · exact cellOk_erased _))

theorem renderable_insertChars {v : Vt} (h : Renderable v) (n : Nat) :
    Renderable (v.insertChars n) := by
  refine renderable_of_gridOk h rfl rfl rfl ?_
  exact renderable_row_mutation h _ _ _ (fun r b => by simp)
    (fun r b hr => cells_set _ _ hr (by
      split
      · exact (rowOk_getRow h v.cursor.y).cells _
      · exact cellOk_erased _))

theorem renderable_insertLines {v : Vt} (h : Renderable v) (n : Nat) :
    Renderable (v.insertLines n) := by
  unfold Vt.insertLines
  split
  · exact h
  · exact renderable_foldl (fun u i hu => renderable_scrollDownIn hu _ _) _ _ h

theorem renderable_deleteLines {v : Vt} (h : Renderable v) (n : Nat) :
    Renderable (v.deleteLines n) := by
  unfold Vt.deleteLines
  split
  · exact h
  · exact renderable_foldl (fun u i hu => renderable_scrollUpIn hu _ _ _) _ _ h

/-! #### Cursor, pen, modes, and the alt screen -/

theorem renderable_moveTo {v : Vt} (h : Renderable v) (x y : Nat) :
    Renderable (v.moveTo x y) := renderable_congr h rfl rfl rfl rfl

/-- Setting a field and then homing the cursor, as one step. Stated over the
*result* record so `csiDispatch`'s `DECSTBM` and `setMode`'s `DECOM` arms unify
with it instead of with the incoming state. -/
theorem renderable_moveTo_congr {v w : Vt} (h : Renderable v)
    (hg : w.grid = v.grid) (hc : w.cols = v.cols) (hr : w.rows = v.rows)
    (ha : w.altGrid = v.altGrid) (x y : Nat) : Renderable (w.moveTo x y) :=
  renderable_moveTo (renderable_congr h hg hc hr ha) x y

theorem renderable_moveRel {v : Vt} (h : Renderable v) (dx dy : Int) :
    Renderable (v.moveRel dx dy) := renderable_congr h rfl rfl rfl rfl

theorem renderable_setCol {v : Vt} (h : Renderable v) (x : Nat) :
    Renderable (v.setCol x) := renderable_congr h rfl rfl rfl rfl

theorem renderable_applySgr {v : Vt} (h : Renderable v) (ps : List (Nat × Bool)) :
    Renderable (v.applySgr ps) := renderable_congr h rfl rfl rfl rfl

theorem renderable_backspace {v : Vt} (h : Renderable v) : Renderable v.backspace := by
  refine renderable_congr h ?_ ?_ ?_ ?_ <;> rw [frame_backspace]

theorem renderable_tab {v : Vt} (h : Renderable v) : Renderable v.tab := by
  refine renderable_congr h ?_ ?_ ?_ ?_ <;> rw [frame_tab]

theorem renderable_backTab {v : Vt} (h : Renderable v) : Renderable v.backTab := by
  refine renderable_congr h ?_ ?_ ?_ ?_ <;> rw [frame_backTab]

theorem renderable_enterAlt {v : Vt} (h : Renderable v) (s : Bool) :
    Renderable (v.enterAlt s) := by
  unfold Vt.enterAlt
  split
  · exact h
  · refine ⟨gridOk_replicate _ _ _, fun g c p hs => ?_⟩
    -- the stash is the main grid we just left
    simp only [Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨hg, -, -⟩ := hs
    subst hg
    exact h.main

theorem renderable_leaveAlt {v : Vt} (h : Renderable v) (s : Bool) :
    Renderable (v.leaveAlt s) := by
  unfold Vt.leaveAlt
  split
  · exact h
  · rename_i g cur pen heq
    exact ⟨h.alt g cur pen heq, fun _ _ _ hs => nomatch hs⟩

theorem renderable_setMode {v : Vt} (h : Renderable v) (priv : Bool) (n : Nat) (on : Bool) :
    Renderable (v.setMode priv n on) := by
  unfold Vt.setMode
  split <;> split
  all_goals first
    | exact h
    | exact renderable_congr h rfl rfl rfl rfl
    | (refine renderable_moveTo_congr h ?_ ?_ ?_ ?_ 0 0 <;> rfl)
    | (split <;> first
        | exact renderable_enterAlt h _
        | exact renderable_leaveAlt h _
        | exact renderable_congr h rfl rfl rfl rfl)

theorem renderable_setModes {v : Vt} (h : Renderable v) (priv : Bool)
    (ps : List (Nat × Bool)) (on : Bool) : Renderable (v.setModes priv ps on) :=
  setModes_invariant Renderable priv on ps
    (fun _ p _ hh => renderable_setMode hh priv p.1 on) v h

/-! #### Dispatch, and the parser -/

theorem renderable_csiDispatch {v : Vt} (h : Renderable v) (s : CsiState) (final : UInt8) :
    Renderable (v.csiDispatch s final) := by
  unfold Vt.csiDispatch
  split
  · exact h
  · split
    all_goals first
      | exact h
      | exact renderable_congr h rfl rfl rfl rfl
      | exact renderable_insertChars h _
      | exact renderable_moveRel h _ _
      | exact renderable_carriageReturn (renderable_moveRel h _ _)
      | exact renderable_setCol h _
      | exact renderable_moveTo h _ _
      | exact renderable_eraseScreen h _
      | exact renderable_eraseLine h _
      | exact renderable_insertLines h _
      | exact renderable_deleteLines h _
      | exact renderable_deleteChars h _
      | exact renderable_eraseChars h _
      | exact renderable_setModes h _ _ _
      | exact renderable_foldl (fun u i hu => renderable_tab hu) _ _ h
      | exact renderable_foldl (fun u i hu => renderable_scrollUp hu) _ _ h
      | exact renderable_foldl (fun u i hu => renderable_scrollDown hu) _ _ h
      | exact renderable_foldl (fun u i hu => renderable_backTab hu) _ _ h
      | (split <;> first
          | exact renderable_applySgr h _
          | exact renderable_congr h rfl rfl rfl rfl
          | exact h
          | (dsimp only
             split <;> first
              | exact h
              | (refine renderable_moveTo_congr h ?_ ?_ ?_ ?_ 0 0 <;> rfl)))

theorem renderable_acceptChar {v : Vt} (h : Renderable v) (n : Nat) :
    Renderable (v.acceptChar n) := by
  unfold Vt.acceptChar
  split <;> exact renderable_print h _

theorem renderable_ctl {v : Vt} (h : Renderable v) (b : UInt8) : Renderable (v.ctl b) := by
  unfold Vt.ctl
  split
  all_goals first
    | exact renderable_congr h rfl rfl rfl rfl
    | exact renderable_backspace h
    | exact renderable_tab h
    | exact renderable_lineFeed h
    | exact renderable_carriageReturn h
    | exact h

theorem renderable_oscFinish {v : Vt} (h : Renderable v) (acc : Array UInt8) :
    Renderable (v.oscFinish acc) := by
  unfold Vt.oscFinish
  dsimp only
  repeat' split
  all_goals exact renderable_congr h rfl rfl rfl rfl

theorem renderable_csiFinish {v : Vt} (h : Renderable v) (s : CsiState) (final : UInt8) :
    Renderable (v.csiFinish s final) := by
  unfold Vt.csiFinish
  exact renderable_congr (renderable_csiDispatch h _ _) rfl rfl rfl rfl

/-- Setting the UTF-8 accumulator and then accepting a codepoint. Named for the
same reason as `renderable_moveTo_congr`: `stepGround`'s continuation-byte arm
applies `acceptChar` to a *record*, and an `exact` with `rfl` arguments would fix
the implicit state to the incoming one instead. -/
theorem renderable_acceptChar_congr {v w : Vt} (h : Renderable v)
    (hg : w.grid = v.grid) (hc : w.cols = v.cols) (hr : w.rows = v.rows)
    (ha : w.altGrid = v.altGrid) (n : Nat) : Renderable (w.acceptChar n) :=
  renderable_acceptChar (renderable_congr h hg hc hr ha) n

theorem renderable_stepGround {v : Vt} (h : Renderable v) (b : UInt8) :
    Renderable (v.stepGround b) := by
  unfold Vt.stepGround
  repeat' split
  all_goals
    grind [renderable_congr, renderable_ctl, renderable_acceptChar,
      renderable_acceptChar_congr]

theorem renderable_stepEsc {v : Vt} (h : Renderable v) (b : UInt8) :
    Renderable (v.stepEsc b) := by
  unfold Vt.stepEsc
  split
  all_goals first
    | exact h
    | exact renderable_congr h rfl rfl rfl rfl
    | exact renderable_congr (renderable_lineFeed h) rfl rfl rfl rfl
    | exact renderable_congr (renderable_lineFeed (renderable_carriageReturn h)) rfl rfl rfl rfl
    | exact renderable_congr (renderable_reverseIndex h) rfl rfl rfl rfl
    | -- RIS: a fresh screen of the same dimensions
      (dsimp only
       split <;> exact renderable_congr (renderable_init v.cols v.rows) rfl rfl rfl rfl)
    | (repeat' split
       all_goals exact renderable_congr h rfl rfl rfl rfl)

theorem renderable_stepEscInter {v : Vt} (h : Renderable v) (i b : UInt8) :
    Renderable (v.stepEscInter i b) := by
  unfold Vt.stepEscInter
  dsimp only
  repeat' split
  all_goals exact renderable_congr h rfl rfl rfl rfl

theorem renderable_stepCsi {v : Vt} (h : Renderable v) (s : CsiState) (b : UInt8) :
    Renderable (v.stepCsi s b) := by
  unfold Vt.stepCsi
  repeat' split
  all_goals first
    | exact renderable_congr h rfl rfl rfl rfl
    | exact renderable_csiFinish h _ _
    | exact renderable_ctl h _

theorem renderable_stepOsc {v : Vt} (h : Renderable v) (acc : Array UInt8) (e : Bool)
    (b : UInt8) : Renderable (v.stepOsc acc e b) := by
  unfold Vt.stepOsc
  repeat' split
  all_goals first
    | exact renderable_oscFinish h _
    | exact renderable_congr h rfl rfl rfl rfl

theorem renderable_stepStr {v : Vt} (h : Renderable v) (e : Bool) (b : UInt8) :
    Renderable (v.stepStr e b) := by
  unfold Vt.stepStr
  repeat' split
  all_goals exact renderable_congr h rfl rfl rfl rfl

/-- **§Renderable is preserved by every byte.** With `renderable_init` this
covers every state the daemon can hold: the emulator never stores a grid the row
painter cannot express, for any input at all. -/
theorem renderable_step {v : Vt} (h : Renderable v) (b : UInt8) : Renderable (v.step b) := by
  unfold Vt.step Vt.abortUtf8
  dsimp only
  have h' : Renderable (if v.u8need > 0 && (b < 0x80 || b ≥ 0xC0) then
      { v with u8need := 0, u8acc := 0 } else v) := by
    split
    · exact renderable_congr h rfl rfl rfl rfl
    · exact h
  split
  all_goals first
    | exact renderable_stepGround h' _
    | exact renderable_stepEsc h' _
    | exact renderable_stepEscInter h' _ _
    | exact renderable_stepCsi h' _ _
    | exact renderable_stepOsc h' _ _ _
    | exact renderable_stepStr h' _ _

/-- The stream form. -/
theorem renderable_feed {v : Vt} (h : Renderable v) (bytes : List UInt8) :
    Renderable (v.feed bytes) :=
  renderable_foldl (fun _ b hu => renderable_step hu b) bytes v h

/-- Forgetting partial parser state cannot change the screen. -/
theorem renderable_quiesce {v : Vt} (h : Renderable v) : Renderable v.quiesce :=
  renderable_congr h rfl rfl rfl rfl

end Linger.Core.Vt

namespace Linger.Core.Vt

/-! #### Resize

The last operation that writes cells. Both `resizeRow` and `Vt.resize`'s `fit`
are maps over their target range, so each needs one lemma about `getD` of a
mapped `Array.range` and nothing about array splicing. -/

/-- Reading a mapped `Array.range`: in range it is the function, out of range the
default. Generic in the element type, because `resizeRow` maps over cells and
`Vt.resize`'s `fit` maps over rows. -/
theorem getD_map_range {α : Type} (f : Nat → α) (n x : Nat) (d : α) :
    ((Array.range n).map f).getD x d = if x < n then f x else d := by
  by_cases hb : x < n
  · rw [ite_eq_left hb]
    have hsz : x < ((Array.range n).map f).size := by simp [hb]
    rw [Array.getD, dite_eq_left hsz]
    simp
  · rw [ite_eq_right hb]
    have hsz : ¬ x < ((Array.range n).map f).size := by simpa using hb
    rw [Array.getD, dite_eq_right hsz]

theorem cells_map_range (f : Nat → Cell) (n : Nat) (hf : ∀ i, CellOk (f i)) :
    ∀ x, CellOk (Row.at ((Array.range n).map f) x) := by
  intro x
  unfold Row.at
  rw [getD_map_range]
  split
  · exact hf x
  · exact cellOk_default

theorem rowOk_resizeRow (row : Row) (c : Nat) (p : Pen) (h : ∀ x, CellOk (row.at x)) :
    RowOk c (resizeRow row c p) := by
  unfold resizeRow
  refine rowOk_mend (by simp) (cells_map_range _ _ (fun i => ?_))
  by_cases hi : i < row.size
  · rw [ite_eq_left hi]
    exact h i
  · rw [ite_eq_right hi]
    exact cellOk_erased p

/-- A grid re-fitted to `c × r` is reproducible: each row is an old row at the
new width, or a blank. -/
theorem gridOk_fit {cols : Nat} {g : Array Row} (c r : Nat)
    (h : ∀ y, RowOk cols (g.getD y (blankRow cols {}))) :
    GridOk c r ((Array.range r).map (fun j =>
      let src := if g.size ≥ r then g.size - r + j else j
      if src < g.size then resizeRow (g.getD src #[]) c {} else blankRow c {})) := by
  -- a source row that exists is one of `g`'s, whatever default the read carries
  have hsrc : ∀ (j : Nat), j < g.size → ∀ x, CellOk (Row.at (g.getD j (#[] : Row)) x) := by
    intro j hj x
    have hc := (h j).cells x
    unfold Row.at at hc ⊢
    rw [getD_of_lt g j (blankRow cols {}) (#[] : Row) hj] at hc
    exact hc
  refine ⟨by simp, fun y => ?_⟩
  rw [getD_map_range]
  by_cases hy : y < r
  · rw [ite_eq_left hy]
    dsimp only
    by_cases hge : g.size ≥ r
    · rw [ite_eq_left hge]
      by_cases hb : g.size - r + y < g.size
      · rw [ite_eq_left hb]
        exact rowOk_resizeRow _ _ _ (hsrc _ hb)
      · rw [ite_eq_right hb]
        exact rowOk_blankRow c {}
    · rw [ite_eq_right hge]
      by_cases hb : y < g.size
      · rw [ite_eq_left hb]
        exact rowOk_resizeRow _ _ _ (hsrc _ hb)
      · rw [ite_eq_right hb]
        exact rowOk_blankRow c {}
  · rw [ite_eq_right hy]
    exact rowOk_blankRow c {}

theorem renderable_resize {v : Vt} (h : Renderable v) (cols rows : Nat) :
    Renderable (v.resize cols rows) := by
  unfold Vt.resize
  refine ⟨gridOk_fit _ _ h.main.2, fun g c p hs => ?_⟩
  dsimp only at hs
  rcases hv : v.altGrid with - | x
  · rw [hv] at hs; exact nomatch hs
  · obtain ⟨g0, c0, p0⟩ := x
    rw [hv] at hs
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨hg, -, -⟩ := hs
    subst hg
    exact gridOk_fit _ _ (h.alt g0 c0 p0 hv).2

end Linger.Core.Vt
