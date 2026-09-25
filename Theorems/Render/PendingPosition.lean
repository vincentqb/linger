module

public import Theorems.Render.History
import all Linger.Core.Render
import all Linger.Core.Vt
import all Theorems.Render.History

/-! A margin cell's bytes arm pending wrap while preserving the rest of the
cursor, even when the receiver's grid is not canonical. -/

namespace Linger.Core.Render

open Linger.Core.Vt

private theorem cursor_marks (ms : List Char) (w : Vt) (h0 : w.g0Line = false)
    (h1 : w.g1Line = false) (hm : ∀ m ∈ ms, charWidth m = 0 ∧ Emittable m) :
    (ms.foldl (fun v m => v.print (safeChar m)) w).cursor = w.cursor := by
  induction ms generalizing w with
  | nil => rfl
  | cons m ms ih =>
    obtain ⟨hw, he⟩ := hm m List.mem_cons_self
    have hp : (w.print (safeChar m)).cursor = w.cursor := by
      rw [safeChar_of_emittable he]
      simp only [Vt.print, printChar_id_of_ascii h0 h1 he.1 he.2, hw, beq_self_eq_true, ite_true]
      rw [frame_printMark]
    rw [List.foldl_cons]
    exact
      (ih _
            (by
              rw [g0_print]; exact h0)
            (by
              rw [g1_print]; exact h1)
            (fun c hc => hm c (List.mem_cons_of_mem m hc))).trans
        hp

/-- A positive-width cell ending at the margin arms wrap-pending. Combining
marks preserve every cursor field, including on malformed or saturated cells;
no receiver grid invariant is needed. -/
theorem cellText_cursor_margin (w : Vt) (c : Cell) (hc : CellOk c) (h0 : w.g0Line = false)
    (h1 : w.g1Line = false) (hwrap : w.modes.wrap = true) (hins : w.modes.insert = false)
    (hpend : w.cursor.pending = false) (hx : w.cursor.x < w.cols) (hwidth : charWidth c.base ≠ 0)
    (hmargin : w.cursor.x + charWidth c.base = w.cols) (hps : w.pstate = .ground)
    (hun : w.u8need = 0) (hua : w.u8acc = 0) :
    (w.feed (cellText c)).cursor =
      { w.cursor with
        x := w.cols - 1, pending := true } := by
  rw [cellText_feed c hps hun hua, safeChar_of_emittable hc.base]
  rw [cursor_marks _ _
      (by
        rw [g0_print]; exact h0)
      (by
        rw [g1_print]; exact h1)
      hc.marks]
  have hpc : w.printChar c.base = c.base := printChar_id_of_ascii h0 h1 hc.base.1 hc.base.2
  have hw : charWidth c.base = 1 ∨ charWidth c.base = 2 := by
    unfold charWidth at hwidth ⊢
    split
    · rename_i hz
      simp only [hz, ite_true] at hwidth
      exact (hwidth rfl).elim
    · split <;> simp
  rcases hw with hw | hw
  · rw [cursor_print_narrow_margin hpc hw hins hpend (by omega), hwrap]
  · have hfit : w.cursor.x + 1 < w.cols :=
      (Nat.lt_or_eq_of_le (Nat.succ_le_of_lt hx)).resolve_right (by omega)
    rw [cursor_print_wide_margin hpc hw hins hpend hfit (by omega), hwrap]

end Linger.Core.Render
