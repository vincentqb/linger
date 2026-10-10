module

import all Linger.Core.Render
import all Linger.Core.Vt
import all Theorems.Render.History

/-! Margin replay accepts a stale UTF-8 accumulator when no continuation is
pending. ASCII retains it; a fresh multibyte lead overwrites it. -/

namespace Linger.Core.Render

open Linger.Core.Vt

theorem utf8_feed_any_acc {v : Vt} (c : Char) (hc : 0x20 ≤ c.toNat ∧ c.toNat ≠ 0x7F)
    (hg : v.pstate = .ground) (hu : v.u8need = 0) :
    v.feed (utf8 c) = (if c.toNat < 0x80 then v else { v with u8acc := 0 }).print c := by
  have hle := char_le c
  have hn : min c.toNat 0x10FFFF = c.toNat := by omega
  by_cases h1 : c.toNat < 0x80
  · simp only [ite_eq_left h1, utf8, hn]
    rw [feed1, step_ascii hg hu hc.1 h1 hc.2, acceptChar_toNat]
  rw [ite_eq_right h1]
  calc
    v.feed (utf8 c) = ({ v with u8acc := 0 } : Vt).feed (utf8 c) := by
      unfold utf8
      dsimp only
      rw [hn, ite_eq_right h1]
      by_cases h2 : c.toNat < 0x800
      · simp only [ite_eq_left h2, feed2]
        rw [step_lead2 hg hu (by omega),
          step_lead2 (v := { v with u8acc := 0 }) (m := c.toNat / 64) hg hu (by omega)]
      rw [ite_eq_right h2]
      by_cases h3 : c.toNat < 0x10000
      · simp only [ite_eq_left h3, feed3]
        rw [step_lead3 hg hu (by omega),
          step_lead3 (v := { v with u8acc := 0 }) (m := c.toNat / 4096) hg hu (by omega)]
      simp only [ite_eq_right h3, feed4]
      rw [step_lead4 hg hu (by omega),
        step_lead4 (v := { v with u8acc := 0 }) (m := c.toNat / 262144) hg hu (by omega)]
    _ = _ := utf8_feed c hc hg hu rfl

theorem utf8_feed_ground_need {v : Vt} (c : Char) (hc : 0x20 ≤ c.toNat ∧ c.toNat ≠ 0x7F)
    (hg : v.pstate = .ground) (hu : v.u8need = 0) :
    (v.feed (utf8 c)).pstate = .ground ∧ (v.feed (utf8 c)).u8need = 0 := by
  rw [utf8_feed_any_acc c hc hg hu]
  split <;> simpa only [ps_print, un_print] using And.intro hg hu

theorem utf8s_feed_ground_need (cs : List Char) {v : Vt} (hg : v.pstate = .ground)
    (hu : v.u8need = 0) :
    (v.feed (utf8s cs)).pstate = .ground ∧ (v.feed (utf8s cs)).u8need = 0 := by
  induction cs generalizing v with
  | nil => exact ⟨hg, hu⟩
  | cons c cs ih =>
    rw [utf8s_cons, feed_append]
    obtain ⟨hg', hu'⟩ := utf8_feed_ground_need (safeChar c) (safeChar_ge c) hg hu
    exact ih hg' hu'

/-- A combining mark leaves the cursor where it was. -/
theorem cursor_mark (m : Char) (w : Vt) (h0 : w.g0Line = false) (h1 : w.g1Line = false)
    (hm : charWidth m = 0 ∧ Emittable m) : (w.print (safeChar m)).cursor = w.cursor := by
  rw [safeChar_of_emittable hm.2]
  simp only [Vt.print, printChar_id_of_ascii h0 h1 hm.2.1 hm.2.2, hm.1, beq_self_eq_true, ite_true]
  rw [frame_printMark]

theorem utf8s_marks_cursor_any_acc (ms : List Char) (w : Vt) (h0 : w.g0Line = false)
    (h1 : w.g1Line = false) (hm : ∀ m ∈ ms, charWidth m = 0 ∧ Emittable m) (hg : w.pstate = .ground)
    (hu : w.u8need = 0) : (w.feed (utf8s ms)).cursor = w.cursor := by
  induction ms generalizing w with
  | nil => rfl
  | cons m ms ih =>
    rw [utf8s_cons, feed_append]
    have hd := utf8_feed_any_acc (v := w) (safeChar m) (safeChar_ge m) hg hu
    have h0' : (w.feed (utf8 (safeChar m))).g0Line = false := by
      rw [hd]
      split <;> simpa only [g0_print] using h0
    have h1' : (w.feed (utf8 (safeChar m))).g1Line = false := by
      rw [hd]
      split <;> simpa only [g1_print] using h1
    obtain ⟨hg', hu'⟩ := utf8_feed_ground_need (safeChar m) (safeChar_ge m) hg hu
    rw [ih _ h0' h1' (fun c hc => hm c (List.mem_cons_of_mem m hc)) hg' hu', hd]
    split <;> exact cursor_mark m _ h0 h1 (hm m List.mem_cons_self)

/-- Cell text completes every emitted codepoint, even with a stale initial
accumulator. The decoder starts and ends in ground with no pending bytes. -/
theorem cellText_ground_need_any_acc (w : Vt) (c : Cell) (hps : w.pstate = .ground)
    (hun : w.u8need = 0) :
    (w.feed (cellText c)).pstate = .ground ∧ (w.feed (cellText c)).u8need = 0 := by
  unfold cellText
  rw [feed_append]
  obtain ⟨hg, hu⟩ := utf8_feed_ground_need (safeChar c.base) (safeChar_ge c.base) hps hun
  exact utf8s_feed_ground_need c.marks hg hu

/-- The complete margin cursor guarantee requires no initial accumulator value,
receiver grid invariant, or storage bound. -/
theorem cellText_cursor_margin_any_acc (w : Vt) (c : Cell) (hc : CellOk c) (h0 : w.g0Line = false)
    (h1 : w.g1Line = false) (hwrap : w.modes.wrap = true) (hins : w.modes.insert = false)
    (hpend : w.cursor.pending = false) (hx : w.cursor.x < w.cols) (hwidth : charWidth c.base ≠ 0)
    (hmargin : w.cursor.x + charWidth c.base = w.cols) (hps : w.pstate = .ground)
    (hun : w.u8need = 0) :
    (w.feed (cellText c)).cursor =
      { w.cursor with
        x := w.cols - 1, pending := true } := by
  unfold cellText
  rw [feed_append]
  have hd := utf8_feed_any_acc (v := w) (safeChar c.base) (safeChar_ge c.base) hps hun
  have h0' : (w.feed (utf8 (safeChar c.base))).g0Line = false := by
    rw [hd]
    split <;> simpa only [g0_print] using h0
  have h1' : (w.feed (utf8 (safeChar c.base))).g1Line = false := by
    rw [hd]
    split <;> simpa only [g1_print] using h1
  obtain ⟨hg, hu⟩ := utf8_feed_ground_need (safeChar c.base) (safeChar_ge c.base) hps hun
  rw [utf8s_marks_cursor_any_acc _ _ h0' h1' hc.marks hg hu, hd, safeChar_of_emittable hc.base]
  have hw : charWidth c.base = 1 ∨ charWidth c.base = 2 := by
    unfold charWidth at hwidth ⊢
    split
    · rename_i hz
      simp only [hz, ite_true] at hwidth
      exact (hwidth rfl).elim
    · split <;> simp
  have hp (a : Nat) :
    (({ w with u8acc := a } : Vt).print c.base).cursor =
      { w.cursor with
        x := w.cols - 1, pending := true } := by
    have hpc : ({ w with u8acc := a } : Vt).printChar c.base = c.base :=
      printChar_id_of_ascii h0 h1 hc.base.1 hc.base.2
    rcases hw with hw | hw
    · rw [cursor_print_narrow_margin hpc hw hins hpend
          (by
            change w.cols ≤ w.cursor.x + 1
            omega),
        hwrap]
    · have hfit : w.cursor.x + 1 < w.cols :=
        (Nat.lt_or_eq_of_le (Nat.succ_le_of_lt hx)).resolve_right (by omega)
      rw [cursor_print_wide_margin hpc hw hins hpend hfit
          (by
            change w.cols ≤ w.cursor.x + 2
            omega),
        hwrap]
  split
  · exact hp w.u8acc
  · exact hp 0

end Linger.Core.Render
