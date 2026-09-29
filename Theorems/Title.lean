module

import all Linger.Core.Title
import all Linger.Core.Vt
import all Theorems.Vt
import all Theorems.Render.Ends

namespace Linger.Core.Vt

@[simp]
theorem windowTitle_eq (v : Vt) : v.windowTitle = v.title := rfl

theorem atBoundary_iff (v : Vt) : v.atBoundary = true ↔ v.pstate = .ground ∧ v.u8need = 0 := by
  simp [Vt.atBoundary]

theorem observe_append (v : Vt) (a b : List UInt8) :
    v.observe (a ++ b) = (v.observe a).observe b := by simp [Vt.observe, List.foldl_append]

/-- Every observer byte is the existing parser step, changing only discarded
history. In particular its title, parser state and partial UTF-8 agree exactly. -/
theorem observe_singleton (v : Vt) (b : UInt8) : v.observe [b] = { (v.step b) with sb := {} } := rfl

theorem observe_no_history (v : Vt) (bytes : List UInt8) (h : v.sb = {}) :
    (v.observe bytes).sb = {} := invariant_foldl (·.sb = {}) _ (fun _ _ _ => rfl) bytes v h

theorem observe_good (v : Vt) (bytes : List UInt8) (h : Good v) : Good (v.observe bytes) :=
  invariant_foldl Good (fun w b => { (w.step b) with sb := {} })
    (fun _ b hw => { Good.step b hw with sbLe := by simp [Ring.size, sbCap] }) bytes v h

/-- Discarding history preserves every invariant required of a public VT
transformer; screen shape and parser state still come from the usual step. -/
theorem observe_invariants (v : Vt) (bytes : List UInt8) (hr : Renderable v) (hu : U8Ok v)
    (ht : TabsOk v) (hc : CsiOk v) :
    Renderable (v.observe bytes) ∧
      U8Ok (v.observe bytes) ∧ TabsOk (v.observe bytes) ∧ CsiOk (v.observe bytes) :=
  invariant_foldl (fun w => Renderable w ∧ U8Ok w ∧ TabsOk w ∧ CsiOk w)
    (fun w b => { (w.step b) with sb := {} })
    (fun _ b hw =>
      ⟨renderable_congr (renderable_step hw.1 b) rfl rfl rfl rfl, u8Ok_step b hw.2.1,
        tabsOk_step b hw.2.2.1, csiOk_step hw.2.2.2 b⟩)
    bytes v ⟨hr, hu, ht, hc⟩

theorem observe_dims (v : Vt) (bytes : List UInt8) (h : Good v) :
    (v.observe bytes).colCount = v.colCount ∧ (v.observe bytes).rowCount = v.rowCount := by
  have hi :=
    invariant_foldl (fun w => Good w ∧ dims w = dims v) (fun w b => { (w.step b) with sb := {} })
      (fun w b hw =>
        ⟨{ Good.step b hw.1 with sbLe := by simp [Ring.size, sbCap] },
          (dims_step b hw.1).trans hw.2⟩)
      bytes v ⟨h, rfl⟩
  exact Prod.mk.inj hi.2

end Linger.Core.Vt

namespace Linger.Core.Title

open Linger.Core.Vt (Vt)
open Linger.Core.Render

theorem compose_quiet (session : String) : compose session "" "" = Name.sanitize session := by
  simp [compose]

theorem compose_parts (session summary application : String) :
    compose session summary application =
      String.intercalate " · "
        (Name.sanitize session :: [summary, application].filter (!·.isEmpty)) := rfl

theorem payload_bound (title : String) : (payload title).length ≤ 500 := by
  simp only [payload, List.length_map, List.length_take]
  omega

theorem payload_safe (title : String) (c : Char) (h : c ∈ payload title) :
    0x20 ≤ c.toNat ∧ c.toNat ≠ 0x7F ∧ ¬(0x80 ≤ c.toNat ∧ c.toNat < 0xA0) := by
  simp only [payload, List.mem_map] at h
  obtain ⟨x, _, rfl⟩ := h
  split
  · decide
  · rename_i hx
    have hs := safeChar_ge x
    simp only [safeChar]
    split
    · decide
    · rename_i hsafe
      simp only [safeChar, ite_eq_right hsafe] at hs
      simp only [Bool.and_eq_true, decide_eq_true_eq, not_and] at hx
      exact ⟨hs.1, hs.2, fun h => hx h.1 h.2⟩

theorem ansi_framing (title : String) :
    ansi title = [0x1B, 0x5D, 0x32, 0x3B] ++ utf8s (payload title) ++ [0x07] := rfl

/-- The payload itself cannot introduce an ESC or BEL to escape the title. -/
theorem ansi_payload_safe (title : String) (b : UInt8) (h : b ∈ utf8s (payload title)) :
    b ≥ 0x20 ∧ b ≠ 0x7F := utf8s_no_ctl _ b h

/-- The title fits the VT's OSC bound, including its two-byte command prefix. -/
theorem ansi_payload_bound (title : String) : 2 + (utf8s (payload title)).length ≤ 2048 := by
  have := utf8s_length_le (payload title)
  have := payload_bound title
  omega

theorem ansi_ends (title : String) : Ends (ansi title) := by
  simpa only [ansi, escB, List.append_assoc, List.cons_append, List.nil_append] using
    ends_osc (payload title)

theorem update_waits (v : Vt) (title : String) (h : v.atBoundary = false) :
    update v title = [] := by simp [update, h]

theorem update_complete (v : Vt) (title : String) (h : v.atBoundary = true) :
    update v title = ansi title := by simp [update, h]

/-- Any actual title write requires both parser and character completion. -/
theorem update_requires_boundary (v : Vt) (title : String) (h : update v title ≠ []) :
    v.pstate = .ground ∧ v.u8need = 0 := by
  apply (Linger.Core.Vt.atBoundary_iff v).mp
  cases hb : v.atBoundary with
  | false => exact False.elim (h (update_waits v title hb))
  | true => rfl

end Linger.Core.Title
