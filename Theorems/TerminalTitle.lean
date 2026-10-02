module

public import Linger.Core.Terminal
import all Linger.Core.Terminal
import all Linger.Core.Vt
import all Theorems.Vt
import all Theorems.Render.Ends

/-! Safe title emission is a terminal contract, independent of how an
application composes its title. Parser observations stay with the VT. -/

namespace Linger.Core.Terminal.Title

open Linger.Core.Vt (Vt)
open Linger.Core.Render

public theorem payload_bound (title : String) : (payload title).length ≤ maxChars := by
  simp only [payload, List.length_map, List.length_take]
  omega

/-- A bounded composition keeps every part through payload encoding. -/
public theorem payload_append (left right : String) (h : left.length + right.length ≤ maxChars) :
    payload (left ++ right) = payload left ++ payload right := by
  have hl : left.toList.length ≤ maxChars := by
    rw [String.length_toList]; omega
  have hr : right.toList.length ≤ maxChars := by
    rw [String.length_toList]; omega
  have hb : (left.toList ++ right.toList).length ≤ maxChars := by
    simpa only [List.length_append, String.length_toList] using h
  simp only [payload, String.toList_append, List.take_of_length_le hb, List.take_of_length_le hl,
    List.take_of_length_le hr, List.map_append]

public theorem payload_safe (title : String) (c : Char) (h : c ∈ payload title) :
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
public theorem ansi_payload_safe (title : String) (b : UInt8) (h : b ∈ utf8s (payload title)) :
    b ≥ 0x20 ∧ b ≠ 0x7F := utf8s_no_ctl _ b h

/-- The title fits the VT's OSC bound, including its two-byte command prefix. -/
public theorem ansi_payload_bound (title : String) : 2 + (utf8s (payload title)).length ≤ 2048 := by
  have := utf8s_length_le (payload title)
  have := payload_bound title
  simp only [maxChars] at *
  omega

theorem ansi_ends (title : String) : Ends (ansi title) := by
  simpa only [ansi, escB, List.append_assoc, List.cons_append, List.nil_append] using
    ends_osc (payload title)

public theorem update_waits (v : Vt) (title : String) (h : v.atBoundary = false) :
    update v title = [] := by simp [update, h]

public theorem update_complete (v : Vt) (title : String) (h : v.atBoundary = true) :
    update v title = ansi title := by simp [update, h]

/-- An update emits a complete title exactly when the observer permits it. -/
public theorem update_nonempty_iff (v : Vt) (title : String) :
    update v title ≠ [] ↔ v.atBoundary = true := by
  cases hb : v.atBoundary <;> simp [update, hb, ansi]

/-- Any actual title write requires both parser and character completion. -/
theorem update_requires_boundary (v : Vt) (title : String) (h : update v title ≠ []) :
    v.pstate = .ground ∧ v.u8need = 0 :=
  (Linger.Core.Vt.atBoundary_iff v).mp ((update_nonempty_iff v title).mp h)

end Linger.Core.Terminal.Title
