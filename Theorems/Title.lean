module

import all Linger.Core.Title
import Theorems.TerminalTitle

namespace Linger.Core.Title

theorem compose_quiet (session : String) (capacity : Nat) :
    compose session "" "" capacity = Name.sanitize session := by
  have ht (n : Nat) : ("".take n).copy = "" := by
    apply String.toList_injective
    simp
  simp [compose, ht]

theorem compose_parts (session application summary : String) (capacity : Nat) :
    let suffix := if summary.isEmpty then "" else " · " ++ summary
    let clipped :=
      (application.take (capacity - (Name.sanitize session).length - suffix.length - 3)).copy
    compose session application summary capacity =
      String.intercalate " · "
        (Name.sanitize session :: [clipped, summary].filter (!·.isEmpty)) := by
  dsimp only [compose]
  generalize
    (application.take
        (capacity - (Name.sanitize session).length -
          (if summary.isEmpty then "" else " · " ++ summary).length -
          3)).copy =
    clipped
  cases hc : clipped.isEmpty <;> cases hs : summary.isEmpty <;> simp [hc, hs, String.append_assoc]

/-- Empty or fully clipped application titles leave no dangling separator. -/
theorem compose_context (session application : String) (capacity : Nat) :
    let clipped := (application.take (capacity - (Name.sanitize session).length - 3)).copy
    compose session application "" capacity =
      if clipped.isEmpty then Name.sanitize session
      else Name.sanitize session ++ " · " ++ clipped := by
  dsimp only
  unfold compose
  simp only [show ("".isEmpty) = true from rfl, ite_true, String.length_empty, Nat.sub_zero,
    String.append_empty]
  generalize (application.take (capacity - (Name.sanitize session).length - 3)).copy = clipped
  cases clipped.isEmpty <;> simp [String.append_assoc]

/-- Attention receives its space before the application title is clipped,
then appends to the context. No attention means no reserved separator. -/
theorem compose_attention_last (session application summary : String) (capacity : Nat) :
    let suffix := if summary.isEmpty then "" else " · " ++ summary
    compose session application summary capacity =
      compose session application "" (capacity - suffix.length) ++ suffix := by
  by_cases hs : summary.isEmpty <;> simp [compose, hs, Nat.sub_sub, Nat.add_comm, Nat.add_assoc]

/-- If the session and attention fit, application text cannot overflow the
encoder's budget. This also covers budgets that leave no room for a separator. -/
theorem compose_bound (session application summary : String) (capacity : Nat)
    (h :
      (Name.sanitize session).length + (if summary.isEmpty then "" else " · " ++ summary).length ≤
        capacity) :
    (compose session application summary capacity).length ≤ capacity := by
  let suffix := if summary.isEmpty then "" else " · " ++ summary
  let clipped :=
    (application.take (capacity - (Name.sanitize session).length - suffix.length - 3)).copy
  have hb : clipped.length ≤ capacity - (Name.sanitize session).length - suffix.length - 3 := by
    dsimp only [clipped]
    rw [← String.length_toList, String.toList_copy_take]
    exact List.length_take_le _ _
  change (Name.sanitize session).length + suffix.length ≤ capacity at h
  change
    (Name.sanitize session ++ (if clipped.isEmpty then "" else " · " ++ clipped) ++ suffix).length ≤
      capacity
  by_cases he : clipped.isEmpty
  · simpa [he] using h
  · have hn : clipped ≠ "" := by simpa only [String.isEmpty_iff] using he
    have hp : clipped.length ≠ 0 := fun hz => hn (String.length_eq_zero_iff.mp hz)
    simp only [ite_eq_right he, String.length_append]
    change (Name.sanitize session).length + (3 + clipped.length) + suffix.length ≤ capacity
    omega

/-- The actual OSC payload retains the attention suffix, including when the
application is arbitrarily long. Controls still pass through the safe encoder. -/
theorem compose_payload_attention_last (session application summary : String)
    (hs : summary.isEmpty = false)
    (h : (Name.sanitize session).length + (" · " ++ summary).length ≤ Terminal.Title.maxChars) :
    Terminal.Title.payload (compose session application summary Terminal.Title.maxChars) =
      Terminal.Title.payload
          (compose session application "" (Terminal.Title.maxChars - (" · " ++ summary).length)) ++
        Terminal.Title.payload (" · " ++ summary) := by
  have hb :=
    compose_bound session application summary Terminal.Title.maxChars (by simpa [hs] using h)
  rw [compose_attention_last] at hb ⊢
  simp only [hs, Bool.false_eq_true, ite_false] at hb ⊢
  apply Terminal.Title.payload_append
  simpa only [String.length_append] using hb

end Linger.Core.Title
