module

import Os.Spec
import all Os.Wait

/-! A wait's sleeps, decided for every deadline, step and time: it gives up exactly once its
deadline has passed, sleeps between 1 ms and its step without passing the deadline, and so,
when each sleep lasts as long as asked (`Wait.Lasts`), gives up after at most one look per
millisecond of its window. -/

namespace Os.Wait

/-- A wait gives up exactly once its deadline has passed. -/
theorem next_eq_none_iff (deadline step now : Nat) :
    next deadline step now = none ↔ deadline ≤ now := by
  unfold next
  split <;> simp_all

/-- Between looks, a wait sleeps at least 1 ms and at most its step, never past its deadline. -/
theorem next_some {deadline step now ms : Nat} (h : next deadline step now = some ms) :
    0 < ms ∧ ms ≤ max step 1 ∧ now + ms ≤ deadline := by
  unfold next at h
  split at h
  · simp at h
  · simp only [Option.some.injEq] at h
    omega

/-- **A wait ends.** When each sleep lasts at least as long as asked, a wait from `now` gives up
after at most `deadline - now + 1` looks. -/
theorem ends_within {after : Nat → Nat → Nat} (lasts : Lasts after) (deadline step : Nat) :
    ∀ now, ∃ looks, looks ≤ deadline - now + 1 ∧ Ends (next deadline step) after now looks := by
  suffices key :
    ∀ k now,
      deadline - now ≤ k →
        ∃ looks, looks ≤ deadline - now + 1 ∧ Ends (next deadline step) after now looks
    from fun now => key _ now (Nat.le_refl _)
  intro k
  induction k with
  | zero =>
    intro now hk
    have hn : next deadline step now = none := (next_eq_none_iff _ _ _).mpr (by omega)
    exact ⟨1, by omega, .missed hn⟩
  | succ k ih =>
    intro now hk
    cases hn : next deadline step now with
    | none => exact ⟨1, by omega, .missed hn⟩
    | some ms =>
      obtain ⟨hpos, -, hle⟩ := next_some hn
      have hafter := lasts now ms
      obtain ⟨looks, hlooks, hends⟩ := ih (after now ms) (by omega)
      exact ⟨looks + 1, by omega, .slept hn hends⟩

end Os.Wait
