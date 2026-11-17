module

public import Os.CoreSpec
import all Os.CoreCode.Lock

/-! # A lock is kept only of the file its path names, within a bounded number of attempts -/

namespace Os.Lock

/-- **A lock is kept exactly when the path names the held file**, and another attempt follows
only within the bound. -/
theorem next_named (attempt : Nat) (named : Bool) :
    (next attempt named = .hold ↔ named = true) ∧
      (next attempt named = .again → attempt + 1 < attempts) := by
  unfold next
  cases named
  · simp only [Bool.false_eq_true, ite_false]
    split <;> simp_all
  · simp

end Os.Lock
