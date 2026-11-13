module

import Os.CoreSpec
import all Os.CoreCode.Write

/-! Each outcome of a write attempt has its one reaction: a full write stops early exactly when
the reader is gone, waits exactly when an attempt wrote nothing with bytes left, is done exactly
when every byte is written, and otherwise writes on from exactly where the attempt stopped. -/

namespace Os.Write

/-- **One outcome, one reaction.** What a full write does after an attempt, by what the attempt
did. -/
theorem next_iff (size off : Nat) (r : Result) :
    (next size off r = .gone ↔ r = .gone) ∧
      (next size off r = .await ↔ r = .full ∨ r = .wrote 0 ∧ off < size) ∧
      (next size off r = .done ↔ ∃ n, r = .wrote n ∧ size ≤ off + n) ∧
      ∀ to, next size off r = .write to ↔ ∃ n, r = .wrote n ∧ 0 < n ∧ to = off + n ∧ to < size := by
  cases r with
  | wrote n =>
    unfold next
    by_cases all : size ≤ off + n
    · simp only [all, ↓reduceIte]
      refine ⟨by simp, ?_, by simp [all], fun to => ?_⟩
      · simp only [reduceCtorEq, Result.wrote.injEq, false_or, false_iff, not_and]
        omega
      · simp only [reduceCtorEq, Result.wrote.injEq, false_iff, not_exists, not_and]
        omega
    · simp only [all, ↓reduceIte]
      by_cases none : n = 0
      · subst none
        simp only [↓reduceIte]
        refine ⟨by simp, ?_, ?_, fun to => by simp⟩
        · simp
          omega
        · simp
          omega
      · simp only [none, ↓reduceIte]
        refine ⟨by simp, by simp [none], ?_, fun to => ?_⟩
        · simp
          omega
        simp only [Next.write.injEq, Result.wrote.injEq]
        constructor
        · intro h
          exact ⟨n, rfl, by omega, h.symm, by omega⟩
        · rintro ⟨m, rfl, -, rfl, -⟩
          rfl
  | full => simp [next]
  | gone => simp [next]

end Os.Write
