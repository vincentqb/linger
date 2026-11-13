module

public import Linger.Os.Spec
import all Linger.Os.Spec
import all Linger.Os.Answer

/-! # The exit statuses

Each of linger's answers has its documented code, a program's status passes through, help lists
each of linger's answers once, and an exit status read back gives an answer with that status. -/

namespace Linger.Os.Answer

/-- **Each answer has its documented code**: a shell's conventions for linger's own, and the
status itself for a program's. -/
theorem code_documented (status : UInt32) :
    code .done = 0 ∧
      code .notDone = 1 ∧
      code .usage = 2 ∧
      code .timedOut = 124 ∧
      code .failed = 125 ∧
      code .cannotRun = 126 ∧
      code .notFound = 127 ∧ code .interrupted = 130 ∧ code (.program status) = status := by
  simp [code]

/-- **Help lists each of linger's answers once**, and no program's status. -/
theorem listed_once : listed.Nodup ∧ ∀ a, a ∈ listed ↔ a.Own := by
  refine ⟨by decide, fun a => ?_⟩
  cases a <;> simp [listed, Answer.Own]

/-- linger's own answers have distinct codes, so a listed code names one answer. -/
theorem listed_codes_nodup : (listed.map code).Nodup := by decide

/-- An exit status read back gives an answer with that status. -/
theorem code_ofCode (status : UInt32) : (ofCode status).code = status := by
  unfold ofCode
  cases h : listed.find? (·.code == status) with
  | none => rfl
  | some a => simpa using List.find?_some h

/-- The code of one of linger's answers reads back as that answer. -/
theorem ofCode_code (a : Answer) (own : a.Own) : ofCode a.code = a := by
  cases a <;>
    first
    | rfl
    | exact absurd own (by simp [Answer.Own])

/-- Help prints a line for each listed answer. -/
theorem legend_length : legend.length = listed.length := by simp [legend]

end Linger.Os.Answer
