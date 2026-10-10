module

import all Linger.Core.Env

/-! Environment policies, decided for every value of the variable, including unset
and empty. The runtime reads each variable once into these functions; source
gates tie the reads, and the suites run the program with unset and empty values. -/

namespace Linger.Core.Env

/-- A session's default program is never the empty word. -/
theorem shellOf_ne_empty (value : Option String) : shellOf value ≠ "" := by
  unfold shellOf
  split
  · split <;> simp_all
  · simp

/-- A nonempty SHELL is the program, unchanged. -/
theorem shellOf_set {shell : String} (set : shell ≠ "") : shellOf (some shell) = shell := by
  simp [shellOf, set]

/-- An unset or empty SHELL starts `sh`. -/
theorem shellOf_absent : shellOf none = "sh" ∧ shellOf (some "") = "sh" := by simp [shellOf]

/-- No remotes file is configured exactly when HOME is unset or empty. -/
theorem remotesFile_eq_none_iff (home : Option String) :
    remotesFile home = none ↔ home = none ∨ home = some "" := by
  unfold remotesFile
  split <;> simp_all

/-- A nonempty HOME names the file under it. -/
theorem remotesFile_set {dir : String} (set : dir ≠ "") :
    remotesFile (some dir) = some (dir ++ "/.config/linger/remotes") := by simp [remotesFile, set]

/-- A read-only view keeps the detach key, whatever `LINGER_NO_DETACH_KEY` holds. -/
theorem detachEnabled_readOnly (flag : Option String) : detachEnabled true flag = true := by
  simp [detachEnabled]

/-- Writable attach detaches exactly when `LINGER_NO_DETACH_KEY` is unset. -/
theorem detachEnabled_writable (flag : Option String) : detachEnabled false flag = flag.isNone := by
  simp [detachEnabled]

end Linger.Core.Env
