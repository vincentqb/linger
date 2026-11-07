module

import all Linger.Session.Record
import all Linger.Session.Wire

/-! # A name's end record

The record reads back as written, and a reader's answer is exactly what the record says: no
record means no session took the name, and a session that took it always leaves an answer. -/

namespace Linger.Session.Record

/-- A record reads back as itself. -/
theorem decode_encode (r : Record) : decode (encode r) = some r := by
  cases r with
  | running => rfl
  | ended outcome => cases outcome <;> rfl

/-- With no record file, no session has taken the name. -/
theorem answer_none : answer none = none := rfl

/-- An ended record answers with how its program ended. -/
theorem answer_ended (outcome : Outcome) :
    answer (some (encode (.ended outcome))) = some outcome := by simp [answer, decode_encode]

/-- A running record found by a reader holding the name, whose session therefore gave the name
up without saying how its program ended, answers that the ending is unknown. -/
theorem answer_running : answer (some (encode .running)) = some .unknown := by
  simp [answer, decode_encode]

/-- Any record file answers, even one that is no record: once a session has taken the name, a
reader always hears something. -/
theorem answer_isSome (file : Option (List UInt8)) : (answer file).isSome = file.isSome := by
  cases file with
  | none => rfl
  | some bytes =>
    simp only [answer]
    split <;> rfl

/-- A reader that does not hold the name hears what one that holds it would, whenever it hears
anything. -/
theorem settled_answer {file : Option (List UInt8)} {known : Option Outcome}
    (h : settled file = some known) : answer file = known := by
  cases file with
  | none =>
    simp only [settled, Option.some.injEq] at h
    exact h ▸ rfl
  | some bytes =>
    simp only [settled] at h
    simp only [answer]
    split at h
    · next outcome heq =>
        simp only [Option.some.injEq] at h ⊢
        exact h
    · cases h

/-- Only a running record, or bytes that are no record, needs the name held to read. -/
theorem settled_eq_none {file : Option (List UInt8)} (h : settled file = none) :
    ∃ bytes, file = some bytes ∧ ∀ outcome, decode bytes ≠ some (.ended outcome) := by
  cases file with
  | none => cases h
  | some bytes =>
    refine ⟨bytes, rfl, fun outcome ended => ?_⟩
    simp [settled, ended] at h

end Linger.Session.Record
