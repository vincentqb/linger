module

public import Linger.App.Spec
import all Linger.App.Spec
import all Linger.App.Wait
import all Linger.Session

/-! # What `wait` answers

An ending the daemon or the end record tells is the answer; `wait` could not find out only when
the ending is unknown or the name stays held, with no daemon answering, for `heldNameMs` from the
look that first found it so; until then it looks again, keeping when that was; and its patience
covers a daemon's ending. -/

namespace Linger.App.Wait

/-- **An ending is the answer**: how the program ended, from its daemon or the end record. -/
theorem wait_ending (deadline heldSince : Option Nat) (now : Nat) (o : Linger.Session.Outcome) :
    decide deadline heldSince now (.ended o) = .answer (Answer.ofOutcome o) ∧
      decide deadline heldSince now (.recorded (some o)) = .answer (Answer.ofOutcome o) :=
  ⟨rfl, rfl⟩

/-- How long `wait`'s patience for a held name is. -/
theorem heldNameMs_eq : heldNameMs = 8000 := rfl

/-- The answer that tells how a program ended is `failed` only for an unknown ending. -/
theorem ofOutcome_failed (o : Linger.Session.Outcome) :
    Answer.ofOutcome o = .failed ↔ o = .unknown := by cases o <;> simp [Answer.ofOutcome]

/-- **`wait` could not find out only when that is so**: the ending is unknown, or the name has
stayed held, with no daemon answering, for `heldNameMs` since the look that first found it so.
Within that window and before the deadline it looks again, keeping when the window began. -/
theorem wait_held (deadline heldSince : Option Nat) (now : Nat) (heard : Heard) :
    (decide deadline heldSince now heard = .answer .failed ↔
        heard = .ended .unknown ∨
          heard = .recorded (some .unknown) ∨
          heard = .held ∧ ∃ since, heldSince = some since ∧ since + heldNameMs ≤ now) ∧
      (heard = .held →
        (∀ due, deadline = some due → now < due) →
        (∀ since, heldSince = some since → now < since + heldNameMs) →
        decide deadline heldSince now heard = .again (some (heldSince.getD now))) := by
  refine ⟨?_, ?_⟩
  · cases heard with
    | ended o => simp [decide, ofOutcome_failed]
    | status s => simp [decide]
    | silent =>
      simp only [decide]; split <;> simp
    | refused => simp [decide]
    | recorded r =>
      cases r with
      | none => simp [decide]
      | some o => simp [decide, ofOutcome_failed]
    | held =>
      simp only [decide]
      cases heldSince with
      | none =>
        have : ¬now + heldNameMs ≤ now := by simp [heldNameMs_eq]
        simp only [Option.getD_none, this, ↓reduceIte]
        split <;> simp
      | some since =>
        by_cases late : since + heldNameMs ≤ now
        · simp [late]
        · simp only [Option.getD_some, late, ↓reduceIte]
          split <;> simp [late]
  · rintro rfl early within
    simp only [decide]
    have notLate : ¬heldSince.getD now + heldNameMs ≤ now := by
      cases heldSince with
      | none => simp [heldNameMs_eq]
      | some since => simpa using within since rfl
    have notDue : ¬deadline.any (· ≤ now) = true := by
      cases deadline with
      | none => simp
      | some due => simpa using early due rfl
    simp [notLate, notDue]

/-- **`wait`'s patience covers a daemon's ending**: its drain, and a second for each signal that
stops its program. -/
theorem held_covers_ending :
    Linger.Session.drainTimeoutMs + (Linger.Session.ending.map (·.2)).sum ≤ heldNameMs := by decide

end Linger.App.Wait
