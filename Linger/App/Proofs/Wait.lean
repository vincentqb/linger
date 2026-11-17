module

public import Linger.Session.CoreSpec
import all Linger.App.CoreSpec
import all Linger.App.CoreCode.Wait
import all Linger.Session.CoreCode

/-! # What `wait` answers

An ending the daemon or the end record tells is the answer, `saved` with its signal for a session
a signal to its daemon saved; `wait` could not find out only when the program's ending is unknown
or the name stays held, with no daemon answering, for `heldNameMs` from the look that first found
it so; until then it looks again, keeping when that was; and its patience covers a daemon's
ending. -/

namespace Linger.App.Wait

/-- **An ending is what `wait` finds**: how the session ended, from its daemon or the end
record. -/
theorem wait_ending (deadline heldSince : Option Nat) (now : Nat) (e : Linger.Session.Ending) :
    decide deadline heldSince now (.ended e) = .answer (.ended e) ∧
      decide deadline heldSince now (.recorded (some e)) = .answer (.ended e) := ⟨rfl, rfl⟩

/-- A session a signal to its daemon saved answers `saved` with that signal, never a status of its
program. -/
theorem saved_answer (signal : UInt8) :
    (Linger.Session.Ending.saved signal).answer = .saved signal := rfl

/-- How long `wait`'s patience for a held name is. -/
theorem heldNameMs_eq : heldNameMs = 8000 := rfl

/-- The answer that tells how a program ended is `failed` only for an unknown ending. -/
theorem outcome_failed (o : Linger.Session.Outcome) : o.answer = .failed ↔ o = .unknown := by
  cases o <;> simp [Linger.Session.Outcome.answer]

/-- …and so is the answer that tells how a session ended, a saved one never. -/
theorem ending_failed (e : Linger.Session.Ending) : e.answer = .failed ↔ e = .program .unknown := by
  cases e with
  | program o => simp [Linger.Session.Ending.answer, outcome_failed]
  | saved signal => simp [Linger.Session.Ending.answer]
  | dismissed => simp [Linger.Session.Ending.answer]

/-- **`wait` could not find out only when that is so**: the ending is unknown, or the name has
stayed held, with no daemon answering, for `heldNameMs` since the look that first found it so.
Within that window and before the deadline it looks again, keeping when the window began. -/
theorem wait_held (deadline heldSince : Option Nat) (now : Nat) (heard : Heard) :
    ((decide deadline heldSince now heard).told = some .failed ↔
        heard = .ended (.program .unknown) ∨
          heard = .recorded (some (.program .unknown)) ∨
          heard = .held ∧ ∃ since, heldSince = some since ∧ since + heldNameMs ≤ now) ∧
      (heard = .held →
        (∀ due, deadline = some due → now < due) →
        (∀ since, heldSince = some since → now < since + heldNameMs) →
        decide deadline heldSince now heard = .again (some (heldSince.getD now))) := by
  refine ⟨?_, ?_⟩
  · cases heard with
    | ended e => simp [decide, Next.told, Api.Found.answer, ending_failed]
    | status s => simp [decide, Next.told, Api.Found.answer]
    | silent =>
      simp only [decide]; split <;> simp [Next.told, Api.Found.answer]
    | refused => simp [decide, Next.told, Api.Found.answer]
    | recorded r =>
      cases r with
      | none => simp [decide, Next.told, Api.Found.answer]
      | some e => simp [decide, Next.told, Api.Found.answer, ending_failed]
    | held =>
      simp only [decide]
      cases heldSince with
      | none =>
        have : ¬now + heldNameMs ≤ now := by simp [heldNameMs_eq]
        simp only [Option.getD_none, this, ↓reduceIte]
        split <;> simp [Next.told, Api.Found.answer]
      | some since =>
        by_cases late : since + heldNameMs ≤ now
        · simp [late, Next.told, Api.Found.answer]
        · simp only [Option.getD_some, late, ↓reduceIte]
          split <;> simp [late, Next.told, Api.Found.answer]
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
    Linger.Session.drainTimeoutMs + (Linger.Session.ending.map (·.wait)).sum ≤ heldNameMs := by
  decide

end Linger.App.Wait
