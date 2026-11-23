module

public import Linger.Session.CoreSpec
import all Linger.App.CoreSpec
import all Linger.App.CoreCode.Kill
import all Linger.App.CoreCode.Wait
import all Linger.App.Proofs.Wait
public import Linger.App.CoreSpec

/-! # What `kill` answers

Once the daemon `kill` asked has taken the request, `kill` answers that it ended the session
exactly when a look finds no process holding the name, or a newer session holding it; that the
session has not ended exactly when, its patience passed, the daemon it asked still answers as
itself; that it could not find out exactly when, its patience passed, a process it cannot tell
from that daemon holds the name; and otherwise it looks again. Its patience covers a daemon's
ending. -/

namespace Linger.App.Kill

/-- **`kill` answers what happened to the session it asked to end**: that it ended exactly when
the name is free or a newer session holds it, that it has not ended exactly when the daemon it
asked still answers as itself once `Wait.heldNameMs` has passed since the daemon took the request,
that it could not find out exactly when a process it cannot tell from that daemon holds the name
then, and nothing before that, when it looks again. -/
theorem kill_answers (taken now : Nat) (heard : Heard) :
    ((decide taken now heard).told = some .done ↔ heard = .free ∨ heard = .newer) ∧
      ((decide taken now heard).told = some .notDone ↔
        heard = .asked ∧ taken + Wait.heldNameMs ≤ now) ∧
      ((decide taken now heard).told = some .failed ↔
        heard = .held ∧ taken + Wait.heldNameMs ≤ now) ∧
      ((decide taken now heard).told = none ↔
        (heard = .asked ∨ heard = .held) ∧ now < taken + Wait.heldNameMs) := by
  cases heard <;> simp only [decide] <;> (try split) <;> simp_all [Next.told, Api.Found.answer]

/-- **`kill`'s patience covers a daemon's ending**: before the daemon's drain and the waits of the
signals that stop its program have passed since it took the request, `kill` answers only that it
ended the session, or looks again. -/
theorem kill_patient (taken now : Nat) (heard : Heard)
    (ending :
      now < taken + (Linger.Session.drainTimeoutMs + (Linger.Session.ending.map (·.wait)).sum)) :
    (decide taken now heard).told = some .done ∨ (decide taken now heard).told = none := by
  have covers := Wait.held_covers_ending
  have early : ¬taken + Wait.heldNameMs ≤ now := by omega
  cases heard <;> simp [decide, early, Next.told, Api.Found.answer]

/-- The rule before this one, with `wait`'s patience, reads a name a newer session took as the
session not ended: it never answers that it ended the session. -/
theorem byLock_newer (taken now : Nat) :
    (byLock Wait.heldNameMs taken now .newer).told ≠ some .done := by
  simp only [byLock]
  split <;> simp [Next.told, Api.Found.answer]

end Linger.App.Kill
