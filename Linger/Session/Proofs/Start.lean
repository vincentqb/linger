module

import all Linger.Session.Start

/-! # What `start` does with a name

`start` takes a name only when no session holds it, and otherwise says which kind of session
does; the report of what a daemon did reads back as written. -/

namespace Linger.Session.Start

/-- `start` takes a name only when no live session holds it and none is saved, and otherwise
says which holds it, a live one first. -/
theorem plan_eq (live saved : Bool) :
    plan live saved = if live then .running else if saved then .saved else .take := rfl

/-- `start` takes a name exactly when no session holds it. -/
theorem plan_take_iff (live saved : Bool) :
    plan live saved = .take ↔ live = false ∧ saved = false := by
  cases live <;> cases saved <;> simp [plan]

/-- **`resume` starts only a saved session**: it runs a program exactly when no live session holds
the name and a saved one does, -/
theorem resumePlan_resume_iff (live saved : Bool) :
    resumePlan live saved = .resume ↔ live = false ∧ saved = true := by
  cases live <;> cases saved <;> simp [resumePlan]

/-- …and starts nothing for a name no session holds. -/
theorem resumePlan_missing_iff (live saved : Bool) :
    resumePlan live saved = .missing ↔ live = false ∧ saved = false := by
  cases live <;> cases saved <;> simp [resumePlan]

/-- A report reads back as itself. -/
theorem decode_encode (r : Report) : Report.decode r.encode = some r := by
  cases r with
  | failed status why => rfl
  | _ => rfl

end Linger.Session.Start
