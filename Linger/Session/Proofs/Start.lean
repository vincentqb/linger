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

/-- A session runs exactly the program and words it was given, and without a command its shell,
alone. -/
theorem programOf_exact (shell : String) (argv : List String) :
    programOf shell argv = (argv.headD shell, (argv.drop 1).toArray) := by cases argv <;> rfl

/-- The daemon runs a program only when it took the request's ticket. -/
theorem proceeds_iff (took : Bool) : proceeds took = true ↔ took = true := Iff.rfl

/-- A command answers that the program runs exactly when the daemon took the ticket and the
program runs. -/
theorem answer_eq_started_iff (took runs : Bool) :
    answer took runs = .started ↔ took = false ∧ runs = true := by
  cases took <;> cases runs <;> simp [answer]

/-- A command that took the ticket answers that the program does not run. -/
theorem answer_command (runs : Bool) : answer true runs = .notStarted := rfl

/-- What holds of every request reached: before anyone takes the ticket nothing has happened;
when the command took it the program does not run and the command said so; when the daemon took
it, the program does not run before the daemon decides, and the command answers only after, with
what the program does. -/
theorem reachable_inv {r : Request} (h : Reachable proceeds answer r) :
    (r.taker = none → r.settled = false ∧ r.runs = false ∧ r.answer = none) ∧
      (r.taker = some .command → r.runs = false ∧ r.answer = some .notStarted) ∧
      (r.taker = some .daemon →
        (r.settled = false → r.runs = false ∧ r.answer = none) ∧
          ∀ a, r.answer = some a → a = answer false r.runs) := by
  induction h with
  | init => simp
  | @step r s _ hstep ih =>
    obtain ⟨hnone, hcmd, hdmn⟩ := ih
    cases hstep with
    | daemonTakes free =>
      obtain ⟨hs, hr, ha⟩ := hnone free
      simp [hs, hr, ha]
    | daemonDecides taken fresh ok =>
      cases ht : r.taker with
      | none => simp [ht] at taken
      | some t =>
        cases t with
        | command =>
          obtain ⟨_, ha⟩ := hcmd ht
          simp [ha, proceeds]
        | daemon =>
          obtain ⟨_, ha⟩ := (hdmn ht).1 fresh
          simp [ha]
    | commandTakes free unanswered =>
      obtain ⟨_, hr, _⟩ := hnone free
      simp [hr, answer]
    | commandAnswers lost decided unanswered => simp [lost, decided]

/-- **A request's answer is true.** Whichever of the command and its daemon takes the ticket first
decides, so the command answers that the program runs only when it does, and that it does not
only when it does not; answers are final, so after `notStarted` the program never runs. -/
theorem answer_true {r : Request} (h : Reachable proceeds answer r) :
    (r.answer = some .started → r.runs = true) ∧
      (r.answer = some .notStarted → r.runs = false) := by
  obtain ⟨hnone, hcmd, hdmn⟩ := reachable_inv h
  cases ht : r.taker with
  | none =>
    obtain ⟨_, _, ha⟩ := hnone ht
    simp [ha]
  | some t =>
    cases t with
    | command =>
      obtain ⟨hr, ha⟩ := hcmd ht
      simp [hr, ha]
    | daemon =>
      have hans := (hdmn ht).2
      constructor
      · intro hs
        have := (answer_eq_started_iff false r.runs).mp (hans _ hs).symm
        exact this.2
      · intro hn
        have heq := hans _ hn
        cases hruns : r.runs with
        | false => rfl
        | true => simp [answer, hruns] at heq

end Linger.Session.Start
