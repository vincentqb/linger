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

/-- A session's program reads each variable `environment` sets as it sets it, and every other as
the command that asked for the session had it. -/
theorem environment_lookup (name key : String) (inherited : String → Option String) :
    ((environment name).reverse.lookup key).orElse (fun _ => inherited key) =
      if key = "LINGER_SESSION" then some name
      else
        if key = "TERM" then some "xterm-256color"
        else
          if key = "TERM_PROGRAM" then some "linger"
          else
            if key = "TERM_PROGRAM_VERSION" then some Terminal.Mediation.versionNumber
            else inherited key := by
  by_cases h1 : key = "LINGER_SESSION"
  · subst h1; rfl
  by_cases h2 : key = "TERM"
  · subst h2; rfl
  by_cases h3 : key = "TERM_PROGRAM"
  · subst h3; rfl
  by_cases h4 : key = "TERM_PROGRAM_VERSION"
  · subst h4; rfl
  simp [environment, List.lookup, beq_eq_false_iff_ne.2 h1, beq_eq_false_iff_ne.2 h2,
    beq_eq_false_iff_ne.2 h3, beq_eq_false_iff_ne.2 h4, h1, h2, h3, h4]

/-- A program that could not start makes `start` return what a shell or `env -C` reports. -/
theorem failureStatus_exact (why : String) :
    failureStatus (.directory why) = 125 ∧
      failureStatus (.notFound why) = 127 ∧
      failureStatus (.notRunnable why) = 126 := ⟨rfl, rfl, rfl⟩

/-- `info` names the directory a session's program runs in, and the saved directory exactly
when a resume runs it elsewhere. -/
theorem metadata_dirs (name pid created cmd dir : String) (saved : Option String) :
    ("start_dir", dir) ∈ metadata name pid created cmd dir saved ∧
      ∀ d,
        ("saved_dir", d) ∈ metadata name pid created cmd dir saved ↔ saved = some d ∧ d ≠ dir := by
  refine ⟨by simp [metadata], fun d => ?_⟩
  cases saved with
  | none => simp [metadata]
  | some s =>
    by_cases h : s = dir
    · subst h; simp [metadata]; intro e; exact e.symm
    · simp [metadata, h]; constructor
      · intro e; subst e; exact ⟨rfl, h⟩
      · rintro ⟨rfl, _⟩; rfl

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
