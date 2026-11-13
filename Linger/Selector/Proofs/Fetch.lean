module

public import Linger.Selector.CoreCode.Fetch
import all Linger.Selector.CoreCode.Fetch

public section

/-! # The chooser queries remote hosts only when an event asks it to

Remote rows are due when the chooser opens and after a refresh key, until the next listing,
which fetches them: `due_fetch_iff` is the headline `fetch_follows_events` (`Challenge.lean`,
part 9). -/

namespace Linger.Selector.Picker

/-- One event more: whether remote rows are due after it is what `fetch` decides from whether
they were before it. -/
theorem due_append (next : Bool → Event → Bool) (events : List Event) (event : Event) :
    due next (events ++ [event]) = next (due next events) event := by simp [due, List.foldl_append]

/-- A key the chooser read is a key. -/
@[simp]
theorem isKey_key (key : Key) : (Event.key key).isKey = true := rfl

/-- A listing the chooser starts is no key. -/
@[simp]
theorem isKey_list : Event.list.isKey = false := rfl

/-- **Work follows events.** A listing the chooser starts after `events` queries remote hosts
exactly when no listing came before it, so the chooser has just opened, or a refresh key came
after the last one. -/
theorem due_fetch_iff (events : List Event) :
    due fetch events = true ↔
      (∀ e ∈ events, e.isKey = true) ∨
        Event.key .refresh ∈ events.reverse.takeWhile Event.isKey := by
  obtain ⟨past, rfl⟩ : ∃ past : List Event, events = past.reverse :=
    ⟨events.reverse, (List.reverse_reverse events).symm⟩
  induction past with
  | nil => simp [due]
  | cons event past ih =>
    rw [List.reverse_cons, due_append]
    simp only [List.reverse_reverse, List.mem_reverse] at ih
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.reverse_reverse, List.singleton_append, List.mem_append, List.mem_reverse,
      List.mem_singleton]
    cases event with
    | list => simp [fetch]
    | key key => cases key <;> simp [fetch, List.takeWhile_cons, ih, or_imp, forall_and]

/-- A listing fetches remote rows when they were due, so none is due right after one. -/
theorem due_list (events : List Event) : due fetch (events ++ [.list]) = false := by
  rw [due_append]
  rfl

/-- A refresh key makes remote rows due, whatever came before it. -/
theorem due_refresh (events : List Event) : due fetch (events ++ [.key .refresh]) = true := by
  rw [due_append]
  rfl

end Linger.Selector.Picker
