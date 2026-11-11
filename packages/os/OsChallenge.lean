module

public import Os.Spec

/-! # Headline theorems of the OS boundary

What the program's bounded waits must do: a wait sleeps between looks as `Os.Wait.next`
decides, and gives up once its deadline has passed, after at most one look per millisecond of
its window when each sleep lasts as long as asked (the world claim `Os.Wait.Lasts`). The
headline is stated over the decision, declared below as a hole: `sorry` here, which the
package's code supplies, and `Os.Solution` proves the same statement of it. -/

public section

/-- How long a wait with a deadline on the monotonic clock sleeps before its next look, asked at
a given time, or `none` once the deadline has passed. -/
@[expose]
def Os.Wait.next : (deadline step now : Nat) → Option Nat := sorry

namespace Os

/-- Every wait ends: it gives up exactly once its deadline has passed, and between looks sleeps at
least 1 ms and at most its step, never past its deadline; so when each sleep lasts at least as
long as asked (`Os.Wait.Lasts`), a wait from `now` gives up after at most `deadline - now + 1`
looks. -/
theorem wait_ends (after : Nat → Nat → Nat) (lasts : Os.Wait.Lasts after) (deadline step : Nat) :
    (∀ now, Os.Wait.next deadline step now = none ↔ deadline ≤ now) ∧
      (∀ now ms,
        Os.Wait.next deadline step now = some ms → 0 < ms ∧ ms ≤ max step 1 ∧ now + ms ≤ deadline) ∧
      ∀ now,
        ∃ looks,
          looks ≤ deadline - now + 1 ∧
            Os.Wait.Ends (Os.Wait.next deadline step) after now looks := by
  sorry

/-- `wait_ends` rejects a wait that never gives up. -/
theorem wait_ends_rejects_endless :
    ¬∀ (after : Nat → Nat → Nat),
        Os.Wait.Lasts after →
          ∀ (deadline step : Nat),
            (∀ now,
                (fun (_ _ _ : Nat) => (some 1 : Option Nat)) deadline step now = none ↔
                  deadline ≤ now) ∧
              (∀ now ms,
                (fun (_ _ _ : Nat) => (some 1 : Option Nat)) deadline step now = some ms →
                  0 < ms ∧ ms ≤ max step 1 ∧ now + ms ≤ deadline) ∧
              ∀ now,
                ∃ looks,
                  looks ≤ deadline - now + 1 ∧
                    Os.Wait.Ends ((fun (_ _ _ : Nat) => (some 1 : Option Nat)) deadline step) after
                      now looks := by
  sorry

end Os
