module

public import Os.CoreSpec
public import Os.WorldSpec
meta import SoftwareChallenge

public section

def Os.Wait.next : (deadline step now : Nat) → Option Nat := sorry

def Os.Write.next : (size off : Nat) → Os.Write.Result → Os.Write.Next := sorry

def Os.Lock.attempts : Nat := sorry

def Os.Lock.next : (attempt : Nat) → (named : Bool) → Os.Lock.Next := sorry

namespace Os

theorem wait_ends (after : Nat → Nat → Nat) (lasts : Os.Wait.Lasts after) (deadline step : Nat) :
    (∀ now, Os.Wait.next deadline step now = none ↔ deadline ≤ now) ∧
      (∀ now ms,
        Os.Wait.next deadline step now = some ms → 0 < ms ∧ ms ≤ max step 1 ∧ now + ms ≤ deadline) ∧
      ∀ now,
        ∃ looks,
          looks ≤ deadline - now + 1 ∧
            Os.Wait.Ends (Os.Wait.next deadline step) after now looks := by
  sorry

@[kills wait_ends]
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

theorem write_full_waits (size off : Nat) (r : Os.Write.Result) :
    (Os.Write.next size off r = .gone ↔ r = .gone) ∧
      (Os.Write.next size off r = .await ↔ r = .full ∨ r = .wrote 0 ∧ off < size) ∧
      (Os.Write.next size off r = .done ↔ ∃ n, r = .wrote n ∧ size ≤ off + n) ∧
      ∀ to,
        Os.Write.next size off r = .write to ↔
          ∃ n, r = .wrote n ∧ 0 < n ∧ to = off + n ∧ to < size := by
  sorry

@[kills write_full_waits]
theorem write_full_waits_rejects_gone :
    ¬∀ (size off : Nat) (r : Os.Write.Result),
        (Os.Write.fullGone size off r = .gone ↔ r = .gone) ∧
          (Os.Write.fullGone size off r = .await ↔ r = .full ∨ r = .wrote 0 ∧ off < size) ∧
          (Os.Write.fullGone size off r = .done ↔ ∃ n, r = .wrote n ∧ size ≤ off + n) ∧
          ∀ to,
            Os.Write.fullGone size off r = .write to ↔
              ∃ n, r = .wrote n ∧ 0 < n ∧ to = off + n ∧ to < size := by
  sorry

theorem lock_named (reads : Bool → Bool) (tells : Os.Lock.Tells reads) (attempt : Nat)
    (named : Bool) :
    (Os.Lock.next attempt (reads named) = .hold ↔ named = true) ∧
      (Os.Lock.next attempt (reads named) = .again → attempt + 1 < Os.Lock.attempts) := by
  sorry

@[kills lock_named]
theorem lock_named_rejects_unchecked :
    ¬∀ (reads : Bool → Bool),
        Os.Lock.Tells reads →
          ∀ (attempt : Nat) (named : Bool),
            ((fun (_ : Nat) (_ : Bool) => Os.Lock.Next.hold) attempt (reads named) = .hold ↔
                named = true) ∧
              ((fun (_ : Nat) (_ : Bool) => Os.Lock.Next.hold) attempt (reads named) = .again →
                attempt + 1 < Os.Lock.attempts) := by
  sorry

end Os
