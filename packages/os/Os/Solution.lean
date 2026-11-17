module

public import Os.CoreSpec
public import Os.WorldSpec
public import Os.CoreCode.Wait
public import Os.CoreCode.Write
public import Os.CoreCode.Lock
import all Os.Proofs.Wait
import all Os.Proofs.Write
import all Os.Proofs.Lock

/-! The OS boundary's headline theorems, proved of the package: `lake comparator` checks that
these are exactly the statements of `Challenge.lean`. -/

public section

namespace Os

theorem wait_ends (after : Nat → Nat → Nat) (lasts : Os.Wait.Lasts after) (deadline step : Nat) :
    (∀ now, Os.Wait.next deadline step now = none ↔ deadline ≤ now) ∧
      (∀ now ms,
        Os.Wait.next deadline step now = some ms → 0 < ms ∧ ms ≤ max step 1 ∧ now + ms ≤ deadline) ∧
      ∀ now,
        ∃ looks,
          looks ≤ deadline - now + 1 ∧ Os.Wait.Ends (Os.Wait.next deadline step) after now looks :=
  ⟨Os.Wait.next_eq_none_iff deadline step, fun _ _ h => Os.Wait.next_some h,
    Os.Wait.ends_within lasts deadline step⟩

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
  intro h
  -- a clock that keeps exact time, and a wait whose deadline has already passed
  have gives := (h (fun now ms => now + ms) (fun _ _ => Nat.le_refl _) 0 1).1 0
  simp at gives

theorem write_full_waits (size off : Nat) (r : Os.Write.Result) :
    (Os.Write.next size off r = .gone ↔ r = .gone) ∧
      (Os.Write.next size off r = .await ↔ r = .full ∨ r = .wrote 0 ∧ off < size) ∧
      (Os.Write.next size off r = .done ↔ ∃ n, r = .wrote n ∧ size ≤ off + n) ∧
      ∀ to,
        Os.Write.next size off r = .write to ↔ ∃ n, r = .wrote n ∧ 0 < n ∧ to = off + n ∧ to < size :=
  Os.Write.next_iff size off r

theorem write_full_waits_rejects_gone :
    ¬∀ (size off : Nat) (r : Os.Write.Result),
        (Os.Write.fullGone size off r =
              .gone ↔
            r = .gone) ∧
          (Os.Write.fullGone size off r =
              .await ↔
            r = .full ∨ r = .wrote 0 ∧ off < size) ∧
          (Os.Write.fullGone size off r =
              .done ↔
            ∃ n, r = .wrote n ∧ size ≤ off + n) ∧
          ∀ to,
            Os.Write.fullGone size off r =
              .write to ↔
            ∃ n, r = .wrote n ∧ 0 < n ∧ to = off + n ∧ to < size := by
  intro h
  -- a full descriptor, which a decision that takes it for a gone reader stops the write for
  have stops := (h 1 0 .full).1
  simp [Os.Write.fullGone] at stops

theorem lock_named (reads : Bool → Bool) (tells : Os.Lock.Tells reads) (attempt : Nat)
    (named : Bool) :
    (Os.Lock.next attempt (reads named) = .hold ↔ named = true) ∧
      (Os.Lock.next attempt (reads named) = .again → attempt + 1 < Os.Lock.attempts) := by
  rw [tells named]
  exact Os.Lock.next_named attempt named

theorem lock_named_rejects_unchecked :
    ¬∀ (reads : Bool → Bool),
        Os.Lock.Tells reads →
          ∀ (attempt : Nat) (named : Bool),
            ((fun (_ : Nat) (_ : Bool) => Os.Lock.Next.hold) attempt (reads named) = .hold ↔
                named = true) ∧
              ((fun (_ : Nat) (_ : Bool) => Os.Lock.Next.hold) attempt (reads named) = .again →
                attempt + 1 < Os.Lock.attempts) := by
  intro h
  -- a lock kept of a file the path no longer names
  cases ((h id (fun _ => rfl) 0 false).1.mp rfl)

end Os
