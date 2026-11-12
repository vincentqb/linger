module

public import Os.Spec

/-! # Headline theorems of the OS boundary

What the program's bounded waits must do: a wait sleeps between looks as `Os.Wait.next`
decides, and gives up once its deadline has passed, after at most one look per millisecond of
its window when each sleep lasts as long as asked (the world claim `Os.Wait.Lasts`). And what a
full write does after each attempt, as `Os.Write.next` decides: an attempt that wrote nothing,
the descriptor full because another program left it nonblocking, waits until the descriptor can
take more, never taken for a reader that is gone; a reader that is gone, and only that, stops a
write early; and every other attempt goes on from where it stopped, so no byte is written twice
or skipped. The headlines are stated over the decisions, declared below as holes: `sorry` here,
which the package's code supplies, and `Os.Solution` proves the same statements of them. Not
claimed: that `Os.Shell.write` reports each outcome as the operating system gave it, nor that a
wait for a full descriptor ends, since that is its reader's to end, which the shim suite and the
robust suite test. -/

public section

def Os.Wait.next : (deadline step now : Nat) → Option Nat := sorry

def Os.Write.next : (size off : Nat) → Os.Write.Result → Os.Write.Next := sorry

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

theorem write_full_waits_rejects_gone :
    ¬∀ (size off : Nat) (r : Os.Write.Result),
        ((fun (size off : Nat) (r : Os.Write.Result) =>
                  match r with
                  | .wrote n =>
                    if size ≤ off + n then Os.Write.Next.done
                    else if n = 0 then .gone else .write (off + n)
                  | .full | .gone => .gone)
                size off r =
              .gone ↔
            r = .gone) ∧
          ((fun (size off : Nat) (r : Os.Write.Result) =>
                  match r with
                  | .wrote n =>
                    if size ≤ off + n then Os.Write.Next.done
                    else if n = 0 then .gone else .write (off + n)
                  | .full | .gone => .gone)
                size off r =
              .await ↔
            r = .full ∨ r = .wrote 0 ∧ off < size) ∧
          ((fun (size off : Nat) (r : Os.Write.Result) =>
                  match r with
                  | .wrote n =>
                    if size ≤ off + n then Os.Write.Next.done
                    else if n = 0 then .gone else .write (off + n)
                  | .full | .gone => .gone)
                size off r =
              .done ↔
            ∃ n, r = .wrote n ∧ size ≤ off + n) ∧
          ∀ to,
            (fun (size off : Nat) (r : Os.Write.Result) =>
                    match r with
                    | .wrote n =>
                      if size ≤ off + n then Os.Write.Next.done
                      else if n = 0 then .gone else .write (off + n)
                    | .full | .gone => .gone)
                  size off r =
                .write to ↔
              ∃ n, r = .wrote n ∧ 0 < n ∧ to = off + n ∧ to < size := by
  sorry

end Os
