module

import SoftwareChallenge.Commands

public section

/-! # What the OS boundary's headlines are stated in

How a polling wait runs against the monotonic clock, and the world claim it relies on: that a
sleep lasts at least as long as it was asked to. Bodies are exposed: each definition here is
its own specification. The claims about a session's processes and descriptors are the
session's, in `Linger/Session/Spec.lean`; this one is about time, which the boundary's own
waits use too. -/

namespace Os.Wait

/-- A wait from `now` gives up after `looks` looks: it looks, and while `next` asks for a sleep
of `ms`, sleeps until the clock reads `after now ms` and looks again, until `next` reports that
its deadline has passed. -/
inductive Ends (next : Nat → Option Nat) (after : Nat → Nat → Nat) : Nat → Nat → Prop where
  /-- The deadline has passed: this look is the last. -/
  | missed {now : Nat} (h : next now = none) : Ends next after now 1
  /-- A sleep of `ms`, then the looks that follow. -/
  |
  slept {now ms looks : Nat} (h : next now = some ms)
    (rest : Ends next after (after now ms) looks) : Ends next after now (looks + 1)

/-- A sleep of `ms` milliseconds asked for when the monotonic clock reads `now` returns, and the
clock then reads `after now ms`, at least `ms` later. A clock reading, after `IO.sleep ms`
returns, less than `ms` above the one before it falsifies it, as would a sleep that never
returns. -/
WorldClaim Lasts (after : Nat → Nat → Nat) := ∀ now ms, now + ms ≤ after now ms

end Os.Wait
