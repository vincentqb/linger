module

public import Os.WorldSpec
import SoftwareChallenge.Commands

/-! # The check of the world claim the waits rest on

`Os.Wait.Lasts` says that a sleep lasts at least as long as it was asked to. The claim takes the
clock as a parameter, which no Lean term computes: `slept` names it, and the check observes it
by sleeping and reading the monotonic clock around each sleep. No program module imports this
one. -/

namespace Os.Checks

/-- What the monotonic clock reads once a sleep of `ms` milliseconds, asked for when it read
`now`, returns: the observation `Os.Wait.Lasts` constrains. It has no body; the check below
observes it. -/
opaque slept : Nat → Nat → Nat

-- A sleep lasts at least as long as asked: around sleeps of 0, 1, 7 and 20 milliseconds, the
-- monotonic clock advances by at least as much.
Check Os.Wait.Lasts slept := do
  for ms in [0, 1, 7, 20] do
    let before ← IO.monoMsNow
    IO.sleep ms.toUInt32
    let after ← IO.monoMsNow
    unless before + ms ≤ after do
      throw (IO.userError s!"a sleep of {ms} ms returned {after - before} ms after it began")

end Os.Checks
