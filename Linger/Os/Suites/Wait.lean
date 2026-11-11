module

public import Linger.Os.Shell
public import Linger.Os.Spec
import SoftwareChallenge.Commands

/-! # The shim smoke tests' wait checks

Kept apart from `Linger/Os/Suites/Shim.lean`, which `lingertest` runs and which defines its
`main`, so that the default build, and with it the audit, sees the claim these checks
exercise. -/

open Linger.Os.Shell

/-- A sleep lasts at least as long as asked (`Linger.Os.Wait.Lasts`), and a wait naps only until
its deadline and then gives up: with the deadline ahead each nap sleeps and none goes past it,
and a nap asked for once the deadline has passed reports so without sleeping. Each result goes
to `check`. -/
@[exercises Linger.Os.Wait.Lasts]
public def testWaits (check : String → Bool → IO Unit) : IO Unit := do
  let mut lasted := true
  for ms in [1, 7, 20] do
    let before ← monotonicMs
    IO.sleep ms.toUInt32
    lasted := lasted && before + ms ≤ (← monotonicMs)
  check "a sleep lasts at least as long as asked" lasted
  let start ← monotonicMs
  let deadline := start + 50
  let mut naps := 0
  repeat
    unless ← nap deadline 7 do
      break
    naps := naps + 1
  let ended ← monotonicMs
  check "a wait naps until its deadline, at most once a millisecond, and then gives up"
      (deadline ≤ ended && 0 < naps && naps ≤ 50)
  let before ← monotonicMs
  let gaveUp := !(← nap start 7)
  check "a wait whose deadline has passed gives up without sleeping"
      (gaveUp && (← monotonicMs) < before + 7)
