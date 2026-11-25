module

import Linger.Session.WorldCode.Checks
import Linger.Target.WorldCode.Checks
import SoftwareChallenge.Tests
meta import SoftwareChallenge.Attributes -- shake: keep

public section

/-! # Verify.Checks — the checks of linger's world claims

Runs every check of linger's world claims, the tests that `Linger.Session.WorldCode.Checks` and
`Linger.Target.WorldCode.Checks` mark `@[tests claim]`, as the challenge library's
`SoftwareChallenge.testsMain` runs them: each with its place, its name and its claim, and how many
passed, exiting 1 when one failed. `scripts/verify.sh` runs it. -/

/-- Run every check of linger's world claims. -/
def main : IO UInt32 := SoftwareChallenge.testsMain
