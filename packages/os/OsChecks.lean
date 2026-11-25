module

import Os.WorldCode.Checks
import SoftwareChallenge.Tests
meta import SoftwareChallenge.Attributes -- shake: keep

public section

/-! # OsChecks — the checks of the OS boundary's world claims

Runs every check of the boundary's world claims, the tests that `Os.WorldCode.Checks` marks
`@[tests claim]`, as the challenge library's `SoftwareChallenge.testsMain` runs them: each with
its place, its name and its claim, and how many passed, exiting 1 when one failed. It is the
package's test driver, so `lake test` runs it. -/

/-- Run every check of the boundary's world claims. -/
def main : IO UInt32 := SoftwareChallenge.testsMain
