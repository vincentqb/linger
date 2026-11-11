module

public section

/-! # Os.Wait — how long a wait sleeps

A wait looks for what it waits for and, between looks, sleeps as `Wait.next` decides, until its
deadline on the monotonic clock passes. The shell runs this decision in `Os.Shell.nap`,
the only sleep a bounded wait takes (`scripts/gates.sh`); `packages/os/Os/Proofs/Wait.lean` proves
that a wait gives up exactly once its deadline has passed, after at most one look per
millisecond of its window. -/

namespace Os.Wait

/-- How long a wait with `deadline` on the monotonic clock sleeps before its next look, asked at
`now`: at least 1 ms and at most `step`, never past the deadline; `none` once the deadline has
passed, when the wait has missed what it waited for. -/
def next (deadline step now : Nat) : Option Nat :=
  if deadline ≤ now then none else some (min (max step 1) (deadline - now))

end Os.Wait
