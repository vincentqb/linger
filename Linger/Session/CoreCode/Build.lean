module

public section

/-! # Linger.Session.Build — the build a binary is

A binary's build number is the step of linger's history it was built at, so a later step's binary
has a higher one. `info` reports it as `build`, beside `version`, and an attach by a binary of a
higher build hands the session's daemon over to that binary before it attaches
(`Handover.plan`). `scripts/gates.sh` ties the number to the history: it is the number of the last
`step N:` commit, or of the next one while the tree holds changes to commit. -/

namespace Linger.Session.Build

/-- This binary's build, as `linger-build:` and its number in decimal. The number is read from
these bytes when the program runs, so the upgrade suite makes a binary of another build by
rewriting the digits in a copy of this one. -/
@[noinline]
def stamp : String := "linger-build:236"

/-- This binary's build number, the digits of `stamp`. -/
def number : Nat := ((stamp.drop "linger-build:".length).toString.toNat?).getD 0

end Linger.Session.Build
