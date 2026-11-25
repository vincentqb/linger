import Lake

open Lake DSL

/-- Bounded terminal key decoding, independent of any application's bindings: bytes in, physical
key events out, and while a paste is in progress only text. It imports no other linger package
and has its own challenge (`Challenge.lean`). It shares the packages of the
checkout that requires it, so building it alone fetches nothing. -/
package input where
  leanOptions :=
  #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩, ⟨`warningAsError, true⟩,
    ⟨`linter.extra.unreachableTactic, true⟩, ⟨`linter.redundantVisibility, true⟩,
    ⟨`linter.extra.unnecessarySeqFocus, true⟩]
  packagesDir := "../../.lake/packages"

require software_challenge from git
  "https://github.com/vincentqb/lean-software-challenge"@"3d5035043af16034bac2a92a7ccbcb2cee68ffa9"

/-- Options for every library but the challenge: with the package's `warningAsError`, a public
declaration without a docstring fails the build. -/
def implementationOptions : Array LeanOption := #[⟨`linter.missingDocs, true⟩]

/-- The decoder, its specification, its proofs, the solution its challenge is checked against and
its unit tests, checked at elaboration time: every module under `Input`. Its roots are the
modules no other imports, from which `lake lint` reaches every module. -/
@[default_target] lean_lib Input where
  roots := #[`Input.Solution, `Input.Tests, `Input.Tests.Api]
  globs := #[.submodules `Input]
  leanOptions := implementationOptions

/-- The decoder's headline theorems and their kills, stated with `sorry` for `lake comparator`,
which checks that `Input.Solution` proves the same statements. The build writes
`comparator.json` from them. -/
lean_lib Challenge where leanOptions := #[⟨`warn.sorry, false⟩]

/-- The Lean Software Challenge's statement step: it checks that every headline of `Challenge.lean`
has its kill, and its witness where a hypothesis is about a hole, and writes `comparator.json`. -/
@[default_target] target statement pkg : Unit := do
  return (← pkg.fetchFacetJob `softwareChallengeStatement).map (fun _ => ())
