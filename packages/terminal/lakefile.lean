import Lake

open Lake DSL

/-- The VT toolkit: the emulator, renderer, streaming replay, child-facing mediation and safe
title emission, with their proofs. It imports no other linger package and has its own challenge
(`Challenge.lean`) and audit. It shares the packages of the checkout that requires it,
so building it alone fetches nothing. -/
package terminal where
  leanOptions :=
  #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩, ⟨`warningAsError, true⟩,
    ⟨`linter.extra.unreachableTactic, true⟩, ⟨`linter.redundantVisibility, true⟩,
    ⟨`linter.extra.unnecessarySeqFocus, true⟩]
  packagesDir := "../../.lake/packages"

require software_challenge from git
  "https://github.com/vincentqb/lean-software-challenge"@"57aae4dfe83ef6f28f313cdec1007fc3554b474c"

/-- Options for every library but the challenge: with the package's `warningAsError`, a public
declaration without a docstring fails the build. -/
def implementationOptions : Array LeanOption := #[⟨`linter.missingDocs, true⟩]

/-- The toolkit, its specification, its proofs, the solution its challenge is checked against
and its unit tests, checked at elaboration time: every module under `Terminal`. Its roots are the
modules no other imports, from which `lake lint` reaches every module. -/
@[default_target] lean_lib Terminal where
  roots :=
  #[`Terminal.Solution, `Terminal.Tests.Fuzz, `Terminal.Tests.Mediation, `Terminal.Tests.Title,
    `Terminal.Tests.ToolkitApi, `Terminal.Tests.Vt, `Terminal.Tests.VtApi]
  globs := #[.submodules `Terminal]
  leanOptions := implementationOptions

/-- The toolkit's headline theorems and their kills, stated with `sorry` for `lake comparator`,
which checks that `Terminal.Solution` proves the same statements. The build writes
`comparator.json` from them. -/
lean_lib Challenge where leanOptions := #[⟨`warn.sorry, false⟩]

/-- The Lean Software Challenge audit of every module the default targets build. -/
@[default_target] target audit pkg : Unit := do
  return (← pkg.fetchFacetJob `softwareChallenge).map (fun _ => ())
