import Lake

open Lake DSL

package linger where leanOptions :=
  #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩, ⟨`warningAsError, true⟩,
    ⟨`linter.extra.unreachableTactic, true⟩, ⟨`linter.redundantVisibility, true⟩,
    ⟨`linter.extra.unnecessarySeqFocus, true⟩]

/-- Linger's own build, required first so that it comes first on the search path: a workspace
looks for a module in its packages' builds, the first required last, and in its own build last of
all. Every package under `packages/` names its challenge `Challenge`, as linger does, so once a
package has been built on its own, its challenge would otherwise stand in for linger's. This
package declares nothing, and its build directory is linger's. -/
require first from "first"

require software_challenge from git
  "https://github.com/vincentqb/lean-software-challenge"@"57aae4dfe83ef6f28f313cdec1007fc3554b474c"

/-- The fuzzy matcher, a package of its own with its own challenge and audit. -/
require fuzzy from "packages/fuzzy"

/-- The terminal key decoder, a package of its own with its own challenge and audit. -/
require input from "packages/input"

/-- The VT toolkit: the emulator, renderer, streaming replay, child-facing mediation and safe
title emission, a package of its own with its own challenge and audit. -/
require terminal from "packages/terminal"

/-- The OS boundary: the foreign declarations, the C shim they bind, the checked wrappers
callers use and the bounded wait, a package of its own with its own challenge and audit. -/
require os from "packages/os"

/-- Options for every library but `Verify`: Lake builds a module with the options of one library
that contains it, and these libraries overlap, so they share a single set. With the package's
`warningAsError`, a public declaration without a docstring fails the build. -/
def implementationOptions : Array LeanOption := #[⟨`linter.missingDocs, true⟩]

/-- The session library, with no external Lean dependencies. -/
@[default_target] lean_lib Linger where leanOptions := implementationOptions

/-- IO smoke tests for the OS boundary: `./lake exe lingertest`. -/
lean_exe lingertest where root := `Linger.Os.Suites.Shim

/-- Proofs have their own import and verification graph: every module under `Theorems/` and
under a component's `Proofs/` is built. Lean erases proofs regardless of file placement. -/
@[default_target] lean_lib Theorems where
  roots := #[`Theorems.Coverage, `Theorems.Solution]
  globs :=
  #[.submodules `Theorems, .submodules `Linger.App.Proofs, .submodules `Linger.Display.Proofs,
    .submodules `Linger.Import.Proofs, .submodules `Linger.Os.Proofs,
    .submodules `Linger.Selector.Proofs, .submodules `Linger.Session.Proofs,
    .submodules `Linger.Target.Proofs]
  leanOptions := implementationOptions

/-- Unit tests checked at elaboration time: every module under a component's `Tests/` is
built. -/
lean_lib Tests where
  globs :=
  #[.submodules `Linger.Display.Tests, .submodules `Linger.Import.Tests,
    .submodules `Linger.Selector.Tests, .submodules `Linger.Session.Tests,
    .submodules `Linger.Target.Tests]
  leanOptions := implementationOptions

/-- The checks of linger's world claims, which no program module imports: built by default, so
the audit counts them, and run by the challenge library's checks runner. -/
@[default_target] lean_lib Checks where
  roots := #[`Linger.Session.WorldCode.Checks, `Linger.Target.WorldCode.Checks]
  leanOptions := implementationOptions

/-- Executable suites: `./lake exe suites <suite>`. -/
lean_lib Verify where

lean_exe suites where root := `Verify.Main

/-- The headline theorems and their kills, stated with `sorry`. The build writes
`comparator.json` from them, and `./lake comparator` builds this library and checks that
`Theorems.Solution` proves the same statements. -/
lean_lib Challenge where leanOptions := #[⟨`warn.sorry, false⟩]

@[default_target] lean_exe linger where root := `Linger.App.WorldCode.Main

/-- The Lean Software Challenge audit of every module the default targets build. -/
@[default_target] target audit pkg : Unit := do
  return (← pkg.fetchFacetJob `softwareChallenge).map (fun _ => ())

/-- Build and run the complete verifier, including live pty suites. -/
@[test_driver] script test do
  let root ← getRootPackage
  let child ←
    IO.Process.spawn
        { cmd := "sh", args := #[(root.dir / "scripts" / "verify.sh").toString],
          cwd := some root.dir }
  child.wait

/-- Run the checks shared with pre-commit and full verification. -/
@[lint_driver] script lint do
  let root ← getRootPackage
  let child ←
    IO.Process.spawn
        { cmd := "sh", args := #[(root.dir / "scripts" / "lint.sh").toString],
          cwd := some root.dir }
  child.wait
