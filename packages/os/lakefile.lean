import Lake

open Lake DSL

/-- The OS boundary: the foreign declarations, the C shim they bind, the checked wrappers callers
use and the bounded wait. It imports no other linger package and has its own challenge
(`OsChallenge.lean`) and audit. It shares the packages of the checkout that requires it, so
building it alone fetches nothing. -/
package os where
  leanOptions :=
  #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩, ⟨`warningAsError, true⟩,
    ⟨`linter.extra.unreachableTactic, true⟩, ⟨`linter.redundantVisibility, true⟩,
    ⟨`linter.extra.unnecessarySeqFocus, true⟩]
  packagesDir := "../../.lake/packages"

require software_challenge from git
  "https://github.com/vincentqb/lean-software-challenge"@"a6725aa1ed50884d52788171a5ebdf0b53bda9c9"

/-- Options for every library but the challenge: with the package's `warningAsError`, a public
declaration without a docstring fails the build. -/
def implementationOptions : Array LeanOption := #[⟨`linter.missingDocs, true⟩]

/-- The native OS boundary, compiled with the clang selected by `./lake`. -/
target shim.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / "c" / "shim.o"
  let srcJob ← inputTextFile <| pkg.dir / "c" / "shim.c"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile srcJob weakArgs #["-fPIC", "-O2", "-Wall", "-Werror"] "clang" getLeanTrace

/-- The shim's static library, which Lake links into every executable that requires this
package. -/
extern_lib liblingershim pkg := do
  let shimO ← fetch <| pkg.target ``shim.o
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "lingershim") #[shimO]

/-- The boundary, its specification, its proofs, the solution its challenge is checked against
and the wait checks a program's shim suite runs: every module under `Os`. -/
@[default_target] lean_lib Os where
  globs := #[.submodules `Os]
  leanOptions := implementationOptions

/-- The boundary's headline theorems and their kills, stated with `sorry` for `lake comparator`,
which checks that `Os.Solution` proves the same statements. -/
lean_lib OsChallenge where leanOptions := #[⟨`warn.sorry, false⟩, ⟨`linter.missingDocs, true⟩]

/-- The Lean Software Challenge audit of every module the default targets build. -/
@[default_target] target audit pkg : Unit := do
  return (← pkg.fetchFacetJob `softwareChallenge).map (fun _ => ())
