import Lake

open Lake DSL

/-- The OS boundary: the foreign declarations, the C shim they bind, the checked wrappers callers
use and the bounded wait. It imports no other linger package and has its own challenge
(`Challenge.lean`). It shares the packages of the checkout that requires it, so
building it alone fetches nothing. -/
package os where
  testDriver := "oschecks"
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

/-- The boundary, its specification, its proofs, its checks and the solution its challenge is
checked against: every module under `Os`. Its roots are the modules no other imports, from which
`lake lint` reaches every module. -/
@[default_target] lean_lib Os where
  roots := #[`Os.Solution, `Os.WorldCode.Checks, `Os.WorldCode.Command]
  globs := #[.submodules `Os]
  leanOptions := implementationOptions

/-- The checks of the boundary's world claims, run against this host as the program links the
shim: the package's test driver, so `lake test` runs them. -/
lean_exe oschecks where root := `OsChecks

/-- The boundary's headline theorems and their kills, stated with `sorry` for `lake comparator`,
which checks that `Os.Solution` proves the same statements. The build writes
`comparator.json` from them. -/
lean_lib Challenge where leanOptions := #[⟨`warn.sorry, false⟩]

/-- The Lean Software Challenge's statement step: it checks that every headline of `Challenge.lean`
has its kill, and its witness where a hypothesis is about a hole, and writes `comparator.json`. -/
@[default_target] target statement pkg : Unit := do
  return (← pkg.fetchFacetJob `softwareChallengeStatement).map (fun _ => ())
