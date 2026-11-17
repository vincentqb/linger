import Lake

open Lake DSL

/-- The OS boundary: the foreign declarations, the C shim they bind, the checked wrappers callers
use and the bounded wait. It imports no other linger package and has its own challenge
(`Challenge.lean`) and audit. It shares the packages of the checkout that requires it, so
building it alone fetches nothing. -/
package os where
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
checked against: every module under `Os`. Each is also compiled to a shared library that links
the shim, which a check of a world claim then calls, as a checkout's checks of its own claims
do through `Os.Shell`. Its roots are the modules no other imports, from which `lake lint`
reaches every module; a root other than `Os`, which is no module, keeps that library from being
loaded as a plugin, whose initializer would be `Os`'s. -/
@[default_target] lean_lib Os where
  roots := #[`Os.Solution, `Os.WorldCode.Checks, `Os.WorldCode.Command]
  globs := #[.submodules `Os]
  leanOptions := implementationOptions
  precompileModules := true

/-- The boundary's headline theorems and their kills, stated with `sorry` for `lake comparator`,
which checks that `Os.Solution` proves the same statements. The build writes
`comparator.json` from them. -/
lean_lib Challenge where leanOptions := #[⟨`warn.sorry, false⟩]

/-- The Lean Software Challenge audit of every module the default targets build. -/
@[default_target] target audit pkg : Unit := do
  return (← pkg.fetchFacetJob `softwareChallenge).map (fun _ => ())
