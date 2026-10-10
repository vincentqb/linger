import Lake

open Lake DSL

package linger where leanOptions :=
  #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩, ⟨`warningAsError, true⟩,
    ⟨`linter.extra.unreachableTactic, true⟩, ⟨`linter.redundantVisibility, true⟩,
    ⟨`linter.extra.unnecessarySeqFocus, true⟩]

/-- The session library, with no external Lean dependencies. -/
@[default_target] lean_lib Linger where

/-- The VT toolkit: the emulator, renderer, streaming replay, child-facing
mediation and safe title emission. Lake roots select what to build;
`scripts/gates.sh` enforces the import boundary. -/
lean_lib LingerVt where roots := #[`Linger.Core.Terminal, `Linger.Core.Replay]

/-- VT contracts build independently, including replay fidelity and title safety. -/
lean_lib LingerVtTheorems where roots :=
  #[`Theorems.Terminal, `Theorems.TerminalTitle, `Theorems.Replay]

/-- Bounded terminal-key decoding, independent of any application's bindings. -/
lean_lib LingerInput where roots := #[`Linger.Tools.Input]

/-- Decoder contracts build without the picker action adapter or session code. -/
lean_lib LingerInputTheorems where roots := #[`Theorems.Input]

/-- Reusable fuzzy alignment, with no session or terminal imports. -/
lean_lib LingerFuzzy where roots := #[`Linger.Tools.Fuzzy]

/-- The native OS boundary, compiled with the clang selected by `./lake`. -/
target shim.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / "c" / "shim.o"
  let srcJob ← inputTextFile <| pkg.dir / "c" / "shim.c"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile srcJob weakArgs #["-fPIC", "-O2", "-Wall", "-Werror"] "clang" getLeanTrace

extern_lib liblingershim pkg := do
  let shimO ← fetch <| pkg.target ``shim.o
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "lingershim") #[shimO]

/-- IO smoke tests for the Posix surface: `./lake exe lingertest`. -/
lean_exe lingertest where root := `LingerTest

/-- Proofs have their own import and verification graph; every module under `Theorems/` is
built. Lean erases proofs regardless of file placement. -/
lean_lib Theorems where globs := #[.andSubmodules `Theorems]

/-- Unit tests checked at elaboration time; every module under `Tests/` is built. -/
lean_lib Tests where globs := #[.andSubmodules `Tests]

/-- Executable suites: `./lake exe e2e <suite>`. -/
lean_lib E2E where

lean_exe e2e where root := `E2ETest

@[default_target] lean_exe linger where root := `Main

/-- Build and run the complete verifier, including live pty suites. -/
@[test_driver] script test do
  let root ← getRootPackage
  let child ←
    IO.Process.spawn
        { cmd := "sh", args := #[(root.dir / "scripts" / "e2e.sh").toString], cwd := some root.dir }
  child.wait

/-- Run the checks shared with pre-commit and full verification. -/
@[lint_driver] script lint do
  let root ← getRootPackage
  let child ←
    IO.Process.spawn
        { cmd := "sh", args := #[(root.dir / "scripts" / "lint.sh").toString],
          cwd := some root.dir }
  child.wait
