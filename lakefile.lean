import Lake
open Lake DSL

package zmx where
  leanOptions := #[
    -- Pure-function port: `partial def` hides a termination argument we
    -- would rather be forced to write down; autoImplicit hides typos.
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

/-- The program. Zero external Lean dependencies (core only): the whole
point is that the state machines are ours to prove things about. -/
@[default_target]
lean_lib Zmx where

/-- The C shim — the project's entire non-Lean surface (see AGENTS.md).
Compiled with clang (the ./lake wrapper puts Homebrew clang on PATH;
the toolchain's bundled one cannot run on this host's glibc 2.26). -/
target shim.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / "c" / "shim.o"
  let srcJob ← inputTextFile <| pkg.dir / "c" / "shim.c"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile srcJob weakArgs #["-fPIC", "-O2", "-Wall", "-Werror"] "clang" getLeanTrace

extern_lib libzmxshim pkg := do
  let shimO ← fetch <| pkg.target ``shim.o
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "zmxshim") #[shimO]

/-- IO smoke tests for the Posix surface (spawns ptys; run, not just built):
`./lake exe ztest`. The shim uses only libc (`posix_openpt`, not the
libutil `forkpty`), so no extra link args on any glibc. -/
lean_exe ztest where
  root := `ZTest

/-- Proofs. Separate from `Zmx` so the executable does not carry them;
`THEOREMS.md` names the tension each section resolves. Root module
imports every Theorems.X — a proof file not imported there is a bug. -/
lean_lib Theorems where

/-- Unit tests: `example`s checked at elaboration time, so building this
target is running them. Same import-from-root convention. -/
lean_lib Tests where

@[default_target]
lean_exe linger where
  root := `Main
