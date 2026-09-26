import Lake

open Lake DSL

package linger where leanOptions :=
  #[
    -- Pure-function port: `partial def` hides a termination argument we
    -- would rather be forced to write down; autoImplicit hides typos.
    ⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩,
    -- A `sorry` is a WARNING, and this repo's ban on it rested on two greps: a
    -- source scan that cannot see a `sorry` a tactic introduced and that fires on
    -- the word in prose, plus a post-hoc scan of a whole build log. This makes it
    -- an error AT THE DECLARATION that caused it — the compiler holding what a
    -- convention held, which is the same move as sealing `Buf`'s fields. It also
    -- makes a deprecation fatal, which is the point: `String.mk` and
    -- `String.splitOn` drifted into the tree unnoticed because a warning scrolled
    -- past. Both greps STAY (specs/archive/lean-modules Decision 3): the source
    -- grep still covers prose, the log scan still covers non-declaration warnings.
    ⟨`warningAsError, true⟩]

/-- The program. Zero external Lean dependencies (core only): the whole
point is that the state machines are ours to prove things about. -/
@[default_target] lean_lib Linger where

/-- The VT toolkit as a library in its own right: the emulator, its emitter, and
the child-facing mediation — `Linger.Core.Vt`, `.Render`, `.Terminal` — with an
import closure that contains nothing else (no `Posix`, no `Runtime`, no
`Checkpoint`, no `Session`). `specs/archive/vt-toolkit.md` Step 4.

Deliberately NOT a `@[default_target]`: `./lake build` is what every other
command in this repo pays for, and its job count is a number people read. Build
this one by name — `./lake build LingerVt`.

This is the POSITIVE half of the closure claim, and it is only half. Lake
resolves imports through one package-wide `LEAN_PATH`, so a `lean_lib` with
restricted `roots` compiles an out-of-set module happily — an `import
Linger.Posix` added to `Terminal.lean` builds here without a murmur (measured,
`specs/archive/vt-toolkit.md`; re-measured at Step 4). A build-level closure failure
needs a sub-package with its own `srcDir` and a path `require`, which
`tests/gates.sh` forbids to keep README's "no external Lean dependencies"
honest. The half that BITES is therefore the import grep in `tests/gates.sh`,
and this target is what that grep is a gate on. -/
lean_lib LingerVt where roots := #[`Linger.Core.Vt, `Linger.Core.Render, `Linger.Core.Terminal]

/-- Optional pure import policy, outside the session and VT libraries. -/
lean_lib Tools where roots := #[`Tools.Resurrect]

/-- Standalone save importer. Build explicitly with `./lake build lzr`. -/
lean_exe lzr where root := `Lzr

/-- The C shim — the program's native OS boundary (see AGENTS.md).
Compiled with clang (the ./lake wrapper puts Homebrew clang on PATH;
the toolchain's bundled one cannot run on this host's glibc 2.26). -/
target shim.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / "c" / "shim.o"
  let srcJob ← inputTextFile <| pkg.dir / "c" / "shim.c"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile srcJob weakArgs #["-fPIC", "-O2", "-Wall", "-Werror"] "clang" getLeanTrace

extern_lib liblingershim pkg := do
  let shimO ← fetch <| pkg.target ``shim.o
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "lingershim") #[shimO]

/-- IO smoke tests for the Posix surface (spawns ptys; run, not just built):
`./lake exe lingertest`. The shim uses only libc (`posix_openpt`, not the
libutil `forkpty`), so no extra link args on any glibc. -/
lean_exe lingertest where root := `LingerTest

/-- Proofs. Separate from `Linger` so the executable does not carry them;
`THEOREMS.md` names the tension each section resolves. Root module
imports every Theorems.X — a proof file not imported there is a bug. -/
lean_lib Theorems where

/-- Unit tests: `example`s checked at elaboration time, so building this
target is running them. Same import-from-root convention. -/
lean_lib Tests where

/-- The pty suites, as Lean rather than Python: `./lake exe e2e <suite>`.

These drive the real binary through real ptys, so they are `IO` and can never be
theorems — `Theorems`/`Tests` above are what covers the pure core. They are Lean
because a test in the implementation's own language cannot drift from it (a suite
reads `Status.ofName`, not the string `"wants-you"`), and because it cost no new
syscall: `Linger.Posix` already had `spawnPty`, `winsizeSet`, `kill`,
`waitpidNohang` and `getcwdOf`, so the C trust boundary — the thing `SHIM_CAP`
ratchets — is unchanged by the port. -/
lean_lib E2E where

lean_exe e2e where root := `E2ETest

@[default_target] lean_exe linger where root := `Main
