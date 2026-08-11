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

/-- Proofs. Separate from `Zmx` so the executable does not carry them;
`THEOREMS.md` names the tension each section resolves. Root module
imports every Theorems.X — a proof file not imported there is a bug. -/
lean_lib Theorems where

/-- Unit tests: `example`s checked at elaboration time, so building this
target is running them. Same import-from-root convention. -/
lean_lib Tests where
