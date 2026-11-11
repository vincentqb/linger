module

public meta import SoftwareChallenge.Audit

/-- The Lean Software Challenge audit of the OS boundary, a library: its users call the wrappers
directly, so it names no entry point. A module takes the role of the longest prefix listed
here. -/
public meta def main : List String → IO Unit :=
  SoftwareChallenge.Audit.run
    { trusted := #[`Init, `Std, `Lean, `SoftwareChallenge]
      entry := none
      layers :=
        #[(`Os, .core), (`Os.Spec, .spec), (`Os.Boundary, .boundary), (`Os.Shell, .shell),
          (`Os.Proofs, .tooling), (`Os.Solution, .tooling), (`Os.Suites, .tooling)] }
