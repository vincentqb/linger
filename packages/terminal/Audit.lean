module

public meta import SoftwareChallenge.Audit

/-- The Lean Software Challenge audit of the VT toolkit, a library: its users call the toolkit
directly, so it names no entry point. A module takes the role of the longest prefix listed
here. -/
public meta def main : List String → IO Unit :=
  SoftwareChallenge.Audit.run
    { trusted := #[`Init, `Std, `Lean, `SoftwareChallenge]
      entry := none
      layers :=
        #[(`Terminal, .core), (`Terminal.Spec, .spec), (`Terminal.Proofs, .tooling),
          (`Terminal.Solution, .tooling), (`Terminal.Tests, .tooling)] }
