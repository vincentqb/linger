module

public meta import SoftwareChallenge.Audit

/-- The Lean Software Challenge audit of the input decoder, a library: its users call the
decoder directly, so it names no entry point. A module takes the role of the longest prefix
listed here. -/
public meta def main : List String → IO Unit :=
  SoftwareChallenge.Audit.run
    { trusted := #[`Init, `Std, `Lean, `SoftwareChallenge]
      entry := none
      layers :=
        #[(`Input, .core), (`Input.Spec, .spec), (`Input.Proofs, .tooling),
          (`Input.Solution, .tooling), (`Input.Tests, .tooling)] }
