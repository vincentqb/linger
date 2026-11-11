module

public meta import SoftwareChallenge.Audit

/-- The Lean Software Challenge audit of the fuzzy matcher, a library: its users call the
matcher directly, so it names no entry point. A module takes the role of the longest prefix
listed here. -/
public meta def main : List String → IO Unit :=
  SoftwareChallenge.Audit.run
    { trusted := #[`Init, `Std, `Lean, `SoftwareChallenge]
      entry := none
      layers :=
        #[(`Fuzzy, .core), (`Fuzzy.Spec, .spec), (`Fuzzy.Proofs, .tooling),
          (`Fuzzy.Solution, .tooling), (`Fuzzy.Tests, .tooling)] }
