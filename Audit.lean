module

public meta import SoftwareChallenge.Audit

/-- The Lean Software Challenge audit. A module takes the role of the longest prefix listed
here. The `Linger` entry covers the umbrella module, which only gathers the session library
for the build, and any module no longer prefix covers: as tooling, none of its code can run in
the program, so a new component joins the program only once it is listed. The packages under
`packages/` are trusted here: each has its own challenge and audit. -/
public meta def main : List String → IO Unit :=
  SoftwareChallenge.Audit.run
    { trusted := #[`Init, `Std, `Lean, `SoftwareChallenge, `Fuzzy, `Input]
      layers :=
        #[(`Linger, .tooling), (`Main, .shell), (`Theorems, .tooling), (`Verify, .tooling),
          (`Linger.App, .core), (`Linger.Display, .core), (`Linger.Import, .core),
          (`Linger.Os, .core), (`Linger.Selector, .core), (`Linger.Session, .core),
          (`Linger.Target, .core), (`Linger.Terminal, .core), (`Linger.App.Spec, .spec),
          (`Linger.Display.Spec, .spec), (`Linger.Import.Spec, .spec), (`Linger.Os.Spec, .spec),
          (`Linger.Selector.Spec, .spec), (`Linger.Session.Spec, .spec),
          (`Linger.Target.Spec, .spec), (`Linger.Terminal.Spec, .spec),
          (`Linger.Os.Boundary, .boundary), (`Linger.App.Shell, .shell),
          (`Linger.Import.Shell, .shell), (`Linger.Os.Shell, .shell),
          (`Linger.Selector.Shell, .shell), (`Linger.Session.Shell, .shell),
          (`Linger.App.Proofs, .tooling), (`Linger.App.Suites, .tooling),
          (`Linger.Display.Proofs, .tooling), (`Linger.Display.Suites, .tooling),
          (`Linger.Display.Tests, .tooling), (`Linger.Import.Proofs, .tooling),
          (`Linger.Import.Suites, .tooling), (`Linger.Import.Tests, .tooling),
          (`Linger.Os.Proofs, .tooling), (`Linger.Os.Suites, .tooling),
          (`Linger.Selector.Proofs, .tooling), (`Linger.Selector.Tests, .tooling),
          (`Linger.Session.Proofs, .tooling), (`Linger.Session.Suites, .tooling),
          (`Linger.Session.Tests, .tooling), (`Linger.Target.Proofs, .tooling),
          (`Linger.Target.Suites, .tooling), (`Linger.Target.Tests, .tooling),
          (`Linger.Terminal.Proofs, .tooling), (`Linger.Terminal.Suites, .tooling),
          (`Linger.Terminal.Tests, .tooling)] }
