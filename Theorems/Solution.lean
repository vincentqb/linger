module

public import Theorems.Transparency -- shake: keep
public import Theorems.Authority -- shake: keep
public import Theorems.Exactness -- shake: keep
public import Theorems.Identity -- shake: keep
public import Theorems.Accountability -- shake: keep
public import Theorems.Bounded -- shake: keep
public import Theorems.Recovery -- shake: keep
public import Theorems.CleanTerminal -- shake: keep
public import Theorems.Events -- shake: keep
public import Theorems.Faults -- shake: keep
public import Theorems.Status -- shake: keep
public import Theorems.Witnesses -- shake: keep

/-! # Proofs of the headline theorems and their kills

`Challenge.lean` states these theorems in ten parts and the status rule, with the witnesses of
the headlines whose hypotheses are about a hole, and each part's module proves its own, as
`Theorems.Witnesses` proves the witnesses; `./lake comparator` checks that this module, with the
parts it imports, proves exactly those statements. -/
