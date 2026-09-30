module

import Tools.Fuzzy

/-! Check the reusable fuzzy API through an ordinary import. Evaluation tests
live in `Tests.Fuzzy`, whose meta import must not hide missing public exports. -/

open Tools.Fuzzy

namespace Tests.FuzzyApi

example : CaseMode := .sensitive

example : CaseMode := .insensitive

example : CaseMode := .smart

example : Scoring := {}

example : Scoring := { word := -5, adjacent := 0, gap := 3 }

example : Config := {}

example : Config := { caseMode := .smart, scoring := { word := -5, adjacent := 0, gap := 3 } }

example : CaseMode → String → Char → Char := CaseMode.fold

example : Config → String → String → Option Alignment := alignWith

example : String → String → Option Alignment := align

example (config : Config) : Int :=
  config.scoring.word + config.scoring.adjacent + config.scoring.gap

example (config : Config) (query : String) : Char → Char := config.caseMode.fold query

example (answer : Alignment) : Int × List Bool := (answer.score, answer.marks)

end Tests.FuzzyApi
