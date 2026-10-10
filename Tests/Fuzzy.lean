module

import Linger.Tools.Fuzzy
meta import Linger.Tools.Fuzzy

open Linger.Tools.Fuzzy

#guard align "" "anything" == some ⟨0, List.replicate 8 false⟩

#guard align "ab" "axab" == some ⟨6, [false, false, true, true]⟩

#guard align "ab" "a-b" == some ⟨7, [true, false, true]⟩

#guard align "ab" "aB" == some ⟨16, [true, true]⟩

#guard align "ab" "ba" == none

#guard align "aa" "a" == none

#guard (align "AA" "aa-a").map (·.marks) == some [true, true, false, false]

#guard (align "é界" "café@世界").map (·.marks) == some [false, false, false, true, false, false, true]

#guard align "É" "é" == none

#guard (align "é" "eé").map (·.marks) == some [false, true, true]

namespace Tests.Fuzzy

/-- Only the small oracle enumerates masks. True-first enumeration breaks ties
by earliest matching positions, independently of the production dynamic program. -/
def masks : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 =>
    let rest := masks n
    rest.map (true :: ·) ++ rest.map (false :: ·)

/-- Compare exact scalars or explicit ASCII letter pairs. Neither production
folding nor character-case predicates participate in this oracle. -/
def spells (mode : CaseMode) (query selected : List Char) : Bool :=
  let capitals := "ABCDEFGHIJKLMNOPQRSTUVWXYZ".toList
  let pairs := capitals.zip "abcdefghijklmnopqrstuvwxyz".toList
  let ignoreCase :=
    match mode with
    | .sensitive => false
    | .insensitive => true
    | .smart => !(query.any capitals.contains)
  query.length == selected.length &&
    (query.zip selected).all fun (q, c) =>
      q == c ||
        (ignoreCase &&
          pairs.any fun (upper, lower) => (q == upper && c == lower) || (q == lower && c == upper))

/-- Score the selected positions as a whole. Boundary and adjacency counts
are independent of the weights; the final selected index determines all gaps.
The target stays in its original case throughout. -/
def score (scoring : Scoring) (target : List Char) (mask : List Bool) : Int :=
  let positions := mask.zipIdx.filterMap fun (marked, index) => if marked then some index else none
  let boundaries :=
    positions.countP fun index =>
      index == 0 || " -_./@:".contains target[index - 1]! ||
        ("abcdefghijklmnopqrstuvwxyz".contains target[index - 1]! &&
          "ABCDEFGHIJKLMNOPQRSTUVWXYZ".contains target[index]!)
  let adjacent := (positions.zip positions.tail).countP fun (a, b) => a + 1 == b
  let skipped := (positions.getLast?.map (· + 1)).getD 0 - positions.length
  scoring.word * boundaries + scoring.adjacent * adjacent + scoring.gap * skipped

def oracleWith (config : Config) (query target : String) : Option Alignment :=
  let candidates :=
    (masks target.toList.length).filterMap fun mask =>
      let selected :=
        (target.toList.zip mask).filterMap fun (c, mark) => if mark then some c else none
      if spells config.caseMode query.toList selected then
        some ⟨score config.scoring target.toList mask, mask⟩
      else none
  candidates.foldl
    (fun best candidate =>
      match best with
      | none => some candidate
      | some old => some (if old.score ≥ candidate.score then old else candidate))
    none

def oracle (query target : String) : Option Alignment := oracleWith {} query target

def words (alphabet : List Char) : Nat → List String
  | 0 => [""]
  | n + 1 => "" :: ((words alphabet n).flatMap fun word => alphabet.map word.push)

-- Exhaustive small cases check completeness, scores, masks and tie-breaking.
#guard
  (words ['a', 'b', 'A', '-'] 4).all fun target =>
    (words ['a', 'b', 'A'] 3).all fun query => align query target == oracle query target

def modes : List CaseMode := [.sensitive, .insensitive, .smart]

def scorings : List Scoring :=
  [{}, { word := 0, adjacent := 0, gap := 0 }, { word := -5, adjacent := -4, gap := -3 },
    { word := -5, adjacent := 0, gap := 0 }, { word := 0, adjacent := -4, gap := 0 },
    { word := 0, adjacent := 0, gap := 3 }, { word := 9, adjacent := -4, gap := 3 }]

def configurations : List Config :=
  modes.flatMap fun mode => scorings.map fun scoring => { caseMode := mode, scoring }

-- Check complete answers, including failures, signed scores, masks and ties.
-- Also exercise the public default wrapper across the unchanged default grid.
#guard
  (words ['a', 'b', 'A', '-'] 4).all fun target =>
    (words ['a', 'b', 'A'] 3).all fun query => alignWith {} query target == align query target

#guard
  configurations.all fun config =>
    (words ['a', 'b', 'A', '-'] 3).all fun target =>
      (words ['a', 'b', 'A'] 2).all fun query =>
        alignWith config query target == oracleWith config query target

-- Longer repeated targets exercise a tie after a shared matching prefix.
#guard
  configurations.all fun config =>
    ["aaaaa", "aAaAa", "a-a-a", "aa-bab", "aB_aB"].all fun target =>
      ["aa", "aaa", "aA", "Aa", "ab", "Ab"].all fun query =>
        alignWith config query target == oracleWith config query target

-- Non-ASCII capitals must neither fold nor trigger smart sensitivity.
-- Combining sequences remain distinct scalars rather than normalized letters.
#guard
  configurations.all fun config =>
    (words ['a', 'A', 'é', 'É', '́', '🙂'] 2 ++ ["界ÉA", "É-a", "🙂éZ", "界é-🙂é"]).all fun target =>
      ["", "a", "A", "é", "É", "Éa", "éA", "é", "🙂é"].all fun query =>
        alignWith config query target == oracleWith config query target

-- Scoring must not affect subsequence acceptance, even when every successful
-- answer is negative. Compare weights for a fixed mode and the same strings.
#guard
  modes.all fun mode =>
    (words ['a', 'b', 'A', '-'] 3).all fun target =>
      (words ['a', 'b', 'A'] 2).all fun query =>
        scorings.all fun scoring =>
          (alignWith { caseMode := mode, scoring } query target).isSome ==
            (alignWith { caseMode := mode } query target).isSome

#guard ({} : Scoring).word == 4

#guard ({} : Scoring).adjacent == 8

#guard ({} : Scoring).gap == -1

#guard ({} : Config).scoring.word == 4

#guard ({} : Config).scoring.adjacent == 8

#guard ({} : Config).scoring.gap == -1

#guard ({} : Config).caseMode.fold "A" 'A' == 'a'

-- Partial records retain the defaults of omitted fields.
#guard alignWith { scoring := { word := 5 } } "ab" "ab" == some ⟨13, [true, true]⟩

#guard alignWith { scoring := { adjacent := 2 } } "ab" "ab" == some ⟨6, [true, true]⟩

#guard alignWith { scoring := { gap := 3 } } "ab" "a-b" == some ⟨11, [true, false, true]⟩

#guard
  ("ABCDEFGHIJKLMNOPQRSTUVWXYZ".toList.zip "abcdefghijklmnopqrstuvwxyz".toList).all
    fun (upper, lower) =>
    CaseMode.sensitive.fold "a" upper == upper && CaseMode.insensitive.fold "Z" upper == lower &&
      CaseMode.insensitive.fold "Z" lower == lower &&
      CaseMode.smart.fold "Éa" upper == lower &&
      CaseMode.smart.fold "aZ" upper == upper

#guard
  modes.all fun mode =>
    ["", "abc", "aZ", "Éa"].all fun query =>
      ['é', 'É', 'İ', 'ß', 'Σ', 'σ', '界', '🙂', '́', '-', '0'].all fun c => mode.fold query c == c

#guard alignWith { caseMode := .sensitive } "A" "a" == none

#guard alignWith { caseMode := .sensitive } "a" "A" == none

#guard alignWith { caseMode := .sensitive } "aA" "aA" == some ⟨16, [true, true]⟩

#guard alignWith { caseMode := .insensitive } "A" "a" == some ⟨4, [true]⟩

#guard alignWith { caseMode := .insensitive } "a" "A" == some ⟨4, [true]⟩

#guard alignWith { caseMode := .smart } "A" "a" == none

#guard alignWith { caseMode := .smart } "aB" "ab" == none

#guard alignWith { caseMode := .smart } "ab" "aB" == some ⟨16, [true, true]⟩

#guard alignWith { caseMode := .smart } "Éa" "ÉA" == some ⟨12, [true, true]⟩

#guard alignWith { caseMode := .smart } "éA" "éa" == none

#guard
  modes.all fun mode =>
    alignWith { caseMode := mode } "É" "é" == none &&
      alignWith { caseMode := mode } "é" "é" == none

-- Every advertised separator is a word boundary, even when skipped. Camel
-- boundaries are detected from original characters, in all case modes.
#guard
  modes.all fun mode =>
    [' ', '-', '_', '.', '/', '@', ':'].all fun separator =>
      alignWith { caseMode := mode, scoring := { word := 9, adjacent := -4, gap := -2 } } "B"
          (String.ofList ['x', separator, 'B']) ==
        some ⟨5, [false, false, true]⟩

#guard
  modes.all fun mode =>
    alignWith { caseMode := mode, scoring := { word := 9, adjacent := -4, gap := -2 } } "B" "B" ==
        some ⟨9, [true]⟩ &&
      alignWith { caseMode := mode, scoring := { word := 9, adjacent := -4, gap := -2 } } "B"
          "aB" ==
        some ⟨7, [false, true]⟩

#guard
  ['+', ',', '\\', '\t', '0', 'X', 'é'].all fun previous =>
    alignWith { scoring := { word := 9, adjacent := -4, gap := -2 } } "B"
        (String.ofList [previous, 'B']) ==
      some ⟨-2, [false, true]⟩

#guard
  alignWith { scoring := { word := 9, adjacent := 0, gap := 0 } } "b" "aB" ==
    some ⟨9, [false, true]⟩

#guard
  alignWith { scoring := { word := 9, adjacent := 0, gap := -2 } } "É" "aÉ" ==
    some ⟨-2, [false, true]⟩

-- Explicit signed-score examples make oracle mistakes visible independently.
#guard alignWith { scoring := { word := -5, adjacent := 0, gap := 0 } } "a" "a" == some ⟨-5, [true]⟩

#guard
  alignWith { scoring := { word := -5, adjacent := -4, gap := -3 } } "ab" "ab" ==
    some ⟨-9, [true, true]⟩

#guard
  alignWith { scoring := { word := -5, adjacent := 0, gap := 0 } } "a" "aa" ==
    some ⟨0, [false, true]⟩

#guard
  alignWith { scoring := { word := 0, adjacent := -4, gap := 0 } } "aa" "aaa" ==
    some ⟨0, [true, false, true]⟩

#guard
  alignWith { scoring := { word := 0, adjacent := 0, gap := 3 } } "a" "aa" ==
    some ⟨3, [false, true]⟩

#guard
  alignWith { scoring := { word := 0, adjacent := 0, gap := -3 } } "ab" "xaxbzz" ==
    some ⟨-6, [false, true, false, true, false, false]⟩

#guard
  alignWith { scoring := { word := 0, adjacent := 0, gap := 3 } } "a" "a🙂界" ==
    some ⟨0, [true, false, false]⟩

#guard
  alignWith { scoring := { word := 0, adjacent := 0, gap := 0 } } "ab" "axab" ==
    some ⟨0, [true, false, false, true]⟩

#guard
  alignWith { scoring := { word := 0, adjacent := 0, gap := 0 } } "aa" "aaaa" ==
    some ⟨0, [true, true, false, false]⟩

#guard
  alignWith
      {
        scoring :=
          { word := 1000000000000000000000000, adjacent := -2000000000000000000000000,
            gap := 3000000000000000000000000 } }
      "ab" "a-b" ==
    some ⟨5000000000000000000000000, [true, false, true]⟩

#guard
  alignWith { scoring := { word := 7, adjacent := -4, gap := 3 } } "é" "🙂éZ" ==
    some ⟨-1, [false, true, true, false]⟩

#guard
  alignWith { scoring := { word := 9, adjacent := -4, gap := 3 } } "é🙂" "界é-🙂é" ==
    some ⟨15, [false, true, false, true, false, false]⟩

-- Empty queries never collect trailing gap rewards, and empty targets cannot
-- satisfy a nonempty query under any configuration.
#guard
  configurations.all fun config =>
    alignWith config "" "" == some ⟨0, []⟩ &&
      alignWith config "" "界🙂é" == some ⟨0, [false, false, false, false]⟩ &&
      alignWith config "a" "" == none &&
      alignWith config "aa" "a" == none

-- Repetitions create exponentially many legal alignments; the production path
-- must still complete at the selector's maximum query length.
#guard
  (align (String.ofList (List.replicate 256 'a')) (String.ofList (List.replicate 512 'a'))).map
      (·.marks) ==
    some (List.replicate 256 true ++ List.replicate 256 false)

end Tests.Fuzzy
