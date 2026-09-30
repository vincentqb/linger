module

import Tools.Fuzzy
public meta import Tools.Fuzzy

open Tools.Fuzzy

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
private def masks : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 =>
    let rest := masks n
    rest.map (true :: ·) ++ rest.map (false :: ·)

/-- Score from the selected positions as a whole: word bonuses plus adjacent
pairs, minus every skipped position up to the final match. -/
private def score (target : List Char) (mask : List Bool) : Int :=
  let positions := mask.zipIdx.filterMap fun (marked, index) => if marked then some index else none
  let boundaries :=
    positions.foldl
      (fun total index =>
        total +
          if
              index == 0 || [' ', '-', '_', '.', '/', '@', ':'].contains target[index - 1]! ||
                (target[index - 1]!.isLower && target[index]!.isUpper) then
            4
          else 0)
      0
  let adjacent := (positions.zip positions.tail).countP fun (a, b) => a + 1 == b
  let skipped := (positions.getLast?.map (· + 1)).getD 0 - positions.length
  (boundaries : Int) + 8 * adjacent - skipped

private def oracle (query target : String) : Option Alignment :=
  let candidates :=
    (masks target.length).filterMap fun mask =>
      let matched :=
        (target.toList.zip mask).filterMap fun (c, mark) => if mark then some c.toLower else none
      if matched == query.toList.map Char.toLower then some ⟨score target.toList mask, mask⟩
      else none
  candidates.foldl
    (fun best candidate =>
      match best with
      | none => some candidate
      | some old => some (if old.score ≥ candidate.score then old else candidate))
    none

private def words (alphabet : List Char) : Nat → List String
  | 0 => [""]
  | n + 1 => "" :: ((words alphabet n).flatMap fun word => alphabet.map word.push)

-- Exhaustive small cases check completeness, scores, masks and tie-breaking.
#guard
  (words ['a', 'b', 'A', '-'] 4).all fun target =>
    (words ['a', 'b', 'A'] 3).all fun query => align query target == oracle query target

-- Repetitions create exponentially many legal alignments; the production path
-- must still complete at the selector's maximum query length.
#guard
  (align (String.ofList (List.replicate 256 'a')) (String.ofList (List.replicate 512 'a'))).map
      (·.marks) ==
    some (List.replicate 256 true ++ List.replicate 256 false)

end Tests.Fuzzy
