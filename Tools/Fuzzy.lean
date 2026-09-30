module

public section

/-! Scored subsequence alignment over Unicode scalar positions.

Case policy and scoring are independent. Defaults fold ASCII capitals, reward
word starts by four and adjacency by eight, and charge one point per skipped
character before the final match. Trailing characters cost nothing. Equal
scores choose the earlier match.

The dynamic program builds each query row from the remaining query suffix's
row. Each cell stores answers for a preceding match and a preceding gap;
their masks share suffixes. Work is proportional to query length times target
length, with a linear base row.
-/

namespace Tools.Fuzzy

inductive CaseMode where
  | sensitive
  | insensitive
  | smart
  deriving BEq, Repr

/-- Resolve smart case once per query. Folding affects ASCII capitals only;
non-ASCII characters remain exact in every mode. -/
def CaseMode.fold (mode : CaseMode) (query : String) : Char → Char :=
  match mode with
  | .sensitive => id
  | .insensitive => Char.toLower
  | .smart => if query.toList.any Char.isUpper then id else Char.toLower

/-- Additive scores may be any integers. Positive gaps reward skipped positions;
they still cannot change whether a subsequence exists. -/
structure Scoring where
  word : Int := 4
  adjacent : Int := 8
  gap : Int := -1
  deriving BEq, Repr

structure Config where
  caseMode : CaseMode := .insensitive
  scoring : Scoring := {}
  deriving BEq, Repr

structure Alignment where
  score : Int
  marks : List Bool
  deriving BEq, Repr

private structure Cell where
  gap : Option Alignment := none
  adjacent : Option Alignment := none
  deriving Inhabited

/-- A left tie keeps the earlier matching position. -/
private def best : Option Alignment → Option Alignment → Option Alignment
  | none, b => b
  | a, none => a
  | some a, some b => some (if a.score ≥ b.score then a else b)

private def prepend (mark : Bool) (score : Int) (answer : Option Alignment) : Option Alignment :=
  answer.map fun a => ⟨a.score + score, mark :: a.marks⟩

/-- Empty queries have an unmarked, zero-score answer at every target suffix. -/
private def emptyRow : Nat → List Cell
  | 0 => [{ gap := some ⟨0, []⟩, adjacent := some ⟨0, []⟩ }]
  | n + 1 =>
    let tail := emptyRow n
    let answer := prepend false 0 (tail.headD default).gap
    { gap := answer, adjacent := answer } :: tail

/-- Word boundaries use the original characters; matching uses their folded form. -/
private def letters (word : Int) (fold : Char → Char) (previous : Char) :
    List Char → List (Char × Int)
  | [] => []
  | c :: cs =>
    let bonus :=
      if
          [' ', '-', '_', '.', '/', '@', ':'].contains previous ||
            (previous.isLower && c.isUpper) then
        word
      else 0
    (fold c, bonus) :: letters word fold c cs

/-- One query row. The previous row's next cell handles a match; this row's
next cell handles a gap, so each target position is visited just once. -/
private def row (scoring : Scoring) (q : Char) : List (Char × Int) → List Cell → List Cell
  | [], _ => [default]
  | (c, bonus) :: target, next =>
    let suffix := next.tail
    let tail := row scoring q target suffix
    let skipped := prepend false scoring.gap (tail.headD default).gap
    let taken := if q == c then (suffix.headD default).adjacent else none
    { gap := best (prepend true bonus taken) skipped,
      adjacent := best (prepend true (bonus + scoring.adjacent) taken) skipped } ::
      tail

private def table (scoring : Scoring) : List Char → List (Char × Int) → List Cell
  | [], target => emptyRow target.length
  | q :: qs, target => row scoring q target (table scoring qs target)

/-- The best alignment under the chosen policy, with one mark per original
target character, or no answer exactly when the query is not a subsequence. -/
def alignWith (config : Config) (query target : String) : Option Alignment :=
  let fold := config.caseMode.fold query
  ((table config.scoring (query.toList.map fold)
          (letters config.scoring.word fold ' ' target.toList)).headD
      default).gap

/-- Default ASCII-insensitive alignment, as used by the linger selector. -/
def align (query target : String) : Option Alignment := alignWith {} query target

end Tools.Fuzzy
