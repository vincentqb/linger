module

public section

/-! Scored subsequence alignment over Unicode scalar positions.

Matching folds ASCII capitals, as `Char.toLower` does. A word start earns four
points, adjacency earns eight, and each skipped character before the final
match costs one. Trailing characters cost nothing. Equal scores choose the
earlier match. Scores choose emphasis, not candidate order.

The dynamic program builds each query row from the remaining query suffix's
row. Each cell stores answers for a preceding match and a preceding gap;
their masks share suffixes. Work is proportional to query length times target
length, with a linear base row.
-/

namespace Tools.Fuzzy

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
private def letters (previous : Char) : List Char → List (Char × Int)
  | [] => []
  | c :: cs =>
    let bonus :=
      if
          [' ', '-', '_', '.', '/', '@', ':'].contains previous ||
            (previous.isLower && c.isUpper) then
        4
      else 0
    (c.toLower, bonus) :: letters c cs

/-- One query row. The previous row's next cell handles a match; this row's
next cell handles a gap, so each target position is visited just once. -/
private def row (q : Char) : List (Char × Int) → List Cell → List Cell
  | [], _ => [default]
  | (c, bonus) :: target, next =>
    let suffix := next.tail
    let tail := row q target suffix
    let skipped := prepend false (-1) (tail.headD default).gap
    let taken := if q == c then (suffix.headD default).adjacent else none
    { gap := best (prepend true bonus taken) skipped,
      adjacent := best (prepend true (bonus + 8) taken) skipped } ::
      tail

private def table : List Char → List (Char × Int) → List Cell
  | [], target => emptyRow target.length
  | q :: qs, target => row q target (table qs target)

/-- The best alignment, with one mark per original target character, or no
answer exactly when the query is not a subsequence. -/
def align (query target : String) : Option Alignment :=
  ((table (query.toList.map Char.toLower) (letters ' ' target.toList)).headD default).gap

end Tools.Fuzzy
