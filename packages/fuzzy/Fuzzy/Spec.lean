module

public section

/-! # What fuzzy-matching headlines are stated in

A successful match of a query against a target. -/

namespace Fuzzy

/-- A successful match: its score and one mark per target character. -/
structure Alignment where
  /-- The sum of the word, adjacency and gap terms along the alignment. -/
  score : Int
  /-- Set at each matched target character; folded, the marked characters spell the
  folded query. -/
  marks : List Bool
  deriving BEq, Repr

end Fuzzy
