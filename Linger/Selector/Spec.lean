module

public section

/-! # What selector headlines are stated in

The actions the selector takes, the state of one selection visit, and what one action leads to. -/

namespace Linger.Selector

/-- One selector action, independent of the key that requests it. -/
inductive Key where
  /-- Append a character to the query. -/
  | text (char : Char)
  /-- Delete the query's last character. -/
  | backspace
  /-- Empty the query. -/
  | clear
  /-- Move the cursor up one row. -/
  | up
  /-- Move the cursor down one row. -/
  | down
  /-- Move the cursor to the first row. -/
  | first
  /-- Move the cursor to the last row. -/
  | last
  /-- Act on the selected row. -/
  | accept
  /-- Leave without a choice. -/
  | cancel
  deriving BEq, Repr

end Linger.Selector

namespace Linger.Selector.Picker

/-- One selection visit over the displayed snapshot's targets. -/
structure State where
  /-- Targets of the displayed snapshot. -/
  candidates : List String
  /-- The typed text that filters rows and, when nonempty, names the creation target. -/
  query : String := ""
  /-- Index of the selected row in `items`; zero when there are none. -/
  cursor : Nat := 0
  /-- Whether `items` may offer a creation row; false for read-only visits and saved
  catalogs. -/
  allowCreate : Bool := true
  deriving BEq, Repr

/-- The result of one action: a next state, or a decision for the executor. -/
inductive Outcome where
  /-- Keep selecting from this state. -/
  | stay (state : State)
  /-- Attach to this listed target. -/
  | attach (target : String)
  /-- Create a session with exactly this target. -/
  | create (target : String)
  /-- Leave without a choice. -/
  | cancel
  deriving BEq, Repr

end Linger.Selector.Picker
