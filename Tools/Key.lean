module

public section

/-! Input events shared by the selector's decoder and selection model.
The decoder cannot request a session creation or execute a command. -/

namespace Tools

inductive Key where
  | text (char : Char)
  | backspace
  | clear
  | up
  | down
  | first
  | last
  | accept
  | cancel
  deriving BEq, Repr

end Tools
