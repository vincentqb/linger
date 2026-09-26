module

public section

/-! Input events shared by the optional manager's decoder and selection model.
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
  | refresh
  deriving BEq, Repr

end Tools
