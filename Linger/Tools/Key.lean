module

public import Linger.Tools.Input

public section

/-! Selector actions and their terminal key bindings. The terminal decoder
reports physical events without deciding which actions they request. -/

namespace Linger.Tools

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

/-- The selector's fixed bindings. Unbound control bytes have no action. -/
def Key.ofInput : Input.Key → Option Key
  | .text char => some (.text char)
  | .control byte =>
    match byte with
    | 21 => some .clear
    | 16 => some .up
    | 14 => some .down
    | 3 | 4 => some .cancel
    | _ => none
  | .backspace => some .backspace
  | .tab | .down => some .down
  | .enter => some .accept
  | .escape => some .cancel
  | .up => some .up
  | .home => some .first
  | .end => some .last

end Linger.Tools
