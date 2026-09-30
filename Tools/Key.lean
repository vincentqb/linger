module

public import Tools.Input

public section

/-! Selector actions and their terminal key bindings. The terminal decoder
reports physical events without deciding which actions they request. -/

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

end Tools
