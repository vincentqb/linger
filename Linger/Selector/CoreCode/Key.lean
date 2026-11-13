module

public import Linger.Selector.CoreSpec
public import Input.CoreSpec

public section

/-! Selector actions and their terminal key bindings. The terminal decoder
reports physical events without deciding which actions they request. Ctrl-R
refreshes: a control byte types no query character, and it is the reload key of
browsers and of fzf's own `reload` example. -/

namespace Linger.Selector

/-- The selector's fixed bindings. Unbound control bytes have no action. -/
def Key.ofInput : Input.Key → Option Key
  | .text char => some (.text char)
  | .control byte =>
    match byte with
    | 21 => some .clear
    | 16 => some .up
    | 14 => some .down
    | 18 => some .refresh
    | 3 | 4 => some .cancel
    | _ => none
  | .backspace => some .backspace
  | .tab | .down => some .down
  | .enter => some .accept
  | .escape => some .cancel
  | .up => some .up
  | .home => some .first
  | .end => some .last

end Linger.Selector
