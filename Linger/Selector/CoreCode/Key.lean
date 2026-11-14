module

public import Linger.Selector.CoreSpec
public import Input.CoreSpec

public section

/-! Selector actions and their terminal key bindings. The terminal decoder
reports physical events without deciding which actions they request. A key means
what it means in a line editor and in fzf, and nothing of linger's own: Ctrl-L
clears and redraws the screen, which for a view of live sessions also lists them
again, remote hosts included (`refresh`); Ctrl-D deletes the character under the
cursor and on an empty line ends the input (`deleteCharEof`); Ctrl-R, a reverse
history search there, which the chooser has no history for, does nothing. -/

namespace Linger.Selector

/-- The selector's fixed bindings. Unbound control bytes have no action. -/
def Key.ofInput : Input.Key → Option Key
  | .text char => some (.text char)
  | .control byte =>
    match byte with
    | 21 => some .clear
    | 16 => some .up
    | 14 => some .down
    | 12 => some .refresh
    | 3 => some .cancel
    | 4 => some .deleteCharEof
    | _ => none
  | .backspace => some .backspace
  | .tab | .down => some .down
  | .enter => some .accept
  | .escape => some .cancel
  | .up => some .up
  | .home => some .first
  | .end => some .last

end Linger.Selector
