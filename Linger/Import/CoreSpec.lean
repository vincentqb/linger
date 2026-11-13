module

public section

/-! # What import headlines are stated in

One pane of a tmux-resurrect save, as an import reads it. -/

namespace Linger.Import.Resurrect

/-- Information about the original tmux pane, retained independently of the fresh shell. -/
structure Details where
  /-- Original tmux session name. -/
  session : String := ""
  /-- Original tmux window index. -/
  window : String := ""
  /-- Original tmux pane index, distinct from tmux's internal pane ID. -/
  index : String := ""
  /-- Saved pane title. -/
  title : String := ""
  /-- Foreground command name at save time, not the last completed shell command. -/
  command : String := ""
  /-- Saved foreground command line, without the file format's colon sentinel. -/
  savedCommand : String := ""
  /-- Saved window title. -/
  windowTitle : String := ""
  /-- Saved layout width; 80 when the layout cannot be resolved. -/
  cols : Nat := 80
  /-- Saved layout height; 24 when the layout cannot be resolved. -/
  rows : Nat := 24
  deriving BEq, Repr

/-- One saved pane and its independent linger session. -/
structure Pane where
  /-- The projected linger session name; parsing accepts only canonical names. -/
  name : String
  /-- The decoded working directory; parsing expands `~` and a `~/` prefix to the home
  directory and rejects NUL. -/
  dir : String
  /-- The 1-based line of the pane record in the save, for diagnostics and catalog rows. -/
  line : Nat
  /-- Original pane metadata; never used to launch a saved command. -/
  details : Details := {}
  deriving BEq, Repr

end Linger.Import.Resurrect
