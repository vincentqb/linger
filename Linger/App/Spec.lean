module

public section

/-! # What command-line headlines are stated in

The executor a command line reaches, and one row of the command table. -/

namespace Linger.App.Entry

/-- The executor that receives a command line: the interactive selector, tmux save
interchange or the session CLI. -/
inductive Route where
  /-- `attach` or `a` without a target: open the selector, read-only on request. -/
  | selector (readOnly : Bool)
  /-- Save interchange, given the arguments after `tmux`. -/
  | tmux (args : List String)
  /-- Every other command line, with its exact arguments; an empty one becomes `help`. -/
  | session (args : List String)
  deriving BEq, Repr

end Linger.App.Entry

namespace Linger.App.Commands

/-- One row of the command table. -/
structure Command where
  /-- The word that names the command. -/
  word : String
  /-- Its other spellings, each a word no other command uses. -/
  aliases : List String := []
  /-- The arguments it takes, as help and its usage error show them. -/
  args : String
  /-- What it does, in a few words. -/
  summary : String
  deriving Repr, DecidableEq

end Linger.App.Commands
