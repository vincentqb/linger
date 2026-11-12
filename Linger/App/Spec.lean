module

public section

/-! # What command-line headlines are stated in

The executor a command line reaches, where a command line of plain words goes, and one row of
the command table. -/

namespace Linger.App.Entry

/-- The executor that receives a command line: the interactive selector, tmux save
interchange or the session CLI, or a usage error for an encoded command line that does not
decode. -/
inductive Route where
  /-- `attach` or `a` without a target: open the selector, read-only on request. -/
  | selector (readOnly : Bool)
  /-- Save interchange, given the arguments after `tmux`. -/
  | tmux (args : List String)
  /-- Every other command line, with its exact arguments; an empty one becomes `help`. -/
  | session (args : List String)
  /-- An encoded command line whose words do not decode: a usage error, exit status 2. -/
  | malformed
  deriving BEq, Repr

/-- Where a command line goes, once its words are the ones its sender meant: bare invocation
explains the CLI, `attach` or `a` alone opens the selector, read-only on request, `tmux` hands
the rest to save interchange, and every other command line reaches the session CLI with its
exact words. -/
@[expose]
def Route.of (args : List String) : Route :=
  if args = [] then .session ["help"]
  else
    if args = ["attach"] ∨ args = ["a"] then .selector false
    else
      if args = ["attach", "--read-only"] ∨ args = ["a", "--read-only"] then .selector true
      else if args.head? = some "tmux" then .tmux args.tail else .session args

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
