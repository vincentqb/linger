module

public section

namespace Linger.Tools.Entry

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

/-- Bare invocation explains the CLI; named commands choose their executor. -/
def route (args : List String) : Route :=
  match args with
  | [] => .session ["help"]
  | ["attach"] | ["a"] => .selector false
  | ["attach", "--read-only"] | ["a", "--read-only"] => .selector true
  | "tmux" :: rest => .tmux rest
  | _ => .session args

end Linger.Tools.Entry
