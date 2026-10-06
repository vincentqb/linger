module

public section

namespace Linger.Tools.Entry

inductive Route where
  | selector
  | tmux (args : List String)
  | session (args : List String)
  deriving BEq, Repr

/-- Bare invocation explains the CLI; named commands choose their executor. -/
def route (args : List String) : Route :=
  match args with
  | [] => .session ["help"]
  | ["attach"] | ["a"] => .selector
  | "tmux" :: rest => .tmux rest
  | _ => .session args

end Linger.Tools.Entry
