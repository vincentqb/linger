module

public import Linger.App.Spec

public section

namespace Linger.App.Entry

/-- Bare invocation explains the CLI; named commands choose their executor. -/
def route (args : List String) : Route :=
  match args with
  | [] => .session ["help"]
  | ["attach"] | ["a"] => .selector false
  | ["attach", "--read-only"] | ["a", "--read-only"] => .selector true
  | "tmux" :: rest => .tmux rest
  | _ => .session args

end Linger.App.Entry
