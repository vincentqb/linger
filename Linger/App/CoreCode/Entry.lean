module

public import Linger.App.CoreSpec

public section

namespace Linger.App.Entry

/-- Bare invocation explains the CLI; named commands choose their executor: `attach` alone opens
the selector, read-only on request, and every other command line reaches the session CLI with its
exact words (`route_eq`). -/
def route (args : List String) : Route :=
  match args with
  | [] => .session ["--help"]
  | ["attach"] => .selector false
  | ["attach", "--read-only"] => .selector true
  | _ => .session args

end Linger.App.Entry
