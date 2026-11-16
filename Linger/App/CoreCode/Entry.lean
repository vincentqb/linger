module

public import Linger.App.CoreSpec
import Linger.Target.CoreSpec
import Linger.Target.CoreCode.Remote

public section

namespace Linger.App.Entry

/-- Where a command line of the words its sender meant goes (`plain_eq`). -/
private def plain (args : List String) : Route :=
  match args with
  | [] => .session ["--help"]
  | ["attach"] => .selector false
  | ["attach", "--read-only"] => .selector true
  | _ => .session args

/-- Bare invocation explains the CLI; named commands choose their executor. An encoded command
line, `Remote.marker` and then the words a remote linger sent it (`Remote.command`), goes where
the words it decodes to go, and one that does not decode is a usage error. -/
def route (args : List String) : Route :=
  match args with
  | word :: encoded =>
    if word = Linger.Target.Remote.marker then
      match Linger.Target.Remote.decode encoded with
      | some argv => plain argv
      | none => .malformed
    else plain args
  | [] => plain []

end Linger.App.Entry
