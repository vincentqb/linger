module

import Linger.Os.CoreCode.Answer
import Linger.App.WorldCode
import Linger.App.CoreCode.Entry
import Linger.Selector.WorldCode
import Linger.Import.WorldCode

public section

/-! Compose session commands, terminal selection and save interchange in one executable.
The session library and VT toolkit do not import the manager. -/

/-- The executable: `Entry.route` sends the argv to interactive selection, tmux
interchange or a session command, each of which answers, and refuses an encoded command line
that does not decode as a usage error. An uncaught error prints `linger: <error>` and answers
`notDone`. Whatever the route, the process exits with the code of its answer. -/
def main (args : List String) : IO UInt32 := do
  let answer : Linger.Os.Answer ←
    try
      match Linger.App.Entry.route args with
      | .selector readOnly =>
        Linger.Selector.Shell.run (← IO.appPath).toString readOnly
      | .tmux rest =>
        Linger.Import.Shell.run (← IO.appPath).toString rest
      | .session argv =>
        Linger.App.Shell.main argv
      | .malformed =>
        IO.eprintln "linger: malformed encoded command line"
        pure .usage
    catch e =>
      IO.eprintln s!"linger: {e}"
      pure .notDone
  return answer.code
