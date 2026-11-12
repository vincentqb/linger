module

import Linger.App.Answer
import Linger.App.Shell
import Linger.App.Entry
import Linger.Selector.Shell
import Linger.Import.Shell

public section

/-! Compose session commands, terminal selection and save interchange in one executable.
The session library and VT toolkit do not import the manager. -/

/-- The executable: `Entry.route` sends the argv to interactive selection, tmux
interchange or a session command, which exits with its answer's code, and refuses an encoded
command line that does not decode as a usage error. An uncaught error prints
`linger: <error>` and answers `notDone`. -/
def main (args : List String) : IO UInt32 := do
  try
    match Linger.App.Entry.route args with
    | .selector readOnly =>
      Linger.Selector.Shell.run (← IO.appPath).toString readOnly
    | .tmux rest =>
      Linger.Import.Shell.run (← IO.appPath).toString rest
    | .session argv =>
      return (← Linger.App.Shell.main argv).code
    | .malformed =>
      IO.eprintln "linger: malformed encoded command line"
      return Linger.App.Answer.usage.code
  catch e =>
    IO.eprintln s!"linger: {e}"
    return Linger.App.Answer.notDone.code
