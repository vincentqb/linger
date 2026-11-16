module

import Linger.Os.CoreCode.Answer
import Linger.App.WorldCode
import Linger.App.CoreCode.Entry
import Linger.Selector.WorldCode
import Linger.Import.WorldCode
import Linger.Session.WorldCode.Names
import Os.WorldCode

public section

/-! Compose session commands, terminal selection and save interchange in one executable.
The session library and VT toolkit do not import the manager. -/

/-- The executable: `Entry.route` sends the argv to interactive selection, tmux
interchange or a session command, each of which answers, and refuses an encoded command line
that does not decode as a usage error. An uncaught error prints `linger: <error>` and answers
`notDone`. Whatever the route, the process exits with the code of its answer, but for one a
signal stopped (`stopped`): having handed its terminal back, it ends by that signal, as a program
that does not catch it ends, so its caller sees the signal itself, and exits with the code only
if the signal does not end it. -/
def main (args : List String) : IO UInt32 := do
  let answer : Linger.Os.Answer ←
    try
      match Linger.App.Entry.route args with
      | .selector readOnly =>
        Linger.Selector.Shell.run (← IO.appPath).toString Linger.Session.Shell.Names.nameOf readOnly
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
  if let .stopped signal := answer then
    try
      Os.Shell.raiseSignal signal
    catch _ =>
      pure ()
  return answer.code
