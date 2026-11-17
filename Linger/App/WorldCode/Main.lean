module

import Linger.Os.CoreCode.Answer
import Linger.App.WorldCode
import Linger.App.CoreCode.Entry
import Linger.Selector.WorldCode
import Linger.Import.WorldCode
import Linger.Session.WorldCode.Names
import Os.WorldCode

public section

/-! Compose session commands, terminal selection and the tmux-resurrect source in one
executable.
The session library and VT toolkit do not import the manager. -/

/-- The latest tmux-resurrect save as the session CLI's source of saved sessions, which the
session library reads only through what this supplies. -/
private def source : Linger.App.Api.Source where
  rows := Linger.Import.Shell.sourceRows
  row := Linger.Import.Shell.sourceRow?
  adopt name := (· matches .recorded) <$> Linger.Import.Shell.adopt name
  dismiss := Linger.Import.Shell.dismiss
  save := Linger.Import.Shell.exportSave

/-- The executable: `Entry.route` sends the argv to interactive selection or a session command,
each of which answers, and refuses an encoded command line that does not decode as a usage
error. An uncaught error prints `linger: <error>` and answers
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
      | .session argv =>
        Linger.App.Shell.main source argv
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
