module

import Linger.Runtime.Cli
import Linger.Tools.Entry
import Linger.Manager.Picker
import Linger.Manager.Resurrect

public section

/-! Compose session commands, terminal selection and save interchange in one executable.
The session library and VT toolkit do not import the manager. -/

def main (args : List String) : IO UInt32 := do
  try
    match Linger.Tools.Entry.route args with
    | .selector readOnly =>
      Linger.Manager.Picker.run (← IO.appPath).toString readOnly
    | .tmux rest =>
      Linger.Manager.Resurrect.run (← IO.appPath).toString rest
    | .session argv =>
      Linger.Runtime.Cli.main argv
  catch e =>
    IO.eprintln s!"linger: {e}"
    return 1
