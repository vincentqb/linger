module

public import Linger.Runtime.Cli
public import Linger.Runtime.Resume
public import Tools.Entry
public import Manager.Picker
public import Manager.Resurrect

public section

/-! Compose session commands, terminal selection and save interchange in one executable.
The session library and VT toolkit do not import the manager. -/

def main (args : List String) : IO UInt32 := do
  try
    match Tools.Entry.route args with
    | .selector =>
      Manager.Picker.run (← IO.appPath).toString
    | .importSave rest =>
      Manager.Resurrect.run (← IO.appPath).toString rest
    | .exportSave rest =>
      Manager.Resurrect.runExport rest
    | .session argv =>
      Linger.Runtime.Cli.main Linger.Runtime.Resume.hooks argv
  catch e =>
    IO.eprintln s!"linger: {e}"
    return 1
