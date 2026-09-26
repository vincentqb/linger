module

public import Linger.Runtime.Cli
public import Linger.Runtime.Resume
public import Tools.Entry
public import Manager.Picker
public import Manager.Resurrect

public section

/-! Compose session commands, terminal selection and save import in one executable.
The session library and VT toolkit do not import the manager. -/

def main (args : List String) : IO UInt32 := do
  try
    let stdinTty ←
      if args.isEmpty then
        (← IO.getStdin).isTty
      else
        pure false
    let stdoutTty ←
      if args.isEmpty then
        (← IO.getStdout).isTty
      else
        pure false
    match Tools.Entry.route args stdinTty stdoutTty with
    | .selector =>
      Manager.Picker.run (← IO.appPath).toString
    | .importSave rest =>
      Manager.Resurrect.run (← IO.appPath).toString rest
    | .session argv =>
      Linger.Runtime.Cli.main Linger.Runtime.Resume.hooks argv
  catch e =>
    IO.eprintln s!"linger: {e}"
    return 1
