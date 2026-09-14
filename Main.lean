module

public import Linger.Runtime.Cli
public import Linger.Runtime.Resume

public section

/-! linger entry point. Resume hooks give the daemon its reboot-surviving
persistence; bare `linger` prints the session overview. -/

def main (args : List String) : IO UInt32 := do
  try
    Linger.Runtime.Cli.main Linger.Runtime.Resume.hooks args
  catch e =>
    IO.eprintln s!"linger: {e}"
    return 1
