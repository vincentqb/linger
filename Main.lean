import Zmx.Runtime.Cli
import Zmx.Runtime.Resume
/-! lzmx entry point. Resume hooks give the daemon its continuum-shape
persistence; bare `lzmx` prints the session overview. -/

def main (args : List String) : IO UInt32 := do
  try
    Zmx.Runtime.Cli.main Zmx.Runtime.Resume.hooks args
  catch e =>
    IO.eprintln s!"lzmx: {e}"
    return 1
