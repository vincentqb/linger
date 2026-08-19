import Linger.Runtime.Cli
import Linger.Runtime.Resume
/-! linger entry point. Resume hooks give the daemon its continuum-shape
persistence; bare `linger` prints the session overview. -/

def main (args : List String) : IO UInt32 := do
  try
    Linger.Runtime.Cli.main Linger.Runtime.Resume.hooks args
  catch e =>
    IO.eprintln s!"linger: {e}"
    return 1
