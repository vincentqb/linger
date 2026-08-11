import Zmx.Runtime.Cli
import Zmx.Runtime.Resume
import Zmx.Runtime.Tui
/-! lzmx entry point. Resume hooks give the daemon its continuum-shape
persistence; bare `lzmx` opens the session-manager TUI. -/

def main (args : List String) : IO UInt32 := do
  try
    Zmx.Runtime.Cli.main Zmx.Runtime.Resume.hooks Zmx.Runtime.Tui.main args
  catch e =>
    IO.eprintln s!"lzmx: {e}"
    return 1
