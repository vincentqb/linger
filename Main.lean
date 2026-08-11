import Zmx.Runtime.Cli
/-! lzmx entry point. Checkpoint hooks are the step-7 seam; until that
lands the daemon runs with persistence disabled. -/

def main (args : List String) : IO UInt32 := do
  try
    Zmx.Runtime.Cli.main {} args
  catch e =>
    IO.eprintln s!"lzmx: {e}"
    return 1
