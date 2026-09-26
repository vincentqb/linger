module

public import Manager.Picker
public import Manager.Resurrect

public section

/-! Optional manager entry point; the session executable does not import it. -/

namespace Lz

private def usage : IO Unit :=
  IO.println
    "Usage: lz
       lz --loop [NAME[@HOST]]
       lz import-resurrect [--restore-processes] [SAVE]
       lz --help

Select an existing session using subsequence filtering (ASCII case-insensitive).
Up/down or ctrl-p/ctrl-n move; Home/End select first/last.
Backspace edits, ctrl-u clears, enter attaches, esc/ctrl-c/ctrl-d cancel.
Ctrl-r reloads the listing and clears the query.
--loop returns to selection after attach exits.
import-resurrect imports a save without an interactive picker."

def main (args : List String) : IO UInt32 := do
  try
    match args with
    | [] =>
      Manager.Picker.run false none
    | ["--loop"] =>
      Manager.Picker.run true none
    | ["--loop", target] =>
      if target.isEmpty then
        usage
        return 2
      Manager.Picker.run true (some target)
    | "import-resurrect" :: rest =>
      Manager.Resurrect.run rest
    | ["--help"] | ["-h"] =>
      usage
      return 0
    | _ =>
      usage
      return 2
  catch error =>
    IO.eprintln s!"lz: {error}"
    return 1

end Lz

def main := Lz.main
