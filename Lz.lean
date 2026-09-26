module

public import Manager.Picker
public import Manager.Resurrect

public section

/-! Optional manager entry point; the session executable does not import it. -/

namespace Lz

private def usage : IO Unit :=
  IO.println
    "Usage: lz
       lz import-resurrect [SAVE]
       lz --help

Select an existing session using subsequence filtering (ASCII case-insensitive).
Up/down or ctrl-p/ctrl-n move; Home/End select first/last.
Backspace edits, ctrl-u clears, enter attaches, esc/ctrl-c/ctrl-d cancel.
Ctrl-r reloads the listing and clears the query.
Selection returns after attach exits.
import-resurrect creates shells in saved directories without replaying commands."

def main (args : List String) : IO UInt32 := do
  try
    match args with
    | [] =>
      Manager.Picker.run
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
