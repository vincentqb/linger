import Zmx.Core.Remote
/-! # Remote parser tests — real porcelain, and hostile porcelain -/

namespace Zmx.Core.Remote.Tests

open Zmx.Core.Remote

def good : String :=
  "name\twork\nstate\tlive\nclients\t2\ncmd\tvim\nlabel.env\tdev\n\n" ++
  "name\tother\nstate\tresumable\n\n"

/-- Two records, fields carried, states distinguished. -/
example : ((parse good).map (fun r => (r.name, r.live, r.clients))
    == [("work", true, 2), ("other", false, 0)]) = true := by native_decide

example : ((parse good).head?.map (·.labels) == some [("env", "dev")]) = true := by
  native_decide

/-- Garbage tolerance: junk lines drop, the record around them survives;
a record with no name drops entirely; empty input gives no rows. -/
example : ((parse "junk\nname\tk\nmore junk here\n").map (·.name) == ["k"]) = true := by
  native_decide

example : (parse "state\tlive\nclients\t1\n").isEmpty = true := by native_decide

example : (parse "").isEmpty = true := by native_decide

example : (parse "\n\n\n\t\t\n").isEmpty = true := by native_decide

/-- §Name carries: a path-ish name comes back with no separators. -/
example : ((parse "name\t../../etc/passwd\n").map (·.name)
    == ["_._.._etc_passwd"]) = true := by native_decide

/-- Control bytes in display fields are scrubbed (no ANSI injection
into the TUI frame). -/
example : ((parse "name\tx\ncmd\tvi\x1b[31mm\x07\n").map (·.cmd)
    == ["vi[31mm"]) = true := by native_decide

/-- A malformed clients count reads as 0, not a failure. -/
example : ((parse "name\tx\nclients\tmany\n").map (·.clients) == [0]) = true := by
  native_decide

/-- Trailing newline vs none: same records either way (§Chunk-ish
robustness at the line level). -/
example : (parse "name\ta\n" == parse "name\ta") = true := by native_decide

end Zmx.Core.Remote.Tests
