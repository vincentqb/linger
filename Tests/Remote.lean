import Linger.Core.Remote

/-! # Remote parser tests — real porcelain, and hostile porcelain -/

namespace Linger.Core.Remote.Tests

open Linger.Core.Remote

def good : String :=
  "name\twork\nstate\tlive\nclients\t2\ncmd\tvim\nlabel.env\tdev\n\n" ++
    "name\tother\nstate\tresumable\n\n"

/-- Two records, fields carried, states distinguished. -/
example :
    ((parse good).map (fun r => (r.name, r.live, r.clients)) ==
        [("work", true, 2), ("other", false, 0)]) =
      true := by
  native_decide

example : ((parse good).head?.map (·.labels) == some [("env", "dev")]) = true := by native_decide

/-- Garbage tolerance: junk lines drop, the record around them survives;
a record with no name drops entirely; empty input gives no rows. -/
example : ((parse "junk\nname\tk\nmore junk here\n").map (·.name) == ["k"]) = true := by
  native_decide

example : (parse "state\tlive\nclients\t1\n").isEmpty = true := by native_decide

example : (parse "").isEmpty = true := by native_decide

example : (parse "\n\n\n\t\t\n").isEmpty = true := by native_decide

/-- §Name carries: a path-ish name comes back with no separators. -/
example : ((parse "name\t../../etc/passwd\n").map (·.name) == ["_._.._etc_passwd"]) = true := by
  native_decide

/-- Control bytes in display fields are scrubbed (no ANSI injection
into the listing). -/
example : ((parse "name\tx\ncmd\tvi\x1b[31mm\x07\n").map (·.cmd) == ["vi[31mm"]) = true := by
  native_decide

/-- A malformed clients count reads as 0, not a failure. -/
example : ((parse "name\tx\nclients\tmany\n").map (·.clients) == [0]) = true := by native_decide

/-- Trailing newline vs none: same records either way (§Chunk-ish
robustness at the line level). -/
example : (parse "name\ta\n" == parse "name\ta") = true := by native_decide

/-- checkHosts: a clean list passes; a duplicate is rejected (the `-r`
flag / remotes-file guard). -/
example :
    (match checkHosts ["gpu2", "gpu3"] with
      | .ok l => l == ["gpu2", "gpu3"]
      | .error _ => false) =
      true := by
  native_decide

example :
    (match checkHosts ["gpu2", "gpu3", "gpu2"] with
      | .ok _ => false
      | .error _ => true) =
      true := by
  native_decide

example :
    (match checkHosts ([] : List String) with
      | .ok l => l.isEmpty
      | .error _ => false) =
      true := by
  native_decide

/-- …and a host carrying a control byte is rejected, not scrubbed: the string goes
into `ssh` argv, so rewriting it would connect somewhere the user did not name.
A legitimate `user@host` must still pass — `Name.sanitize` would have eaten the `@`,
which is why `hostClean` is its own predicate. -/
example :
    (match checkHosts ["ok", "ev\x1b[31mil"] with
      | .ok _ => false
      | .error _ => true) =
      true := by
  native_decide

example :
    (match checkHosts ["ta\tb"] with
      | .ok _ => false
      | .error _ => true) =
      true := by
  native_decide

example :
    (match checkHosts ["de\x7fl"] with
      | .ok _ => false
      | .error _ => true) =
      true := by
  native_decide

example :
    (match checkHosts ["user@gpu2.example.com", "root@10.0.0.1"] with
      | .ok l => l.length == 2
      | .error _ => false) =
      true := by
  native_decide

/-- The refusal message cannot itself carry the escape it is complaining about. -/
example :
    (match checkHosts ["ev\x1b[31mil"] with
      | .ok _ => false
      | .error e => !(e.toList.any (fun c => c.toNat == 0x1B))) =
      true := by
  native_decide

end Linger.Core.Remote.Tests
