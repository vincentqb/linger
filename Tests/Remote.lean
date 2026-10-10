import Linger.Core.Remote

/-! # Remote parser tests — real porcelain, and hostile porcelain -/

namespace Linger.Core.Remote.Tests

def good : String :=
  "name\twork\nstate\tlive\nclients\t2\ncmd\tvim\nlabel.env\tdev\n\n" ++
    "name\tother\nstate\tresumable\n\n"

/-- Two records, fields carried, states distinguished. An unread key
(`clients`, `label.*`) drops like any other: the peer emits them, and this
parser has no field to put them in. -/
example :
    ((parse good).map (fun r => (r.name, r.live, r.cmd)) ==
        [("work", true, "vim"), ("other", false, "")]) =
      true := by
  native_decide

/-- Garbage tolerance: junk lines drop, the record around them survives;
a record with no name drops entirely; empty input gives no rows. -/
example : ((parse "junk\nname\tk\nmore junk here\n").map (·.name) == ["k"]) = true := by
  native_decide

example : (parse "state\tlive\nclients\t1\n").isEmpty = true := by native_decide

example : (parse "").isEmpty = true := by native_decide

example : (parse "\n\n\n\t\t\n").isEmpty = true := by native_decide

/-- Invalid names are refused, without inventing a different session identity. -/
example : (parse "name\t../../etc/passwd\n").isEmpty = true := by native_decide

example : parseTarget "work@me@dev-a" == some { name := "work", host := some "me@dev-a" } := by
  native_decide

example : parseTarget "work" == some { name := "work", host := none } := by native_decide

example :
    ["", "work@", "two words", "foo/bar", ".hidden", "work@bad\x1bhost"].all
      (fun s => (parseTarget s).isNone) := by
  native_decide

example : shellQuote "" == "''" ∧ shellQuote "a'b" == "'a'\\''b'" := by native_decide

/-- Control bytes in display fields are scrubbed (no ANSI injection
into the listing). -/
example : ((parse "name\tx\ncmd\tvi\x1b[31mm\x07\n").map (·.cmd) == ["vi[31mm"]) = true := by
  native_decide

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

/-- The first repeated host wins, even if a different duplicate completes
earlier or a dirty host precedes it. Refusal precedence is stable. -/
example :
    (match checkHosts ["bad\x1b", "gpu2", "gpu3", "gpu3", "gpu2", "gpu3"] with
      | .error e => e == "remote host 'gpu2' listed more than once"
      | .ok _ => false) =
      true := by
  native_decide

/-- A duplicate diagnostic scrubs its host just like a control-byte refusal. -/
example :
    (match checkHosts ["ev\x1b[31mil", "ev\x1b[31mil"] with
      | .error e => e == "remote host 'ev[31mil' listed more than once"
      | .ok _ => false) =
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

/-- Configured hosts obey the same control-character rule as command targets. -/
example :
    (match checkHosts ["bad\u009bhost"] with
        | .ok _ => false
        | .error e => !e.contains '\u009b') =
        true ∧
      (parseTarget "work@bad\u009bhost").isNone = true := by
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
