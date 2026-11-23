module

import Linger.Target.CoreCode.Remote
meta import Linger.Target.CoreCode.Remote

/-! # Remote targets, host lists, the remotes file and the transport's argv -/

namespace Linger.Target.Remote.Tests

example : parseTarget "work@me@dev-a" == some { name := "work", host := some "me@dev-a" } := by
  native_decide

example : parseTarget "work" == some { name := "work", host := none } := by native_decide

example :
    ["", "work@", "-a b", "   ", "bad\x01name", "work@bad\x1bhost"].all
      (fun s => (parseTarget s).isNone) := by
  native_decide

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

/-- The remotes file: a host alone reaches it with ssh, as such a line always did; the words after
it are its command, every one of them, a `|` among them. Blanks separate words; a comment or an
empty line names nothing. -/
example :
    (match
        config
          ["# hosts", "", "dev", "  box\tdocker exec -i box  ", "pod kubectl exec -i pod --",
            "far\r", "old ssh -T old | mosh old", "   # indented comment"] with
      | .ok entries =>
        entries ==
          [("dev", ssh "dev"), ("box", { command := ["docker", "exec", "-i", "box"] }),
            ("pod", { command := ["kubectl", "exec", "-i", "pod", "--"] }), ("far", ssh "far"),
            ("old", { command := ["ssh", "-T", "old", "|", "mosh", "old"] })]
      | .error _ => false) =
      true := by
  native_decide

/-- A file with no one meaning is refused, naming its host: a host listed twice, or a command word
holding a control character. -/
example :
    ((match config ["dev", "far ssh\x1b[31m far"] with
        | .ok _ => false
        | .error e => e.startsWith "remote host 'far'" && !e.toList.contains '\x1b') &&
        (match config ["far", "far ssh -T -- far"] with
        | .ok _ => false
        | .error e => e == "remote host 'far' listed more than once")) =
      true := by
  native_decide

/-- A host the file does not name is reached with ssh; one it names, with its own command. -/
example :
    (transportFor [("box", { command := ["q"] })] "box" == { command := ["q"] } &&
        transportFor [("box", { command := ["q"] })] "dev" == ssh "dev") =
      true := by
  native_decide

/-- A host's `serve` runs with its transport's command, then `linger serve`, and nothing else:
`ssh -T`, since no far end needs a terminal. -/
example :
    (argv (ssh "dev") == ["ssh", "-T", "--", "dev", "linger", "serve"] &&
        argv { command := ["docker", "exec", "-i", "box"] } ==
          ["docker", "exec", "-i", "box", "linger", "serve"]) =
      true := by
  native_decide

end Linger.Target.Remote.Tests
