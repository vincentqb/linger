module

import Linger.Target.CoreCode.Remote
meta import Linger.Target.CoreCode.Remote

/-! # Remote parser tests — real porcelain, and hostile porcelain -/

namespace Linger.Target.Remote.Tests

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
example : (parse "name\t-r f\n").isEmpty = true := by native_decide

/-- A name is clean text, kept exactly: it is never a path. -/
example : (parse "name\t../my build ✓\n").map (·.name) = ["../my build ✓"] := by native_decide

example : parseTarget "work@me@dev-a" == some { name := "work", host := some "me@dev-a" } := by
  native_decide

example : parseTarget "work" == some { name := "work", host := none } := by native_decide

example :
    ["", "work@", "-a b", "   ", "bad\x01name", "work@bad\x1bhost"].all
      (fun s => (parseTarget s).isNone) := by
  native_decide

/-- The encoded command line: `linger`, the marker, then each word as `x` and its UTF-8 bytes in
lowercase hex, so the empty word is `x`. -/
example : command "send" ["", "a b", "é"] == "linger argv:hex x73656e64 x x612062 xc3a9" := by
  native_decide

/-- Only the encoder's spelling decodes: a word without its `x`, with an odd digit, an uppercase
or other character, or bytes that are not UTF-8 is refused, and one refused word refuses the
line. -/
example :
    ["", "61", "x6", "x6A", "x6g", "xff", "xc3"].all (decodeWord · == none) &&
      decode ["x61", "x"] == some ["a", ""] &&
      decode ["x61", "y"] == none := by
  native_decide

/-- Control bytes in display fields are scrubbed (no ANSI injection
into the listing). -/
example : ((parse "name\tx\ncmd\tvi\x1b[31mm\x07\n").map (·.cmd) == ["vi[31mm"]) = true := by
  native_decide

/-- A peer's status is kept verbatim for `Status.ofName`: a control byte inside a
healthy name leaves a name it does not recognise, not the name scrubbing would leave. -/
example : ((parse "name\tw\nstatus\tid\x01le\n").map (·.status) == ["id\x01le"]) = true := by
  native_decide

/-- Trailing newline vs none: same records either way (robustness to where the
peer's output ends, at the line level). -/
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

/-- The remotes file: a host alone reaches it with ssh, as such a line always did; the words after
it are its command for every verb, or, either side of one `|`, the query's and the attach's.
Blanks separate words; a comment or an empty line names nothing. -/
example :
    (match
        config
          ["# hosts", "", "dev", "  box\tdocker exec -i box | docker exec -it box  ",
            "pod kubectl exec -i pod --", "far\r", "   # indented comment"] with
      | .ok entries =>
        entries ==
          [("dev", ssh "dev"),
            ("box",
              { query := ["docker", "exec", "-i", "box"],
                attach := ["docker", "exec", "-it", "box"] }),
            ("pod",
              { query := ["kubectl", "exec", "-i", "pod", "--"],
                attach := ["kubectl", "exec", "-i", "pod", "--"] }),
            ("far", ssh "far")]
      | .error _ => false) =
      true := by
  native_decide

/-- A line with no one meaning refuses the whole file, naming its host: an empty side of the
`|`, a second `|`, a host listed twice, or a command word holding a control character. -/
example :
    (["far |", "far | ssh -t far", "far ssh -T far |", "far a | b | c", "far ssh\x1b[31m far"].all
        fun line =>
        match config ["dev", line] with
        | .ok _ => false
        | .error e => e.startsWith "remote host 'far'" && !e.toList.contains '\x1b') &&
      (match config ["far", "far ssh -T -- far"] with
        | .ok _ => false
        | .error e => e == "remote host 'far' listed more than once") =
        true := by
  native_decide

/-- A host the file does not name reaches with ssh; one it names, with its own commands. -/
example :
    (transportFor [("box", { query := ["q"], attach := ["a"] })] "box" ==
          { query := ["q"], attach := ["a"] } &&
        transportFor [("box", { query := ["q"], attach := ["a"] })] "dev" == ssh "dev") =
      true := by
  native_decide

/-- A target verb's argv: the host's attach command for an attach and its query command otherwise,
then `linger`, the marker and the encoded words, the target after `--` for an attach or capture
whose name starts with `-`, and by position for the other verbs. -/
example :
    (targetArgv (ssh "dev") "attach" ["--read-only"] "-w" [] ==
          ["ssh", "-t", "--", "dev", "linger", "argv:hex"] ++
            ["attach", "--read-only", "--", "-w"].map encodeWord &&
        targetArgv { query := ["docker", "exec", "-i", "box"], attach := ["docker"] } "kill" [] "-w"
            [] ==
          ["docker", "exec", "-i", "box", "linger", "argv:hex"] ++ ["kill", "-w"].map encodeWord &&
        argv (ssh "dev") "ls" ["--porcelain"] ==
          ["ssh", "-T", "--", "dev", "linger", "argv:hex", "x6c73", "x2d2d706f7263656c61696e"]) =
      true := by
  native_decide

end Linger.Target.Remote.Tests
