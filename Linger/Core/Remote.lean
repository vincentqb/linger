module

import Linger.Core.Name

public section

/-! # Linger.Core.Remote — parsing `linger ls --porcelain` from other machines

The overview (`linger -r <hosts>`) folds in sessions from configured
remote hosts by running `ssh <host> linger ls --porcelain` and parsing
stdout here.

§Remote (THEOREMS.md): the parser is total (any bytes → some rows,
never ⊥), garbage-tolerant (a malformed line or record is dropped, not
fatal), and §Name carries through — every name in the result is
validated without rewriting, so a hostile remote cannot inject a path or control bytes
into the local listing or the ssh argv.

Format (one record per session, blank-line separated):
```
name\twork
state\tlive
clients\t1
label.env\tdev

name\tother
state\tresumable
```
-/

namespace Linger.Core.Remote

open Linger.Core.Name (sanitize)

structure RemoteRow where
  name : String
  live : Bool := true
  cmd : String := ""
  /-- The peer's own `status` name, verbatim from its porcelain. Interpreted
  by `Status.ofName`, which is total and maps anything unrecognised — including
  an absent field from an older peer — to `unknown`. So a remote row can never
  claim a state we could not actually read. -/
  status : String := ""
  deriving Repr, DecidableEq, Inhabited

/-- Strip ANSI/control bytes from a display string (a remote could
embed escape sequences in `cmd` or label values; the overview prints
these verbatim into the listing, so control characters must die here). -/
def scrub (s : String) : String :=
  String.ofList (s.toList.filter (fun c => c.toNat ≥ 32 && (c.toNat < 127 || c.toNat ≥ 160)))

def parseRecord (lines : List String) : Option RemoteRow :=
  let kvs :=
    lines.filterMap
      (fun l =>
        match l.splitOn "\t" with
        | [k, v] => some (k, v)
        | _ => none) -- malformed line: dropped, record survives
  match kvs.lookup "name" with
  | none => none -- no name: not a session record
  | some rawName => do
    let name ← Linger.Core.Name.check rawName
    some {
          name
          live := (kvs.lookup "state").getD "live" == "live"
          cmd := scrub ((kvs.lookup "cmd").getD "")
          -- the peer's own status name, scrubbed like any other display field.
          -- `Status.ofName` is total and maps anything unrecognised -- including
          -- an absent field from an older peer -- to `unknown`, so a remote row
          -- can never look healthier than we can actually read it
          status := scrub ((kvs.lookup "status").getD "") }

/-- Split on blank lines into records. -/
def records (lines : List String) : List (List String) :=
  (lines.splitOnP (·.trimAscii.isEmpty)).filter (!·.isEmpty)

/-- The parser: total, garbage-tolerant, names validated without rewriting. -/
def parse (out : String) : List RemoteRow := (records (out.splitOn "\n")).filterMap parseRecord

/-- First host that appears more than once (for the error message). -/
def firstDupHost : List String → Option String
  | [] => none
  | h :: t => if t.contains h then some h else firstDupHost t

/-- A host string fit to hand to `ssh` argv: no C0/C1 controls or DEL. **Not**
`Name.sanitize`, which would be wrong twice over — `@` is not an `okChar`, so it
would destroy a legitimate `user@host` target, and silently rewriting a host means
connecting somewhere the user did not ask for. -/
def hostClean (h : String) : Bool :=
  h.toList.all (fun c => c.toNat ≥ 32 && (c.toNat < 127 || c.toNat ≥ 160))

/-- The first host carrying a control byte, for the error message. -/
def firstDirtyHost (hosts : List String) : Option String := hosts.find? (!hostClean ·)

/-- Validate the `-r` host list. Two rejections, both **loud**, because each is a
configuration mistake with no valid meaning: a repeated host would double-query and
show duplicate rows, and a host with a control byte in it goes into `ssh` argv, so
scrubbing it would connect somewhere the user did not name. Reject rather than
silently dedup or rewrite. The overview runs this *before* any connection is
attempted, so a bad list refuses immediately and names the offender. Pure; the `IO`
caller turns `.error` into `IO.userError`.

The message reports the offending host **scrubbed**: it is printed to a terminal,
and echoing the raw bytes back is how a hostile remotes file would inject an escape
sequence through the error path rather than the listing (`terminalListing` covers the
listing; this covers here). -/
def checkHosts (hosts : List String) : Except String (List String) :=
  match firstDupHost hosts with
  | some h => .error s!"remote host '{scrub h}' listed more than once"
  | none =>
    match firstDirtyHost hosts with
    | some h => .error s!"remote host '{scrub h}' contains a control character"
    | none => .ok hosts

/-- Exact local name and optional SSH destination. The first `@` separates them. -/
structure Target where
  name : String
  host : Option String
  deriving BEq, Repr

/-- One target grammar for command arguments, listed targets and selector creation.
The host is preserved verbatim, including a possible `user@host` suffix. -/
def targetValid (target : String) : Bool :=
  let parts := target.splitOn "@"
  let name := parts.headD ""
  !target.isEmpty && sanitize name == name && hostClean target &&
    (parts.tail.isEmpty || !(String.intercalate "@" parts.tail).isEmpty)

def parseTarget (target : String) : Option Target :=
  if targetValid target then
    let parts := target.splitOn "@"
    some
      { name := parts.headD ""
        host := if parts.tail.isEmpty then none else some (String.intercalate "@" parts.tail) }
  else none

/-- A positional target after optional flags. `--` preserves option-like names;
everything after the target belongs to the command, without reinterpretation. -/
def targetArgs (args : List String) : Option (String × List String) :=
  match args with
  | "--" :: name :: rest => some (name, rest)
  | name :: rest => if name.startsWith "-" then none else some (name, rest)
  | [] => none

/-- The operands `targetArgs` reads back as exactly `name`: a name starting with `-`
follows `--`. Every attach or capture argv linger builds for itself places its
target this way; verbs that take their target by position never read `--`. -/
def targetOperands (name : String) : List String :=
  if name.startsWith "-" then ["--", name] else [name]

/-- One POSIX shell word. Quotes in the payload briefly close the single-quoted
region, emit an escaped quote, and reopen it; all other characters remain literal. -/
def shellQuote (s : String) : String :=
  String.ofList
    (['\''] ++ s.toList.flatMap (fun c => if c == '\'' then ['\'', '\\', '\'', '\''] else [c]) ++
      ['\''])

/-- SSH passes a command string to a shell, so quote every word after the verb,
including empty words and the session name. The caller orders them: options, the
target's operands, then the command's arguments, which remain opaque. -/
def command (verb : String) (words : List String) : String :=
  String.intercalate " " (("linger" :: verb :: words).map shellQuote)

end Linger.Core.Remote
