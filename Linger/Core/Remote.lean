module

public import Linger.Core.Name

public section

/-! # Linger.Core.Remote — parsing `linger ls --porcelain` from other machines

The overview (`linger -r <hosts>`) folds in sessions from configured
remote hosts by running `ssh <host> linger ls --porcelain` and parsing
stdout here.

§Remote (THEOREMS.md): the parser is total (any bytes → some rows,
never ⊥), garbage-tolerant (a malformed line or record is dropped, not
fatal), and §Name carries through — every name in the result is
sanitized, so a hostile remote cannot inject a path or control bytes
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
  String.ofList (s.toList.filter (fun c => c.toNat ≥ 0x20 && c.toNat != 0x7F))

def parseRecord (lines : List String) : Option RemoteRow :=
  let kvs :=
    lines.filterMap
      (fun l =>
        match l.splitOn "\t" with
        | [k, v] => some (k, v)
        | _ => none) -- malformed line: dropped, record survives
  match kvs.find? (·.1 == "name") with
  | none => none -- no name: not a session record
  | some (_, rawName) =>
    some
      { name := sanitize rawName
        live := ((kvs.find? (·.1 == "state")).map (·.2)).getD "live" == "live"
        cmd := scrub (((kvs.find? (·.1 == "cmd")).map (·.2)).getD "")
        -- the peer's own status name, scrubbed like any other display field.
        -- `Status.ofName` is total and maps anything unrecognised -- including
        -- an absent field from an older peer -- to `unknown`, so a remote row
        -- can never look healthier than we can actually read it
        status := scrub (((kvs.find? (·.1 == "status")).map (·.2)).getD "") }

/-- Split on blank lines into records. -/
def records (lines : List String) : List (List String) :=
  let step := fun (acc : List (List String) × List String) (l : String) =>
    let (done, cur) := acc
    if l.trimAscii.isEmpty then (if cur.isEmpty then done else done ++ [cur.reverse], [])
    else (done, l :: cur)
  let (done, cur) := lines.foldl step ([], [])
  if cur.isEmpty then done else done ++ [cur.reverse]

/-- The parser: total, garbage-tolerant, names sanitized. -/
def parse (out : String) : List RemoteRow := (records (out.splitOn "\n")).filterMap parseRecord

/-- First host that appears more than once (for the error message). -/
def firstDupHost : List String → Option String
  | [] => none
  | h :: t => if t.contains h then some h else firstDupHost t

/-- A host string fit to hand to `ssh` argv: no C0 control, no DEL. **Not**
`Name.sanitize`, which would be wrong twice over — `@` is not an `okChar`, so it
would destroy a legitimate `user@host` target, and silently rewriting a host means
connecting somewhere the user did not ask for. -/
def hostClean (h : String) : Bool :=
  h.toList.all (fun c => decide (c.toNat ≥ 0x20) && decide (c.toNat ≠ 0x7F))

/-- The first host carrying a control byte, for the error message. -/
def firstDirtyHost : List String → Option String
  | [] => none
  | h :: t => if hostClean h then firstDirtyHost t else some h

/-- Validate the `-r` host list. Two rejections, both **loud**, because each is a
configuration mistake with no valid meaning: a repeated host would double-query and
show duplicate rows, and a host with a control byte in it goes into `ssh` argv, so
scrubbing it would connect somewhere the user did not name. Reject rather than
silently dedup or rewrite. The overview runs this *before* any connection is
attempted, so a bad list refuses immediately and names the offender. Pure; the IO
caller turns `.error` into `IO.userError`.

The message reports the offending host **scrubbed**: it is printed to a terminal,
and echoing the raw bytes back is how a hostile remotes file would inject an escape
sequence through the error path rather than the listing (`humanListing` covers the
listing; this covers here). -/
def checkHosts (hosts : List String) : Except String (List String) :=
  if !hosts.Nodup then
    .error s!"remote host '{scrub ((firstDupHost hosts).getD "")}' listed more than once"
  else
    match firstDirtyHost hosts with
    | some h => .error s!"remote host '{scrub h}' contains a control character"
    | none => .ok hosts

end Linger.Core.Remote
