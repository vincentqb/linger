import Zmx.Core.Name
/-! # Zmx.Core.Remote — parsing `lzmx ls --porcelain` from other machines

The overview (`lzmx -r <hosts>`) folds in sessions from configured
remote hosts by running `ssh <host> lzmx ls --porcelain` and parsing
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

namespace Zmx.Core.Remote

open Zmx.Core.Name (sanitize)

structure RemoteRow where
  name : String
  live : Bool := true
  cmd : String := ""
  clients : Nat := 0
  labels : List (String × String) := []
  deriving Repr, DecidableEq, Inhabited

/-- Strip ANSI/control bytes from a display string (a remote could
embed escape sequences in `cmd` or label values; the overview prints
these verbatim into the listing, so control characters must die here). -/
def scrub (s : String) : String :=
  String.ofList (s.toList.filter (fun c => c.toNat ≥ 0x20 && c.toNat != 0x7F))

def parseRecord (lines : List String) : Option RemoteRow :=
  let kvs := lines.filterMap (fun l =>
    match l.splitOn "\t" with
    | [k, v] => some (k, v)
    | _ => none)  -- malformed line: dropped, record survives
  match kvs.find? (·.1 == "name") with
  | none => none  -- no name: not a session record
  | some (_, rawName) =>
    some {
      name := sanitize rawName
      live := ((kvs.find? (·.1 == "state")).map (·.2)).getD "live" == "live"
      cmd := scrub (((kvs.find? (·.1 == "cmd")).map (·.2)).getD "")
      clients := (((kvs.find? (·.1 == "clients")).map (·.2)).getD "").toNat?.getD 0
      labels := kvs.filterMap (fun (k, v) =>
        if k.startsWith "label." then some (scrub (k.drop 6).toString, scrub v)
        else none) }

/-- Split on blank lines into records. -/
def records (lines : List String) : List (List String) :=
  let step := fun (acc : List (List String) × List String) (l : String) =>
    let (done, cur) := acc
    if l.trimAscii.isEmpty then
      (if cur.isEmpty then done else done ++ [cur.reverse], [])
    else (done, l :: cur)
  let (done, cur) := lines.foldl step ([], [])
  if cur.isEmpty then done else done ++ [cur.reverse]

/-- The parser: total, garbage-tolerant, names sanitized. -/
def parse (out : String) : List RemoteRow :=
  (records (out.splitOn "\n")).filterMap parseRecord

/-- First host that appears more than once (for the error message). -/
def firstDupHost : List String → Option String
  | [] => none
  | h :: t => if t.contains h then some h else firstDupHost t

/-- Validate a remote-host list. A repeated host is a configuration
mistake with no valid meaning — it would double-query and show
duplicate rows — so reject it loudly rather than silently dedup. The
overview runs this *before* any connection is attempted, so a bad host
list refuses immediately and names the offender. Pure; the IO caller
turns `.error` into `IO.userError`. -/
def checkHosts (hosts : List String) : Except String (List String) :=
  if hosts.Nodup then .ok hosts
  else .error s!"remote host '{(firstDupHost hosts).getD ""}' listed more than once"

end Zmx.Core.Remote
