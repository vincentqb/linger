module

import Linger.Target.Name
import Linger.Target.Spec

public section

/-! # Linger.Target.Remote — other machines' listings, targets and command lines

The overview (`linger -r <hosts>`) folds in sessions from configured
remote hosts by running `ssh <host> linger ls --porcelain` and parsing
stdout here. A session verb on a `name@host` target runs on that host as the encoded command
line `command` builds, which the remote entry decodes (`decode`).

§Remote: the parser is total (any bytes → some rows,
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

namespace Linger.Target.Remote

open Linger.Target.Name (sanitize)

/-- One session from a peer's porcelain listing. -/
structure RemoteRow where
  /-- The session name, validated without rewriting. -/
  name : String
  /-- True unless the peer's `state` field names something other than `live`. -/
  live : Bool := true
  /-- The peer's `cmd` field, with control characters removed. -/
  cmd : String := ""
  /-- The peer's own `status` name, verbatim from its porcelain. Interpreted
  by `Status.ofName`, which is total and maps anything unrecognised — including
  an absent field from an older peer — to `unknown`. So a remote row can never
  claim a state we could not actually read. -/
  status : String := ""
  deriving Repr, DecidableEq, Inhabited

/-- Drop C0 and C1 controls and DEL from untrusted text: `ls -r --porcelain`
prints a remote `cmd` verbatim, and `Client.replyText` prints a daemon's reason. -/
def scrub (s : String) : String :=
  String.ofList (s.toList.filter (fun c => c.toNat ≥ 32 && (c.toNat < 127 || c.toNat ≥ 160)))

/-- One record's tab-separated key/value lines as a row, or `none` when the `name` is
absent or invalid (`parseRecord_name_valid`). Malformed lines are skipped. -/
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
    let name ← Linger.Target.Name.check rawName
    some {
          name
          live := (kvs.lookup "state").getD "live" == "live"
          cmd := scrub ((kvs.lookup "cmd").getD "")
          status := (kvs.lookup "status").getD "" }

/-- The parser: total, garbage-tolerant, names validated without rewriting. Records are
separated by blank lines; an empty group has no `name` and yields no row. -/
def parse (out : String) : List RemoteRow :=
  ((out.splitOn "\n").splitOnP (·.trimAscii.isEmpty)).filterMap parseRecord

/-- First host that appears more than once (for the error message). -/
def firstDupHost : List String → Option String
  | [] => none
  | h :: t => if t.contains h then some h else firstDupHost t

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
    match hosts.find? (!hostClean ·) with
    | some h => .error s!"remote host '{scrub h}' contains a control character"
    | none => .ok hosts

/-- Exact local name and optional SSH destination. -/
structure Target where
  /-- The session name: everything before the first `@`. -/
  name : String
  /-- Everything after the first `@`, verbatim, or `none` without one. -/
  host : Option String
  deriving BEq, Repr

/-- One target grammar for command arguments, listed targets and selector creation.
The host is preserved verbatim, including a possible `user@host` suffix. -/
def targetValid (target : String) : Bool :=
  let parts := target.splitOn "@"
  let name := parts.headD ""
  !target.isEmpty && sanitize name == name && hostClean target &&
    (parts.tail.isEmpty || !(String.intercalate "@" parts.tail).isEmpty)

/-- Split a target that `targetValid` accepts at its first `@`, and refuse any other
(`parseTarget_exact`). -/
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

/-! ## Encoded command lines

SSH hands its command line to the login shell of the remote account, whichever shell that is,
and shells disagree about quotes: fish reads a backslash inside single quotes, so POSIX quoting
lets a word close its quote there and run what follows. So linger gives the shell nothing to
interpret: after `marker`, `command` spells the verb and each word as an `x` and the lowercase
hex of its UTF-8 bytes, plain words every shell passes on as they are (`Shell.Literal`), and the
remote linger's entry decodes them (`decode`) before it routes the command line. -/

/-- The hex digit of `n`, which is below 16: `0`–`9`, then `a`–`f`. -/
def hexDigit (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- Each byte as two hex digits, the high one first. -/
def hexChars (bytes : List UInt8) : List Char :=
  bytes.flatMap fun b => [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)]

/-- One word, encoded: an `x`, so that the empty word is a word too, then the hex digits of its
UTF-8 bytes. Every encoded word is plain (`plain_encodeWord`). -/
def encodeWord (word : String) : String := String.ofList ('x' :: hexChars word.toUTF8.data.toList)

/-- The value of a lowercase hex digit, or `none` for any other character. -/
def digitValue (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - 48)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 87) else none

/-- The bytes that pairs of lowercase hex digits spell, after the bytes `done` holds in reverse,
or `none` for an odd digit or any other character. -/
def unhex : List Char → List UInt8 → Option (List UInt8)
  | [], done => some done.reverse
  | high :: low :: rest, done =>
    match digitValue high, digitValue low with
    | some h, some l => unhex rest (UInt8.ofNat (16 * h + l) :: done)
    | _, _ => none
  | [_], _ => none

/-- The word an encoded word spells, or `none` when it does not start with `x`, its digits do
not spell bytes, or the bytes are not UTF-8. Only `encodeWord`'s spelling decodes
(`decodeWord_eq_some_iff`). -/
def decodeWord (word : String) : Option String :=
  match word.toList with
  | 'x' :: digits =>
    (unhex digits []).bind fun bytes => String.fromUTF8? (ByteArray.mk bytes.toArray)
  | _ => none

/-- The words an encoded command line carries after `marker`: each word decoded, or `none` when
one does not decode, which the entry route turns into a usage error. -/
def decode (words : List String) : Option (List String) := words.mapM decodeWord

/-- The command line SSH hands the remote shell: `linger`, `marker`, then the verb and every word
encoded, the empty ones and the session name included. The caller orders the words: options, the
target's operands, then the command's arguments, which remain opaque. The remote linger routes
exactly the verb and words (`command_exact`). -/
def command (verb : String) (words : List String) : String :=
  String.intercalate " " ("linger" :: marker :: (verb :: words).map encodeWord)

end Linger.Target.Remote
