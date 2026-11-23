module

public import Linger.Session.CoreSpec
import Linger.Target.CoreCode.Name

public section

/-! # Linger.Session.Names — which ID a name leads to

The names table (`Names.Table`) holds an entry for each session whose name is not its ID. A
name leads to its entry's ID, or else to the ID that is the name, unless an entry leads to that
ID (`resolve`); an ID shows as the name of its entry, or else as itself when it is a name that
no entry holds (`nameOf`), never as a fresh ID. A start that finds its name leading nowhere makes
a fresh ID and an entry for it (`claim`); a rename moves the session's entry, or makes one for a
session whose name is its ID (`rename`), refused as `Rename.plan` says, and places it on disk
without replacing a name (`call`). -/

namespace Linger.Session.Names

/-- Whether `id` is a fresh ID: a dot, then one or more lowercase hexadecimal digits. -/
def isFresh (id : String) : Bool :=
  match id.toList with
  | '.' :: digits => !digits.isEmpty && digits.all hexDigit
  | _ => false

/-! ## A name in hexadecimal

A name that is no key is spelled in the names directory as an `x` and the lowercase hex of its UTF-8
bytes (`encodeWord`), which reads back as exactly the name (`decodeWord_encodeWord`). -/

/-- The hex digit of `n`, which is below 16: `0`–`9`, then `a`–`f`. -/
def hexChar (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- Each byte as two hex digits, the high one first. -/
def hexChars (bytes : List UInt8) : List Char :=
  bytes.flatMap fun b => [hexChar (b.toNat / 16), hexChar (b.toNat % 16)]

/-- One word, spelled: an `x`, so that the empty word is a word too, then the hex digits of its
UTF-8 bytes. -/
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

/-- The word a spelled word spells, or `none` when it does not start with `x`, its digits do not
spell bytes, or the bytes are not UTF-8. -/
def decodeWord (word : String) : Option String :=
  match word.toList with
  | 'x' :: digits =>
    (unhex digits []).bind fun bytes => String.fromUTF8? (ByteArray.mk bytes.toArray)
  | _ => none

/-- The file a name's entry is in the names directory: the name itself when it is a key, as every
entry was before names were clean text, and otherwise `=` and the name spelled in hexadecimal
(`encodeWord`), which no key can be, since `=` is no `Name.okChar` (`entryName_entryFile`). -/
def entryFile (name : String) : String :=
  if (Linger.Target.Name.check name).isSome then name else "=" ++ encodeWord name

/-- The name an entry's file holds, the inverse of `entryFile`: `none` for a file that is neither a
key nor `=` and the hexadecimal of a name. -/
def entryName (file : String) : Option String :=
  if (Linger.Target.Name.check file).isSome then some file
  else
    match file.toList with
    | '=' :: rest => (decodeWord (String.ofList rest)).bind Linger.Target.Name.accept
    | _ => none

/-- Whether `key` may key a session's files: a valid name, or a fresh ID. -/
def validKey (key : String) : Bool := (Linger.Target.Name.check key).isSome || isFresh key

/-- The ID `name` leads to: its entry's, else the name itself when it is a valid name and no entry
leads to it; `none` when a rename gave the session whose ID is the name another name, or the name
is not valid. -/
def resolve (t : Table) (name : String) : Option String :=
  match t.lookup name with
  | some id => some id
  | none =>
    if (Linger.Target.Name.check name).isSome && !t.any (fun e => e.2 == name) then some name
    else none

/-- The name the session with ID `id` shows: its entry's, else the ID itself when it is a valid
name that no entry holds; `none` for an ID no name leads to. -/
def nameOf (t : Table) (id : String) : Option String :=
  match t.find? (fun e => e.2 == id) with
  | some e => some e.1
  | none =>
    if (Linger.Target.Name.check id).isSome && !t.any (fun e => e.1 == id) then some id else none

/-- The table once a start gave `name`, which leads nowhere, the fresh ID `id`. -/
def claim (t : Table) (name id : String) : Table := (name, id) :: t

/-- The table once the session with ID `id`, which `old` leads to, is renamed `new`: `new` leads
to `id`, and `old` has no entry. -/
def rename (t : Table) (old new id : String) : Table := (new, id) :: t.filter (fun e => e.1 != old)

/-- How each operation places a name on disk: an entry is created by linking a temporary file
that holds its ID, and moved by a rename that may not replace. -/
def call : Op → Call
  | .create => .link
  | .move => .renameNew

/-- What `rename` does, from whether the new name is valid, whether a live or saved session has
the old name, whether its daemon was started by an older linger, and whether a live or saved
session has the new name: it refuses an invalid new name, a missing old one, a new one taken,
and a daemon that keeps no name but its ID, in that order, and otherwise moves the name. -/
def Rename.plan (valid oldHeld older newHeld : Bool) : Rename.Plan :=
  if !valid then .refuse .invalid
  else
    if !oldHeld then .refuse .missing
    else if newHeld then .refuse .taken else if older then .refuse .older else .move

end Linger.Session.Names
