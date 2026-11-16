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
