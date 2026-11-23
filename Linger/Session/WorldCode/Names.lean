module

import Linger.Session.CoreCode.Names
import Linger.Session.WorldCode.Paths
import Linger.Target.CoreCode.Name
import Os.WorldCode
public import Linger.Session.CoreSpec

public section

/-! # Linger.Session.Shell.Names — the names directory

The names table (`Linger.Session.Names`) on disk: `names/` in `Paths.stateDir` holds a file for
each entry, named as the session is when that name is a key, else `=` and the name in hexadecimal
(`Names.entryFile`), and holding its ID. A session whose name is its ID, as every
session an older linger started is, has no file, so nothing an older linger wrote is moved or
rewritten. A start places an entry by linking a temporary file that holds the ID, and a rename
moves one with a rename that may not replace, so neither ever replaces a name
(`Os.Place.NoReplace`): of a start and a rename onto one name, at once, exactly one places it
(`Names.call_second_fails`). A fresh ID is claimed by creating its persistent checkpoint lock the
same way, and that lock stays while a record or an entry names the ID (`Locks.release`). Renames, and the
removal of an entry whose session is gone, hold the names lock, `names/.lock`; a start needs no
lock to place an entry, since it places one only where none is. -/

namespace Linger.Session.Shell.Names

open Linger.Session.Names (Table)

/-- A session as a command reached it: the name it was asked by, and the ID that name led to
then, which keys every file of the session for the rest of the command, whatever renames
follow. -/
structure Ref where
  /-- The name, as the command was given it. -/
  name : String
  /-- The session's ID. -/
  id : String

/-- The names directory, `names/` in `Paths.stateDir`. -/
def namesDir : IO String := do
  return (← Paths.stateDir) ++ "/names"

/-- The path of `name`'s entry, its file `Names.entryFile` spells, after `Paths.ensureDir` creates
the directory; a name that is not clean text throws, and so does an entry spelled differently on a
file system that does not tell case apart (`Paths.checkSpelling`). -/
private def entryPath (name : String) : IO String := do
  let some name :=
    Linger.Target.Name.accept
      name | throw (IO.userError s!"invalid session name (use {Paths.nameRule})")
  let dir ← namesDir
  Paths.ensureDir dir
  let path := s!"{dir}/{Linger.Session.Names.entryFile name}"
  Paths.checkSpelling path
  return path

/-- The names table the directory holds now: each file that holds a name (`Names.entryName`), as
the directory spells it, and a valid ID (`Names.validKey`). A file removed while this reads is
left out. -/
def load : IO Table := do
  let dir ← namesDir
  if !(← System.FilePath.isDir dir) then
    return []
  let mut table := []
  for entry in ← System.FilePath.readDir dir do
    if let some name := Linger.Session.Names.entryName entry.fileName then
      let id ←
        try
          pure (some (← IO.FS.readFile entry.path).trimAscii.toString)
        catch _ =>
          pure none
      if let some id := id then
        if Linger.Session.Names.validKey id then
          table := table ++ [(name, id)]
  return table

/-- The ID `name` leads to now (`Names.resolve`). -/
def resolve (name : String) : IO (Option String) := do
  return Linger.Session.Names.resolve (← load) name

/-- The session `name` leads to now, or `none`. -/
def find (name : String) : IO (Option Ref) := do
  return (← resolve name).map ({ name, id := · })

/-- The name the session with ID `id` shows now (`Names.nameOf`). -/
def nameOf (id : String) : IO (Option String) := do
  return Linger.Session.Names.nameOf (← load) id

/-- The name to say in a message about the session with ID `id`: the name it shows, or `?` for
an ID no name leads to, since an ID is never shown as a name. -/
def said (id : String) : IO String := do
  return (← nameOf id).getD "?"

/-- Place `src`'s file at the name `dst` as `Names.call` says `op` does, with a link or a rename
that may not replace (`Os.Place.NoReplace`): `false` when `dst` already names something, which
stays as it is. No operation places a name with a rename that replaces. -/
private def place (op : Linger.Session.Names.Op) (src dst : String) : IO Bool := do
  match Linger.Session.Names.call op with
  | .link =>
    Os.Shell.linkNew src dst
  | .renameNew =>
    Os.Shell.renameNew src dst
  | .replace =>
    throw (IO.userError "linger never places a name by replacing one")

/-- Draw a fresh ID, a dot and 16 hexadecimal digits of the operating system's randomness, and
claim it by creating its persistent checkpoint lock as an entry is created (`place .create`), which
no other start can create while it stays, as it does while an entry leads to its ID; a drawn ID whose lock exists is drawn again, eight times at
most. -/
private def mint : IO String := do
  let locks := (← Paths.stateDir) ++ "/.locks"
  Paths.ensureDir locks
  let tmp := s!"{locks}/.claim-{← Os.Shell.getpid}-{(← IO.monoNanosNow)}"
  IO.FS.writeFile tmp ""
  try
    for _ in [0:8] do
      let bytes ← IO.getRandomBytes 8
      let digits := bytes.toList.foldl (fun acc b => acc ++ hex2 b) ""
      let id := "." ++ digits
      if ← place .create tmp s!"{locks}/{id}.lock" then
        return id
    throw (IO.userError "no fresh session ID could be claimed")
  finally
    try
      IO.FS.removeFile tmp
    catch _ =>
      pure ()
where hex2 (b : UInt8) : String :=
    let digit (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)
    String.ofList [digit (b.toNat / 16), digit (b.toNat % 16)]

/-- Place an entry for `name` leading to `id`, linking a temporary file that holds the ID onto the
name (`Names.call .create`): `false` when the name already has an entry, which stays as it is. -/
def create (name id : String) : IO Bool := do
  let path ← entryPath name
  let tmp := s!"{← namesDir}/.new-{← Os.Shell.getpid}-{(← IO.monoNanosNow)}"
  IO.FS.writeFile tmp id
  try
    place .create tmp path
  finally
    try
      IO.FS.removeFile tmp
    catch _ =>
      pure ()

/-- Move `old`'s entry to `new` with a rename that may not replace (`Names.call .move`): `false`
when `new` already has an entry, and then both stay as they are. -/
def move (old new : String) : IO Bool := do
  place .move (← entryPath old) (← entryPath new)

/-- Remove `name`'s entry. Only under the names lock, for an entry whose session is gone. -/
def remove (name : String) : IO Unit := do
  IO.FS.removeFile (← entryPath name)

/-- The ID a new session under `name` takes: the one `name` leads to (`Names.resolve`), or, when
it leads nowhere because a renamed session holds the name's own ID, a fresh one (`mint`), given
an entry (`create`, `Names.claim_fresh`). A start or a rename that places the name first wins,
and then the name leads to that one's session. -/
def claim (name : String) : IO Ref := do
  let table ← load
  if let some id := Linger.Session.Names.resolve table name then
    return { name, id }
  let id ← mint
  if ← create name id then
    -- the entry placed, the name leads where `Names.claim` says: to the fresh ID (`claim_fresh`)
    if let some id :=
        Linger.Session.Names.resolve (Linger.Session.Names.claim table name id) name then
      return { name, id }
  match ← resolve name with
  | some other =>
    return { name, id := other }
  | none =>
    throw (IO.userError s!"session '{name}' could not be given an ID")

/-- Run `action` holding the names lock, `names/.lock`, which every rename and every removal of
an entry holds; one held by another rename is tried again for up to a second. Its holder deletes
the lock file as it lets it go, since it names no session (`Os.Shell.unlinkHeld`), and the next
holder creates it again (`Os.Shell.flock`). -/
def withLock {α : Type} (action : IO α) : IO α := do
  let dir ← namesDir
  Paths.ensureDir dir
  let path := s!"{dir}/.lock"
  let deadline := (← Os.Shell.monotonicMs) + 1000
  let mut fd ← Os.Shell.flock path
  while fd < 0 do
    unless ← Os.Shell.nap deadline 10 do
      break
    fd ← Os.Shell.flock path
  if fd < 0 then
    throw (IO.userError "the names are being changed by another rename")
  let held := fd.toUInt64.toUInt32
  try
    action
  finally
    -- the names lock names no session: its holder deletes it as it lets it go (`locks_named`)
    try
      Os.Shell.unlinkHeld held path
    finally
      Os.Shell.close held

end Linger.Session.Shell.Names
