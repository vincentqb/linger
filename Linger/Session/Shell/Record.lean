module

public import Linger.Session.Record
public import Linger.Session.Shell.Paths

public section

/-! # Linger.Session.Shell.Record — a name's end record on disk

The record is `Paths.recordPath`, replaced whole through a temporary sibling, as checkpoints
are. Only the daemon that holds the name writes it. A reader needs the name only to read a
running record (`Record.settled`): one it reads while holding the name is one whose daemon gave
the name up without saying how its program ended. -/

namespace Linger.Session.Shell.Record

/-- Replace the name's end record with `record`, whole. -/
def save (name : String) (record : Linger.Session.Record) : IO Unit := do
  let path ← Paths.recordPath name
  let tmp := path ++ ".tmp"
  IO.FS.writeBinFile tmp (ByteArray.mk (Linger.Session.Record.encode record).toArray)
  IO.FS.rename tmp path

/-- The bytes of the end record at `path`, or `none` when there is none. -/
private def loadAt (path : String) : IO (Option (List UInt8)) := do
  if !(← System.FilePath.pathExists path) then
    return none
  return some (← IO.FS.readBinFile path).toList

/-- The bytes of the name's end record, or `none` when there is none because no session has
taken the name. A record that exists but cannot be read throws. -/
def load (name : String) : IO (Option (List UInt8)) := do
  loadAt (← Paths.recordPath name)

/-- `load` for a session a listing named. -/
def loadListed (n : Paths.Listed) : IO (Option (List UInt8)) := do
  loadAt (← n.recordPath)

/-- Put back bytes `load` gave, whole, or remove the record when it gave none: what a session
whose program never started leaves. -/
def restore (name : String) (previous : Option (List UInt8)) : IO Unit := do
  let path ← Paths.recordPath name
  match previous with
  | some bytes =>
    let tmp := path ++ ".tmp"
    IO.FS.writeBinFile tmp (ByteArray.mk bytes.toArray)
    IO.FS.rename tmp path
  | none =>
    if ← System.FilePath.pathExists path then
      IO.FS.removeFile path

end Linger.Session.Shell.Record
