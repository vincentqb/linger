module

import Linger.Session.CoreCode.Checkpoint
public import Linger.Session.CoreCode
import Linger.Session.WorldCode.Paths
import Os.WorldCode

public section

/-! # Linger.Session.Shell.Resume — checkpoint hooks

The daemon decides *when*; this module serializes with the proven codec and replaces the file
whole and durably (`Os.Shell.replaceFile`, the world claim `Disk.Durable`), reads the file's
bytes for `Linger.App.Recovery.decide` to judge, and surfaces save, read and delete errors for
the daemon to log without exiting.
-/

namespace Linger.Session.Shell.Resume

open Linger.Session.Checkpoint (Ckpt saveBytes)
open Linger.Session (State)

/-- The checkpoint hook of one daemon: write the session's terminal state, record fields and working
directory to its checkpoint, replacing the file whole and durably (`Os.Shell.replaceFile`): a
crash leaves the previous checkpoint or this one, and this one once the hook returns. The
directory is the program's live cwd when readable; else the last one this hook read, as for the
save after the program has ended, whose directory can no longer be read; else the start
directory the daemon recorded. -/
def saver (name : String) : IO (State → IO Unit) := do
  let lastDir ← IO.mkRef ""
  return fun st => do
    let path ← Paths.ckptPath name
    -- live cwd beats the recorded start_dir: resume should reopen where
    -- the user actually was
    let live ←
      match (st.metaKv.lookup "pid").bind String.toNat? with
      | some p =>
        Os.Shell.getcwdOf (UInt32.ofNat p)
      | none =>
        pure ""
    if !live.isEmpty then
      lastDir.set live
    let known ← lastDir.get
    let cwd := if known.isEmpty then (st.metaKv.lookup "start_dir").getD "" else known
    let ck : Ckpt Terminal.Vt.Vt := { vt := st.terminal, cwd, fields := st.fieldList }
    let bytes := saveBytes ck
    Os.Shell.replaceFile path bytes

/-- Delete the session's checkpoint if it exists; a missing file is not an error. -/
def dropCkpt (name : String) : IO Unit := do
  let path ← Paths.ckptPath name
  if ← System.FilePath.pathExists path then
    IO.FS.removeFile path

/-- The bytes of the session's checkpoint, `none` when there is no file; a file that exists
and cannot be read throws. Whether the bytes decode is `Linger.App.Recovery.decide`'s to say:
bytes that do not are never taken for no file. -/
def readCkpt (name : String) : IO (Option ByteArray) := do
  let path ← Paths.ckptPath name
  if !(← System.FilePath.pathExists path) then
    return none
  try
    return some (← IO.FS.readBinFile path)
  catch err =>
    throw (IO.userError s!"checkpoint read failed for '{name}': {err}")

end Linger.Session.Shell.Resume
