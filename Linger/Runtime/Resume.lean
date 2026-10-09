module

import Linger.Core.Checkpoint
public import Linger.Core.Session
import Linger.Runtime.Paths
import Linger.Posix

public section

/-! # Linger.Runtime.Resume — checkpoint hooks

The daemon decides *when*; this module serializes with the proven codec,
writes by tmp+rename, distinguishes corrupt bytes from read failure, and
surfaces save/delete errors for the daemon to log without exiting.
-/

namespace Linger.Runtime.Resume

open Linger.Core.Checkpoint (Ckpt save load)
open Linger.Core.Session (State)

def saveCkpt (name : String) (st : State) : IO Unit := do
  let path ← Paths.ckptPath name
  -- live cwd beats the recorded start_dir: resume should reopen where
  -- the user actually was
  let live ←
    match (st.metaKv.lookup "pid").bind String.toNat? with
    | some p =>
      Linger.Posix.getcwdOf (UInt32.ofNat p)
    | none =>
      pure ""
  let cwd := if live.isEmpty then (st.metaKv.lookup "start_dir").getD "" else live
  let ck : Ckpt := { vt := st.vt, cwd, labels := st.labels }
  let bytes := ByteArray.mk (save ck).toArray
  let tmp := path ++ ".tmp"
  IO.FS.writeBinFile tmp bytes
  IO.FS.rename tmp path

def dropCkpt (name : String) : IO Unit := do
  let path ← Paths.ckptPath name
  if ← System.FilePath.pathExists path then
    IO.FS.removeFile path

def loadCkpt (name : String) : IO (Option (Linger.Core.Vt.Vt × String × List (String × String))) :=
  do
  let path ← Paths.ckptPath name
  if !(← System.FilePath.pathExists path) then
    return none
  let bytes ←
    try
      IO.FS.readBinFile path
    catch err =>
      throw (IO.userError s!"checkpoint read failed for '{name}': {err}")
  match load bytes.toList with
  | some ck =>
    return some (ck.vt, ck.cwd, ck.labels)
  | none =>
    return none -- corrupt/foreign bytes are a cache miss; I/O failure is not

end Linger.Runtime.Resume
