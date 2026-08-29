module

public import Linger.Core.Checkpoint
public import Linger.Core.Session
public import Linger.Runtime.Paths
public import Linger.Runtime.Cli

public section

/-! # Linger.Runtime.Resume — checkpoint hooks (the continuum shape)

The daemon decides *when* (60s cadence while dirty, last-detach,
drop-on-clean-exit — all in the pure machine); this module is the
*what*: serialize `Ckpt` via the proven codec, write atomically
(tmp + rename — a torn write is unloadable by §Restore's totality and
simply ignored), read it back on resume.
-/

namespace Linger.Runtime.Resume

open Linger.Core.Checkpoint (Ckpt save load)
open Linger.Core.Session (State)

def saveCkpt (name : String) (st : State) : IO Unit := do
  let path ← Paths.ckptPath name
  -- live cwd beats the recorded start_dir: resume should reopen where
  -- the user actually was
  let pid := (st.metaKv.find? (·.1 == "pid")).map (·.2) |>.getD ""
  let cwd ← match pid.toNat? with
    | some p => do
      let c ← Linger.Posix.getcwdOf (UInt32.ofNat p)
      pure (if c.isEmpty then (st.metaKv.find? (·.1 == "start_dir")).map (·.2) |>.getD "" else c)
    | none => pure ((st.metaKv.find? (·.1 == "start_dir")).map (·.2) |>.getD "")
  let ck : Ckpt := { vt := st.vt, cwd, labels := st.labels }
  let bytes := ByteArray.mk (save ck).toArray
  let tmp := path ++ ".tmp"
  IO.FS.writeBinFile tmp bytes
  IO.FS.rename tmp path

def dropCkpt (name : String) : IO Unit := do
  try IO.FS.removeFile (← Paths.ckptPath name) catch _ => pure ()

def loadCkpt (name : String) :
    IO (Option (Linger.Core.Vt.Vt × String × List (String × String))) := do
  let path ← Paths.ckptPath name
  let bytes ← try IO.FS.readBinFile path catch _ => return none
  match load bytes.toList with
  | some ck => return some (ck.vt, ck.cwd, ck.labels)
  | none => return none  -- torn/corrupt/foreign: start fresh (§Restore totality)

def hooks : Cli.Hooks := { save := saveCkpt, drop := dropCkpt, load := loadCkpt }

end Linger.Runtime.Resume
