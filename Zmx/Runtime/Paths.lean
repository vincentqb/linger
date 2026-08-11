import Zmx.Posix
import Zmx.Core.Name
/-! # Zmx.Runtime.Paths — where sockets, checkpoints and logs live

Same resolution order as zmx:
* sockets: `$LZMX_DIR` > `$XDG_RUNTIME_DIR/lzmx` > `/tmp/lzmx-$UID`
* state (checkpoints, logs): `$LZMX_DIR` > `$XDG_STATE_HOME/lzmx` >
  `~/.local/state/lzmx`

Every name passes `Name.sanitize` before touching a path (AGENTS.md
rule; §Name is the theorem that makes it sufficient).
-/

namespace Zmx.Runtime.Paths

open Zmx.Core.Name (sanitize)

def socketDir : IO String := do
  if let some d ← IO.getEnv "LZMX_DIR" then return d
  if let some d ← IO.getEnv "XDG_RUNTIME_DIR" then return s!"{d}/lzmx"
  return s!"/tmp/lzmx-{← Zmx.Posix.getuid}"

def stateDir : IO String := do
  if let some d ← IO.getEnv "LZMX_DIR" then return d
  if let some d ← IO.getEnv "XDG_STATE_HOME" then return s!"{d}/lzmx"
  let home := (← IO.getEnv "HOME").getD "/tmp"
  return s!"{home}/.local/state/lzmx"

def ensureDir (d : String) : IO Unit := do
  IO.FS.createDirAll d
  Zmx.Posix.chmod d 0o700

def socketPath (name : String) : IO String := do
  let d ← socketDir
  ensureDir d
  return s!"{d}/{sanitize name}.sock"

def ckptPath (name : String) : IO String := do
  let d ← stateDir
  ensureDir d
  return s!"{d}/{sanitize name}.ckpt"

/-- Name-ownership lock (see `Zmx.Posix.flock`). Lives beside the
socket: same directory lifetime, same 0700 permissions. Never
unlinked — a lock file that gets unlinked stops being a lock. -/
def lockPath (name : String) : IO String := do
  let d ← socketDir
  ensureDir d
  return s!"{d}/{sanitize name}.lock"

def logPath (name : String) : IO String := do
  let d := (← stateDir) ++ "/logs"
  ensureDir d
  return s!"{d}/{sanitize name}.log"

/-- Session names present as sockets, live or stale. -/
def listSocketNames : IO (List String) := do
  let d ← socketDir
  ensureDir d
  let entries ← System.FilePath.readDir d
  return entries.toList.filterMap (fun e =>
    let n := e.fileName
    if n.endsWith ".sock" then some ((n.dropEnd 5).toString) else none)

/-- Checkpoint names (resumable sessions after a reboot). -/
def listCkptNames : IO (List String) := do
  let d ← stateDir
  ensureDir d
  let entries ← System.FilePath.readDir d
  return entries.toList.filterMap (fun e =>
    let n := e.fileName
    if n.endsWith ".ckpt" then some ((n.dropEnd 5).toString) else none)

end Zmx.Runtime.Paths
