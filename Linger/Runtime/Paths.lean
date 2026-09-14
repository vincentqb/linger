module

public import Linger.Posix
public import Linger.Core.Name

public section

/-! # Linger.Runtime.Paths — where sockets, checkpoints and logs live

Resolution order:
* sockets: `$LINGER_DIR` > `$XDG_RUNTIME_DIR/linger` > `/tmp/linger-$UID`
* state (checkpoints, logs): `$LINGER_DIR` > `$XDG_STATE_HOME/linger` >
  `~/.local/state/linger`

Every name passes `Name.sanitize` before touching a path (AGENTS.md
rule; §Name is the theorem that makes it sufficient).
-/

namespace Linger.Runtime.Paths

open Linger.Core.Name (sanitize)

def socketDir : IO String := do
  if let some d← IO.getEnv "LINGER_DIR" then
    return d
  if let some d← IO.getEnv "XDG_RUNTIME_DIR" then
    return s!"{d}/linger"
  return s!"/tmp/linger-{← Linger.Posix.getuid}"

/-- Checkpoints and logs. The default is namespaced by hostname: a
network-mounted `$HOME` is shared between machines, and two hosts each
running a session called `work` would otherwise clobber one another's
checkpoint — and resuming machine B's terminal on machine A is wrong
anyway (different working tree, different process world). An explicit
`LINGER_DIR` is taken verbatim: an override is an instruction, not an
accident. -/
def stateDir : IO String := do
  if let some d← IO.getEnv "LINGER_DIR" then
    return d
  let host := sanitize (← Linger.Posix.gethostname)
  if let some d← IO.getEnv "XDG_STATE_HOME" then
    return s!"{d}/linger/{host}"
  let home := (← IO.getEnv "HOME").getD "/tmp"
  return s!"{home}/.local/state/linger/{host}"

def ensureDir (d : String) : IO Unit := do
  IO.FS.createDirAll d
  Linger.Posix.chmod d 0o700

def socketPath (name : String) : IO String := do
  let d ← socketDir
  ensureDir d
  return s!"{d}/{sanitize name}.sock"

def ckptPath (name : String) : IO String := do
  let d ← stateDir
  ensureDir d
  return s!"{d}/{sanitize name}.ckpt"

/-- Name-ownership lock (see `Linger.Posix.flock`). Lives beside the
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
  return entries.toList.filterMap
      (fun e =>
        let n := e.fileName
        if n.endsWith ".sock" then some ((n.dropEnd 5).toString) else none)

/-- Checkpoint names (resumable sessions after a reboot). -/
def listCkptNames : IO (List String) := do
  let d ← stateDir
  ensureDir d
  let entries ← System.FilePath.readDir d
  return entries.toList.filterMap
      (fun e =>
        let n := e.fileName
        if n.endsWith ".ckpt" then some ((n.dropEnd 5).toString) else none)

end Linger.Runtime.Paths
