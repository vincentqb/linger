module

import Linger.Posix
import Linger.Core.Name

public section

/-! # Linger.Runtime.Paths — where sockets, checkpoints and logs live

Resolution order:
* sockets: `$LINGER_DIR` > `$XDG_RUNTIME_DIR/linger` > `/tmp/linger-$UID`
* state: `$LINGER_DIR` > `$XDG_STATE_HOME/linger/<host>` >
  `$HOME/.local/state/linger/<host>` > `/tmp/linger-$UID/state/<host>`

Empty XDG and HOME values fall through to the next fallback. `LINGER_DIR`
is an explicit override even when empty.

Every name must already equal `Name.sanitize` before touching a path.
Invalid input is rejected, never converted into another session's name.
-/

namespace Linger.Runtime.Paths

open Linger.Core.Name (sanitize)

def socketDir : IO String := do
  if let some d← IO.getEnv "LINGER_DIR" then
    return d
  if let some d← IO.getEnv "XDG_RUNTIME_DIR" then
    unless d.isEmpty do
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
    unless d.isEmpty do
      return s!"{d}/linger/{host}"
  if let some home← IO.getEnv "HOME" then
    unless home.isEmpty do
      return s!"{home}/.local/state/linger/{host}"
  return s!"/tmp/linger-{← Linger.Posix.getuid}/state/{host}"

def ensureDir (d : String) : IO Unit := do
  IO.FS.createDirAll d
  Linger.Posix.chmod d 0o700

/-- The accepted name alphabet, as every diagnostic and help text states it. -/
def nameRule : String := s!"1–{Linger.Core.Name.maxLen} ASCII letters, digits, -_.+; no leading dot"

def checkName (name : String) : IO String := do
  match Linger.Core.Name.check name with
  | some name =>
    return name
  | none =>
    throw (IO.userError s!"invalid session name (use {nameRule})")

/-- On a case-insensitive filesystem, a different spelling must not open an
existing session. Check again after creating/locking or connecting to a path. -/
def checkSpelling (path : String) : IO Unit := do
  let p := System.FilePath.mk path
  if ← p.pathExists then
    let entries ← p.parent.getD "." |>.readDir
    unless entries.any (fun entry => some entry.fileName == p.fileName) do
      throw (IO.userError "session name differs from an existing filename's spelling")

def namedPath (dir name suffix : String) : IO String := do
  let name ← checkName name
  ensureDir dir
  let path := s!"{dir}/{name}{suffix}"
  checkSpelling path
  return path

def socketPath (name : String) : IO String := do
  namedPath (← socketDir) name ".sock"

def ckptPath (name : String) : IO String := do
  namedPath (← stateDir) name ".ckpt"

/-- Name-ownership lock (see `Linger.Posix.flock`). Lives beside the
socket: same directory lifetime, same 0700 permissions. Never
unlinked — a lock file that gets unlinked stops being a lock. -/
def lockPath (name : String) : IO String := do
  namedPath (← socketDir) name ".lock"

/-- Persistent checkpoint ownership, independent of the runtime directory.
Keep these lock inodes across daemon exits and reboots; never unlink them. -/
def stateLockPath (name : String) : IO String := do
  namedPath ((← stateDir) ++ "/.locks") name ".lock"

def logPath (name : String) : IO String := do
  namedPath ((← stateDir) ++ "/logs") name ".log"

/-- Failed acquisition does not run the action. Always release after the action,
including startup/read exceptions; recheck spelling after the atomic acquisition. -/
def withLock {α : Type} (path : String) (action : IO α) : IO α := do
  let fd ← Linger.Posix.flock path
  if fd < 0 then
    throw (IO.userError s!"session is owned by another process ({path})")
  try
    checkSpelling path
    action
  finally
    Linger.Posix.close fd.toUInt64.toUInt32

/-- All daemon lifetimes and offline reads take both locks in the same order.
Either shared socket storage or shared checkpoint storage excludes another owner. -/
def withSessionLock {α : Type} (name : String) (action : IO α) : IO α := do
  withLock (← lockPath name) do
      withLock (← stateLockPath name) action

/-- Valid session names among `dir`'s entries ending in `suffix`. -/
private def listNames (dir suffix : String) : IO (List String) := do
  ensureDir dir
  return (← System.FilePath.readDir dir).toList.filterMap fun e =>
      (e.fileName.dropSuffix? suffix).bind (Linger.Core.Name.check ·.toString)

/-- Session names present as sockets, live or stale. -/
def listSocketNames : IO (List String) := do
  listNames (← socketDir) ".sock"

/-- Checkpoint names (resumable sessions after a reboot). -/
def listCkptNames : IO (List String) := do
  listNames (← stateDir) ".ckpt"

end Linger.Runtime.Paths
