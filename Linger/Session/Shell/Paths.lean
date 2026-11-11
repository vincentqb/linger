module

import Linger.Session.Claim
import Os.Shell
import Linger.Target.Name
import Linger.Target.Spec

public section

/-! # Linger.Session.Shell.Paths — where sockets, checkpoints and logs live

Resolution order:
* sockets: `$LINGER_DIR` > `$XDG_RUNTIME_DIR/linger` > `/tmp/linger-$UID`
* state: `$LINGER_DIR` > `$XDG_STATE_HOME/linger/<host>` >
  `$HOME/.local/state/linger/<host>` > `/tmp/linger-$UID/state/<host>`

Empty XDG and HOME values fall through to the next fallback. `LINGER_DIR`
is an explicit override even when empty. The last fallback is `/tmp`, not `$TMPDIR`:
like tmux's `/tmp/tmux-$UID`, it is a short, stable location that every login context
of the same user agrees on, and `LINGER_DIR` overrides it.

Every name must already equal `Name.sanitize` before touching a path.
Invalid input is rejected, never converted into another session's name.
-/

namespace Linger.Session.Shell.Paths

open Linger.Target.Name (sanitize)

/-- Sockets and their name locks: `$LINGER_DIR` verbatim, else `$XDG_RUNTIME_DIR/linger`
when that is nonempty, else `/tmp/linger-$UID`. -/
def socketDir : IO String := do
  if let some d← IO.getEnv "LINGER_DIR" then
    return d
  if let some d← IO.getEnv "XDG_RUNTIME_DIR" then
    unless d.isEmpty do
      return s!"{d}/linger"
  return s!"/tmp/linger-{← Os.Shell.getuid}"

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
  let host := sanitize (← Os.Shell.gethostname)
  if let some d← IO.getEnv "XDG_STATE_HOME" then
    unless d.isEmpty do
      return s!"{d}/linger/{host}"
  if let some home← IO.getEnv "HOME" then
    unless home.isEmpty do
      return s!"{home}/.local/state/linger/{host}"
  return s!"/tmp/linger-{← Os.Shell.getuid}/state/{host}"

/-- Create `d` and any missing parents, then restrict `d` itself to its owner (0700). -/
def ensureDir (d : String) : IO Unit := do
  IO.FS.createDirAll d
  Os.Shell.chmod d 0o700

/-- The accepted name alphabet, as every diagnostic and help text states it. -/
def nameRule : String :=
  s!"1–{Linger.Target.Name.maxLen} ASCII letters, digits, -_.+; no leading dot"

/-- Return `name` unchanged when `Name.check` accepts it, and throw with `nameRule`
otherwise; a name is never rewritten into another. -/
private def checkName (name : String) : IO String := do
  match Linger.Target.Name.check name with
  | some name =>
    return name
  | none =>
    throw (IO.userError s!"invalid session name (use {nameRule})")

/-- `s` with the case of each ASCII letter swapped. -/
private def swapCase (s : String) : String :=
  s.map fun c => if c.isLower then c.toUpper else if c.isUpper then c.toLower else c

/-- On a case-insensitive filesystem, a different spelling must not open an
existing session. Check again after creating/locking or connecting to a path. A directory
that tells case apart has no entry under the swapped spelling, because linger writes only
lower-case suffixes, so there the existing entry is the exact spelling and two lookups
settle it; only a directory that finds the swapped spelling is listed. -/
def checkSpelling (path : String) : IO Unit := do
  let p := System.FilePath.mk path
  if ← p.pathExists then
    let dir := p.parent.getD "."
    let some file := p.fileName | return
    if ← (dir / swapCase file).pathExists then
      let entries ← dir.readDir
      unless entries.any (fun entry => entry.fileName == file) do
        throw (IO.userError "session name differs from an existing filename's spelling")

/-- A session name as a directory listing spells it, which is the spelling on disk, so its
paths need no `checkSpelling`. Only `listSocketNames` and `listCkptNames` make one. -/
structure Listed where private mk ::
  /-- The name, spelled as on disk. -/
  name : String

/-- `dir/<name><suffix>`. A name a listing read is taken as spelled, in the directory the listing
made sure of (`listNames`), so its paths cost no system call; any other must pass `checkName`,
and then `checkSpelling` after `ensureDir` creates `dir`. -/
private def pathIn (dir name suffix : String) (listed : Bool) : IO String := do
  if listed then
    return s!"{dir}/{name}{suffix}"
  let name ← checkName name
  ensureDir dir
  let path := s!"{dir}/{name}{suffix}"
  checkSpelling path
  return path

/-- `dir/<name><suffix>` once `checkName` accepts `name`, after creating `dir` with
`ensureDir` and rejecting an existing entry spelled differently (`checkSpelling`). -/
private def namedPath (dir name suffix : String) : IO String := pathIn dir name suffix false

/-- The session's socket, `<name>.sock` in `socketDir`. -/
def socketPath (name : String) : IO String := do
  namedPath (← socketDir) name ".sock"

/-- The session's checkpoint, `<name>.ckpt` in `stateDir`. -/
def ckptPath (name : String) : IO String := do
  namedPath (← stateDir) name ".ckpt"

/-- The name's end record (`Linger.Session.Record`), `<name>.end` in `stateDir`. -/
def recordPath (name : String) : IO String := do
  namedPath (← stateDir) name ".end"

/-- Name-ownership lock (see `Os.Shell.flock`). Lives beside the
socket: same directory lifetime, same 0700 permissions. Never
unlinked — a lock file that gets unlinked stops being a lock. -/
def lockPath (name : String) : IO String := do
  namedPath (← socketDir) name ".lock"

/-- Persistent checkpoint ownership, independent of the runtime directory.
Keep these lock inodes across daemon exits and reboots; never unlink them. -/
private def stateLockPath (name : String) : IO String := do
  namedPath ((← stateDir) ++ "/.locks") name ".lock"

/-- The daemon's output log, `logs/<name>.log` in `stateDir`. -/
def logPath (name : String) : IO String := do
  namedPath ((← stateDir) ++ "/logs") name ".log"

/-- Where the daemon a `start` began tells it what it did, `logs/<name>.start-<nonce>` in
`stateDir`: a name each `start` makes its own with `nonce`. -/
def startReportPath (name nonce : String) : IO String := do
  namedPath ((← stateDir) ++ "/logs") name s!".start-{nonce}"

/-- The socket of a session a listing named. -/
def Listed.socketPath (n : Listed) : IO String := do
  pathIn (← socketDir) n.name ".sock" true

/-- The end record of a session a listing named. -/
def Listed.recordPath (n : Listed) : IO String := do
  pathIn (← stateDir) n.name ".end" true

/-- The lock at `path`: its descriptor, or `none` when another process holds it. A held lock
is tried again while `retry`, asked only after a failed attempt, holds. Recheck spelling after
the atomic acquisition unless a listing read the name, letting the lock go when that fails. -/
private def acquire (path : String) (retry : IO Bool) (listed : Bool) : IO (Option UInt32) := do
  let mut fd ← Os.Shell.flock path
  while fd < 0 do
    unless ← retry do
      break
    fd ← Os.Shell.flock path
  if fd < 0 then
    return none
  let held := fd.toUInt64.toUInt32
  unless listed do
    try
      checkSpelling path
    catch err =>
      Os.Shell.close held
      throw err
  return some held

/-- Failed acquisition does not run the action. Always release after the action, including
startup/read exceptions. -/
private def withLockRetrying {α : Type} (path : String) (retry : IO Bool) (action : IO α)
    (listed : Bool := false) : IO α := do
  let some fd ←
    acquire path retry
        listed | throw (IO.userError s!"session is owned by another process ({path})")
  try
    action
  finally
    Os.Shell.close fd

/-- Act as the session's owner: take the socket lock at `socket`, then the checkpoint lock at
the path `checkpoint` gives, and run `action` only when `Claim.enters` says a process holding
them may, which `Claim.Reachable` models. Both locks are let go after the action, in reverse
order, whatever it does; the checkpoint lock is tried only once the socket lock is taken. -/
private def withOwnership {α : Type} (socket : String) (checkpoint : IO String) (retry : IO Bool)
    (listed : Bool) (action : IO α) : IO α := do
  let held ← acquire socket retry listed
  try
    let (state, refused) ←
      match held with
      | none =>
        pure (none, socket)
      | some _ =>
        do
          let path ← checkpoint
          pure (← acquire path retry listed, path)
    try
      unless Claim.enters held.isSome state.isSome do
        throw (IO.userError s!"session is owned by another process ({refused})")
      action
    finally
      if let some fd := state then
        Os.Shell.close fd
  finally
    if let some fd := held then
      Os.Shell.close fd

/-- One attempt: a held lock fails at once. Only a starting daemon retries. -/
def withLock {α : Type} (path : String) (action : IO α) : IO α :=
  withLockRetrying path (pure false) action

/-- All daemon lifetimes and offline reads take both locks in the same order.
Either shared socket storage or shared checkpoint storage excludes another owner.
`retry` applies to both acquisitions. -/
def withSessionLockRetrying {α : Type} (name : String) (retry : IO Bool) (action : IO α) : IO α :=
  do
  withOwnership (← lockPath name) (stateLockPath name) retry false action

/-- Both locks, one attempt each: every offline reader. -/
def withSessionLock {α : Type} (name : String) (action : IO α) : IO α :=
  withSessionLockRetrying name (pure false) action

/-- The name lock of a session a listing named, without retrying. -/
def Listed.withLock {α : Type} (n : Listed) (action : IO α) : IO α := do
  withLockRetrying (← pathIn (← socketDir) n.name ".lock" true) (pure false) action (listed := true)

/-- `withSessionLock` for a session a listing named. A listing makes sure of the directories it
reads, not of the persistent lock directory, so this does. -/
def Listed.withSessionLock {α : Type} (n : Listed) (action : IO α) : IO α := do
  withOwnership (← pathIn (← socketDir) n.name ".lock" true)
      (do
        let locks := (← stateDir) ++ "/.locks"
        ensureDir locks
        pathIn locks n.name ".lock" true)
      (pure false) true action

/-- Valid session names among `dir`'s entries ending in `suffix`, as the directory spells them. -/
private def listNames (dir suffix : String) : IO (List Listed) := do
  ensureDir dir
  return (← System.FilePath.readDir dir).toList.filterMap fun e =>
      ((e.fileName.dropSuffix? suffix).bind (Linger.Target.Name.check ·.toString)).map (⟨·⟩)

/-- Session names present as sockets, live or stale. -/
def listSocketNames : IO (List Listed) := do
  listNames (← socketDir) ".sock"

/-- Checkpoint names (resumable sessions after a reboot). -/
def listCkptNames : IO (List Listed) := do
  listNames (← stateDir) ".ckpt"

end Linger.Session.Shell.Paths
