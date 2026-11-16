module

public import Linger.Os.CoreSpec
public import Linger.Session.CoreSpec
import Linger.Import.CoreCode.Resurrect
import Linger.Session.CoreCode.Checkpoint
import Os.WorldCode
import Linger.Display.CoreCode.View
import Linger.Session.WorldCode.Paths
import Linger.Session.WorldCode.Names
import Linger.Session.WorldCode.Resume
import Linger.Session.WorldCode.Record
import Linger.Session.WorldCode.Inventory
import Os.WorldCode.Command
import Std.Async.System

public section

/-! # Linger.Import.Shell — the latest tmux-resurrect save, read in place

A tmux-resurrect save is a source linger reads and never writes: nothing here creates, moves or
deletes a file in tmux's directory. Its panes are listed while linger keeps no record of their
names (`Resurrect.listed`), an attach or a resume of one writes its checkpoint where no record is
(`Resurrect.adopt`), and a kill of one writes the end record a kill leaves (`Resurrect.dismiss`),
each decided holding the name's locks; the rest of linger then treats the name as any other. An
export writes the sessions' names and directories as a save, to standard output only. -/

namespace Linger.Import.Shell

open Linger.Session.Shell
open Linger.Import.Resurrect
open Os.Shell

/-- Resolve existing relative path components physically, retaining a missing
suffix for directories linger will create. Resolve symlinks before `..`. -/
private def resolveRelative (origin : System.FilePath) (path : String) : IO String := do
  if (System.FilePath.mk path).isAbsolute then
    return path
  let mut resolved := origin
  for part in path.splitOn "/" do
    if part.isEmpty then
      continue
    let next := resolved / part
    match ← (IO.FS.realPath next).toBaseIO with
    | .ok physical =>
      resolved := physical
    | .error (.noFileOrDirectory ..) =>
      resolved := next
    | .error error =>
      throw error
  return resolved.toString

/-- The invocation's directory and the home directory a save's `~` stands for: `HOME`, resolved
from the invocation's directory, or the account's when `HOME` is unset or empty. -/
private def context : IO (System.FilePath × String) := do
  let origin ← IO.currentDir
  match (← IO.getEnv "HOME").filter (!·.isEmpty) with
  | some value =>
    return (origin, ← resolveRelative origin value)
  | none =>
    -- Read the account record directly: shell expansion of ~ with HOME absent
    -- is not portable, and getHomeDir may still observe an empty HOME.
    match (← Std.Async.System.getCurrentUser).homeDir.filter (·.isAbsolute) with
    | some home =>
      return (origin, home.toString)
    | none =>
      throw (IO.userError "could not determine the account home directory")

/-- Query an existing server only. A missing tmux or server leaves default
discovery available. Poll for one second, then force-retire the owned process group. -/
private def configuredDirectory : IO (Option String) := do
  let pending ← IO.mkRef (none : Option Command.Job)
  try
    let job ←
      try
        Command.start "tmux" #["show-options", "-gqv", "@resurrect-dir"]
      catch
      | .noFileOrDirectory .. =>
        return none
      | error =>
        throw error
    pending.set (some job)
    let deadline := (← Os.Shell.monotonicMs) + 1000
    repeat
      if let some output← Command.poll pending then
        if output.exitCode != 0 then
          return none
        let dir := (output.stdout.dropSuffix "\n").toString
        return if dir.isEmpty then none else some dir
      unless ← Os.Shell.nap deadline 10 do
        break
    throw (IO.userError "tmux configuration query timed out")
  finally
    Command.stop pending

/-- Where the latest save is, as tmux-resurrect keeps it: `last` in tmux's effective
`@resurrect-dir`, asked of a running server without evaluating configuration files, else in the
legacy `~/.tmux/resurrect`, when that has one, else in `$XDG_DATA_HOME/tmux/resurrect`. -/
private def savePath (origin : System.FilePath) (home : String) : IO System.FilePath := do
  let path ←
    if let some dir← configuredDirectory then
      let dir :=
        if dir == "~" then home
        else if dir.startsWith "~/" then home ++ (dir.drop 1).toString else dir
      pure (System.FilePath.mk dir / "last").toString
    else
      let legacy := System.FilePath.mk s!"{home}/.tmux/resurrect/last"
      if ← legacy.pathExists then
        pure legacy.toString
      else
        let data := (← IO.getEnv "XDG_DATA_HOME").filter (!·.isEmpty)
        pure
            (System.FilePath.mk (data.getD s!"{home}/.local/share") /
                "tmux/resurrect/last").toString
  let path := System.FilePath.mk path
  return if path.isAbsolute then path else origin / path

/-- A save as read: the physical path of its file and its panes. -/
private structure Save where
  path : System.FilePath
  panes : List Pane

/-- Read and validate the latest save, `none` when there is none. Relative saved directories are
taken from the invocation's directory. -/
private def readSave (origin : System.FilePath) (home : String) : IO (Option Save) := do
  let save ← savePath origin home
  let metadata ← save.metadata.toBaseIO
  unless metadata.toOption.any (·.type == .file) do
    return none
  let path ← IO.FS.realPath save
  let content ← IO.FS.readFile path
  let panes ← IO.ofExcept (parseSave home content)
  let panes :=
    panes.map fun pane =>
      if pane.dir.isEmpty || (System.FilePath.mk pane.dir).isAbsolute then pane
      else { pane with dir := (origin / pane.dir).toString }
  return some { path, panes := panes.map (preparePane content panes) }

/-- A capture archive belongs only to the save reached by the adjacent `last`, as it stood when
it was read: its physical path, modification time, size and members. -/
private structure Archive where
  path : System.FilePath
  save : System.FilePath
  modified : IO.FS.SystemTime
  byteSize : UInt64
  members : List String

private def latestSave (save : System.FilePath) : IO Bool := do
  let last := save.parent.getD "." / "last"
  try
    return (← IO.FS.realPath last) == save
  catch
  | .noFileOrDirectory .. =>
    return false
  | error =>
    throw error

/-- No archive extraction writes files. Both tar operations stream bounded output
through an owned process group, with a five-second deadline and unconditional cleanup. -/
private def archiveOutput (args : Array String) (limit : Nat) : IO String := do
  let pending ← IO.mkRef (none : Option Command.Job)
  try
    pending.set (some (← Command.startLimited "tar" args limit))
    let deadline := (← Os.Shell.monotonicMs) + 5000
    repeat
      if let some output← Command.poll pending then
        unless output.exitCode == 0 do
          throw (IO.userError s!"could not read pane capture archive: {output.stderr}")
        return output.stdout
      unless ← Os.Shell.nap deadline 10 do
        break
    throw (IO.userError "pane capture archive timed out")
  finally
    Command.stop pending

private def checkArchive (archive : Archive) : IO Unit := do
  let metadata ← archive.path.metadata
  unless
    metadata.type == .file && metadata.modified == archive.modified &&
      metadata.byteSize == archive.byteSize &&
      (← latestSave archive.save) do
    throw (IO.userError "pane capture archive changed; refresh the saved panes")

private def readArchive (save : System.FilePath) : IO (Option Archive) := do
  unless ← latestSave save do
    return none
  let path := save.parent.getD "." / "pane_contents.tar.gz"
  let metadata ←
    try
      path.metadata
    catch
    | .noFileOrDirectory .. =>
      return none
    | error =>
      throw error
  unless metadata.type == .file && metadata.byteSize.toNat ≤ 64 * 1024 * 1024 do
    throw (IO.userError "pane capture archive is not a file of at most 64 MiB")
  let path ← IO.FS.realPath path
  let text ← archiveOutput #["-tzf", path.toString] (1024 * 1024)
  let archive : Archive :=
    { path, save, modified := metadata.modified, byteSize := metadata.byteSize,
      members := text.splitOn "\n" |>.filter (!·.isEmpty) }
  checkArchive archive
  return some archive

private def capturedPane (archive : Option Archive) (pane : Pane) : IO (Option String) := do
  let some archive := archive | return none
  let some member := contentMember pane
    | throw (IO.userError "invalid pane capture identity")
  checkArchive archive
  match archive.members.filter (· == member) with
  | [] =>
    return none
  | [_] =>
    let text ← archiveOutput #["-xOzf", archive.path.toString, "--", member] captureLimit
    checkArchive archive
    return some text
  | _ =>
    throw (IO.userError s!"duplicate pane capture: {pane.name}")

/-- What linger keeps of `name`: an entry of the names directory that names it or leads to it,
and, since with no entry a name keys its session's files itself (`Names.resolve`), its socket,
its checkpoint and its end record, each present or not. A caller that decides from it holds the
name's locks. -/
private def recordsOf (name : String) : IO Linger.Session.Records := do
  let has := fun (path : String) => System.FilePath.pathExists path
  let only := fun (present : Bool) => if present then [name] else []
  let table ← Names.load
  return { sockets := only (← has (← Paths.socketPath name)),
           checkpoints := only (← has (← Paths.ckptPath name)),
           endings := only (← has (← Paths.recordPath name)),
           entries := only (table.any fun (entry, id) => entry == name || id == name) }

/-- The latest save's file and panes, `none` when there is no save, or when it cannot be read or
does not parse, which this says on standard error: what linger does with its own sessions never
depends on a foreign save. -/
private def latest : IO (Option (System.FilePath × List Pane)) := do
  let read : IO (Option (System.FilePath × List Pane)) := do
    let (origin, home) ← context
    return (← readSave origin home).map fun save => (save.path, save.panes)
  match ← read.toBaseIO with
  | .ok found =>
    return found
  | .error error =>
    IO.eprintln s!"linger: could not read the tmux-resurrect save: {diagnostic (toString error)}"
    return none

/-- The listing rows of the latest save's panes that `records` does not name
(`Resurrect.listed`), in name order (`View.byName`), each marked with its source
(`Resurrect.sourceRow`). No save, or one that cannot be read, lists none. -/
def sourceRows (records : Linger.Session.Records) : IO (List (List (String × String))) := do
  let some (_, panes) ← latest | return []
  return (Linger.Display.View.byName (·.name) (listed records panes)).map sourceRow

/-- The latest save's pane named `name`, if any. -/
private def paneNamed (name : String) : IO (Option Pane) := do
  return (← latest).bind fun (_, panes) => panes.find? (·.name == name)

/-- The listing row of the latest save's pane `name`, while no record names it. -/
def sourceRow? (name : String) : IO (Option (List (String × String))) := do
  let some pane ← paneNamed name | return none
  if (← recordsOf name).holds name then
    return none
  return some (sourceRow pane)

/-- What an attach or a resume of a name did with the latest save's pane of that name. -/
inductive Adopted where
  /-- The save has no pane of the name, or a record names it, so the save was not read. -/
  | none
  /-- The pane's checkpoint was written, so the name is a saved session to resume. -/
  | written
  /-- A record named the pane by the time the name's locks were held, so nothing was written. -/
  | recorded

/-- An attach or a resume of `name`, when no record names it and the latest save has a pane of
that name: write the pane's checkpoint, with its captured contents, holding the name's locks, as
`Resurrect.adopt` decides from the name's records there, and only where no file is
(`Os.Shell.createFile`), so it never replaces a record. A name a record names reads no save. -/
def adopt (name : String) : IO Adopted := do
  if (← recordsOf name).holds name then
    return .none
  let some found ← latest | return .none
  let (save, panes) := found
  let some pane := panes.find? (·.name == name) | return .none
  let contents ← capturedPane (← readArchive save) pane
  Paths.withSessionLock name do
      match Linger.Import.Resurrect.adopt (← recordsOf name) pane contents with
      | none =>
        return .recorded
      | some ck =>
        if
            ←
              Os.Shell.createFile (← Paths.ckptPath name)
                  (Linger.Session.Checkpoint.saveBytes ck) then
          return .written
        return .recorded

/-- A kill of `name`, when no record names it and the latest save has a pane of that name: write
the end record a kill leaves (`Resurrect.dismissal`) and nothing else, holding the name's locks,
as `Resurrect.dismiss` models, so the pane is not listed again. `false`, writing nothing, when
the save has no such pane or a record names it by then. -/
def dismiss (name : String) : IO Bool := do
  if (← recordsOf name).holds name then
    return false
  let some _ ← paneNamed name | return false
  Paths.withSessionLock name do
      let records ← recordsOf name
      if records.holds name then
        return false
      -- the end records `dismiss` adds: the name's
      for ended in (Linger.Import.Resurrect.dismiss records name).endings do
        unless records.endings.contains ended do
          Record.save ended dismissal
      return true

/-- A failed live observation must not export a stale startup directory.
Checkpoint decoding supplies the cwd for resumable sessions. -/
private def snapshot : IO (List (String × String)) := do
  let rows ← Inventory.localRows
  rows.mapM fun row => do
      let name := (row.lookup "name").getD ""
      let dir ←
        if row.lookup "state" == some "resumable" then
          let some id ←
            Names.resolve
                name | throw (IO.userError s!"could not read checkpoint for session: {name}")
          Paths.withSessionLock id do
              let some saved := (← Resume.readCkpt id).bind Linger.Session.Checkpoint.loadBytes
                | throw (IO.userError s!"could not read checkpoint for session: {name}")
              pure saved.cwd
        else
          do
            let some pid := (row.lookup "pid").bind String.toNat?
              | throw (IO.userError s!"could not read live session: {name}")
            unless pid < UInt32.size do
              throw (IO.userError s!"invalid process id for session: {name}")
            discard <| Os.Shell.checkPid "export" pid.toUInt32
            Os.Shell.getcwdOf pid.toUInt32
      unless !dir.isEmpty && (System.FilePath.mk dir).isAbsolute do
        throw (IO.userError s!"could not read working directory for session: {name}")
      return (name, (← IO.FS.realPath dir).toString)

/-- `ls --resurrect`: the local sessions' names and directories, as `ls` lists them, written to
standard output as a tmux-resurrect save, with one window and pane a session (`renderSave`).
linger writes no file. -/
def exportSave : IO Unit := do
  IO.print (← IO.ofExcept (renderSave (← snapshot)))

end Linger.Import.Shell
