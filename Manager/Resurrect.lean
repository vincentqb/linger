module

public import Tools.Resurrect
public import Linger.Core.Remote
public import Linger.Runtime.Resume
public import Manager.Picker
public import Std.Async.System
public import Lean.Data.Json

public section

/-! tmux-resurrect interchange. Pure parsing and export policy live in
`Tools.Resurrect`. This boundary creates sessions in imported directories and
publishes current native names and directories atomically. -/

namespace Manager.Resurrect

open Tools.Resurrect
open Linger.Runtime

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

/-- Check every directory before the first session creation. Core IO provides
the access check; the import command has no concurrent cwd-changing tasks. -/
private def preflight (origin : System.FilePath) (panes : List Pane) : IO Unit := do
  for pane in panes do
    unless ← (System.FilePath.mk pane.dir).isDir do
      throw (IO.userError s!"working directory not found at line {pane.line}: {pane.dir}")
    try
      IO.Process.setCurrentDir pane.dir
    catch _ =>
      throw (IO.userError s!"working directory not accessible at line {pane.line}: {pane.dir}")
    finally
      IO.Process.setCurrentDir origin

/-- Freeze physical home and state paths for import children.
These commands have no concurrent environment users.
Restore the caller's environment even when a subprocess fails. -/
private def inContext {α : Type}
    (action : System.FilePath → String → Array (String × Option String) → IO α) : IO α := do
  let origin ← IO.currentDir
  let home ←
    match (← IO.getEnv "HOME").filter (!·.isEmpty) with
    | some value =>
      resolveRelative origin value
    | none =>
      -- Read the account record directly: shell expansion of ~ with HOME absent
      -- is not portable, and getHomeDir may still observe an empty HOME.
      match (← Std.Async.System.getCurrentUser).homeDir.filter (·.isAbsolute) with
      | some home =>
        pure home.toString
      | none =>
        throw (IO.userError "could not determine the account home directory")
  let mut env : Array (String × Option String) := #[("HOME", some home)]
  for key in ["LINGER_DIR", "XDG_RUNTIME_DIR", "XDG_STATE_HOME"] do
    if let some value← IO.getEnv key then
      if key == "LINGER_DIR" || !value.isEmpty then
        env := env.push (key, some (← resolveRelative origin value))
  let previous ← env.mapM fun (key, _) => return (key, ← IO.getEnv key)
  let set := fun (key, value) =>
    match value with
    | some value => Std.Async.System.setEnvVar key value
    | none => Std.Async.System.unsetEnvVar key
  try
    env.forM set
    action origin home env
  finally
    previous.forM set

/-- Exclusive temporary creation protects a previous file even if a stale
temporary exists. Linking publishes a complete new export without overwriting
any destination. -/
private def publish (path : System.FilePath) (content : String) : IO Unit := do
  let tmp :=
    System.FilePath.mk s!"{path}.linger-{← Linger.Posix.getpid}-{← IO.rand 0 0xFFFFFFFF}.tmp"
  let handle ← IO.FS.Handle.mk tmp .writeNew
  try
    Linger.Posix.chmod tmp.toString 0o600
    handle.putStr content
    handle.flush
    IO.FS.hardLink tmp path
  finally
    try
      IO.FS.removeFile tmp
    catch
    | .noFileOrDirectory .. =>
      pure ()
    | error =>
      throw error

/-- Query an existing server only. A missing tmux or server leaves default
discovery available. Poll for one second, then retire the owned process group;
joining it relies on the child honoring Lean core's termination signal. -/
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
    let deadline := (← Linger.Posix.monotonicMs) + 1000
    while (← Linger.Posix.monotonicMs) < deadline do
      if let some output← Command.poll pending then
        if output.exitCode != 0 then
          return none
        let dir :=
          if output.stdout.endsWith "\n" then (output.stdout.dropEnd 1).toString else output.stdout
        return if dir.isEmpty then none else some dir
      IO.sleep 10
    throw (IO.userError "tmux configuration query timed out; pass a save file explicitly")
  finally
    Command.stop pending

/-- An explicit file wins. Otherwise consult tmux's effective directory without
evaluating configuration files, then the conventional legacy and XDG locations. -/
private def savePath (origin : System.FilePath) (home : String) (file : Option String) :
    IO System.FilePath := do
  let path ←
    match file with
    | some path =>
      pure path
    | none =>
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

private structure Save where
  path : System.FilePath
  modified : String
  content : String
  panes : List Pane

/-- Read and validate a single resolved file. Relative saved directories remain
relative to the invocation, and are frozen before the picker changes anything. -/
private def readSave (origin : System.FilePath) (home : String) (file : Option String) : IO Save :=
  do
  let save ← savePath origin home file
  let metadata ← save.metadata.toBaseIO
  unless metadata.toOption.any (·.type == .file) do
    throw (IO.userError s!"save not found: {save}")
  let path ← IO.FS.realPath save
  let metadata ← path.metadata
  let content ← IO.FS.readFile path
  let panes ← IO.ofExcept (parseSave home content)
  let panes :=
    panes.map fun pane =>
      if pane.dir.isEmpty || (System.FilePath.mk pane.dir).isAbsolute then pane
      else { pane with dir := (origin / pane.dir).toString }
  let timestamp := Std.Time.Timestamp.ofSecondsSinceUnixEpoch (.ofInt metadata.modified.sec)
  let modified := (Std.Time.DateTime.ofTimestamp timestamp .UTC).toISO8601String
  return { path, modified, content, panes }

/-- Both bulk import and individual selection preflight before effects, then
skip existing identities. Only the fixed shell-starting command is executed. -/
private def createPanes (executable : String) (origin : System.FilePath)
    (env : Array (String × Option String)) (panes : List Pane) : IO Unit := do
  preflight origin panes
  let listing ← IO.Process.output { cmd := executable, args := #["ls", "--porcelain"], env }
  unless listing.exitCode == 0 do
    throw (IO.userError "could not list existing linger sessions")
  let existing := (Linger.Core.Remote.parse listing.stdout).map (·.name)
  for pane in plan existing panes do
    let created ←
      IO.Process.output
          { cmd := executable, args := #["run", pane.name, "true"],
            cwd := some (System.FilePath.mk pane.dir), env }
    unless created.exitCode == 0 do
      throw
          (IO.userError s!"could not create session: {pane.name}: {created.stdout}{created.stderr}")

private def importSave (executable : String) (file : Option String) : IO Unit :=
  inContext fun origin home env => do
    let save ← readSave origin home file
    createPanes executable origin env save.panes

private def listSave (file : Option String) (porcelain : Bool) : IO Unit :=
  inContext fun origin home _ => do
    let save ← readSave origin home file
    let rows := catalogRows save.content save.panes
    let out ← IO.getStdout
    if porcelain then
      out.putStr s!"source\t{diagnostic save.path.toString}\nsaved\t{save.modified}\n\n"
      for row in rows do
        for (key, value) in row do
          -- JSON string framing preserves control characters in action data.
          let value :=
            if key == "directory" then (Lean.Json.str value).compress else diagnostic value
          out.putStr s!"{key}\t{value}\n"
        out.putStr "\n"
    else
      out.putStr s!"tmux save · {save.modified}\n{diagnostic save.path.toString}\n\n"
      out.flush
      let withColor := (← out.isTty) && (← IO.getEnv "NO_COLOR").isNone
      Linger.Posix.writeAll Linger.Posix.stdoutFd
          (ByteArray.mk (Linger.Core.Listing.terminalListing withColor rows).toArray)

/-- Act on the selected snapshot's exact directory, never on a reread of `last`.
Resolve default discovery once per visit; the picker follows that path on refresh. -/
private def selectSave (executable : String) (file : Option String) : IO UInt32 :=
  inContext fun origin home env => do
    let path ← savePath origin home file
    while true do
      match ← Manager.Picker.choose executable true (some path.toString) with
      | .cancel =>
        return 130
      | .failed status stderr =>
        if !stderr.isEmpty then
          IO.eprint stderr
        return status
      | .attach target displayed =>
        unless displayed.candidates.contains target do
          throw (IO.userError "selected pane was absent from the displayed save")
        let row := displayed.row target
        let dir ←
          IO.ofExcept do
              let some value := row.lookup "directory"
                | throw "selected pane has no directory"
              let json ← Lean.Json.parse value
              json.getStr?
        let some line := (row.lookup "line").bind String.toNat?
          | throw (IO.userError "selected pane has no source line")
        let some pane := selectedPane target dir line
          | throw (IO.userError "invalid selected pane")
        createPanes executable origin env [pane]
        let child ←
          IO.Process.spawn
              { cmd := executable, args := #["attach", pane.name],
                cwd := some (System.FilePath.mk pane.dir), env }
        discard child.wait
    return 0

/-- A failed live observation must not export a stale startup directory.
Checkpoint decoding supplies the cwd for resumable sessions. -/
private def snapshot : IO (List (String × String)) := do
  let rows ← Cli.localRows
  rows.mapM fun row => do
      let name := Cli.kv row "name"
      let dir ←
        if Cli.kv row "state" == "resumable" then
          do
            let some (_, cwd, _) ←
              Resume.loadCkpt
                  name | throw (IO.userError s!"could not read checkpoint for session: {name}")
            pure cwd
        else
          do
            let some pid := (Cli.kv row "pid").toNat?
              | throw (IO.userError s!"could not read live session: {name}")
            unless pid < UInt32.size do
              throw (IO.userError s!"invalid process id for session: {name}")
            Linger.Posix.checkPid "export" pid.toUInt32
            Linger.Posix.getcwdOf pid.toUInt32
      unless !dir.isEmpty && (System.FilePath.mk dir).isAbsolute do
        throw (IO.userError s!"could not read working directory for session: {name}")
      return (name, (← IO.FS.realPath dir).toString)

/-- Observe the same native namespace as listing, including its no-HOME fallback,
and export only the current names and directories. -/
private def writeSave (path : String) (capture : IO (List (String × String)) := snapshot) :
    IO Unit := do
  let fields ← capture
  let content ← IO.ofExcept (renderSave fields)
  publish path content

private def usage : String :=
  "Usage: linger tmux <command>

  ls [SAVE]       List saved panes without starting sessions
  select [SAVE]   Choose a saved pane, create its shell if needed, and attach
  import [SAVE]   Import every saved pane, skipping existing identities
  export SAVE     Save native session names and directories to a new file

SAVE defaults to last in tmux's configured resurrect directory, then
~/.tmux/resurrect or $XDG_DATA_HOME/tmux/resurrect (~/.local/share by default).
ls shows the resolved path and save time; pass an older file to browse it.
These are saved snapshots. Imported sessions start fresh shells; saved
commands and live tmux processes are never restored.
"

/-- The caller supplies its absolute executable path for every listing and run. -/
def run (executable : String) (args : List String) : IO UInt32 := do
  if args.isEmpty || args == ["help"] || args == ["--help"] || args == ["-h"] then
    IO.print usage
    return 0
  let command := args.headD ""
  unless ["ls", "select", "import", "export"].contains command do
    IO.eprint usage
    return 2
  let porcelain := command == "ls" && args[1]? == some "--porcelain"
  let paths := if porcelain then args.drop 2 else args.tail
  if
      paths.length > 1 || (command == "export" && paths.isEmpty) ||
        paths.any (fun path => path.isEmpty || path.startsWith "-") then
    IO.eprintln s!"usage: linger tmux {command} {if command == "export" then "SAVE" else "[SAVE]"}"
    return 2
  try
    match command with
    | "ls" =>
      listSave paths.head? porcelain;
      return 0
    | "select" =>
      selectSave executable paths.head?
    | "import" =>
      importSave executable paths.head?;
      return 0
    | _ =>
      writeSave (paths.headD "");
      return 0
  catch e =>
    IO.eprintln s!"linger tmux {command}: {diagnostic (toString e)}"
    return 1

end Manager.Resurrect
