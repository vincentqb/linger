module

public import Tools.Resurrect
public import Linger.Core.Remote

public section

/-! Optional tmux-resurrect importer. The main linger executable never imports
this module. Parsing and policy live in `Tools.Resurrect`; this entry point
preflights directories, obtains a successful listing, and executes that plan. -/

namespace Lzr

open Tools.Resurrect

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
the access check; the standalone tool has no concurrent cwd-changing tasks. -/
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

private def importSave (restore : Bool) (file : Option String) : IO Unit := do
  let origin ← IO.currentDir
  let home ←
    match (← IO.getEnv "HOME").filter (!·.isEmpty) with
    | some value =>
      resolveRelative origin value
    | none =>
      -- With HOME absent, the platform shell expands ~ from the account record.
      -- An empty environment also excludes exported functions and startup hooks.
      let found ←
        IO.Process.output
            { cmd := "/bin/sh", args := #["-c", "printf '%s\\n' ~"], inheritEnv := false }
      let home := (found.stdout.dropEnd 1).toString
      unless found.exitCode == 0 && (System.FilePath.mk home).isAbsolute do
        throw (IO.userError "could not determine the account home directory")
      pure home
  let mut env : Array (String × Option String) := #[("HOME", some home)]
  for key in ["LINGER_DIR", "XDG_RUNTIME_DIR", "XDG_STATE_HOME"] do
    if let some value← IO.getEnv key then
      if key == "LINGER_DIR" || !value.isEmpty then
        env := env.push (key, some (← resolveRelative origin value))
  -- Saved cwd spellings retain symlink/parent traversal until the OS enters them.
  let absolute := fun path : String =>
    if (System.FilePath.mk path).isAbsolute then path else (origin / path).toString
  let save ←
    match file with
    | some path =>
      pure (System.FilePath.mk path)
    | none =>
      let legacy := System.FilePath.mk s!"{home}/.tmux/resurrect"
      if ← legacy.isDir then
        pure (legacy / "last")
      else
        let data := (← IO.getEnv "XDG_DATA_HOME").filter (!·.isEmpty)
        pure (System.FilePath.mk (data.getD s!"{home}/.local/share") / "tmux/resurrect/last")
  let metadata ← save.metadata.toBaseIO
  unless metadata.toOption.any (·.type == .file) do
    throw (IO.userError s!"save not found: {save}")
  let panes ← IO.ofExcept (parseSave home (← IO.FS.readFile save))
  preflight origin panes
  -- Lean's process API searches PATH but does not return the resolved path.
  -- This fixed POSIX lookup freezes it before children enter their saved cwd.
  let located ←
    IO.Process.output
        { cmd := "/bin/sh", args := #["-c", "command -v linger"], inheritEnv := false,
          env := #[("PATH", ← IO.getEnv "PATH")] }
  unless located.exitCode == 0 && !located.stdout.isEmpty do
    throw (IO.userError "linger is not on PATH")
  let bin ← IO.FS.realPath (located.stdout.dropEnd 1).toString
  let listing ← IO.Process.output { cmd := bin.toString, args := #["ls", "--porcelain"], env }
  unless listing.exitCode == 0 do
    throw (IO.userError "could not list existing linger sessions")
  let existing := (Linger.Core.Remote.parse listing.stdout).map (·.name)
  for action in plan restore existing panes do
    let child ←
      IO.Process.spawn
          { cmd := bin.toString, args := #["run", action.pane.name, "true"],
            cwd := some (System.FilePath.mk (absolute action.pane.dir)), env }
    unless (← child.wait) == 0 do
      throw (IO.userError s!"could not create session: {action.pane.name}")
    if let some command := action.command then
      let child ←
        IO.Process.spawn { cmd := bin.toString, args := #["run", action.pane.name, command], env }
      unless (← child.wait) == 0 do
        throw (IO.userError s!"could not restore process in session: {action.pane.name}")

def main (args : List String) : IO UInt32 := do
  let (restore, files) :=
    match args with
    | "--restore-processes" :: rest => (true, rest)
    | _ => (false, args)
  if files.length > 1 then
    IO.eprintln "usage: lzr [--restore-processes] [SAVE]"
    return 2
  try
    importSave restore files.head?
    return 0
  catch e =>
    IO.eprintln s!"lzr: {e}"
    return 1

end Lzr

def main := Lzr.main
