module

public import Tools.Resurrect
public import Linger.Core.Remote
public import Std.Async.System

public section

/-! tmux-resurrect importer for `linger import`. Parsing and policy live in
`Tools.Resurrect`; this executor preflights directories, obtains a successful
listing, and executes that plan using the entry point's absolute executable. -/

namespace Manager.Resurrect

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

private def importSave (executable : String) (file : Option String) : IO Unit := do
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
  -- The entry point freezes its absolute appPath before any child changes cwd.
  let listing ← IO.Process.output { cmd := executable, args := #["ls", "--porcelain"], env }
  unless listing.exitCode == 0 do
    throw (IO.userError "could not list existing linger sessions")
  let existing := (Linger.Core.Remote.parse listing.stdout).map (·.name)
  for pane in plan existing panes do
    let created ←
      IO.Process.output
          { cmd := executable, args := #["run", pane.name, "true"],
            cwd := some (System.FilePath.mk (absolute pane.dir)), env }
    unless created.exitCode == 0 do
      throw
          (IO.userError s!"could not create session: {pane.name}: {created.stdout}{created.stderr}")

/-- The caller supplies its absolute executable path for every listing and run. -/
def run (executable : String) (args : List String) : IO UInt32 := do
  if args.length > 1 || args.any (fun path => path.isEmpty || path.startsWith "-") then
    IO.eprintln "usage: linger import [SAVE]"
    return 2
  try
    importSave executable args.head?
    return 0
  catch e =>
    IO.eprintln s!"linger import: {diagnostic (toString e)}"
    return 1

end Manager.Resurrect
