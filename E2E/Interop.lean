module

public import E2E.Recipes
public import Linger.Core.Checkpoint
import all Manager.Resurrect

public section

/-! # E2E.Interop — real import/export boundaries

Each check owns fresh state below a new `/tmp` directory. Foreign commands only
write a fixture marker if accidentally executed; a subsequent shell command is
the completion barrier. No tmux server or user save is involved.

The parser supplies the common-field projection. Checkpoint fixtures use the
production codec, and the crash check also exercises an actual last detach.
-/

namespace E2E.Interop

open E2E.Harness
open E2E.Recipes (paneLine)
open Linger.Core.Checkpoint

private def process (args : IO.Process.SpawnArgs) (ms : Nat := 10000) :
    IO (UInt32 × String × String) := do
  let child ←
    IO.Process.spawn
        { args with
          stdin := .null, stdout := .piped, stderr := .piped }
  match ← waitProcess child ms with
  | some code =>
    return (code, ← child.stdout.readToEnd, ← child.stderr.readToEnd)
  | none =>
    child.kill
    if (← waitProcess child 1000).isNone then
      Linger.Posix.kill child.pid 9
      let _ ← waitProcess child 1000
      pure ()
    throw (IO.userError s!"process timed out: {args.cmd} {args.args}")

private structure Fixture where
  root : System.FilePath
  env : Env
  owned : IO.Ref (List (Env × String))

private def Fixture.procEnv (f : Fixture) : Array (String × Option String) :=
  f.env.procEnv ++
    #[("HOME", some (f.root / "home").toString), ("XDG_DATA_HOME", some (f.root / "data").toString),
      ("LINGER_SESSION", none), ("ENV", none), ("BASH_ENV", none)]

private def Fixture.cli (f : Fixture) (args : Array String)
    (extra : Array (String × Option String) := #[]) (cwd : Option System.FilePath := none) :
    IO (UInt32 × String × String) :=
  process { cmd := f.env.bin, args, env := f.procEnv ++ extra, cwd := cwd.or (some f.root) }

private def Fixture.own (f : Fixture) (name : String) : IO Unit :=
  f.owned.modify fun names =>
    if names.any (fun (e, n) => e.dir == f.env.dir && n == name) then names
    else (f.env, name) :: names

private def Fixture.info (f : Fixture) (name field : String) : IO (Option String) := do
  let (code, out, _) ← f.cli #["info", name]
  return if code != 0 then none else (records out |>.find? (·.1 == field)).map (·.2)

private def Fixture.pid (f : Fixture) (name : String) : IO (Option UInt32) := do
  return (← f.info name "pid").bind fun text => do
      let n ← text.toNat?
      if 0 < n && n < UInt32.size then
        some n.toUInt32
      else
        none

private def Fixture.cwdIs (f : Fixture) (name : String) (dir : System.FilePath) : IO Bool :=
  waitFor 5000 do
    match ← f.pid name with
    | none =>
      return false
    | some pid =>
      return (← Linger.Posix.getcwdOf pid) == dir.toString

private def Fixture.start (f : Fixture) (name : String) (dir : System.FilePath) : IO Unit := do
  f.own name
  let (code, _, err) ← f.cli #["run", name, "true"] (cwd := some dir)
  unless code == 0 && (← f.cwdIs name dir) do
    throw (IO.userError s!"session did not start in {dir}: {name}: {err}")

private def Fixture.seed (f : Fixture) (name cwd : String) : IO Unit := do
  let ck : Ckpt := { vt := Linger.Core.Vt.Vt.init 20 5, cwd, labels := [] }
  IO.FS.writeBinFile (System.FilePath.mk f.env.dir / s!"{name}.ckpt")
      (ByteArray.mk (save ck).toArray)

private def Fixture.importText (f : Fixture) (text : String) : IO (UInt32 × String × String) := do
  match Tools.Resurrect.parseSave (f.root / "home").toString text with
  | .ok panes =>
    for pane in panes do
      f.own pane.name
  | .error _ =>
    pure ()
  let path := f.root / "source"
  IO.FS.writeFile path text
  f.cli #["import", path.toString]

private def readBytes (path : System.FilePath) : IO (Option ByteArray) := do
  try
    return some (← IO.FS.readBinFile path)
  catch _ =>
    return none

private def namesIn (dir : System.FilePath) : IO (List String) := do
  return (← dir.readDir).toList.map (·.fileName) |>.toArray.qsort (· < ·) |>.toList

private def commonFields (home text : String) : Option (List (String × String)) :=
  (Tools.Resurrect.parseSave home text).toOption.map Tools.Resurrect.common

private def sameFields (a b : List (String × String)) : Bool :=
  a.toArray.qsort (fun x y => x.1 < y.1 || (x.1 == y.1 && x.2 < y.2)) ==
    b.toArray.qsort (fun x y => x.1 < y.1 || (x.1 == y.1 && x.2 < y.2))

private def Fixture.exportFields (f : Fixture) (file : String) (expected : List (String × String)) :
    IO Bool := do
  let target := f.root / "out" / file
  let (code, _, _) ← f.cli #["export", target.toString]
  let some bytes ← readBytes target | return false
  let some text := String.fromUTF8? bytes | return false
  let some fields := commonFields (f.root / "home").toString text | return false
  return code == 0 && sameFields fields expected

private def Fixture.refused (f : Fixture) (file : String := "refused") : IO Bool := do
  let out := f.root / "out"
  let before ← namesIn out
  let (code, _, err) ← f.cli #["export", (out / file).toString]
  return code == 1 && err.startsWith "linger export: " && (← namesIn out) == before

private def privateFile (path : System.FilePath) : IO Bool := do
  let (code, out, _) ←
    process
        { cmd := "find",
          args := #[path.toString, "-prune", "-type", "f", "-perm", "0600", "-print"] }
  return code == 0 && out == path.toString ++ "\n"

private def link (target path : System.FilePath) : IO Unit := do
  let (code, _, err) ← process { cmd := "ln", args := #["-s", target.toString, path.toString] }
  unless code == 0 do
    throw (IO.userError s!"could not create fixture symlink: {err}")

private def rawText (f : Fixture) (revision : String := "first") : String :=
  ("# UTF8 café 会 — " ++ revision ++ "\n" ++
        "window\tforeign\t7\tunknown window fields\tlayout\n" ++
        paneLine "foreign" "7" "2" (f.root / "alias" / "..").toString
          s!"printf executed > '{f.root}/saved-command-ran'" ++
        "state\tforeign\t7\t2\tunknown state fields\n" ++
        "future-record\tkeep\tall\tthese\tfields\n").replace
    "\n" "\r\n"

private def setupRaw (f : Fixture) : IO String := do
  let dir := f.root / "pane 'quoted' $cash a b"
  IO.FS.createDirAll (dir / "child")
  link (dir / "child") (f.root / "alias")
  let text := rawText f
  let (code, _, err) ← f.importText text
  unless code == 0 && (← f.cwdIs "foreign-w7-p2" dir) do
    throw (IO.userError s!"foreign import did not start its physical cwd: {err}")
  return text

private def rawRoundtrip (f : Fixture) : IO Bool := do
  let original ← setupRaw f
  IO.FS.writeFile (f.root / "source") "source replaced after import\n"
  let first := f.root / "out" / "replaced"
  let (firstCode, _, _) ← f.cli #["export", first.toString]
  IO.FS.removeFile (f.root / "source")
  let second := f.root / "out" / "removed"
  let (secondCode, _, _) ← f.cli #["export", second.toString]
  return firstCode == 0 && secondCode == 0 && (← readBytes first) == some original.toUTF8 &&
      (← readBytes second) == some original.toUTF8 &&
      (← namesIn (f.root / "out")) == ["removed", "replaced"]

private def latestImport (f : Fixture) : IO Bool := do
  let _ ← setupRaw f
  let latest := rawText f "latest successful import" ++ "last-record\tno trailing newline"
  let (importCode, _, _) ← f.importText latest
  let target := f.root / "out" / "latest"
  let (exportCode, _, _) ← f.cli #["export", target.toString]
  return importCode == 0 && exportCode == 0 && (← readBytes target) == some latest.toUTF8

private def failedImport (f : Fixture) : IO Bool := do
  let original ← setupRaw f
  let provenance := System.FilePath.mk f.env.dir / "tmux-import.json"
  let before ← readBytes provenance
  f.own "must-not-start-w0-p0"
  let malformed :=
    paneLine "must-not-start" "0" "0" (f.root / "home").toString "" ++ "pane\tbroken\n"
  let (importCode, _, _) ← f.importText malformed
  let after ← readBytes provenance
  let target := f.root / "out" / "previous"
  let (exportCode, _, _) ← f.cli #["export", target.toString]
  return importCode == 1 && before.isSome && before == after && exportCode == 0 &&
      (← readBytes target) == some original.toUTF8 &&
      !(← (System.FilePath.mk f.env.dir / "must-not-start-w0-p0.sock").pathExists)

private def topologyChange (f : Fixture) (remove : Bool) : IO Bool := do
  let original ← setupRaw f
  let dir := f.root / "home"
  f.start "added.name+" dir
  if remove then
    let (code, _, _) ← f.cli #["kill", "foreign-w7-p2"]
    unless
      code == 0 &&
        (←
          waitFor 5000 do
              return !(← (System.FilePath.mk f.env.dir / "foreign-w7-p2.sock").pathExists)) do
      throw (IO.userError "fixture session was not removed")
  let expected :=
    [("added.name+", dir.toString)] ++
      if remove then [] else [("foreign-w7-p2", (f.root / "pane 'quoted' $cash a b").toString)]
  let ok ← f.exportFields "changed" expected
  return ok && (← readBytes (f.root / "out" / "changed")) != some original.toUTF8

private def liveCwd (f : Fixture) : IO Bool := do
  let _ ← setupRaw f
  let changed := f.root / "home"
  let (code, _, _) ← f.cli #["run", "foreign-w7-p2", "cd", changed.toString]
  return code == 0 && (← f.cwdIs "foreign-w7-p2" changed) &&
      (← f.exportFields "changed-cwd" [("foreign-w7-p2", changed.toString)])

private def nativeRoundtrip (f : Fixture) : IO Bool := do
  let dir := f.root / "one two 'three' $four 会é"
  IO.FS.createDirAll dir
  let inputs := ["a.b", "plus+", "会é"]
  let names := inputs.map Linger.Core.Name.sanitize
  for name in inputs do
    f.start name dir
  let fields := names.map fun name => (name, dir.toString)
  unless ← f.exportFields "native" fields do
    return false
  let second := { f with env := { f.env with dir := (f.root / "second").toString } }
  IO.FS.createDirAll second.env.dir
  for name in names do
    second.own name
  let (code, _, _) ← second.cli #["import", (f.root / "out" / "native").toString]
  let mut ready := code == 0
  for name in names do
    let there ← second.cwdIs name dir
    let here ← f.cwdIs name dir
    ready := ready && there && here
  return ready && (← second.exportFields "second" fields)

private def resumableCwd (f : Fixture) : IO Bool := do
  let name := "resumed.name"
  f.start name (f.root / "home")
  let changed := f.root / "saved cwd"
  IO.FS.createDirAll changed
  let (code, _, _) ← f.cli #["run", name, s!"cd '{changed}'"]
  unless code == 0 && (← f.cwdIs name changed) do
    throw (IO.userError "live fixture cwd did not change")
  let some shellPid ← f.pid name | throw (IO.userError "fixture shell pid is missing")
  let (psCode, parent, _) ←
    process { cmd := "ps", args := #["-o", "ppid=", "-p", toString shellPid] }
  let some daemon :=
    parent.trimAscii.toString.toNat? | throw (IO.userError "fixture daemon pid is missing")
  unless psCode == 0 && 1 < daemon && daemon < UInt32.size do
    throw (IO.userError "invalid fixture daemon pid")
  let client ← f.env.spawnEnv #[s!"HOME={f.root}/home"] #["attach", name]
  try
    unless
      ←
        waitFor 5000
            (do
              return (← f.info name "clients") == some "1") do
      throw (IO.userError "checkpoint fixture client did not attach")
    client.detach
    let _ ← client.reap
  finally
    client.bye (sendDetach := false)
  let checkpoint := System.FilePath.mk f.env.dir / s!"{name}.ckpt"
  unless
    ←
      waitFor 5000
          (do
            let some bytes ← readBytes checkpoint | return false
            return (load bytes.toList).any (·.cwd == changed.toString)) do
    throw (IO.userError "last detach did not checkpoint the changed cwd")
  try
    Linger.Posix.kill daemon.toUInt32 9
    unless
      ←
        waitFor 5000
            (do
              return !(← Linger.Posix.alive daemon.toUInt32)) do
      throw (IO.userError "fixture daemon did not stop")
    return (← f.exportFields "resumable" [(name, changed.toString)]) && (← f.pid name).isNone
  finally
    if ← Linger.Posix.alive shellPid then
      Linger.Posix.kill shellPid 9

private def publication (f : Fixture) (kind : String) : IO Bool := do
  f.seed "native" (f.root / "home").toString
  let target := f.root / "out" / "kept"
  let sentinel := "existing destination stays byte-exact\n"
  if kind == "file" then
    IO.FS.writeFile target sentinel
  else
    let victim := f.root / "victim"
    if kind == "symlink" then
      IO.FS.writeFile victim sentinel
    link victim target
  let before ← namesIn (f.root / "out")
  let (code, _, _) ← f.cli #["export", target.toString]
  let intact ←
    if kind == "file" then
      pure ((← readBytes target) == some sentinel.toUTF8)
    else
      do
        let metadata ← target.symlinkMetadata
        let expected := if kind == "symlink" then some sentinel.toUTF8 else none
        pure (metadata.type == .symlink && (← readBytes (f.root / "victim")) == expected)
  return code == 1 && intact && (← namesIn (f.root / "out")) == before

private def privatePublication (f : Fixture) : IO Bool := do
  let _ ← setupRaw f
  let target := f.root / "out" / "private"
  let (code, _, _) ← f.cli #["export", target.toString]
  return code == 0 && (← privateFile target) &&
      (← privateFile (System.FilePath.mk f.env.dir / "tmux-import.json")) &&
      (← namesIn (f.root / "out")) == ["private"] &&
      (← namesIn (System.FilePath.mk f.env.dir)).all
        (fun name => !name.contains '~' && !name.endsWith ".tmp")

private def corruptCheckpoint (f : Fixture) (unreadable : Bool) : IO Bool := do
  f.seed "valid" (f.root / "home").toString
  let checkpoint := System.FilePath.mk f.env.dir / "broken.ckpt"
  if unreadable then
    IO.FS.createDirAll checkpoint
  else
    IO.FS.writeBinFile checkpoint (ByteArray.mk (magic ++ [80, 24, 0xFF]).toArray)
  f.refused

private def corruptProvenance (f : Fixture) (text : String) : IO Bool := do
  f.seed "valid" (f.root / "home").toString
  let path := System.FilePath.mk f.env.dir / "tmux-import.json"
  IO.FS.writeFile path text
  return (← f.refused) && (← readBytes path) == some text.toUTF8

private def incompleteSnapshot (f : Fixture) : IO Bool := do
  f.seed "valid" (f.root / "home").toString
  let socket := System.FilePath.mk f.env.dir / "unresponsive.sock"
  let fd ← Linger.Posix.unixListen socket.toString
  try
    f.refused
  finally
    Linger.Posix.close fd
    IO.FS.removeFile socket

private def unrepresentableCwd (f : Fixture) : IO Bool := do
  f.seed "valid" (f.root / "home").toString
  for (label, suffix) in
    [("backslash", "back\\slash"), ("tab", "a\tb"), ("LF", "a\nb"), ("CR", "a\rb"),
      ("repeated spaces", "a  b"), ("trailing space", "a "), ("star", "a*b"),
      ("question mark", "a?b"), ("bracket", "a[b"), ("hash format", "a#{pid}"),
      ("NUL", "home\x00ignored")] do
    let dir := f.root / suffix
    unless suffix.contains '\x00' do
      IO.FS.createDirAll dir
    f.seed "unsupported" dir.toString
    unless ← f.refused do
      throw (IO.userError s!"unsupported cwd was not refused without output: {label}")
  return true

private def inertCommands (f : Fixture) : IO Bool := do
  let _ ← setupRaw f
  let barrier := f.root / "barrier"
  let (code, _, _) ← f.cli #["run", "foreign-w7-p2", s!"printf ready > '{barrier}'"]
  let ready ←
    waitFor 5000 do
        return (← readBytes barrier) == some "ready".toUTF8
  return code == 0 && ready && !(← (f.root / "saved-command-ran").pathExists)

private def relativeEnvironment (f : Fixture) : IO Bool := do
  let origin := f.root / "invoke"
  IO.FS.createDirAll origin
  let text := paneLine "relative" "0" "0" "~" ""
  IO.FS.writeFile (origin / "save") text
  f.own "relative-w0-p0"
  let extra :=
    #[("HOME", some "../home"), ("LINGER_DIR", some "../state"),
      ("XDG_RUNTIME_DIR", some "../runtime"), ("XDG_STATE_HOME", some "../persistent")]
  let (importCode, _, _) ← f.cli #["import", "save"] extra (some origin)
  let (exportCode, _, _) ← f.cli #["export", "../out/relative"] extra (some origin)
  return importCode == 0 && exportCode == 0 && (← f.cwdIs "relative-w0-p0" (f.root / "home")) &&
      (← readBytes (f.root / "out" / "relative")) == some text.toUTF8 &&
      (← privateFile (System.FilePath.mk f.env.dir / "tmux-import.json"))

private def fallbackHome (f : Fixture) (home : Option String) : IO Bool := do
  let text := paneLine "fallback" "0" "0" "~" ""
  IO.FS.writeFile (f.root / "source") text
  f.own "fallback-w0-p0"
  let (importCode, _, _) ← f.cli #["import", (f.root / "source").toString] #[("HOME", home)]
  let target := f.root / "out" / "fallback"
  let (exportCode, _, _) ← f.cli #["export", target.toString] #[("HOME", home)]
  return importCode == 0 && exportCode == 0 && (← readBytes target) == some text.toUTF8

private def withVariables {α : Type} (values : Array (String × Option String)) (action : IO α) :
    IO α := do
  let previous ← values.mapM fun (key, _) => return (key, ← IO.getEnv key)
  let set := fun (key, value) =>
    match value with
    | some value => Std.Async.System.setEnvVar key value
    | none => Std.Async.System.unsetEnvVar key
  try
    values.forM set
    action
  finally
    previous.forM set

/-- Observe the real default namespace without opening it. Only after that
observation does the capture callback redirect checkpoint IO into a fixture.
The live socket remains visible in both namespaces, so the wrong context can
produce a successful but incomplete save. These probes run serially. -/
private def nativeFallback (f : Fixture) (home : Option String) (mixed : Bool) : IO Bool := do
  let runtime := f.root / "runtime"
  let sockets := runtime / "linger"
  IO.FS.createDirAll sockets
  let live := { f with env := { f.env with dir := sockets.toString } }
  if mixed then
    live.start "live.name" (f.root / "home")
  let savedCwd := f.root / "saved cwd"
  IO.FS.createDirAll savedCwd
  withVariables
      #[("HOME", home), ("LINGER_DIR", none), ("XDG_STATE_HOME", none),
        ("XDG_RUNTIME_DIR", some runtime.toString)]
      do
      let native ← Linger.Runtime.Paths.stateDir
      let original := f.root / "native"
      let alternate := f.root / "alternate"
      let checkpointDir ←
        withVariables #[("XDG_STATE_HOME", some original.toString)] do
            let dir ← Linger.Runtime.Paths.stateDir
            Linger.Runtime.Paths.ensureDir dir
            return dir
      let checkpoints := { f with env := { f.env with dir := checkpointDir } }
      checkpoints.seed "saved.name" savedCwd.toString
      let target := f.root / "out" / "native-fallback"
      let observed ← IO.mkRef (none : Option String)
      let capture := do
        let observedDir ← Linger.Runtime.Paths.stateDir
        observed.set (some observedDir)
        let selected := if observedDir == native then original else alternate
        Std.Async.System.setEnvVar "XDG_STATE_HOME" selected.toString
        Manager.Resurrect.snapshot
      let outcome ← (Manager.Resurrect.writeSave target.toString capture).toBaseIO
      let actual :=
        (← readBytes target).bind fun bytes =>
          (String.fromUTF8? bytes).bind (commonFields (f.root / "home").toString)
      let expected :=
        [("saved.name", savedCwd.toString)] ++
          if mixed then [("live.name", (f.root / "home").toString)] else []
      let complete :=
        outcome.isOk && (← observed.get) == some native && actual.any (sameFields · expected)
      unless complete do
        let status :=
          match outcome with
          | .ok _ => "success"
          | .error error => toString error
        IO.eprintln
            s!"native fallback: expected namespace {native}; observed {← observed.get}; export {status}; expected {expected}; actual {actual}"
      return complete && (← namesIn (f.root / "out")) == ["native-fallback"] &&
          (← privateFile target)

private def check (root : System.FilePath) (bin : String) (index : Nat) (label : String)
    (body : Fixture → IO Bool) : IO Nat := do
  let root := root / toString index
  for dir in [root / "state", root / "home", root / "data", root / "out"] do
    IO.FS.createDirAll dir
  let owned ← IO.mkRef []
  let f : Fixture := { root, env := { bin, dir := (root / "state").toString }, owned }
  let (ok, detail) ←
    try
      pure (← body f, label)
    catch error =>
      pure (false, s!"{label}: {error}")
  let mut clean := true
  for (env, name) in ← owned.get do
    let cleanup := { f with env }
    try
      let _ ← cleanup.cli #["kill", name]
      let _ ← cleanup.cli #["list"]
      let gone ←
        waitFor 5000 do
            return !(← (System.FilePath.mk env.dir / s!"{name}.sock").pathExists)
      clean := clean && gone
    catch _ =>
      clean := false
  expect (ok && clean) (if clean then detail else detail ++ " (fixture cleanup failed)")

/-- Exercise a selected build from an isolated probe runner. -/
def runWith (binary : String) : IO UInt32 := do
  let bin ← IO.FS.realPath binary
  let (code, temp, err) ← process { cmd := "mktemp", args := #["-d", "/tmp/linger-i-XXXXXX"] }
  unless code == 0 do
    throw (IO.userError s!"could not create fresh fixture root: {err}")
  let root ← IO.FS.realPath temp.trimAscii.toString
  IO.println s!"interop fixtures: {root}"
  let mut cases : List (String × (Fixture → IO Bool)) := []
  for (label, args) in
    [("missing", #[]), ("empty", #[""]), ("leading dash", #["-save"]), ("option", #["--"]),
      ("extra", #["one", "extra"])] do
    cases :=
      cases ++
        [(s!"export rejects {label} arguments with exit 2", fun (f : Fixture) => do
            let (code, _, _) ← f.cli (#["export"] ++ args)
            return code == 2 && (← namesIn (System.FilePath.mk f.env.dir)).isEmpty)]
  cases :=
    cases ++
      [("export refuses an empty session set without publishing", fun (f : Fixture) => f.refused),
        ("export accepts an explicit ./-save path", fun (f : Fixture) => do
          f.seed "native" (f.root / "home").toString
          let (code, _, _) ← f.cli #["export", "./-save"] (cwd := some (f.root / "out"))
          return code == 0 && (← readBytes (f.root / "out" / "-save")).isSome),
        ("unchanged import preserves UTF8, CRLF and unknown rows after source replacement and deletion",
          rawRoundtrip),
        ("the latest successful import replaces retained source even when every session exists",
          latestImport),
        ("a malformed import preserves provenance and creates no partial session", failedImport),
        ("adding a session generates complete current common fields", fun f =>
          topologyChange f false),
        ("removing an imported session generates complete current common fields", fun f =>
          topologyChange f true),
        ("export observes a live cwd change instead of its startup directory", liveCwd),
        ("native identities follow name sanitization and preserve dot, plus and UTF8 cwd in a second state dir",
          nativeRoundtrip),
        ("export reads the changed checkpoint cwd after last detach and daemon crash",
          resumableCwd),
        ("export preserves an existing destination with no temporary leak", fun f =>
          publication f "file"),
        ("export preserves a symlink and its target with no temporary leak", fun f =>
          publication f "symlink"),
        ("export preserves a dangling symlink with no temporary leak", fun f =>
          publication f "dangling"),
        ("provenance and exported saves are private 0600 files with no temporary leak",
          privatePublication),
        ("a corrupt checkpoint refuses the entire export", fun f => corruptCheckpoint f false),
        ("an unreadable checkpoint refuses the entire export", fun f => corruptCheckpoint f true),
        ("corrupt provenance refuses export without changing provenance", fun f =>
          corruptProvenance f "{not-json"),
        ("incomplete provenance refuses export without changing provenance", fun f =>
          corruptProvenance f "{}"),
        ("an unresponsive live socket refuses a partial export", incompleteSnapshot),
        ("unrepresentable cwd fields are refused without a partial export", unrepresentableCwd),
        ("saved commands remain inert after a shell completion barrier", inertCommands),
        ("import and export share relative HOME and state overrides", relativeEnvironment),
        ("import and export share account-home fallback when HOME is unset", fun f =>
          fallbackHome f none),
        ("import and export share account-home fallback when HOME is empty", fun f =>
          fallbackHome f (some "")),
        ("export preserves the native resumable namespace without HOME or state overrides", fun f =>
          nativeFallback f none false),
        ("export preserves the native resumable namespace with empty HOME and no state overrides",
          fun f => nativeFallback f (some "") false),
        ("export includes live and resumable sessions without HOME or state overrides", fun f =>
          nativeFallback f none true),
        ("export includes live and resumable sessions with empty HOME and no state overrides",
          fun f => nativeFallback f (some "") true)]
  let mut failures := 0
  for (index, (label, body)) in cases.zipIdx |>.map (fun (item, i) => (i, item)) do
    failures := failures + (← check root bin.toString index label body)
  if failures == 0 then
    IO.FS.removeDirAll root
  verdict { bin := bin.toString, dir := root.toString } failures

def run : IO UInt32 := do
  runWith ((← IO.currentDir) / ".lake/build/bin/linger").toString

end E2E.Interop
