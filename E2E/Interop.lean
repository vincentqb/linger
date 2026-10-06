module

public import E2E.Recipes
public import Linger.Core.Checkpoint
public import Lean.Data.Json
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
open E2E.Recipes (paneLine tmuxFixtureEnv)
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
  tmuxEnv : Array (String × Option String)

private def Fixture.procEnv (f : Fixture) : Array (String × Option String) :=
  f.env.procEnv ++
    #[("HOME", some (f.root / "home").toString), ("XDG_DATA_HOME", some (f.root / "data").toString),
      ("LINGER_SESSION", none), ("ENV", none), ("BASH_ENV", none)] ++
    f.tmuxEnv

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
  f.cli #["tmux", "import", path.toString]

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
  let (code, _, _) ← f.cli #["tmux", "export", target.toString]
  let some bytes ← readBytes target | return false
  let some text := String.fromUTF8? bytes | return false
  let some fields := commonFields (f.root / "home").toString text | return false
  return code == 0 && sameFields fields expected

private def Fixture.refused (f : Fixture) (file : String := "refused") : IO Bool := do
  let out := f.root / "out"
  let before ← namesIn out
  let (code, _, err) ← f.cli #["tmux", "export", (out / file).toString]
  return code == 1 && err.startsWith "linger tmux export: " && (← namesIn out) == before

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

private def queryCall : String := "CALL\x00show-options\x00-gqv\x00@resurrect-dir\x00\n"

private def Fixture.queries (f : Fixture) : IO String := IO.FS.readFile (f.root / "tmux-calls")

/-- Fix the file's UTC mtime independently of the program's timestamp formatter. -/
private def Fixture.catalogSave (f : Fixture) (path : System.FilePath) (text : String) : IO Unit :=
  do
  IO.FS.createDirAll (path.parent.getD f.root)
  IO.FS.writeFile path text
  let (code, _, err) ←
    process
        { cmd := "touch", args := #["-t", "200102030405.06", path.toString],
          env := #[("TZ", some "UTC")] }
  unless code == 0 do
    throw (IO.userError s!"could not timestamp fixture save: {err}")
  for pane in (Tools.Resurrect.parseSave (f.root / "home").toString text).toOption.getD [] do
    f.own pane.name

private def catalogDate (text : String) : Bool :=
  text == "2001-02-03T04:05:06Z" || text == "2001-02-03T04:05:06+00:00"

private def field (row : List (String × String)) (key : String) : String := (row.lookup key).getD ""

/-- Check the wire framing as well as the production parser's identities.
Action directories are decoded as JSON, never compared through display escaping. -/
private def Fixture.catalogMatches (f : Fixture) (path : System.FilePath) (out : String) :
    IO Bool := do
  let text ← IO.FS.readFile path
  let .ok panes := Tools.Resurrect.parseSave (f.root / "home").toString text | return false
  let sections := out.splitOn "\n\n"
  let header := records (sections.headD "")
  let source ← IO.FS.realPath path
  unless
    sections.length == panes.length + 2 && sections.getLast? == some "" &&
      header.map (·.1) == ["source", "saved"] &&
      field header "source" == Tools.Resurrect.diagnostic source.toString &&
      catalogDate (field header "saved") &&
      ((sections.headD "").splitOn "\n").length == 2 do
    return false
  unless sections.tail.dropLast.all (fun row => (row.splitOn "\n").length == 5) do
    return false
  let rows := sections.tail.dropLast.map records
  return (rows.zip panes).all fun (row, pane) =>
      let dir :=
        if pane.dir.isEmpty || (System.FilePath.mk pane.dir).isAbsolute then pane.dir
        else (f.root / pane.dir).toString
      row.map (·.1) == ["name", "status", "cmd", "directory", "line"] &&
        field row "name" == pane.name &&
        field row "status" == Linger.Core.Status.name .resumable &&
        has (field row "cmd") (Tools.Resurrect.diagnostic dir) &&
        ((Lean.Json.parse (field row "directory")).toOption.bind
            (fun json => json.getStr?.toOption)) ==
          some dir &&
        field row "line" == toString pane.line

private def catalogOrder (f : Fixture) : IO Bool := do
  let path := f.root / "snapshot-with-order-20010203.txt"
  let last := f.root / "last"
  let first := (f.root / "first dir").toString
  let second := (f.root / "second dir").toString
  let third := (f.root / "third dir").toString
  let text :=
    "# Save order is deliberately neither name nor numeric order.\n" ++
      "window\tzeta\t12\t:Review window\tlayout\tunused\n" ++
      paneLine "zeta" "12" "8" first "" ++
      "state\tzeta\tunused\n" ++
      paneLine "alpha" "3" "1" second "" ++
      paneLine "zeta" "12" "2" third "" ++
      "window\talpha\t3\t:Build window\tignored\n"
  f.catalogSave path text
  link path last
  let (rc, out, err) ← f.cli #["tmux", "ls", "--porcelain", "last"]
  let (humanRc, human, humanErr) ← f.cli #["tmux", "ls", "last"]
  -- The source path can also contain "-w"; rows follow the two-line header.
  let rows := (lines human).drop 3
  return rc == 0 && err.isEmpty && (← f.catalogMatches last out) && humanRc == 0 &&
      humanErr.isEmpty &&
      has human path.toString &&
      has human "2001-02-03T04:05:06" &&
      rows.length == 3 &&
      (rows.zip ["zeta-w12-p8", "alpha-w3-p1", "zeta-w12-p2"]).all
        (fun (row, name) => has row name) &&
      (rows.zip [first, second, third]).all (fun (row, dir) => has row dir) &&
      has (rows[0]?.getD "") "zeta:12 Review window" &&
      has (rows[1]?.getD "") "alpha:3 Build window" &&
      has (rows[2]?.getD "") "zeta:12 Review window" &&
      (← f.queries).isEmpty &&
      (← namesIn (System.FilePath.mk f.env.dir)).isEmpty

private def catalogControls (f : Fixture) : IO Bool := do
  let controls := "\x07\x1b[2J\r\x7f\u0080\u0085\u009b\u009d\u009f"
  let path := f.root / ("snapshot" ++ controls)
  let dir := (f.root / ("quote \" and backslash\\ café 会" ++ controls ++ "  trailing ")).toString
  let text := "window\tcontrol\t4\t:title" ++ controls ++ "\n" ++ paneLine "control" "4" "0" dir ""
  f.catalogSave path text
  let (rc, out, err) ← f.cli #["tmux", "ls", "--porcelain", path.toString]
  let (humanRc, human, humanErr) ← f.cli #["tmux", "ls", path.toString]
  let printable := fun c : Char => 32 ≤ c.toNat && (c.toNat < 127 || 160 ≤ c.toNat)
  return rc == 0 && err.isEmpty && (← f.catalogMatches path out) && humanRc == 0 &&
      humanErr.isEmpty &&
      human.toList.all (fun c => c == '\n' || printable c) &&
      ((out.splitOn "\n").filter (fun row => !row.startsWith "directory\t")).all
        (fun row => row.toList.all (fun c => c == '\t' || printable c)) &&
      has human (Tools.Resurrect.diagnostic dir.trimAscii.toString) &&
      has human (Tools.Resurrect.diagnostic path.toString) &&
      (← namesIn (System.FilePath.mk f.env.dir)).isEmpty

private def catalogRelativeCwd (f : Fixture) : IO Bool := do
  let path := f.root / "elsewhere" / "last"
  IO.FS.createDirAll (f.root / "physical" / "child")
  link (f.root / "physical" / "child") (f.root / "alias")
  f.catalogSave path (paneLine "relative" "0" "0" "alias/.." "")
  let (rc, out, err) ← f.cli #["tmux", "ls", "--porcelain", path.toString]
  return rc == 0 && err.isEmpty && (← f.catalogMatches path out) &&
      has out ((Lean.Json.str (f.root / "alias" / "..").toString).compress) &&
      !has out ((Lean.Json.str (f.root / "physical").toString).compress) &&
      (← namesIn (System.FilePath.mk f.env.dir)).isEmpty

private def catalogReadOnly (f : Fixture) : IO Bool := do
  let path := f.root / "save"
  let marker := f.root / "saved-command-marker"
  IO.FS.writeFile marker "UNTOUCHED\n"
  f.seed "native.only" (f.root / "home").toString
  let before ← f.cli #["ls", "--porcelain"]
  let checkpoint ← readBytes (System.FilePath.mk f.env.dir / "native.only.ckpt")
  let entries ← namesIn (System.FilePath.mk f.env.dir)
  let text :=
    paneLine "foreign" "2" "0" (f.root / "home").toString s!"printf EXECUTED > '{marker}'" ++
      "window\tforeign\t2\t:Original title\tlayout\n" ++
      "state\tforeign\tignored\nfuture-record\tignored\x00metadata\n"
  f.catalogSave path text
  let (rc, out, err) ← f.cli #["tmux", "ls", "--porcelain", path.toString]
  let (humanRc, _, humanErr) ← f.cli #["tmux", "ls", path.toString]
  IO.sleep 200 -- negative assertion: allow an accidentally started saved command to run
  let after ← f.cli #["ls", "--porcelain"]
  return rc == 0 && err.isEmpty && (← f.catalogMatches path out) && humanRc == 0 &&
      humanErr.isEmpty &&
      before.1 == 0 &&
      after == before &&
      !has before.2.1 "foreign-w2-p0" &&
      has before.2.1 "native.only" &&
      !has out "EXECUTED" &&
      !has out "future-record" &&
      (← IO.FS.readFile path) == text &&
      (← IO.FS.readFile marker) == "UNTOUCHED\n" &&
      (← readBytes (System.FilePath.mk f.env.dir / "native.only.ckpt")) == checkpoint &&
      (← namesIn (System.FilePath.mk f.env.dir)) == entries &&
      (← f.queries).isEmpty

private def catalogMissingCwd (f : Fixture) : IO Bool := do
  let path := f.root / "save"
  f.catalogSave path
      (paneLine "first" "1" "0" (f.root / "home").toString "" ++
        paneLine "missing" "1" "0" (f.root / "missing dir").toString "")
  let (rc, out, err) ← f.cli #["tmux", "ls", "--porcelain", path.toString]
  let (importRc, imported, importErr) ← f.cli #["tmux", "import", path.toString]
  return rc == 0 && err.isEmpty && (← f.catalogMatches path out) && importRc == 1 &&
      imported.isEmpty &&
      importErr.startsWith "linger tmux import: " &&
      has importErr "working directory not found at line 2" &&
      (← namesIn (System.FilePath.mk f.env.dir)).isEmpty &&
      (← f.queries).isEmpty

private structure Discovery where
  directory : System.FilePath → String := fun _ => ""
  source : String := "data/tmux/resurrect/last"
  legacy : Bool := false
  xdg : Option String := some "data"
  rc : String := "0"
  missingTmux : Bool := false

private def discovery (f : Fixture) (config : Discovery) : IO Bool := do
  let legacy := "home/.tmux/resurrect/last"
  IO.FS.createDirAll (f.root / "home/.tmux/resurrect")
  let files :=
    ["data/tmux/resurrect/last", "home/.local/share/tmux/resurrect/last", "configured/last",
        "home/configured/last", "relative config /last", "home/last"] ++
      if config.legacy then [legacy] else []
  for (file, index) in files.zipIdx do
    f.catalogSave (f.root / file) (paneLine s!"saved{index}" "0" "0" (f.root / "home").toString "")
  let extra :=
    #[("LINGER_TMUX_DIRECTORY", some (config.directory f.root)), ("LINGER_TMUX_RC", some config.rc),
        ("XDG_DATA_HOME", config.xdg)] ++
      if config.missingTmux then #[("PATH", some (f.root / "tmux-sockets").toString)] else #[]
  let (rc, out, err) ← f.cli #["tmux", "ls", "--porcelain"] extra
  let (humanRc, human, humanErr) ← f.cli #["tmux", "ls"] extra
  return rc == 0 && err.isEmpty && (← f.catalogMatches (f.root / config.source) out) &&
      humanRc == 0 &&
      humanErr.isEmpty &&
      has human (f.root / config.source).toString &&
      has human "2001-02-03T04:05:06" &&
      (← f.queries) == (if config.missingTmux then "" else queryCall ++ queryCall) &&
      (← namesIn (System.FilePath.mk f.env.dir)).isEmpty

private def explicitDiscovery (f : Fixture) : IO Bool := do
  let chosen := f.root / "older-save"
  f.catalogSave chosen (paneLine "chosen" "0" "0" (f.root / "home").toString "")
  for path in ["configured/last", "home/.tmux/resurrect/last", "data/tmux/resurrect/last"] do
    f.catalogSave (f.root / path) (paneLine "other" "0" "0" (f.root / "home").toString "")
  let (rc, out, err) ←
    f.cli #["tmux", "ls", "--porcelain", "older-save"]
        #[("LINGER_TMUX_DIRECTORY", some (f.root / "configured").toString),
          ("LINGER_TMUX_WAIT", some "1")]
  return rc == 0 && err.isEmpty && (← f.catalogMatches chosen out) && (← f.queries).isEmpty &&
      (← namesIn (System.FilePath.mk f.env.dir)).isEmpty

private def missingDiscovery (f : Fixture) (configured : Bool) : IO Bool := do
  let dir := if configured then f.root / "configured" else f.root / "data/tmux/resurrect"
  -- Historical files are never merged or substituted for a missing last.
  f.catalogSave (dir / "tmux_resurrect_20010203T040506.txt")
      (paneLine "historical" "0" "0" (f.root / "home").toString "")
  if configured then
    f.catalogSave (f.root / "home/.tmux/resurrect/last")
        (paneLine "fallback" "0" "0" (f.root / "home").toString "")
  let (rc, out, err) ←
    f.cli #["tmux", "ls"]
        #[("LINGER_TMUX_DIRECTORY", some (if configured then dir.toString else ""))]
  return rc == 1 && out.isEmpty && err.startsWith "linger tmux ls: " && has err "save not found" &&
      has err (dir / "last").toString &&
      (← f.queries) == queryCall &&
      (← namesIn (System.FilePath.mk f.env.dir)).isEmpty

private def discoveryTimeout (f : Fixture) : IO Bool := do
  f.catalogSave (f.root / "data/tmux/resurrect/last")
      (paneLine "fallback" "0" "0" (f.root / "home").toString "")
  let before ← IO.monoMsNow
  let (rc, out, err) ← f.cli #["tmux", "ls"] #[("LINGER_TMUX_WAIT", some "1")]
  let elapsed := (← IO.monoMsNow) - before
  return elapsed < 4500 && rc == 1 && out.isEmpty && has err "tmux configuration query timed out" &&
      has err "explicitly" &&
      (← f.queries) == queryCall &&
      (← namesIn (System.FilePath.mk f.env.dir)).isEmpty

private def catalogInvalid (f : Fixture) (kind : String) : IO Bool := do
  let path := f.root / "invalid-save"
  let valid := paneLine "mustnot" "1" "0" (f.root / "home").toString ""
  let text :=
    match kind with
    | "malformed" => valid ++ "pane\tshort\n"
    | "duplicate" => valid ++ valid
    | "NUL" => valid ++ paneLine "invalid" "1" "0" (f.root / "home").toString "printf\x00ignored"
    | "empty" => "window\tignored\nstate\tignored\n"
    | _ => ""
  f.own "mustnot-w1-p0"
  if kind != "absent" then
    IO.FS.writeFile path text
  let mut ok := true
  for args in [#["ls"], #["ls", "--porcelain"], #["import"]] do
    let (rc, out, err) ← f.cli (#["tmux"] ++ args ++ #[path.toString])
    ok := ok && rc == 1 && out.isEmpty && err.startsWith s!"linger tmux {args[0]!}: "
  return ok && (← f.queries).isEmpty && (← namesIn (System.FilePath.mk f.env.dir)).isEmpty

private def groupUsage (f : Fixture) : IO Bool := do
  let path := f.root / "save"
  f.catalogSave path (paneLine "mustnot" "0" "0" (f.root / "home").toString "")
  let mut ok := true
  for command in ["ls", "select", "import", "export"] do
    for args in [#[""], #["--unknown"], #[path.toString, "extra"], #["--", path.toString]] do
      let (rc, out, err) ← f.cli (#["tmux", command] ++ args)
      ok :=
        ok && rc == 2 && out.isEmpty &&
          err ==
            s!"usage: linger tmux {command} {if command == "export" then "SAVE" else "[SAVE]"}\n"
  for args in
    [#["tmux", "unknown"], #["tmux", "ls", "--porcelain", path.toString, "extra"],
      #["tmux", "ls", path.toString, "--porcelain"], #["tmux", "import", "--porcelain"],
      #["import", path.toString], #["export", (f.root / "out/save").toString]] do
    let (rc, out, err) ← f.cli args
    ok := ok && rc == 2 && out.isEmpty && !err.isEmpty
  return ok && (← f.queries).isEmpty && (← namesIn (System.FilePath.mk f.env.dir)).isEmpty &&
      (← namesIn (f.root / "out")).isEmpty

private def groupHelp (f : Fixture) : IO Bool := do
  let mut ok := true
  for args in [#["tmux"], #["tmux", "help"], #["tmux", "--help"], #["tmux", "-h"]] do
    let (rc, out, err) ← f.cli args
    ok :=
      ok && rc == 0 && err.isEmpty && has out "Usage: linger tmux" &&
        (["ls [SAVE]", "select [SAVE]", "import [SAVE]", "export SAVE"].all (has out ·))
  return ok && (← f.queries).isEmpty && (← namesIn (System.FilePath.mk f.env.dir)).isEmpty

private def rawText (f : Fixture) (revision : String := "first") : String :=
  ("# UTF8 café 会 — " ++ revision ++ "\n" ++
        "window\tforeign\t7\tunknown window fields\tlayout\n" ++
        paneLine "foreign" "7" "2" (f.root / "alias" / "..").toString
          s!"printf executed > '{f.root}/saved-command-ran'" ++
        "state\tforeign\t7\t2\tunknown state fields\n" ++
        "future-record\tkeep\tall\tthese\tfields\n").replace
    "\n" "\r\n"

private def setupRaw (f : Fixture) : IO Unit := do
  let dir := f.root / "pane 'quoted' $cash a b"
  IO.FS.createDirAll (dir / "child")
  link (dir / "child") (f.root / "alias")
  let text := rawText f
  let (code, _, err) ← f.importText text
  unless code == 0 && (← f.cwdIs "foreign-w7-p2" dir) do
    throw (IO.userError s!"foreign import did not start its physical cwd: {err}")

private def sourceIndependent (f : Fixture) : IO Bool := do
  setupRaw f
  let expected := [("foreign-w7-p2", (f.root / "pane 'quoted' $cash a b").toString)]
  IO.FS.writeFile (f.root / "source") "source replaced after import\n"
  let first ← f.exportFields "replaced" expected
  IO.FS.removeFile (f.root / "source")
  let second ← f.exportFields "removed" expected
  return first && second && !(← (System.FilePath.mk f.env.dir / "tmux-import.json").pathExists) &&
      (← namesIn (f.root / "out")) == ["removed", "replaced"]

private def metadataOnlyImport (f : Fixture) : IO Bool := do
  setupRaw f
  let before ← f.pid "foreign-w7-p2"
  let expected := [("foreign-w7-p2", (f.root / "pane 'quoted' $cash a b").toString)]
  let first ← f.exportFields "first" expected
  let latest := rawText f "latest successful import" ++ "last-record\tno trailing newline"
  let (importCode, _, _) ← f.importText latest
  let second ← f.exportFields "second" expected
  return importCode == 0 && before.isSome && (← f.pid "foreign-w7-p2") == before && first &&
      second &&
      (← readBytes (f.root / "out" / "first")) == (← readBytes (f.root / "out" / "second")) &&
      !(← (System.FilePath.mk f.env.dir / "tmux-import.json").pathExists)

private def failedImport (f : Fixture) : IO Bool := do
  setupRaw f
  let before ← f.pid "foreign-w7-p2"
  f.own "must-not-start-w0-p0"
  let malformed :=
    paneLine "must-not-start" "0" "0" (f.root / "home").toString "" ++ "pane\tbroken\n"
  let (importCode, _, _) ← f.importText malformed
  return importCode == 1 && before.isSome && (← f.pid "foreign-w7-p2") == before &&
      (←
        f.exportFields "previous"
            [("foreign-w7-p2", (f.root / "pane 'quoted' $cash a b").toString)]) &&
      !(← (System.FilePath.mk f.env.dir / "tmux-import.json").pathExists) &&
      !(← (System.FilePath.mk f.env.dir / "must-not-start-w0-p0.sock").pathExists)

private def topologyChange (f : Fixture) (remove : Bool) : IO Bool := do
  setupRaw f
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
  f.exportFields "changed" expected

private def liveCwd (f : Fixture) : IO Bool := do
  setupRaw f
  let changed := f.root / "home"
  let (code, _, _) ← f.cli #["run", "foreign-w7-p2", "cd", changed.toString]
  return code == 0 && (← f.cwdIs "foreign-w7-p2" changed) &&
      (← f.exportFields "changed-cwd" [("foreign-w7-p2", changed.toString)])

private def nativeRoundtrip (f : Fixture) : IO Bool := do
  let dir := f.root / "one two 'three' $four 会é"
  IO.FS.createDirAll dir
  let names := ["a.b", "plus+", "plain"]
  for name in names do
    f.start name dir
  let fields := names.map fun name => (name, dir.toString)
  unless ← f.exportFields "native" fields do
    return false
  let second := { f with env := { f.env with dir := (f.root / "second").toString } }
  IO.FS.createDirAll second.env.dir
  for name in names do
    second.own name
  let (code, _, _) ← second.cli #["tmux", "import", (f.root / "out" / "native").toString]
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
  let (code, _, _) ← f.cli #["tmux", "export", target.toString]
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
  setupRaw f
  let target := f.root / "out" / "private"
  let (code, _, _) ← f.cli #["tmux", "export", target.toString]
  return code == 0 && (← privateFile target) && (← namesIn (f.root / "out")) == ["private"] &&
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

private def obsoleteProvenance (f : Fixture) (matching : Bool) : IO Bool := do
  let cwd := (f.root / "home").toString
  f.seed "valid" cwd
  let text :=
    if matching then
      "{\"version\":1,\"source\":\"obsolete foreign source\",\"fields\":[[\"valid\",\"" ++ cwd ++
        "\"]]}"
    else "{not-json"
  let path := System.FilePath.mk f.env.dir / "tmux-import.json"
  IO.FS.writeFile path text
  return (← f.exportFields "current" [("valid", cwd)]) && (← readBytes path) == some text.toUTF8

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

private def discardedCommands (f : Fixture) : IO Bool := do
  setupRaw f
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
  let (importCode, _, _) ← f.cli #["tmux", "import", "save"] extra (some origin)
  let (exportCode, _, _) ← f.cli #["tmux", "export", "../out/relative"] extra (some origin)
  let exported ← IO.FS.readFile (f.root / "out" / "relative")
  return importCode == 0 && exportCode == 0 && (← f.cwdIs "relative-w0-p0" (f.root / "home")) &&
      commonFields "" exported == some [("relative-w0-p0", (f.root / "home").toString)]

private def fallbackHome (f : Fixture) (home : Option String) : IO Bool := do
  let text := paneLine "fallback" "0" "0" "~" ""
  IO.FS.writeFile (f.root / "source") text
  f.own "fallback-w0-p0"
  let (importCode, _, _) ← f.cli #["tmux", "import", (f.root / "source").toString] #[("HOME", home)]
  let target := f.root / "out" / "fallback"
  let (exportCode, _, _) ← f.cli #["tmux", "export", target.toString] #[("HOME", home)]
  let some accountHome := (← Std.Async.System.getCurrentUser).homeDir | return false
  let cwd ← IO.FS.realPath accountHome
  let exported ← IO.FS.readFile target
  return importCode == 0 && exportCode == 0 && (← f.cwdIs "fallback-w0-p0" cwd) &&
      commonFields "" exported == some [("fallback-w0-p0", cwd.toString)]

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
  let tmuxEnv ← tmuxFixtureEnv root
  let f : Fixture := { root, env := { bin, dir := (root / "state").toString }, owned, tmuxEnv }
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
            let (code, _, _) ← f.cli (#["tmux", "export"] ++ args)
            return code == 2 && (← namesIn (System.FilePath.mk f.env.dir)).isEmpty)]
  cases :=
    cases ++
      [("export refuses an empty session set without publishing", fun (f : Fixture) => f.refused),
        ("export accepts an explicit ./-save path", fun (f : Fixture) => do
          f.seed "native" (f.root / "home").toString
          let (code, _, _) ← f.cli #["tmux", "export", "./-save"] (cwd := some (f.root / "out"))
          return code == 0 && (← readBytes (f.root / "out" / "-save")).isSome),
        ("import retains no foreign source and exports current fields after source replacement and deletion",
          sourceIndependent),
        ("reimporting changed foreign metadata preserves the existing session and current export",
          metadataOnlyImport),
        ("a malformed import preserves existing sessions and creates no partial session",
          failedImport),
        ("adding a session generates complete current common fields", fun f =>
          topologyChange f false),
        ("removing an imported session generates complete current common fields", fun f =>
          topologyChange f true),
        ("export observes a live cwd change instead of its startup directory", liveCwd),
        ("native identities remain exact and preserve dot, plus and UTF8 cwd in a second state dir",
          nativeRoundtrip),
        ("export reads the changed checkpoint cwd after last detach and daemon crash",
          resumableCwd),
        ("export preserves an existing destination with no temporary leak", fun f =>
          publication f "file"),
        ("export preserves a symlink and its target with no temporary leak", fun f =>
          publication f "symlink"),
        ("export preserves a dangling symlink with no temporary leak", fun f =>
          publication f "dangling"),
        ("exported saves are private 0600 files with no temporary leak", privatePublication),
        ("a corrupt checkpoint refuses the entire export", fun f => corruptCheckpoint f false),
        ("an unreadable checkpoint refuses the entire export", fun f => corruptCheckpoint f true),
        ("corrupt obsolete provenance cannot block export and stays untouched", fun f =>
          obsoleteProvenance f false),
        ("matching obsolete provenance cannot replace current fields and stays untouched", fun f =>
          obsoleteProvenance f true),
        ("an unresponsive live socket refuses a partial export", incompleteSnapshot),
        ("unrepresentable cwd fields are refused without a partial export", unrepresentableCwd),
        ("discarded saved commands are never executed after a shell completion barrier",
          discardedCommands),
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
  cases :=
    cases ++
      [("tmux ls preserves parseSave order, original window context, canonical source and save time",
          catalogOrder),
        ("tmux ls escapes display controls while directory JSON preserves exact cwd",
          catalogControls),
        ("tmux ls freezes relative cwd against invocation without resolving its symlink spelling",
          catalogRelativeCwd),
        ("tmux ls leaves native listings, checkpoints, source bytes and saved commands untouched",
          catalogReadOnly),
        ("tmux ls displays missing directories but import preflights before any creation",
          catalogMissingCwd),
        ("an explicit historical save bypasses configured tmux and both conventional last files",
          explicitDiscovery),
        ("a configured directory with no last fails without falling back or scanning history",
          fun f => missingDiscovery f true),
        ("a conventional directory with no last fails without scanning history", fun f =>
          missingDiscovery f false),
        ("tmux discovery times out with an explicit-save diagnostic before effects",
          discoveryTimeout),
        ("tmux group and retired top-level spellings reject invalid arguments before effects",
          groupUsage),
        ("bare tmux and every group help spelling explain the saved commands without discovery",
          groupHelp)]
  for kind in ["absent", "malformed", "duplicate", "NUL", "empty"] do
    cases :=
      cases ++
        [(s!"tmux ls and import reject an {kind} save before output or session creation", fun f =>
            catalogInvalid f kind)]
  let discoveries : List (String × Discovery) :=
    [("configured absolute directory",
        { directory := fun root => (root / "configured").toString, source := "configured/last",
          legacy := true }),
      ("configured ~/ directory",
        { directory := fun _ => "~/configured", source := "home/configured/last", legacy := true }),
      ("configured bare ~ directory",
        { directory := fun _ => "~", source := "home/last", legacy := true }),
      ("configured invocation-relative directory with a trailing space",
        { directory := fun _ => "relative config ", source := "relative config /last",
          legacy := true }),
      ("legacy last before XDG", { source := "home/.tmux/resurrect/last", legacy := true }),
      ("XDG when only the legacy directory exists", {}),
      ("default data directory with unset XDG",
        { xdg := none, source := "home/.local/share/tmux/resurrect/last" }),
      ("default data directory with empty XDG",
        { xdg := some "", source := "home/.local/share/tmux/resurrect/last" }),
      ("legacy after a failed tmux query",
        { directory := fun _ => "configured", rc := "1", legacy := true,
          source := "home/.tmux/resurrect/last" }),
      ("XDG after a failed tmux query", { directory := fun _ => "configured", rc := "1" }),
      ("XDG without tmux on PATH", { missingTmux := true }),
      ("legacy without tmux on PATH",
        { missingTmux := true, legacy := true, source := "home/.tmux/resurrect/last" })]
  for (label, config) in discoveries do
    cases :=
      cases ++
        [(s!"tmux ls discovers {label} using only the read-only current-server query", fun f =>
            discovery f config)]
  let mut failures := 0
  for (index, (label, body)) in cases.zipIdx |>.map (fun (item, i) => (i, item)) do
    failures := failures + (← check root bin.toString index label body)
  if failures == 0 then
    IO.FS.removeDirAll root
  verdict { bin := bin.toString, dir := root.toString } failures

def run : IO UInt32 := do
  let binary :=
    (← IO.getEnv "LINGER_EXE").getD ((← IO.currentDir) / ".lake/build/bin/linger").toString
  runWith binary

end E2E.Interop
