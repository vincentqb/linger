module

import Linger.Import.Suites.Recipes
import Linger.Os.CoreCode.Answer
import Linger.Target.CoreCode.Name
import Linger.Session.CoreCode.Checkpoint
import all Linger.Import.WorldCode

public section

/-! # Linger.Import.Suites.Interop — a tmux-resurrect save as a read-only source

Each check owns fresh state below a new directory under `socketRoot`, since its
sessions put their sockets there. Its saves sit where tmux-resurrect keeps them for the fixture's
home and data directories, and every linger command it runs is bracketed by a digest of each
directory a save or archive was written to (`Fixture.cli`): a command that writes, moves or
deletes anything there fails the check. Foreign commands only write a fixture marker if
accidentally executed; a subsequent shell command is the completion barrier. No tmux server or
user save is involved.

The parser supplies the common-field projection. Checkpoint fixtures use the
production codec, and the crash check also exercises an actual last detach.
-/

namespace Linger.Import.Suites.Interop

open Verify.Harness
open Linger.Import.Suites.Recipes (paneLine tmuxFixtureEnv sourceNames)
open Linger.Session.Checkpoint

private def process (args : IO.Process.SpawnArgs) (ms : Nat := hangMs) :
    IO (UInt32 × String × String) := do
  let child ←
    IO.Process.spawn
        { args with
          stdin := .null, stdout := .piped, stderr := .piped }
  match ← waitOrKill child ms with
  | some code =>
    return (code, ← child.stdout.readToEnd, ← child.stderr.readToEnd)
  | none =>
    throw (IO.userError s!"process timed out: {args.cmd} {args.args}")

private structure Fixture where
  root : System.FilePath
  env : Env
  owned : IO.Ref (List (Env × String))
  tmuxEnv : Array (String × Option String)
  /-- The directories a save or a capture archive was written to, which no command may change. -/
  saveDirs : IO.Ref (List System.FilePath)

private def Fixture.procEnv (f : Fixture) : Array (String × Option String) :=
  f.env.procEnv ++
    #[("HOME", some (f.root / "home").toString), ("XDG_DATA_HOME", some (f.root / "data").toString),
      ("LINGER_SESSION", none), ("ENV", none), ("BASH_ENV", none)] ++
    f.tmuxEnv

/-- What a directory holds, as a digest of each entry's name, type, size, modification time and,
for a file, its bytes; `none` for no directory. -/
private def digest (dir : System.FilePath) : IO (Option UInt64) := do
  let some entries ← (dir.readDir).toBaseIO.map (·.toOption) | return none
  let mut acc : UInt64 := 7
  for entry in entries.qsort (·.fileName < ·.fileName) do
    let metadata ← entry.path.symlinkMetadata
    let bytes ←
      if metadata.type == .file then
        IO.FS.readBinFile entry.path
      else
        pure ByteArray.empty
    acc :=
      mixHash acc
        (hash
          (entry.fileName, toString (repr metadata.type), metadata.byteSize,
            toString metadata.modified.sec, metadata.modified.nsec, bytes))
  return some acc

/-- The digests of every directory a save or archive was written to. -/
private def Fixture.saveState (f : Fixture) : IO (List (System.FilePath × Option UInt64)) := do
  (← f.saveDirs.get).mapM fun dir => return (dir, ← digest dir)

/-- Run linger with the fixture's environment, failing the check when the command changed a
directory a save or archive was written to: linger writes, moves and deletes nothing in tmux's
directory. -/
private def Fixture.cli (f : Fixture) (args : Array String)
    (extra : Array (String × Option String) := #[]) (cwd : Option System.FilePath := none) :
    IO (UInt32 × String × String) := do
  let before ← f.saveState
  let result ←
    process { cmd := f.env.bin, args, env := f.procEnv ++ extra, cwd := cwd.or (some f.root) }
  let after ← f.saveState
  unless after == before do
    throw (IO.userError s!"linger {args} changed tmux's directory")
  return result

private def Fixture.own (f : Fixture) (name : String) : IO Unit :=
  f.owned.modify fun names =>
    if names.any (fun (e, n) => e.dir == f.env.dir && n == name) then names
    else (f.env, name) :: names

private def Fixture.info (f : Fixture) (name field : String) : IO (Option String) := do
  let (code, out, _) ← f.cli #["ls", name, "--porcelain"]
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
      return (← Os.Shell.getcwdOf pid) == dir.toString

/-- The field `key` that session `name`'s checkpoint holds. -/
private def Fixture.savedLabel (f : Fixture) (name key : String) : IO (Option String) := do
  match ← (IO.FS.readBinFile (System.FilePath.mk f.env.dir / s!"{name}.ckpt")).toBaseIO with
  | .ok bytes =>
    return (Linger.Session.Checkpoint.loadBytes bytes).bind (·.fields.lookup key)
  | .error _ =>
    return none

/-- Run a saved session's shell again, as an attach would: whether `resume` succeeded. -/
private def Fixture.resume (f : Fixture) (name : String) : IO Bool := do
  return (← f.cli #["resume", name]).1 == 0

private def Fixture.start (f : Fixture) (name : String) (dir : System.FilePath) : IO Unit := do
  f.own name
  let (code, _, err) ← f.cli #["start", name, "/bin/sh"] (cwd := some dir)
  unless code == 0 && (← f.cwdIs name dir) do
    throw (IO.userError s!"session did not start in {dir}: {name}: {err}")

private def Fixture.seed (f : Fixture) (name cwd : String) : IO Unit := do
  let ck : Ckpt Terminal.Vt.Vt := { vt := Terminal.Vt.Vt.init 20 5, cwd, fields := [] }
  IO.FS.writeBinFile (System.FilePath.mk f.env.dir / s!"{name}.ckpt") (saveBytes ck)

/-- Where tmux-resurrect keeps the latest save for the fixture's data directory. -/
private def Fixture.latest (f : Fixture) : System.FilePath := f.root / "data/tmux/resurrect/last"

/-- The panes of the save `text`, named as `ls` names them (`Resurrect.named`); none for a save
that does not parse. -/
private def savedPanes (f : Fixture) (text : String) : List Linger.Import.Resurrect.Pane :=
  match Linger.Import.Resurrect.parseSave (f.root / "home").toString text with
  | .ok raw =>
    Linger.Import.Resurrect.named (raw.map (Linger.Import.Resurrect.preparePane text raw))
  | .error _ => []

/-- Write `text` as the save at `path`, with its file's UTC mtime fixed, and own its panes'
names. Its directory is one no command may change. -/
private def Fixture.writeSave (f : Fixture) (text : String) (path : System.FilePath := f.latest) :
    IO Unit := do
  let dir := path.parent.getD f.root
  IO.FS.createDirAll dir
  IO.FS.writeFile path text
  let (code, _, err) ←
    process
        { cmd := "touch", args := #["-h", "-t", "200102030405.06", path.toString],
          env := #[("TZ", some "UTC")] }
  unless code == 0 do
    throw (IO.userError s!"could not timestamp fixture save: {err}")
  f.saveDirs.modify fun dirs => if dirs.contains dir then dirs else dirs ++ [dir]
  for pane in savedPanes f text do
    f.own pane.name

/-- Make `text` the latest save and resume each of its panes, as an attach would: the first
failing resume's result, or, for a save that does not parse, what `ls` says of it. -/
private def Fixture.importText (f : Fixture) (text : String) : IO (UInt32 × String × String) := do
  f.writeSave text
  match Linger.Import.Resurrect.parseSave (f.root / "home").toString text with
  | .ok _ =>
    for pane in savedPanes f text do
      let result ← f.cli #["resume", pane.name]
      unless result.1 == 0 do
        return result
    return (0, "", "")
  | .error _ =>
    let (_, out, err) ← f.cli #["ls", "--porcelain"]
    return (1, out, err)

private def readBytes (path : System.FilePath) : IO (Option ByteArray) := do
  try
    return some (← IO.FS.readBinFile path)
  catch _ =>
    return none

private def namesIn (dir : System.FilePath) : IO (List String) := do
  return (← dir.readDir).toList.map (·.fileName) |>.toArray.qsort (· < ·) |>.toList

private def commonFields (home text : String) : Option (List (String × String)) :=
  (Linger.Import.Resurrect.parseSave home text).toOption.map fun raw =>
    Linger.Import.Resurrect.common
      (Linger.Import.Resurrect.named (raw.map (Linger.Import.Resurrect.preparePane text raw)))

private def sameFields (a b : List (String × String)) : Bool :=
  a.toArray.qsort (fun x y => x.1 < y.1 || (x.1 == y.1 && x.2 < y.2)) ==
    b.toArray.qsort (fun x y => x.1 < y.1 || (x.1 == y.1 && x.2 < y.2))

/-- `ls --resurrect`: its exit status, what it wrote to standard output and to standard error,
and whether it left the state directory and the output directory as they were, since it
writes no file. -/
private def Fixture.export (f : Fixture) (extra : Array (String × Option String) := #[])
    (cwd : Option System.FilePath := none) : IO (UInt32 × String × String × Bool) := do
  let state ← namesIn (System.FilePath.mk f.env.dir)
  let outs ← namesIn (f.root / "out")
  let (code, out, err) ← f.cli #["ls", "--resurrect"] extra cwd
  -- the export takes the locks of the saved sessions it reads, whose lock files may appear
  let unchanged :=
    ((← namesIn (System.FilePath.mk f.env.dir)).filter (!state.contains ·)).all
        (fun name => name.endsWith ".lock" || name == ".locks") &&
      (← namesIn (f.root / "out")) == outs
  return (code, out, err, unchanged)

/-- `ls --resurrect` writes, to standard output alone, a save of exactly `expected`; the check
keeps that save as `out/file`. -/
private def Fixture.exportFields (f : Fixture) (file : String) (expected : List (String × String)) :
    IO Bool := do
  let (code, text, _, unchanged) ← f.export
  IO.FS.writeFile (f.root / "out" / file) text
  let some fields := commonFields (f.root / "home").toString text | return false
  return code == 0 && unchanged && sameFields fields expected

/-- `ls --resurrect` refuses, writing nothing to standard output and saying why. -/
private def Fixture.refused (f : Fixture) : IO Bool := do
  let (code, out, err, unchanged) ← f.export
  return code == 1 && out.isEmpty && err.startsWith "linger: " && unchanged

private def link (target path : System.FilePath) : IO Unit := do
  let (code, _, err) ← process { cmd := "ln", args := #["-s", target.toString, path.toString] }
  unless code == 0 do
    throw (IO.userError s!"could not create fixture symlink: {err}")

private def queryCall : String := "CALL\x00show-options\x00-gqv\x00@resurrect-dir\x00\n"

private def Fixture.queries (f : Fixture) : IO String := IO.FS.readFile (f.root / "tmux-calls")

private def field (row : List (String × String)) (key : String) : String := (row.lookup key).getD ""

/-- The source rows of a porcelain listing, as records. -/
private def sourceRecords (listing : String) : List (List (String × String)) :=
  ((listing.splitOn "\n\n").map records).filter
    (·.lookup "source" == some Linger.Import.Resurrect.sourceName)

/-- The porcelain rows of the saved panes `ls` lists match the save's panes `expected`, by name
order, each with its source, its status and state, the window's name as its description, its
directory and the provenance an import records. -/
private def Fixture.rowsMatch (f : Fixture) (text out : String) (expected : List String) : Bool :=
  match Linger.Import.Resurrect.parseSave (f.root / "home").toString text with
  | .error _ => false
  | .ok raw =>
    let panes :=
      Linger.Import.Resurrect.named (raw.map (Linger.Import.Resurrect.preparePane text raw))
    let rows := sourceRecords out
    rows.map (field · "name") == expected &&
      rows.all fun row =>
        match panes.find? (·.name == field row "name") with
        | none => false
        | some pane =>
          let dir :=
            if pane.dir.isEmpty || (System.FilePath.mk pane.dir).isAbsolute then pane.dir
            else (f.root / pane.dir).toString
          let shown := Linger.Import.Resurrect.diagnostic
          row.map (·.1) ==
              ["name", "state", "status", "source"] ++
                (if pane.details.windowTitle.isEmpty then [] else ["description"]) ++
                ["directory", "tmux.session", "tmux.window", "tmux.pane", "tmux.title",
                  "tmux.command", "tmux.saved-command", "tmux.window-title"] &&
            field row "status" == Linger.Display.Status.name .resumable &&
            field row "state" == "resumable" &&
            field row "description" == shown pane.details.windowTitle &&
            field row "directory" == shown dir &&
            field row "tmux.session" == shown pane.details.session &&
            field row "tmux.window" == shown pane.details.window &&
            field row "tmux.pane" == shown pane.details.index &&
            field row "tmux.title" == shown pane.details.title &&
            field row "tmux.command" == shown pane.details.command &&
            field row "tmux.saved-command" == shown pane.details.savedCommand &&
            field row "tmux.window-title" == shown pane.details.windowTitle

private def sourceOrder (f : Fixture) : IO Bool := do
  let first := (f.root / "first dir").toString
  let second := (f.root / "second dir").toString
  let third := (f.root / "third dir").toString
  let text :=
    "# Save order is deliberately neither name nor numeric order.\n" ++
      "window\tzeta\t12\t:Review window\tlayout\tunused\n" ++
      paneLine "zeta" "12" "8" first "vi 'draft.txt'" ++
      "state\tzeta\tunused\n" ++
      paneLine "alpha" "3" "1" second "" ++
      paneLine "zeta" "12" "2" third "make check" ++
      "window\talpha\t3\t:Build window\tignored\n"
  f.writeSave text
  let (rc, out, err) ← f.cli #["ls", "--porcelain"]
  let (humanRc, human, humanErr) ← f.cli #["ls"]
  let rows := (lines human).filter (has · "(saved by tmux)")
  return rc == 0 && err.isEmpty &&
      f.rowsMatch text out ["Build_window", "Review_window", "Review_window-2"] &&
      humanRc == 0 &&
      humanErr.isEmpty &&
      rows.length == 3 &&
      (rows.zip ["Build_window", "Review_window", "Review_window-2"]).all
        (fun (row, name) => has row name) &&
      has (rows[0]?.getD "") "Build window" &&
      has (rows[1]?.getD "") "Review window" &&
      (← f.queries) == queryCall ++ queryCall &&
      (← namesIn (System.FilePath.mk f.env.dir)).isEmpty

/-- A pane takes its name from its window, as a key, and a later pane whose window's name an
earlier pane took gets the next natural-order suffix, so two windows of one name and two panes of
one window each get their own; a pane of a window the save names nothing keeps the name its record
projects. -/
private def windowNames (f : Fixture) : IO Bool := do
  let home := (f.root / "home").toString
  f.writeSave
      ("window\tdesk\t0\t:editor\n" ++ "window\tdesk\t1\t:editor\n" ++
        "window\tlab\t0\t:my notes\n" ++
        paneLine "desk" "0" "0" home "" ++
        paneLine "desk" "0" "1" home "" ++
        paneLine "desk" "1" "0" home "" ++
        paneLine "lab" "0" "0" home "" ++
        paneLine "bare" "0" "0" home "")
  let (rc, out, err) ← f.cli #["ls", "--porcelain"]
  let names := sourceNames out
  let desk := (sourceRecords out).filter (field · "tmux.session" == "desk")
  return rc == 0 && err.isEmpty &&
      names == ["bare-w0-p0", "editor", "editor-2", "editor-3", "my_notes"] &&
      desk.map (fun row => (field row "tmux.window", field row "tmux.pane", field row "name")) ==
        [("0", "0", "editor"), ("0", "1", "editor-2"), ("1", "0", "editor-3")]

private def sourceControls (f : Fixture) : IO Bool := do
  let controls := "\x07\x1b[2J\r\x7f\u0080\u0085\u009b\u009d\u009f"
  let dir := (f.root / ("quote \" and backslash\\ café 会" ++ controls ++ "  trailing ")).toString
  let command := "printf 'saved command' " ++ controls
  let text :=
    "window\tcontrol\t4\t:title" ++ controls ++ "\n" ++ paneLine "control" "4" "0" dir command
  f.writeSave text
  let (rc, out, err) ← f.cli #["ls", "--porcelain"]
  let (humanRc, human, humanErr) ← f.cli #["ls"]
  let printable := fun c => Terminal.Render.textChar c == c
  return rc == 0 && err.isEmpty &&
      f.rowsMatch text out [Linger.Target.Name.sanitize ("title" ++ controls)] &&
      humanRc == 0 &&
      humanErr.isEmpty &&
      human.toList.all (fun c => c == '\n' || printable c) &&
      (out.splitOn "\n").all (fun row => row.toList.all (fun c => c == '\t' || printable c)) &&
      has out (Linger.Import.Resurrect.diagnostic command) &&
      (← namesIn (System.FilePath.mk f.env.dir)).isEmpty

private def sourceRelativeCwd (f : Fixture) : IO Bool := do
  IO.FS.createDirAll (f.root / "physical" / "child")
  link (f.root / "physical" / "child") (f.root / "alias")
  let text := paneLine "relative" "0" "0" "alias/.." ""
  f.writeSave text
  let (rc, out, err) ← f.cli #["ls", "--porcelain"]
  return rc == 0 && err.isEmpty && f.rowsMatch text out ["relative-w0-p0"] &&
      has out s!"directory\t{f.root / "alias" / ".."}\n" &&
      !has out (f.root / "physical").toString &&
      (← namesIn (System.FilePath.mk f.env.dir)).isEmpty

private def sourceReadOnly (f : Fixture) : IO Bool := do
  let marker := f.root / "saved-command-marker"
  IO.FS.writeFile marker "UNTOUCHED\n"
  f.seed "native.only" (f.root / "home").toString
  let before ← f.cli #["ls", "native.only", "--porcelain"]
  let checkpoint ← readBytes (System.FilePath.mk f.env.dir / "native.only.ckpt")
  let entries ← namesIn (System.FilePath.mk f.env.dir)
  let command := s!"printf EXECUTED > '{marker}'"
  let text :=
    paneLine "foreign" "2" "0" (f.root / "home").toString command ++
      "window\tforeign\t2\t:Original title\tlayout\n" ++
      "state\tforeign\tignored\nfuture-record\tignored\x00metadata\n"
  f.writeSave text
  let (rc, out, err) ← f.cli #["ls", "--porcelain"]
  let (humanRc, human, humanErr) ← f.cli #["ls"]
  IO.sleep 200 -- negative assertion: allow an accidentally started saved command to run
  let after ← f.cli #["ls", "native.only", "--porcelain"]
  return rc == 0 && err.isEmpty && f.rowsMatch text out ["Original_title"] && humanRc == 0 &&
      humanErr.isEmpty &&
      before.1 == 0 &&
      after == before &&
      has out "native.only" &&
      has out "EXECUTED" &&
      has human "Original title" &&
      !has out "future-record" &&
      (← IO.FS.readFile f.latest) == text &&
      (← IO.FS.readFile marker) == "UNTOUCHED\n" &&
      (← readBytes (System.FilePath.mk f.env.dir / "native.only.ckpt")) == checkpoint &&
      (← namesIn (System.FilePath.mk f.env.dir)) == entries

/-- A pane is listed exactly while linger keeps no record of its name: a live session's socket, a
saved one's checkpoint and an ended one's end record each hide the pane of that name, and
`ls NAME` lists the pane of a name no record names. -/
private def listedUnrecorded (f : Fixture) : IO Bool := do
  let home := (f.root / "home").toString
  f.start "live-w0-p0" (f.root / "home")
  f.seed "saved-w0-p0" home
  f.start "ended-w0-p0" (f.root / "home")
  let (killed, _, _) ← f.cli #["kill", "ended-w0-p0"]
  let text :=
    paneLine "live" "0" "0" home "" ++ paneLine "saved" "0" "0" home "" ++
      paneLine "ended" "0" "0" home "" ++
      paneLine "fresh" "0" "0" home ""
  f.writeSave text
  let (rc, out, err) ← f.cli #["ls", "--porcelain"]
  let (namedRc, named, _) ← f.cli #["ls", "fresh-w0-p0", "--porcelain"]
  let (endedRc, ended, _) ← f.cli #["ls", "ended-w0-p0", "--porcelain"]
  return killed == 0 && rc == 0 && err.isEmpty && sourceNames out == ["fresh-w0-p0"] &&
      namedRc == 0 &&
      sourceNames named == ["fresh-w0-p0"] &&
      endedRc == 0 &&
      sourceNames ended == [] &&
      has ended "name\tended-w0-p0" &&
      (← (System.FilePath.mk f.env.dir / "ended-w0-p0.end").pathExists)

/-- The saved panes sort last within `~`: after a saved session whose name sorts after theirs. -/
private def sourceLast (f : Fixture) : IO Bool := do
  f.seed "zzz" (f.root / "home").toString
  f.writeSave (paneLine "aaa" "0" "0" (f.root / "home").toString "")
  let (rc, human, _) ← f.cli #["ls"]
  let names := (lines human).filterMap fun line => (line.splitOn " ")[1]?
  return rc == 0 && names == ["zzz", "aaa-w0-p0"]

/-- An attach of a saved pane through a terminal writes its checkpoint and attaches to the fresh
shell in its directory, and the pane is no longer listed as saved. -/
private def attachPane (f : Fixture) : IO Bool := do
  let dir := f.root / "attached cwd"
  IO.FS.createDirAll dir
  let marker := f.root / "saved-command-ran"
  f.writeSave
      ("window\tpty\t1\t:Pty window\n" ++
        paneLine "pty" "1" "0" dir.toString s!"printf bad > '{marker}'")
  let client ←
    f.env.spawnEnv
        (#[s!"HOME={f.root}/home", s!"XDG_DATA_HOME={f.root}/data"] ++
          f.tmuxEnv.filterMap fun (k, v) => v.map (s!"{k}={·}"))
        #["attach", "Pty_window"]
  try
    let shown ← client.awaitNeedle "Saved foreground command"
    let attached ←
      waitFor 5000 do
          return (← f.info "Pty_window" "clients") == some "1"
    let here ← f.cwdIs "Pty_window" dir
    let description ← f.info "Pty_window" "description"
    client.detach
    let _ ← client.reap
    let (_, out, _) ← f.cli #["ls", "--porcelain"]
    return shown && attached && here && description == some "Pty window" && sourceNames out == [] &&
        has out "name\tPty_window" &&
        !(← marker.pathExists)
  finally
    client.bye (sendDetach := false)

/-- An attach or a resume never replaces a record: a name with a checkpoint resumes that
checkpoint, not the pane, and a name with only an end record starts no pane and writes no
checkpoint. -/
private def adoptExclusive (f : Fixture) : IO Bool := do
  let mine := f.root / "mine"
  IO.FS.createDirAll mine
  f.seed "taken-w0-p0" mine.toString
  let checkpoint := System.FilePath.mk f.env.dir / "taken-w0-p0.ckpt"
  let before ← readBytes checkpoint
  f.start "gone-w0-p0" (f.root / "home")
  let (killed, _, _) ← f.cli #["kill", "gone-w0-p0"]
  f.writeSave
      (paneLine "taken" "0" "0" (f.root / "home").toString "" ++
        paneLine "gone" "0" "0" (f.root / "home").toString "")
  let unchanged := (← readBytes checkpoint) == before
  let (rc, _, _) ← f.cli #["resume", "taken-w0-p0"]
  let here ← f.cwdIs "taken-w0-p0" mine
  let labels ← f.info "taken-w0-p0" "tmux.session"
  let (goneRc, _, _) ← f.cli #["resume", "gone-w0-p0"]
  return killed == 0 && unchanged && rc == 0 && here && labels.isNone && goneRc == 127 &&
      !(← (System.FilePath.mk f.env.dir / "gone-w0-p0.ckpt").pathExists)

/-- A kill of a saved pane writes an end record and nothing else, which says only that the pane
was dismissed, so `wait` answers for it, as before the kill, that no session has the name, and no
signal; the pane stays hidden, even once the save is written again; a kill of a name neither
linger nor the save knows finds nothing. -/
private def killDismisses (f : Fixture) : IO Bool := do
  let text := paneLine "dismissed" "0" "0" (f.root / "home").toString ""
  f.writeSave text
  let before ← namesIn (System.FilePath.mk f.env.dir)
  let (waitBefore, _, _) ← f.cli #["wait", "dismissed-w0-p0"]
  let (rc, _, err) ← f.cli #["kill", "dismissed-w0-p0"]
  let after ← namesIn (System.FilePath.mk f.env.dir)
  let written := after.filter (!before.contains ·)
  let (waitRc, _, waitErr) ← f.cli #["wait", "dismissed-w0-p0"]
  let (_, out, _) ← f.cli #["ls", "--porcelain"]
  f.writeSave text
  let (_, again, _) ← f.cli #["ls", "--porcelain"]
  let (unknownRc, _, _) ← f.cli #["kill", "unknown-w0-p0"]
  return rc == 0 && err.isEmpty &&
      written.all
        (fun name => name == "dismissed-w0-p0.end" || name.endsWith ".lock" || name == ".locks") &&
      written.contains "dismissed-w0-p0.end" &&
      waitBefore == (Linger.Os.Answer.code .notFound) &&
      waitRc == (Linger.Os.Answer.code .notFound) &&
      has waitErr "dismissed" &&
      sourceNames out == [] &&
      sourceNames again == [] &&
      unknownRc == 127 &&
      !(← (System.FilePath.mk f.env.dir / "unknown-w0-p0.end").pathExists) &&
      !(← (System.FilePath.mk f.env.dir / "dismissed-w0-p0.ckpt").pathExists)

/-- `tmux`, a word no command has, gets the usage error any unknown word gets, saying nothing of
what it once was, and reads no save. -/
private def retiredSpellings (f : Fixture) : IO Bool := do
  f.writeSave (paneLine "mustnot" "0" "0" (f.root / "home").toString "")
  let (_, _, unknown) ← f.cli #["no-such-word"]
  let mut ok := true
  for args in
    [#["tmux"], #["tmux", "help"], #["tmux", "ls", "--porcelain"], #["tmux", "select"],
      #["tmux", "import", "save"], #["tmux", "export", "save"]] do
    let (rc, out, err) ← f.cli args
    ok := ok && rc == 2 && out.isEmpty && err == unknown && !has err "removed"
  return ok && (← f.queries).isEmpty && (← namesIn (System.FilePath.mk f.env.dir)).isEmpty &&
      (← namesIn (f.root / "out")).isEmpty

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
    f.writeSave (paneLine s!"saved{index}" "0" "0" (f.root / "home").toString "") (f.root / file)
  let some index := files.idxOf? config.source | return false
  let extra :=
    #[("LINGER_TMUX_DIRECTORY", some (config.directory f.root)), ("LINGER_TMUX_RC", some config.rc),
        ("XDG_DATA_HOME", config.xdg)] ++
      if config.missingTmux then #[("PATH", some (f.root / "tmux-sockets").toString)] else #[]
  let (rc, out, err) ← f.cli #["ls", "--porcelain"] extra
  let (humanRc, human, humanErr) ← f.cli #["ls"] extra
  return rc == 0 && err.isEmpty && sourceNames out == [s!"saved{index}-w0-p0"] && humanRc == 0 &&
      humanErr.isEmpty &&
      has human s!"saved{index}-w0-p0" &&
      (← f.queries) == (if config.missingTmux then "" else queryCall ++ queryCall) &&
      (← namesIn (System.FilePath.mk f.env.dir)).isEmpty

private def missingDiscovery (f : Fixture) (configured : Bool) : IO Bool := do
  let dir := if configured then f.root / "configured" else f.root / "data/tmux/resurrect"
  -- Historical files are never merged or substituted for a missing last.
  f.writeSave (paneLine "historical" "0" "0" (f.root / "home").toString "")
      (dir / "tmux_resurrect_20010203T040506.txt")
  if configured then
    f.writeSave (paneLine "fallback" "0" "0" (f.root / "home").toString "")
        (f.root / "home/.tmux/resurrect/last")
  let (rc, out, err) ←
    f.cli #["ls", "--porcelain"]
        #[("LINGER_TMUX_DIRECTORY", some (if configured then dir.toString else ""))]
  return rc == 0 && sourceNames out == [] && err.isEmpty && (← f.queries) == queryCall &&
      (← namesIn (System.FilePath.mk f.env.dir)).isEmpty

/-- The fixture's tmux answers only after twice `hangMs`, and `Fixture.cli` gives up at `hangMs`:
a query that timed out but was then waited for, rather than retired, cannot end in time, however
fast the host. The listing still lists the sessions, and says why it lists no pane. -/
private def discoveryTimeout (f : Fixture) : IO Bool := do
  f.writeSave (paneLine "fallback" "0" "0" (f.root / "home").toString "")
  f.seed "native" (f.root / "home").toString
  let (rc, out, err) ← f.cli #["ls", "--porcelain"] #[("LINGER_TMUX_WAIT", some "1")]
  return rc == 0 && sourceNames out == [] && has out "name\tnative" &&
      has err "tmux configuration query timed out" &&
      (← f.queries) == queryCall

private def sourceInvalid (f : Fixture) (kind : String) : IO Bool := do
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
    f.writeSave text
  let (rc, out, err) ← f.cli #["ls", "--porcelain"]
  let (resumed, _, _) ← f.cli #["resume", "mustnot-w1-p0"]
  let (killed, _, _) ← f.cli #["kill", "mustnot-w1-p0"]
  let said :=
    if kind == "absent" then err.isEmpty else has err "could not read the tmux-resurrect save"
  return rc == 0 && sourceNames out == [] && said && resumed == 127 && killed == 127 &&
      (← namesIn (System.FilePath.mk f.env.dir)).all
        (fun name => name.endsWith ".lock" || name == ".locks") &&
      !(← (System.FilePath.mk f.env.dir / "mustnot-w1-p0.ckpt").pathExists) &&
      !(← (System.FilePath.mk f.env.dir / "mustnot-w1-p0.end").pathExists)

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
  unless code == 0 && (← f.cwdIs "unknown_window_fields" dir) do
    throw (IO.userError s!"foreign pane did not resume in its physical cwd: {err}")

private def sourceIndependent (f : Fixture) : IO Bool := do
  setupRaw f
  let expected := [("unknown_window_fields", (f.root / "pane 'quoted' $cash a b").toString)]
  f.writeSave "source replaced after import\n"
  let first ← f.exportFields "replaced" expected
  IO.FS.removeFile f.latest
  let second ← f.exportFields "removed" expected
  return first && second && !(← (System.FilePath.mk f.env.dir / "tmux-import.json").pathExists) &&
      (← namesIn (f.root / "out")) == ["removed", "replaced"]

private def metadataOnlyImport (f : Fixture) : IO Bool := do
  setupRaw f
  let before ← f.pid "unknown_window_fields"
  let expected := [("unknown_window_fields", (f.root / "pane 'quoted' $cash a b").toString)]
  let first ← f.exportFields "first" expected
  let latest := rawText f "latest successful import" ++ "last-record\tno trailing newline"
  let (importCode, _, _) ← f.importText latest
  let second ← f.exportFields "second" expected
  return importCode == 0 && before.isSome && (← f.pid "unknown_window_fields") == before && first &&
      second &&
      (← readBytes (f.root / "out" / "first")) == (← readBytes (f.root / "out" / "second")) &&
      !(← (System.FilePath.mk f.env.dir / "tmux-import.json").pathExists)

private def failedImport (f : Fixture) : IO Bool := do
  setupRaw f
  let before ← f.pid "unknown_window_fields"
  f.own "must-not-start-w0-p0"
  let malformed :=
    paneLine "must-not-start" "0" "0" (f.root / "home").toString "" ++ "pane\tbroken\n"
  let (importCode, _, _) ← f.importText malformed
  return importCode == 1 && before.isSome && (← f.pid "unknown_window_fields") == before &&
      (←
        f.exportFields "previous"
            [("unknown_window_fields", (f.root / "pane 'quoted' $cash a b").toString)]) &&
      !(← (System.FilePath.mk f.env.dir / "tmux-import.json").pathExists) &&
      !(← (System.FilePath.mk f.env.dir / "must-not-start-w0-p0.sock").pathExists)

private def topologyChange (f : Fixture) (remove : Bool) : IO Bool := do
  setupRaw f
  let dir := f.root / "home"
  f.start "added.name+" dir
  if remove then
    let (code, _, _) ← f.cli #["kill", "unknown_window_fields"]
    unless
      code == 0 &&
        (←
          waitFor 5000 do
              return !(←
                    (System.FilePath.mk f.env.dir / "unknown_window_fields.sock").pathExists)) do
      throw (IO.userError "fixture session was not removed")
  let expected :=
    [("added.name+", dir.toString)] ++
      if remove then []
      else [("unknown_window_fields", (f.root / "pane 'quoted' $cash a b").toString)]
  f.exportFields "changed" expected

private def liveCwd (f : Fixture) : IO Bool := do
  setupRaw f
  let changed := f.root / "home"
  let (code, _, _) ← f.cli #["send", "unknown_window_fields", s!"cd {changed}\n"]
  return code == 0 && (← f.cwdIs "unknown_window_fields" changed) &&
      (← f.exportFields "changed-cwd" [("unknown_window_fields", changed.toString)])

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
  f.writeSave (← IO.FS.readFile (f.root / "out" / "native"))
  let mut ready := true
  for name in names do
    let resumed ← second.resume name
    let there ← second.cwdIs name dir
    let here ← f.cwdIs name dir
    ready := ready && resumed && there && here
  return ready && (← second.exportFields "second" fields)

private def resumableCwd (f : Fixture) : IO Bool := do
  let name := "resumed.name"
  f.start name (f.root / "home")
  let changed := f.root / "saved cwd"
  IO.FS.createDirAll changed
  let (code, _, _) ← f.cli #["send", name, s!"cd '{changed}'\n"]
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
            return (loadBytes bytes).any (·.cwd == changed.toString)) do
    throw (IO.userError "last detach did not checkpoint the changed cwd")
  try
    Os.Shell.kill daemon.toUInt32 9
    unless
      ←
        waitFor 5000
            (do
              return !(← Os.Shell.alive daemon.toUInt32)) do
      throw (IO.userError "fixture daemon did not stop")
    return (← f.exportFields "resumable" [(name, changed.toString)]) && (← f.pid name).isNone
  finally
    if ← Os.Shell.alive shellPid then
      Os.Shell.kill shellPid 9

/-- The row of session `name` in `ls`, empty when none lists it. -/
private def Fixture.row (f : Fixture) (name : String) : IO String := do
  let (_, out, _) ← f.cli #["ls"]
  return ((out.splitOn "\n").find? fun line => (line.splitOn " ")[1]? == some name).getD ""

/-- A session an import made before a row had a description: its checkpoint, in the format a
linger of then wrote, holds the import's provenance and no description. Resumed, its row shows the
description today's import gives, the window's name, until a rename ends it, which a crash and a
resume keep ended. -/
private def olderImport (f : Fixture) : IO Bool := do
  let dir := f.root / "home"
  let pane : Linger.Import.Resurrect.Pane :=
    { name := "older-w4-p0", dir := dir.toString, line := 1,
      details :=
        { session := "older", window := "4", index := "0", title := "pane title", command := "sh",
          windowTitle := "Old window" } }
  let today := Linger.Import.Resurrect.checkpoint pane none
  -- the record of a linger older than descriptions: the same layout under the tag 3
  let old : Ckpt Terminal.Vt.Vt :=
    { today with fields := today.fields.filter (·.1 != "description") }
  f.own "newer"
  let checkpoint := System.FilePath.mk f.env.dir / s!"{pane.name}.ckpt"
  IO.FS.writeBinFile checkpoint ((saveBytes old).set! 4 3)
  unless ← f.resume pane.name do
    throw (IO.userError "older import did not resume")
  let described ← f.info pane.name "description"
  let row ← f.row pane.name
  let (renamed, _, _) ← f.cli #["rename", pane.name, "newer"]
  let after ← f.info "newer" "description"
  let some shellPid ← f.pid "newer" | throw (IO.userError "fixture shell pid is missing")
  let (psCode, parent, _) ←
    process { cmd := "ps", args := #["-o", "ppid=", "-p", toString shellPid] }
  let some daemon :=
    parent.trimAscii.toString.toNat? | throw (IO.userError "fixture daemon pid is missing")
  unless psCode == 0 && 1 < daemon && daemon < UInt32.size do
    throw (IO.userError "invalid fixture daemon pid")
  Os.Shell.kill daemon.toUInt32 9
  unless
    ←
      waitFor 5000
          (do
            return !(← Os.Shell.alive daemon.toUInt32)) do
    throw (IO.userError "older import daemon did not stop")
  if ← Os.Shell.alive shellPid then
    Os.Shell.kill shellPid 9
  let resumed ← f.resume "newer"
  let again ← f.info "newer" "description"
  let window ← f.info "newer" "tmux.window-title"
  return described == some "Old window" && has row "Old window" && renamed == 0 && after.isNone &&
      resumed &&
      again.isNone &&
      window == some "Old window"

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
  let fd ← Os.Shell.unixListen socket.toString
  try
    f.refused
  finally
    Os.Shell.close fd
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
  let (code, _, _) ← f.cli #["send", "unknown_window_fields", s!"printf ready > '{barrier}'\n"]
  let ready ←
    waitFor 5000 do
        return (← readBytes barrier) == some "ready".toUTF8
  return code == 0 && ready && !(← (f.root / "saved-command-ran").pathExists)

/-- `ls --resurrect` writes its save to standard output alone, a private file of no one's: no file
appears in the state or output directory, and the save it writes reads back as the sessions. -/
private def exportStdout (f : Fixture) : IO Bool := do
  setupRaw f
  let (code, text, err, unchanged) ← f.export
  return code == 0 && err.isEmpty && unchanged &&
      commonFields (f.root / "home").toString text ==
        some [("unknown_window_fields", (f.root / "pane 'quoted' $cash a b").toString)] &&
      (← namesIn (System.FilePath.mk f.env.dir)).all
        (fun name => !name.contains '~' && !name.endsWith ".tmp")

private def relativeEnvironment (f : Fixture) : IO Bool := do
  let origin := f.root / "invoke"
  IO.FS.createDirAll origin
  f.writeSave (paneLine "relative" "0" "0" "~" "")
  let extra :=
    #[("HOME", some "../home"), ("LINGER_DIR", some "../state"),
      ("XDG_RUNTIME_DIR", some "../runtime"), ("XDG_STATE_HOME", some "../persistent")]
  let (importCode, _, _) ← f.cli #["resume", "relative-w0-p0"] extra (some origin)
  let (exportCode, exported, _, _) ← f.export extra (some origin)
  return importCode == 0 && exportCode == 0 && (← f.cwdIs "relative-w0-p0" (f.root / "home")) &&
      commonFields "" exported == some [("relative-w0-p0", (f.root / "home").toString)]

private def fallbackHome (f : Fixture) (home : Option String) : IO Bool := do
  f.writeSave (paneLine "fallback" "0" "0" "~" "")
  let (importCode, _, _) ← f.cli #["resume", "fallback-w0-p0"] #[("HOME", home)]
  let (exportCode, exported, _, _) ← f.export #[("HOME", home)]
  let some accountHome := (← Std.Async.System.getCurrentUser).homeDir | return false
  let cwd ← IO.FS.realPath accountHome
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

/-- Build the same relative archive members tmux-resurrect saves, without a server, beside the
latest save. Its directory is one no command may change. -/
private def Fixture.archive (f : Fixture) (captures : List (String × ByteArray)) :
    IO System.FilePath := do
  let staging := f.root / "archive-source"
  IO.FS.createDirAll (staging / "pane_contents")
  for (member, bytes) in captures do
    IO.FS.writeBinFile (staging / "pane_contents" / member) bytes
  let dir := f.latest.parent.getD f.root
  IO.FS.createDirAll dir
  f.saveDirs.modify fun dirs => if dirs.contains dir then dirs else dirs ++ [dir]
  let path := dir / "pane_contents.tar.gz"
  let (rc, _, err) ←
    process
        { cmd := "tar",
          args := #["-czf", path.toString, "-C", staging.toString, "./pane_contents"] }
  unless rc == 0 do
    throw (IO.userError s!"could not create fixture archive: {err}")
  return path

private def captureImport (f : Fixture) : IO Bool := do
  let first := f.root / "first cwd"
  let second := f.root / "second cwd"
  IO.FS.createDirAll first
  IO.FS.createDirAll second
  let marker := f.root / "saved-command-ran"
  let command := s!"printf bad > '{marker}'"
  let secondCommand := s!"printf second > '{marker}'"
  let text :=
    "window\tcaptured\t3\t:Build window\t1\t:*\t1234,481x4,0,0{240x4,0,0,8,240x4,241,0,9}\toff\n" ++
      paneLine "captured" "3" "1" second.toString secondCommand ++
      paneLine "captured" "3" "0" first.toString command
  f.writeSave text
  let archive ←
    f.archive
        [("pane-captured:3.0", "first old λ\n\x1b[31mfirst red\x1b[0m\nfirst screen\n".toUTF8),
          ("pane-captured:3.1", "second old\nsecond saved\nsecond screen\n".toUTF8)]
  let savedBytes ← readBytes f.latest
  let archiveBytes ← readBytes archive
  let (listed, catalog, listError) ← f.cli #["ls", "--porcelain"]
  let (rc, _, err) ← f.importText text
  unless
    rc == 0 && err.isEmpty && listed == 0 && listError.isEmpty &&
      f.rowsMatch text catalog ["Build_window", "Build_window-2"] &&
      (← f.cwdIs "Build_window-2" first) &&
      (← f.cwdIs "Build_window" second) do
    return false
  let firstPid ← f.pid "Build_window-2"
  let secondPid ← f.pid "Build_window"
  let (firstRc, firstHistory, _) ← f.cli #["capture", "--history", "Build_window-2"]
  let (secondRc, secondHistory, _) ← f.cli #["capture", "--history", "Build_window"]
  let labels ←
    ["tmux.session", "tmux.window", "tmux.pane", "tmux.title", "tmux.command", "tmux.saved-command",
            "tmux.window-title", "tmux.capture", "description"].mapM
        (fun key => f.info "Build_window-2" key)
  let barrier := f.root / "shell-ready"
  let secondBarrier := f.root / "second-shell-ready"
  let (ran, _, _) ← f.cli #["send", "Build_window-2", s!"printf ready > '{barrier}'\n"]
  let (secondRan, _, _) ← f.cli #["send", "Build_window", s!"printf ready > '{secondBarrier}'\n"]
  let ready ←
    waitFor 5000 do
        return (← readBytes barrier) == some "ready".toUTF8 &&
            (← readBytes secondBarrier) == some "ready".toUTF8
  let (again, _, againError) ← f.importText text
  let (_, repeatedHistory, _) ← f.cli #["capture", "--history", "Build_window-2"]
  return firstPid.isSome && secondPid.isSome && firstPid != secondPid && firstRc == 0 &&
      secondRc == 0 &&
      has firstHistory "first old λ" &&
      has firstHistory "first red" &&
      has firstHistory s!"first screen\nSaved foreground command: {command}\n" &&
      (firstHistory.splitOn "Saved foreground command: ").length == 2 &&
      !has firstHistory secondCommand &&
      !has firstHistory "second old" &&
      has secondHistory "second old" &&
      has secondHistory s!"second screen\nSaved foreground command: {secondCommand}\n" &&
      (secondHistory.splitOn "Saved foreground command: ").length == 2 &&
      !has secondHistory command &&
      !has secondHistory "first old" &&
      labels ==
        [some "captured", some "3", some "0", some "title", some "sh", some command,
          some "Build window", some "saved", some "Build window"] &&
      ran == 0 &&
      secondRan == 0 &&
      ready &&
      !(← marker.pathExists) &&
      again == 0 &&
      againError.isEmpty &&
      (← f.pid "Build_window-2") == firstPid &&
      (← f.pid "Build_window") == secondPid &&
      has repeatedHistory "first old λ" &&
      (repeatedHistory.splitOn "Saved foreground command: ").length == 2 &&
      (← readBytes f.latest) == savedBytes &&
      (← readBytes archive) == archiveBytes

private def emptyCapture (f : Fixture) : IO Bool := do
  let text :=
    paneLine "empty" "0" "0" (f.root / "home").toString "" ++
      paneLine "missing" "0" "0" (f.root / "home").toString ""
  f.writeSave text
  discard <| f.archive [("pane-empty:0.0", ByteArray.empty)]
  let (rc, _, err) ← f.importText text
  return rc == 0 && err.isEmpty && (← f.info "empty-w0-p0" "tmux.capture") == some "saved" &&
      (← f.info "missing-w0-p0" "tmux.capture") == some "none"

private def badCapture (f : Fixture) (kind : String) : IO Bool := do
  f.writeSave (paneLine "bad" "0" "0" (f.root / "home").toString "")
  let archive := f.latest.parent.getD f.root / "pane_contents.tar.gz"
  let expected ←
    if kind == "corrupt" then
      IO.FS.writeFile archive "not a gzip archive"
      pure "could not read pane capture archive"
    else
      let bytes :=
        if kind == "UTF-8" then ByteArray.mk #[0xFF]
        else
          if kind == "oversize" then
            ByteArray.mk (Array.replicate (Linger.Import.Resurrect.captureLimit + 1) 0x41)
          else "duplicate\n".toUTF8
      discard <| f.archive [("pane-bad:0.0", bytes)]
      if kind == "duplicate" then
        let (rc, _, err) ←
          process
              { cmd := "tar",
                args :=
                  #["-czf", archive.toString, "-C", (f.root / "archive-source").toString,
                    "./pane_contents/pane-bad:0.0", "./pane_contents/pane-bad:0.0"] }
        unless rc == 0 do
          throw (IO.userError s!"could not create duplicate fixture: {err}")
        pure "duplicate pane capture"
      else if kind == "oversize" then
        pure s!"command output exceeds {Linger.Import.Resurrect.captureLimit} bytes"
      else
        pure "command output is not UTF-8"
  let archiveBytes ← readBytes archive
  let (rc, _, err) ← f.cli #["resume", "bad-w0-p0"]
  return rc == 1 && has err expected &&
      (← namesIn (System.FilePath.mk f.env.dir)).all
        (fun name => name.endsWith ".lock" || name == ".locks") &&
      (← readBytes archive) == archiveBytes

/-- Overflow must drain both pipes, and collection must release ownership even on error. -/
private def boundedCommand (f : Fixture) (stderr : Bool) : IO Bool := do
  let reached := f.root / "output-finished"
  let redirect := if stderr then " >&2" else ""
  let script :=
    s!"i=0; while [ \"$i\" -lt 30000 ]; do printf 1234567890{redirect}; i=$((i+1)); done; printf done > '{reached}'"
  let pending ← IO.mkRef (some (← Os.Shell.Command.startLimited "/bin/sh" #["-c", script] 100))
  let refused ← IO.mkRef false
  try
    let done ←
      waitFor 5000 do
          let result ← (Os.Shell.Command.poll pending).toBaseIO
          match result with
          | .error error =>
            refused.set <|
                has (toString error)
                  s!"command output exceeds {if stderr then 64 * 1024 else 100} bytes"
            return true
          | .ok result =>
            return result.isSome
    return done && (← refused.get) && (← pending.get).isNone &&
        (← readBytes reached) == some "done".toUTF8
  finally
    Os.Shell.Command.stop pending

/-- An exited leader must still own and retire a descendant holding its pipes open. -/
private def heldPipeCommand (f : Fixture) : IO Bool := do
  let reached := f.root / "descendant-pid"
  let script := s!"sleep 30 & printf '%s' \"$!\" > '{reached}'"
  let job ← Os.Shell.Command.startLimited "/bin/sh" #["-c", script] 100
  let pending ← IO.mkRef (some job)
  try
    unless ← waitFor 3000 (reached.pathExists) do
      return false
    let some pid := (← IO.FS.readFile reached).toNat? | return false
    let running ← Os.Shell.alive pid.toUInt32
    let uncollected ← Os.Shell.Command.poll pending
    let stillOwned := (← pending.get).isSome
    Os.Shell.Command.stop pending
    let retired ←
      waitFor 3000 do
          return !(← Os.Shell.alive pid.toUInt32)
    return running && uncollected.isNone && stillOwned && retired && (← pending.get).isNone &&
        (← IO.hasFinished job.stdout) &&
        (← IO.hasFinished job.stderr)
  finally
    Os.Shell.Command.stop pending

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
      let native ← Linger.Session.Shell.Paths.stateDir
      let original := f.root / "native"
      let alternate := f.root / "alternate"
      let checkpointDir ←
        withVariables #[("XDG_STATE_HOME", some original.toString)] do
            let dir ← Linger.Session.Shell.Paths.stateDir
            Linger.Session.Shell.Paths.ensureDir dir
            return dir
      let checkpoints := { f with env := { f.env with dir := checkpointDir } }
      checkpoints.seed "saved.name" savedCwd.toString
      let target := f.root / "out" / "native-fallback"
      let observed ← IO.mkRef (none : Option String)
      let capture := do
        let observedDir ← Linger.Session.Shell.Paths.stateDir
        observed.set (some observedDir)
        let selected := if observedDir == native then original else alternate
        Std.Async.System.setEnvVar "XDG_STATE_HOME" selected.toString
        Linger.Import.Shell.snapshot
      let outcome ←
        (do
              let text ← IO.ofExcept (Linger.Import.Resurrect.renderSave (← capture))
              IO.FS.writeFile target text).toBaseIO
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
      return complete && (← namesIn (f.root / "out")) == ["native-fallback"]

private def check (root : System.FilePath) (bin : String) (index : Nat) (label : String)
    (body : Fixture → IO Bool) : IO Unit := do
  let root := root / toString index
  for dir in [root / "state", root / "home", root / "data", root / "out"] do
    IO.FS.createDirAll dir
  let owned ← IO.mkRef []
  let saveDirs ← IO.mkRef []
  let tmuxEnv ← tmuxFixtureEnv root
  let f : Fixture :=
    { root, env := { bin, dir := (root / "state").toString }, owned, tmuxEnv, saveDirs }
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
      let _ ← cleanup.cli #["ls"]
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
  let (code, temp, err) ←
    process { cmd := "mktemp", args := #["-d", (socketRoot / "linger-i-XXXXXX").toString] }
  unless code == 0 do
    throw (IO.userError s!"could not create fresh fixture root: {err}")
  let root ← IO.FS.realPath temp.trimAscii.toString
  IO.println s!"interop fixtures: {root}"
  let mut cases : List (String × (Fixture → IO Bool)) := []
  cases :=
    cases ++
      [("ls --resurrect rejects other arguments with exit 2", fun (f : Fixture) => do
          let mut ok := true
          for args in
            [#["ls", "--resurrect", "save"], #["ls", "--resurrect", "--porcelain"],
              #["ls", "--porcelain", "--resurrect"], #["ls", "name", "--resurrect"]] do
            let (code, out, _) ← f.cli args
            ok := ok && code == 2 && out.isEmpty
          return ok && (← namesIn (System.FilePath.mk f.env.dir)).isEmpty),
        ("ls --resurrect refuses an empty session set, writing nothing", fun (f : Fixture) =>
          f.refused),
        ("ls --resurrect writes its save to standard output and creates no file", exportStdout),
        ("a resumed pane retains no foreign source and exports current fields after source replacement and deletion",
          sourceIndependent),
        ("resuming a changed save's pane again preserves the existing session and current export",
          metadataOnlyImport),
        ("a malformed save preserves existing sessions and creates no partial session",
          failedImport),
        ("adding a session generates complete current common fields", fun f =>
          topologyChange f false),
        ("removing a resumed pane's session generates complete current common fields", fun f =>
          topologyChange f true),
        ("export observes a live cwd change instead of its startup directory", liveCwd),
        ("native identities remain exact and preserve dot, plus and UTF8 cwd in a second state dir",
          nativeRoundtrip),
        ("a session an older import saved without a description reads with the import's, until a rename ends it",
          olderImport),
        ("export reads the changed checkpoint cwd after last detach and daemon crash",
          resumableCwd),
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
        ("resume and export share relative HOME and state overrides", relativeEnvironment),
        ("resume and export share account-home fallback when HOME is unset", fun f =>
          fallbackHome f none),
        ("resume and export share account-home fallback when HOME is empty", fun f =>
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
      [("ls lists the latest save's panes in name order with their window, directory and provenance",
          sourceOrder),
        ("ls escapes titles, directories and commands in the rows of saved panes", sourceControls),
        ("ls takes a relative saved cwd from the invocation without resolving its symlink spelling",
          sourceRelativeCwd),
        ("ls leaves sessions, checkpoints, the save and its saved commands untouched",
          sourceReadOnly),
        ("a pane is listed exactly while no socket, checkpoint or end record names it",
          listedUnrecorded),
        ("saved panes sort last within the saved status", sourceLast),
        ("a pane takes its window's name, a duplicate the next natural-order suffix", windowNames),
        ("an attach of a saved pane resumes it as a fresh shell in its directory", attachPane),
        ("an attach or a resume never replaces a record of the pane's name", adoptExclusive),
        ("a kill of a saved pane leaves only an end record that says it was dismissed, and hides it for good",
          killDismisses),
        ("tmux is an unknown word, refused as any other", retiredSpellings),
        ("a configured directory with no last lists no pane, without falling back or scanning history",
          fun f => missingDiscovery f true),
        ("a conventional directory with no last lists no pane, without scanning history", fun f =>
          missingDiscovery f false),
        ("tmux discovery times out, and the listing still lists the sessions", discoveryTimeout),
        ("resume keeps independent pane contents, layout, metadata and fresh shells; a second resume preserves them",
          captureImport),
        ("empty captures remain distinct from missing pane captures", emptyCapture),
        ("bounded command stdout overflow drains the pipe and releases ownership", fun f =>
          boundedCommand f false),
        ("bounded command stderr overflow drains the pipe and releases ownership", fun f =>
          boundedCommand f true),
        ("cancellation retires a descendant holding an exited leader's pipes", heldPipeCommand)]
  for kind in ["corrupt", "duplicate", "oversize", "UTF-8"] do
    cases :=
      cases ++
        [(s!"{kind} pane captures fail with a reached diagnostic before checkpoint publication",
            fun f => badCapture f kind)]
  for kind in ["absent", "malformed", "duplicate", "NUL", "empty"] do
    cases :=
      cases ++
        [(s!"an {kind} save lists no pane and creates no session", fun f => sourceInvalid f kind)]
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
        [(s!"ls discovers {label} using only the read-only current-server query", fun f =>
            discovery f config)]
  -- This run created the fixture root with `mktemp`, so a green run removes it
  -- whatever `LINGER_TEST_DIR` says.
  let before ← failureCount
  for ((label, body), index) in cases.zipIdx do
    check root bin.toString index label body
  if (← failureCount) == before then
    IO.FS.removeDirAll root
  finish

/-- The interop suite: a tmux-resurrect save as a read-only source, against `LINGER_EXE` when it is set
and the built `linger` otherwise. -/
def run : IO UInt32 := do
  let binary :=
    (← IO.getEnv "LINGER_EXE").getD ((← IO.currentDir) / ".lake/build/bin/linger").toString
  runWith binary

end Linger.Import.Suites.Interop
