module

public import E2E.Harness

public section

/-! # E2E.Recipes — composition kept outside the linger binary

`lzr` projects tmux-resurrect pane records into independent linger sessions.
This suite drives the fish function against real daemons and synthetic save
files: the foreign parser is exercised here, not admitted into `Linger/`.
-/

namespace E2E.Recipes

open E2E.Harness

/-- tmux-resurrect prefixes the saved directory and full command with `:` and
escapes spaces in the directory field. The other fields are present only to
exercise the real eleven-field pane shape. -/
def paneLine (session window pane dir command : String) : String :=
  let savedDir := String.intercalate "\\ " (dir.splitOn " ")
  String.intercalate "\t"
      ["pane", session, window, "0", ":", pane, "title", ":" ++ savedDir, "1", "sh",
        ":" ++ command] ++
    "\n"

/-- Source the autoload file in a fresh fish and invoke its function. The built
linger binary leads PATH; HOME and XDG data are fixture-owned so the default
resurrect path cannot read the developer's files. -/
def runLzr (e : Env) (home data : String) (args : Array String) : IO (UInt32 × String × String) :=
  do
  let cwd ← IO.currentDir
  let path := s!"{(cwd / ".lake" / "build" / "bin").toString}:{(← IO.getEnv "PATH").getD ""}"
  let out ←
    IO.Process.output
        { cmd := "fish", args := #["-c", "source recipes/lzr.fish; lzr $argv", "--"] ++ args,
          env :=
            e.procEnv ++ #[("HOME", some home), ("XDG_DATA_HOME", some data), ("PATH", some path)] }
  return (out.exitCode, out.stdout, out.stderr)

def run : IO UInt32 := do
  let e ← Env.make "recipes"
  let root := System.FilePath.mk e.dir
  let home := root / "home"
  let data := root / "data"
  IO.FS.createDirAll home
  IO.FS.createDirAll data
  let mut f := 0
  -- Default path, escaped cwd, and no-command default.
  let defaultDir := root / "work space"
  let defaultSource := root / "default-source"
  let defaultSink := root / "default-sink"
  let resurrectDir := data / "tmux" / "resurrect"
  IO.FS.createDirAll defaultDir
  IO.FS.createDirAll resurrectDir
  IO.FS.writeFile defaultSource "DEFAULT-RAN\n"
  IO.FS.writeFile (resurrectDir / "last")
      (paneLine "desk" "1" "0" defaultDir.toString s!"tail -n 1 {defaultSource} >> {defaultSink}" ++
        "window\tdesk\t1\t:ignored\nstate\tdesk\t\n")
  let (drc, _, _) ← runLzr e home.toString data.toString #[]
  f :=
    f +
      (←
        expect (drc == 0 && (← e.info "desk-w1-p0" "start_dir") == some defaultDir.toString)
            "lzr reads the default XDG save and restores an escaped cwd")
  IO.sleep 700 -- negative assertion: give a wrongly-started command time to run
  f :=
    f +
      (←
        expect (!(← System.FilePath.pathExists defaultSink))
            "lzr does not execute a saved command by default")
  -- An explicitly empty XDG value has the documented shell `:-` semantics.
  let emptyXdgDir := root / "empty-xdg"
  let fallbackResurrectDir := home / ".local" / "share" / "tmux" / "resurrect"
  IO.FS.createDirAll emptyXdgDir
  IO.FS.createDirAll fallbackResurrectDir
  IO.FS.writeFile (fallbackResurrectDir / "last")
      (paneLine "emptyxdg" "3" "0" emptyXdgDir.toString "")
  let (xrc, _, _) ← runLzr e home.toString "" #[]
  f :=
    f +
      (←
        expect (xrc == 0 && (← e.info "emptyxdg-w3-p0" "start_dir") == some emptyXdgDir.toString)
            "lzr treats an empty XDG data home as unset")
  -- Once the legacy directory exists, it takes precedence over the XDG path.
  let legacyDir := root / "legacy"
  let legacyResurrectDir := home / ".tmux" / "resurrect"
  IO.FS.createDirAll legacyDir
  IO.FS.createDirAll legacyResurrectDir
  IO.FS.writeFile (legacyResurrectDir / "last") (paneLine "legacy" "2" "0" legacyDir.toString "")
  let (lrc, _, _) ← runLzr e home.toString data.toString #[]
  f :=
    f +
      (←
        expect (lrc == 0 && (← e.info "legacy-w2-p0" "start_dir") == some legacyDir.toString)
            "lzr prefers the legacy default save directory when it exists")
  -- Explicit process restart: an empty command, one default-allowlisted
  -- command, and one outsider. The leading empty entry pins pane/command array
  -- alignment instead of merely proving that some pane ran the command.
  let processDir := root / "processes"
  let processSource := root / "process-source"
  let processSink := root / "process-sink"
  let blockedSink := root / "blocked-sink"
  let processSave := root / "process-save"
  IO.FS.createDirAll processDir
  IO.FS.writeFile processSource "RESTORED-ONCE\n"
  IO.FS.writeFile processSave
      (paneLine "dev" "1" "0" processDir.toString "" ++
        paneLine "dev" "1" "1" processDir.toString
          s!"tail -n 1 {processSource} | tee -a {processSink}" ++
        paneLine "dev" "1" "2" processDir.toString s!"printf BLOCKED > {blockedSink}")
  let (prc, _, _) ←
    runLzr e home.toString data.toString #["--restore-processes", processSave.toString]
  f :=
    f +
      (←
        expect
            (prc == 0 && (← e.info "dev-w1-p0" "start_dir") == some processDir.toString &&
              (← e.info "dev-w1-p1" "start_dir") == some processDir.toString &&
              (← e.info "dev-w1-p2" "start_dir") == some processDir.toString)
            "lzr projects every pane into a named linger session")
  let restored ← waitFor 5000 (System.FilePath.pathExists processSink)
  let restoredText ←
    if restored then
      IO.FS.readFile processSink
    else
      pure ""
  let allowedScreen ← e.out #["capture", "dev-w1-p1"]
  let emptyScreen ← e.out #["capture", "dev-w1-p0"]
  f :=
    f +
      (←
        expect
            (restored && restoredText == "RESTORED-ONCE\n" && has allowedScreen "RESTORED-ONCE" &&
              !has emptyScreen "RESTORED-ONCE")
            "lzr --restore-processes keeps commands aligned and runs an allowlisted one")
  IO.sleep 700 -- negative assertion after the import process itself has exited
  f :=
    f +
      (←
        expect (!(← System.FilePath.pathExists blockedSink))
            "lzr --restore-processes skips a command outside the allowlist")
  let (rrc, _, _) ←
    runLzr e home.toString data.toString #["--restore-processes", processSave.toString]
  IO.sleep 700
  let rerunExists ← System.FilePath.pathExists processSink
  let rerunText ←
    if rerunExists then
      IO.FS.readFile processSink
    else
      pure ""
  f :=
    f +
      (←
        expect (rrc == 0 && rerunText == "RESTORED-ONCE\n")
            "lzr skips existing sessions on a sequential rerun")
  -- A checkpoint-only identity is also existing state: importing must neither
  -- revive it nor send the saved process command.
  let resumableSource := root / "resumable-source"
  let resumableSink := root / "resumable-sink"
  let resumableSave := root / "resumable-save"
  IO.FS.writeFile resumableSource "MUST-NOT-RUN\n"
  let owner ← e.spawn #["attach", "resumable-w1-p0"]
  IO.sleep 800
  owner.type "echo CHECKPOINTED\n"
  IO.sleep 500
  owner.bye
  let checkpointed ←
    waitFor 3000
        (do
          return (← e.dirNames ".ckpt").contains "resumable-w1-p0.ckpt")
  let crashed ←
    if checkpointed then
      e.crashDaemon "resumable-w1-p0"
    else
      pure false
  IO.FS.writeFile resumableSave
      (paneLine "resumable" "1" "0" processDir.toString
        s!"tail -n 1 {resumableSource} >> {resumableSink}")
  let (src, _, _) ←
    runLzr e home.toString data.toString #["--restore-processes", resumableSave.toString]
  IO.sleep 700
  let resumableState ← e.status "resumable-w1-p0"
  f :=
    f +
      (←
        expect
            (checkpointed && crashed && src == 0 && resumableState == .resumable &&
              !(← System.FilePath.pathExists resumableSink))
            "lzr skips a resumable checkpoint instead of reviving and replaying it")
  -- Validate the complete pane set before the first daemon can be created.
  let absentDir := root / "absent"
  let invalidSave := root / "invalid-save"
  IO.FS.writeFile invalidSave
      (paneLine "prevalid" "1" "0" processDir.toString "" ++
        paneLine "prevalid" "1" "1" absentDir.toString "")
  let (irc, _, ierr) ← runLzr e home.toString data.toString #[invalidSave.toString]
  f :=
    f +
      (←
        expect
            (irc == 1 && has ierr "working directory not found" &&
              (← e.cli #["info", "prevalid-w1-p0"]).1 == 1)
            "lzr validates every cwd before creating any session")
  let invalidNameSave := root / "invalid-name-save"
  let longNameSave := root / "long-name-save"
  IO.FS.writeFile invalidNameSave (paneLine "bad/name" "1" "0" processDir.toString "")
  let longName := String.ofList (List.replicate 80 'a')
  IO.FS.writeFile longNameSave (paneLine longName "1" "0" processDir.toString "")
  let (urc, _, uerr) ← runLzr e home.toString data.toString #[invalidNameSave.toString]
  let (longRc, _, longErr) ← runLzr e home.toString data.toString #[longNameSave.toString]
  f :=
    f +
      (←
        expect
            (urc == 1 && longRc == 1 && has uerr "not a valid linger name" &&
              has longErr "not a valid linger name" &&
              (← e.cli #["info", "bad_name-w1-p0"]).1 == 1)
            "lzr rejects names that linger would rewrite or truncate")
  let inaccessibleDir := root / "inaccessible"
  let inaccessibleSave := root / "inaccessible-save"
  IO.FS.createDirAll inaccessibleDir
  IO.FS.writeFile inaccessibleSave
      (paneLine "accessvalid" "1" "0" processDir.toString "" ++
        paneLine "inaccessible" "1" "0" inaccessibleDir.toString "")
  Linger.Posix.chmod inaccessibleDir.toString 0
  let (accessRc, _, accessErr) ←
    try
      runLzr e home.toString data.toString #[inaccessibleSave.toString]
    finally
      Linger.Posix.chmod inaccessibleDir.toString 0o700
  f :=
    f +
      (←
        expect
            (accessRc == 1 && has accessErr "working directory not accessible" &&
              (← e.cli #["info", "accessvalid-w1-p0"]).1 == 1)
            "lzr validates directory access before creating any session")
  let malformedSave := root / "malformed-save"
  IO.FS.writeFile malformedSave "pane\tshort\n"
  let (mrc, _, merr) ← runLzr e home.toString data.toString #[malformedSave.toString]
  f :=
    f +
      (←
        expect (mrc == 1 && has merr "malformed pane record") "lzr rejects a malformed pane record")
  let emptySave := root / "empty-save"
  IO.FS.writeFile emptySave "window\tignored\nstate\tignored\t\n"
  let (erc, _, eerr) ← runLzr e home.toString data.toString #[emptySave.toString]
  f :=
    f +
      (← expect (erc == 1 && has eerr "no pane records") "lzr rejects a save with no pane records")
  let (nrc, _, nerr) ← runLzr e home.toString data.toString #[s!"{e.dir}/missing-save"]
  f := f + (← expect (nrc == 1 && has nerr "save not found") "lzr reports a missing save")
  e.killAll
      #["desk-w1-p0", "emptyxdg-w3-p0", "legacy-w2-p0", "dev-w1-p0", "dev-w1-p1", "dev-w1-p2",
        "resumable-w1-p0", "prevalid-w1-p0", "prevalid-w1-p1", "bad_name-w1-p0",
        "accessvalid-w1-p0", "inaccessible-w1-p0"]
  verdict e f

end E2E.Recipes
