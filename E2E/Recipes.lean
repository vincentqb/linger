module

public import E2E.Harness
public import Manager.Resurrect

public section

/-! # E2E.Recipes — native launch settings and foreign-save import

`linger import` projects pane records into independent linger sessions. This
suite drives the actual CLI against real daemons and synthetic saves. Recorder
checks call the same executor through this test binary's `--import-probe` mode.
Native configuration assertions inspect their effective settings; they do not
claim to launch or exercise any terminal GUI.
-/

namespace E2E.Recipes

open E2E.Harness

private def call (args : List String) : String :=
  "CALL\x00" ++ String.intercalate "\x00" args ++ "\x00\n"

/-- Test-only protocol: `--import-probe ABSOLUTE_EXECUTABLE [SAVE]`. The executor
is production code; only the supplied child executable records instead of
starting sessions. `E2ETest.main` dispatches the arguments after the flag here. -/
def importProbe (args : List String) : IO UInt32 := do
  match args with
  | executable :: rest =>
    Manager.Resurrect.run executable rest
  | [] =>
    IO.eprintln "usage: e2e --import-probe ABSOLUTE_EXECUTABLE [SAVE]"
    return 98

private def configChecks : IO Nat := do
  let root := (← IO.currentDir) / "recipes"
  let mut f := 0
  for (file, comment, setting, label) in
    [("ghostty_config", "#", "command = direct:linger select", "Ghostty"),
      ("kitty.conf", "#", "shell linger select", "Kitty"),
      ("wezterm.lua", "--", "return { default_prog = { 'linger', 'select' } }", "WezTerm")] do
    let content ←
      try
        IO.FS.readFile (root / file)
      catch _ =>
        pure ""
    let settings :=
      (content.splitOn "\n").map (·.trimAscii.toString) |>.filter fun line =>
        !line.isEmpty && !line.startsWith comment
    f :=
      f + (← expect (settings == [setting]) s!"{label} native configuration launches linger select")
  return f

/-- tmux-resurrect prefixes the saved directory and full command with `:` and
escapes spaces in the directory field. The other fields are present only to
exercise the real eleven-field pane shape. -/
def paneLine (session window pane dir command : String) : String :=
  let savedDir := String.intercalate "\\ " (dir.splitOn " ")
  String.intercalate "\t"
      ["pane", session, window, "0", ":", pane, "title", ":" ++ savedDir, "1", "sh",
        ":" ++ command] ++
    "\n"

/-- Invoke the public import command through the actual absolute linger binary.
HOME and XDG data are fixture-owned so defaults cannot read user saves. -/
def runImport (e : Env) (home data : String) (args : Array String)
    (extra : Array (String × Option String) := #[]) : IO (UInt32 × String × String) := do
  let out ←
    IO.Process.output
        { cmd := e.bin, args := #["import"] ++ args,
          env := e.procEnv ++ #[("HOME", some home), ("XDG_DATA_HOME", some data)] ++ extra }
  return (out.exitCode, out.stdout, out.stderr)

private def runImportProbe (e : Env) (home data executable : String) (args : Array String)
    (extra : Array (String × Option String) := #[]) : IO (UInt32 × String × String) := do
  let out ←
    IO.Process.output
        { cmd := (← IO.appPath).toString, args := #["--import-probe", executable] ++ args,
          env := e.procEnv ++ #[("HOME", some home), ("XDG_DATA_HOME", some data)] ++ extra }
  return (out.exitCode, out.stdout, out.stderr)

private def absoluteExecutableChecks (e : Env) (home data : String) : IO Nat := do
  let root := System.FilePath.mk e.dir / "absolute-import"
  let path := root / "path"
  let pane := root / "saved cwd"
  let marker := root / "impostor-called"
  let save := root / "save"
  IO.FS.createDirAll path
  IO.FS.createDirAll pane
  let mut f := 0
  for impostor in [false, true] do
    let name := if impostor then "impostor" else "no-path"
    if impostor then
      IO.FS.writeFile (path / "linger")
          "#!/bin/sh\nprintf 'called\\n' >> \"$IMPORT_IMPOSTOR_MARKER\"\nexit 97\n"
      Linger.Posix.chmod (path / "linger").toString 0o700
    IO.FS.writeFile marker ""
    IO.FS.writeFile save (paneLine name "1" "0" pane.toString "")
    try
      let (rc, _, _) ←
        runImport e home data #[save.toString]
            #[("PATH", some path.toString), ("IMPORT_IMPOSTOR_MARKER", some marker.toString)]
      f :=
        f +
          (←
            expect
                (rc == 0 && (← e.info s!"{name}-w1-p0" "start_dir") == some pane.toString &&
                  (← IO.FS.readFile marker).isEmpty)
                s!"linger import reuses its absolute executable (PATH impostor: {impostor})")
    finally
      e.killAll #[s!"{name}-w1-p0"]
  return f

private def relativePathChecks (e : Env) : IO Nat := do
  let root := System.FilePath.mk e.dir
  let origin := root / "relative" / "from"
  let pane := root / "relative" / "to" / "inner"
  let binDir := origin / "bin"
  IO.FS.createDirAll binDir
  IO.FS.createDirAll pane
  IO.FS.writeFile (binDir / "linger") "#!/bin/sh\nexit 97\n"
  Linger.Posix.chmod (binDir / "linger").toString 0o700
  discard <|
      IO.Process.run
        { cmd := "ln", args := #["-s", (root / "relative").toString, (origin / "link").toString] }
  let wrongDir := { e with dir := (root / "relative").toString }
  let wrongSymlinkDir := { e with dir := origin.toString }
  let mut f := 0
  for (label, path, state) in
    [("PATH", "bin:/usr/bin:/bin", e.dir), ("state", s!"{binDir}:/usr/bin:/bin", "../.."),
      ("symlink-state", s!"{binDir}:/usr/bin:/bin", "link/..")] do
    let name := s!"relative-{label}-w1-p0"
    let save := root / s!"relative-{label}-save"
    IO.FS.writeFile save (paneLine s!"relative-{label}" "1" "0" pane.toString "")
    try
      let out ←
        IO.Process.output
            { cmd := e.bin, args := #["import", save.toString], cwd := some origin.toString,
              env := e.procEnv ++ #[("PATH", some path), ("LINGER_DIR", some state)] }
      f :=
        f +
          (←
            expect (out.exitCode == 0 && (← e.info name "start_dir") == some pane.toString)
                s!"linger import uses its absolute executable with invocation-relative {label} settings")
    finally
      e.killAll #[name]
      wrongDir.killAll #[name]
      wrongSymlinkDir.killAll #[name]
  -- The physical state path is short even when the invocation spelling is too
  -- long for a Unix socket. Exercise resolution before either an existing or
  -- a not-yet-created state directory; the symlink case above must still pass.
  let physicalRoot ← IO.FS.realPath root
  let deepOrigin :=
    physicalRoot / String.ofList (List.replicate 64 'a') / String.ofList (List.replicate 64 'b')
  IO.FS.createDirAll deepOrigin
  let physicalPane ← IO.FS.realPath pane
  for preexisting in [true, false] do
    let stateName := if preexisting then "len-e" else "len-m"
    let state := physicalRoot / stateName
    if preexisting then
      IO.FS.createDirAll state
    let present ← state.pathExists
    let owned := { e with dir := state.toString }
    let name := "long-w1-p0"
    let save := physicalRoot / s!"{stateName}-save"
    IO.FS.writeFile save (paneLine "long" "1" "0" physicalPane.toString "")
    try
      let out ←
        IO.Process.output
            { cmd := e.bin, args := #["import", save.toString], cwd := some deepOrigin,
              env :=
                e.procEnv ++
                  #[("PATH", some s!"{binDir}:/usr/bin:/bin"),
                    ("LINGER_DIR", some s!"../../{stateName}")] }
      f :=
        f +
          (←
            expect
                (present == preexisting && out.exitCode == 0 &&
                  (← owned.info name "start_dir") == some physicalPane.toString)
                s!"linger import resolves a long relative state path before spawning (already exists: {preexisting})")
    finally
      owned.killAll #[name]
  return f

private def importBoundaryChecks (e : Env) (home data : String) : IO Nat := do
  let root := System.FilePath.mk e.dir / "import-boundary"
  IO.FS.createDirAll root
  let save := root / "save"
  let callsFile := root / "calls"
  let executable := root / "recorder with spaces"
  IO.FS.writeFile executable
      r#"#!/bin/sh
printf 'CALL\000linger\000' >> "$IMPORT_PROBE_CALLS"
printf '%s\000' "$@" >> "$IMPORT_PROBE_CALLS"
printf '\n' >> "$IMPORT_PROBE_CALLS"
if [ "$1" = ls ]; then
    printf '%s' "$IMPORT_PROBE_LISTING"
    exit "$IMPORT_PROBE_LIST_RC"
fi
printf '%s' "$IMPORT_PROBE_STDOUT"
if [ "$IMPORT_PROBE_FAIL" = "$2" ]; then
    printf '%s' "$IMPORT_PROBE_STDERR" >&2
    exit 7
fi
exit 0
"#
  Linger.Posix.chmod executable.toString 0o700
  let command := "tail -n 1 'a b' | tee -a 'c d'"
  let panes :=
    paneLine "live" "1" "0" home command ++ paneLine "resume" "1" "0" home command ++
      paneLine "first" "2" "0" home command ++
      paneLine "second" "2" "1" home "" ++
      paneLine "third" "2" "2" home command
  let listing := "name\tlive-w1-p0\nstate\tlive\n\nname\tresume-w1-p0\nstate\tresumable\n\n"
  let invoke := fun (text failure listRc : String) (args : Array String) => do
    IO.FS.writeFile save text
    IO.FS.writeFile callsFile ""
    let (rc, _, err) ←
      runImportProbe e home data executable.toString args
          #[("PATH", some root.toString), ("IMPORT_PROBE_CALLS", some callsFile.toString),
            ("IMPORT_PROBE_LISTING", some listing), ("IMPORT_PROBE_LIST_RC", some listRc),
            ("IMPORT_PROBE_FAIL", some failure)]
    return (rc, err, ← IO.FS.readFile callsFile)
  let args := #[save.toString]
  let listCall := call ["linger", "ls", "--porcelain"]
  let createCall := call ["linger", "run", "first-w2-p0", "true"]
  let secondCall := call ["linger", "run", "second-w2-p1", "true"]
  let (rc, _, calls) ← invoke panes "" "0" args
  let mut f ←
    expect
        (rc == 0 &&
          calls ==
            listCall ++ createCall ++ secondCall ++ call ["linger", "run", "third-w2-p2", "true"])
        "linger import skips every existing identity and creates shells without saved commands"
  let (rc, _, calls) ←
    invoke (paneLine "live" "1" "0" home command ++ paneLine "resume" "1" "0" home "") "" "0" args
  f :=
    f +
      (←
        expect (rc == 0 && calls == listCall)
            "linger import lists once and creates nothing when every identity already exists")
  let (rc, err, calls) ← invoke panes "" "7" args
  f :=
    f +
      (←
        expect
            (rc == 1 && err.startsWith "linger import: " && has err "could not list" &&
              calls == listCall)
            "linger import rejects a failed listing even when it contains existing names")
  for (failed, expected) in
    [("first-w2-p0", listCall ++ createCall),
      ("second-w2-p1", listCall ++ createCall ++ secondCall)] do
    let (rc, err, calls) ← invoke panes failed "0" args
    f :=
      f +
        (←
          expect
              (rc == 1 && err.startsWith "linger import: " &&
                has err s!"could not create session: {failed}" &&
                calls == expected)
              s!"linger import preserves order and stops at the failed creation ({failed})")
  let controls := "\x07\x1b[2J\r\x7f\u0080\u0085\u009b\u009d\u009f"
  IO.FS.writeFile save panes
  IO.FS.writeFile callsFile ""
  let (rc, out, err) ←
    runImportProbe e home data executable.toString args
        #[("PATH", some root.toString), ("IMPORT_PROBE_CALLS", some callsFile.toString),
          ("IMPORT_PROBE_LISTING", some listing), ("IMPORT_PROBE_LIST_RC", some "0"),
          ("IMPORT_PROBE_FAIL", some "second-w2-p1"),
          ("IMPORT_PROBE_STDOUT", some ("child stdout" ++ controls ++ "\n")),
          ("IMPORT_PROBE_STDERR", some ("permission denied: é path" ++ controls ++ "\n"))]
  f :=
    f +
      (←
        expect
            (rc == 1 && out.isEmpty && err.startsWith "linger import: " &&
              has err "could not create session: second-w2-p1" &&
              has err "child stdout" &&
              has err "permission denied: é path" &&
              err.endsWith "\n" &&
              (err.dropEnd 1).toString.toList.all
                (fun c => 32 ≤ c.toNat && (c.toNat < 127 || 160 ≤ c.toNat)) &&
              (← IO.FS.readFile callsFile) == listCall ++ createCall ++ secondCall)
            "linger import sanitizes both child streams and preserves a failed creation's cause")
  let (rc, err, calls) ← invoke panes "" "0" #["--restore-processes", save.toString]
  f :=
    f +
      (←
        expect (rc == 2 && err == "usage: linger import [SAVE]\n" && calls.isEmpty)
            "linger import rejects the retired replay option before invoking linger")
  let mut preflightOk := true
  let valid := paneLine "valid" "3" "0" home ""
  for invalid in
    ["pane\tshort\n", valid, paneLine "nul" "1" "0" home "tail\x00 -f log",
      paneLine "nul" "1" "0" (home ++ "\x00ignored") ""] do
    let (rc, err, calls) ← invoke (valid ++ invalid) "" "0" args
    preflightOk := preflightOk && rc == 1 && err.startsWith "linger import: " && calls.isEmpty
  f :=
    f +
      (←
        expect preflightOk
            "linger import rejects malformed, duplicate and NUL-bearing saves before invoking linger")
  let missing := (root / ("missing" ++ controls)).toString
  for (text, path, cause) in
    [(paneLine ("bad" ++ controls) "1" "0" home "", save.toString, "projected session"),
      (paneLine "control" "1" "0" missing "", save.toString, "working directory not found"),
      (valid, missing, "save not found")] do
    let (rc, err, calls) ← invoke text "" "0" #[path]
    f :=
      f +
        (←
          expect
              (rc == 1 && err.startsWith "linger import: " && has err cause && err.endsWith "\n" &&
                (err.dropEnd 1).toString.toList.all
                  (fun c => 32 ≤ c.toNat && (c.toNat < 127 || 160 ≤ c.toNat)) &&
                calls.isEmpty)
              s!"linger import renders {cause} errors without terminal controls")
  let regular := root / "regular-file"
  IO.FS.writeFile regular ""
  for dir in [root / "missing", regular] do
    let (rc, err, calls) ← invoke (valid ++ paneLine "live" "1" "0" dir.toString "") "" "0" args
    f :=
      f +
        (←
          expect (rc == 1 && has err "working directory not found at line 2" && calls.isEmpty)
              s!"linger import preflights even a skipped identity before listing ({dir.fileName.getD ""})")
  let inaccessible := root / "inaccessible"
  IO.FS.createDirAll inaccessible
  Linger.Posix.chmod inaccessible.toString 0
  let (rc, err, calls) ←
    try
      invoke (valid ++ paneLine "resume" "1" "0" inaccessible.toString "") "" "0" args
    finally
      Linger.Posix.chmod inaccessible.toString 0o700
  f :=
    f +
      (←
        expect (rc == 1 && has err "working directory not accessible at line 2" && calls.isEmpty)
            "linger import checks access for skipped identities before listing or creating")
  let mut usageOk := true
  for args in [#[""], #["--restore-processes"], #["--unknown"], #[save.toString, "extra"]] do
    let (rc, err, calls) ← invoke panes "" "0" args
    usageOk := usageOk && rc == 2 && err == "usage: linger import [SAVE]\n" && calls.isEmpty
  f :=
    f +
      (←
        expect usageOk
            "linger import rejects empty paths, options and extra arguments before invoking linger")
  return f

private def importEnvironmentChecks (e : Env) (home data : String) : IO Nat := do
  let root := System.FilePath.mk e.dir / "import-env"
  let bin := root / "bin"
  let pane := root / "pane"
  IO.FS.createDirAll bin
  IO.FS.createDirAll (pane / "inner")
  let origin ← IO.FS.realPath root
  let paneDir ← IO.FS.realPath pane
  discard <|
      IO.Process.run
        { cmd := "ln",
          args := #["-s", (paneDir / "inner").toString, (origin / "saved-link").toString] }
  let save := origin / "save"
  let callsFile := origin / "calls"
  let executable := origin / "recorder with spaces"
  IO.FS.writeFile executable
      r#"#!/bin/sh
printf 'CALL\000linger\000' >> "$IMPORT_PROBE_CALLS"
printf '%s\000' "$@" >> "$IMPORT_PROBE_CALLS"
printf '\nCALL\000cwd\000%s\000\n' "$(pwd -P)" >> "$IMPORT_PROBE_CALLS"
if [ "$IMPORT_PROBE_CHECK_HOME" = 1 ]; then
    printf 'CALL\000home\000%s\000\n' "${HOME-}" >> "$IMPORT_PROBE_CALLS"
fi
if [ "$IMPORT_PROBE_CHECK_ENV" = 1 ]; then
    printf 'CALL\000env\000%s\000%s\000%s\000%s\000\n' \
        "${HOME-<unset>}" "${LINGER_DIR-<unset>}" "${XDG_RUNTIME_DIR-<unset>}" \
        "${XDG_STATE_HOME-<unset>}" >> "$IMPORT_PROBE_CALLS"
fi
"#
  Linger.Posix.chmod executable.toString 0o700
  let self := (← IO.appPath).toString
  let probeArgs := #["--import-probe", executable.toString, save.toString]
  let env :=
    e.procEnv ++
      #[("PATH", some "bin:/usr/bin:/bin"), ("HOME", some home), ("XDG_DATA_HOME", some data),
        ("IMPORT_PROBE_CALLS", some callsFile.toString), ("IMPORT_PROBE_CHECK_HOME", some "0"),
        ("IMPORT_PROBE_CHECK_ENV", some "0")]
  let listCalls := call ["linger", "ls", "--porcelain"] ++ call ["cwd", origin.toString]
  -- Parent traversal follows the saved symlink physically, so the pane starts
  -- in paneDir rather than the lexical parent of saved-link.
  IO.FS.writeFile save (paneLine "lookup" "1" "0" "saved-link/.." "")
  let mut f := 0
  for impostor in [false, true] do
    if impostor then
      for path in [origin / "linger", bin / "linger"] do
        IO.FS.writeFile path
            "#!/bin/sh\nprintf 'CALL\\000impostor\\000\\n' >> \"$IMPORT_PROBE_CALLS\"\nexit 97\n"
        Linger.Posix.chmod path.toString 0o700
    let present ← (origin / "linger").pathExists
    IO.FS.writeFile callsFile ""
    let out ←
      IO.Process.output
          { cmd := "/bin/bash",
            args :=
              #["--noprofile", "--norc", "-c",
                  "linger() { printf 'FUNCTION\\n' >> \"$IMPORT_PROBE_CALLS\"; }; export -f linger || exit 98; exec \"$@\"",
                  "--", self] ++
                probeArgs,
            cwd := some origin, env }
    f :=
      f +
        (←
          expect
              (present == impostor && out.exitCode == 0 &&
                (← IO.FS.readFile callsFile) ==
                  listCalls ++ call ["linger", "run", "lookup-w1-p0", "true"] ++
                    call ["cwd", paneDir.toString])
              s!"linger import uses the supplied executable past an exported Bash function (PATH/cwd impostor: {impostor})")
  IO.FS.removeFile (origin / "linger")
  IO.FS.removeFile (bin / "linger")
  -- The same effective home and state paths reach ls in the invocation cwd and
  -- run in the saved cwd. Missing suffixes, empty overrides and absent variables
  -- must retain their meanings across both children.
  IO.FS.writeFile save (paneLine "environment" "1" "0" "~" "")
  let states :=
    #[("LINGER_DIR", some "saved-link/../state"), ("XDG_RUNTIME_DIR", some "saved-link/../runtime"),
      ("XDG_STATE_HOME", some "saved-link/../persistent")]
  for (label, extra, expected) in
    [("relative", states,
        [(paneDir / "state").toString, (paneDir / "runtime").toString,
          (paneDir / "persistent").toString]),
      ("empty", states.map fun (key, _) => (key, some ""), [origin.toString, "", ""]),
      ("unset", states.map fun (key, _) => (key, none), ["<unset>", "<unset>", "<unset>"])] do
    IO.FS.writeFile callsFile ""
    let out ←
      IO.Process.output
          { cmd := self, args := probeArgs, cwd := some origin,
            env :=
              env ++ #[("HOME", some "saved-link/.."), ("IMPORT_PROBE_CHECK_ENV", some "1")] ++
                extra }
    let envCall := call (["env", paneDir.toString] ++ expected)
    f :=
      f +
        (←
          expect
              (out.exitCode == 0 &&
                (← IO.FS.readFile callsFile) ==
                  listCalls ++ envCall ++ call ["linger", "run", "environment-w1-p0", "true"] ++
                    call ["cwd", paneDir.toString] ++
                    envCall)
              s!"linger import freezes physical home and child state environment ({label})")
  -- Fish supplies the account-home baseline without reading any save. Explicit
  -- SAVE and the recorder keep these checks from touching the user's files.
  let fallback ←
    IO.Process.output
        { cmd := "fish", args := #["--no-config", "-c", "printf '%s' \"$HOME\""],
          env :=
            e.procEnv ++
              #[("HOME", none), ("XDG_CONFIG_HOME", some (origin / "config").toString),
                ("XDG_DATA_HOME", some data)] }
  unless fallback.exitCode == 0 && !fallback.stdout.isEmpty do
    throw (IO.userError "could not obtain fish's account-home baseline")
  let accountHome ← IO.FS.realPath fallback.stdout
  let command := "tail -n 1 'home probe'"
  IO.FS.writeFile save (paneLine "fallback" "1" "0" "~" command)
  for (label, value) in [("unset", none), ("empty", some "")] do
    IO.FS.writeFile callsFile ""
    let out ←
      IO.Process.output
          { cmd := self, args := probeArgs, cwd := some origin,
            env := env ++ #[("HOME", value), ("IMPORT_PROBE_CHECK_HOME", some "1")] }
    let lines := (← IO.FS.readFile callsFile).splitOn "\n"
    let homes :=
      lines.filterMap fun line =>
        match line.splitOn "\x00" with
        | ["CALL", "home", value, ""] => some value
        | _ => none
    let homeOk ←
      match homes with
      | [listed, created] =>
        if listed.isEmpty || listed != created || !(System.FilePath.mk listed).isAbsolute then
          pure false
        else
          try
            pure ((← IO.FS.realPath listed) == accountHome)
          catch _ =>
            pure false
      | _ =>
        pure false
    let calls :=
      String.join
        ((lines.filter fun line => !line.isEmpty && !line.startsWith "CALL\x00home\x00").map
          (· ++ "\n"))
    f :=
      f +
        (←
          expect
              (out.exitCode == 0 && homeOk &&
                calls ==
                  listCalls ++ call ["linger", "run", "fallback-w1-p0", "true"] ++
                    call ["cwd", accountHome.toString])
              s!"linger import uses account home for saved tilde and every child (HOME {label})")
  return f

def run : IO UInt32 := do
  let e ← Env.make "recipes"
  let root := System.FilePath.mk e.dir
  let home := root / "home"
  let data := root / "data"
  IO.FS.createDirAll home
  IO.FS.createDirAll data
  let mut f ← configChecks
  f := f + (← absoluteExecutableChecks e home.toString data.toString)
  f := f + (← importBoundaryChecks e home.toString data.toString)
  f := f + (← importEnvironmentChecks e home.toString data.toString)
  f := f + (← relativePathChecks e)
  -- Default path, escaped cwd, and ignored saved command.
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
  let (drc, dout, derr) ← runImport e home.toString data.toString #[]
  f :=
    f +
      (←
        expect
            (drc == 0 && dout.isEmpty && derr.isEmpty &&
              (← e.info "desk-w1-p0" "start_dir") == some defaultDir.toString)
            "linger import reads the default XDG save and restores an escaped cwd")
  IO.sleep 700 -- negative assertion: give a wrongly-started command time to run
  f :=
    f +
      (←
        expect (!(← System.FilePath.pathExists defaultSink))
            "linger import never executes the default save's command")
  -- An explicitly empty XDG value has the documented shell `:-` semantics.
  let emptyXdgDir := root / "empty-xdg"
  let fallbackResurrectDir := home / ".local" / "share" / "tmux" / "resurrect"
  IO.FS.createDirAll emptyXdgDir
  IO.FS.createDirAll fallbackResurrectDir
  IO.FS.writeFile (fallbackResurrectDir / "last")
      (paneLine "emptyxdg" "3" "0" emptyXdgDir.toString "")
  let (xrc, _, _) ← runImport e home.toString "" #[]
  f :=
    f +
      (←
        expect (xrc == 0 && (← e.info "emptyxdg-w3-p0" "start_dir") == some emptyXdgDir.toString)
            "linger import treats an empty XDG data home as unset")
  -- Once the legacy directory exists, it takes precedence over the XDG path.
  let legacyDir := root / "legacy"
  let legacyResurrectDir := home / ".tmux" / "resurrect"
  IO.FS.createDirAll legacyDir
  IO.FS.createDirAll legacyResurrectDir
  IO.FS.writeFile (legacyResurrectDir / "last") (paneLine "legacy" "2" "0" legacyDir.toString "")
  let (lrc, _, _) ← runImport e home.toString data.toString #[]
  f :=
    f +
      (←
        expect (lrc == 0 && (← e.info "legacy-w2-p0" "start_dir") == some legacyDir.toString)
            "linger import prefers the legacy default save directory when it exists")
  -- Empty commands, pipelines and other shell syntax all leave ordinary shells.
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
  let (prc, _, _) ← runImport e home.toString data.toString #[processSave.toString]
  f :=
    f +
      (←
        expect
            (prc == 0 && (← e.info "dev-w1-p0" "start_dir") == some processDir.toString &&
              (← e.info "dev-w1-p1" "start_dir") == some processDir.toString &&
              (← e.info "dev-w1-p2" "start_dir") == some processDir.toString)
            "linger import projects every pane into a named linger session")
  IO.sleep 700 -- negative assertion after the import process itself has exited
  f :=
    f +
      (←
        expect (!(← System.FilePath.pathExists processSink))
            "linger import ignores a saved pipeline")
  f :=
    f +
      (←
        expect (!(← System.FilePath.pathExists blockedSink))
            "linger import ignores arbitrary saved shell syntax")
  let names := #["dev-w1-p0", "dev-w1-p1", "dev-w1-p2"]
  let before ← names.mapM (fun name => e.info name "outseq")
  let (rrc, _, _) ← runImport e home.toString data.toString #[processSave.toString]
  IO.sleep 700
  let after ← names.mapM (fun name => e.info name "outseq")
  f :=
    f +
      (←
        expect (rrc == 0 && before.all (·.isSome) && after == before)
            "linger import leaves existing shells untouched on a sequential rerun")
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
  let (src, _, _) ← runImport e home.toString data.toString #[resumableSave.toString]
  IO.sleep 700
  let resumableState ← e.status "resumable-w1-p0"
  f :=
    f +
      (←
        expect
            (checkpointed && crashed && src == 0 && resumableState == .resumable &&
              !(← System.FilePath.pathExists resumableSink))
            "linger import skips a resumable checkpoint instead of reviving and replaying it")
  -- Validate the complete pane set before the first daemon can be created.
  let absentDir := root / "absent"
  let invalidSave := root / "invalid-save"
  IO.FS.writeFile invalidSave
      (paneLine "prevalid" "1" "0" processDir.toString "" ++
        paneLine "prevalid" "1" "1" absentDir.toString "")
  let (irc, _, ierr) ← runImport e home.toString data.toString #[invalidSave.toString]
  f :=
    f +
      (←
        expect
            (irc == 1 && has ierr "working directory not found" &&
              (← e.cli #["info", "prevalid-w1-p0"]).1 == 1)
            "linger import validates every cwd before creating any session")
  let invalidNameSave := root / "invalid-name-save"
  let longNameSave := root / "long-name-save"
  IO.FS.writeFile invalidNameSave (paneLine "bad/name" "1" "0" processDir.toString "")
  let longName := String.ofList (List.replicate 80 'a')
  IO.FS.writeFile longNameSave (paneLine longName "1" "0" processDir.toString "")
  let (urc, _, uerr) ← runImport e home.toString data.toString #[invalidNameSave.toString]
  let (longRc, _, longErr) ← runImport e home.toString data.toString #[longNameSave.toString]
  f :=
    f +
      (←
        expect
            (urc == 1 && longRc == 1 && has uerr "not a valid linger name" &&
              has longErr "not a valid linger name" &&
              (← e.cli #["info", "bad_name-w1-p0"]).1 == 1)
            "linger import rejects names that linger would rewrite or truncate")
  let inaccessibleDir := root / "inaccessible"
  let inaccessibleSave := root / "inaccessible-save"
  IO.FS.createDirAll inaccessibleDir
  IO.FS.writeFile inaccessibleSave
      (paneLine "accessvalid" "1" "0" processDir.toString "" ++
        paneLine "inaccessible" "1" "0" inaccessibleDir.toString "")
  Linger.Posix.chmod inaccessibleDir.toString 0
  let (accessRc, _, accessErr) ←
    try
      runImport e home.toString data.toString #[inaccessibleSave.toString]
    finally
      Linger.Posix.chmod inaccessibleDir.toString 0o700
  f :=
    f +
      (←
        expect
            (accessRc == 1 && has accessErr "working directory not accessible" &&
              (← e.cli #["info", "accessvalid-w1-p0"]).1 == 1)
            "linger import validates directory access before creating any session")
  let malformedSave := root / "malformed-save"
  IO.FS.writeFile malformedSave "pane\tshort\n"
  let (mrc, _, merr) ← runImport e home.toString data.toString #[malformedSave.toString]
  f :=
    f +
      (←
        expect (mrc == 1 && has merr "malformed pane record")
            "linger import rejects a malformed pane record")
  let emptySave := root / "empty-save"
  IO.FS.writeFile emptySave "window\tignored\nstate\tignored\t\n"
  let (erc, _, eerr) ← runImport e home.toString data.toString #[emptySave.toString]
  f :=
    f +
      (←
        expect (erc == 1 && has eerr "no pane records")
            "linger import rejects a save with no pane records")
  let (nrc, _, nerr) ← runImport e home.toString data.toString #[s!"{e.dir}/missing-save"]
  f := f + (← expect (nrc == 1 && has nerr "save not found") "linger import reports a missing save")
  e.killAll
      #["desk-w1-p0", "emptyxdg-w3-p0", "legacy-w2-p0", "dev-w1-p0", "dev-w1-p1", "dev-w1-p2",
        "resumable-w1-p0", "prevalid-w1-p0", "prevalid-w1-p1", "bad_name-w1-p0",
        "accessvalid-w1-p0", "inaccessible-w1-p0"]
  verdict e f

end E2E.Recipes
