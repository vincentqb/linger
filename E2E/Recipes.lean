module

public import E2E.Harness
public import Linger.Core.Name

public section

/-! # E2E.Recipes — composition kept outside the linger binary

`lz import-resurrect` projects pane records into independent linger sessions.
This suite drives the optional Lean executable against real daemons and
synthetic saves, and records commands to check its IO boundary.
The smaller helpers run against command recorders to check error propagation
and argument boundaries without contacting hosts or opening GUI windows.
-/

namespace E2E.Recipes

open E2E.Harness

private def call (args : List String) : String :=
  "CALL\x00" ++ String.intercalate "\x00" args ++ "\x00\n"

/-- Run the actual script under `/bin/sh`, or execute its shebang directly.
External command recorders share a fixture-owned counter; a process deadline
also catches a broken loop that ignores the recorder's call-budget failure. -/
private def probe (e : Env) (recipe : String) (args : Array String := #[])
    (settings : Array (String × String) := #[]) (direct : Bool := false)
    (closeOutput : Bool := false) : IO (UInt32 × String × String) := do
  let root := System.FilePath.mk e.dir / "probe"
  let counter := root / "counter"
  IO.FS.createDirAll root
  IO.FS.writeFile counter "0 0\n"
  let recorder :=
    r#"#!/bin/sh
read -r calls attaches < "$RECIPE_COUNTER" || exit 98
calls=$((calls + 1))
[ "$calls" -le 12 ] || exit 99
tool=${0##*/}
if [ "$tool" = linger ] && [ "$1" = attach ]; then
    attaches=$((attaches + 1))
fi
printf '%s %s\n' "$calls" "$attaches" > "$RECIPE_COUNTER" || exit 98
printf 'CALL\000%s\000' "$tool" >&2
if [ "$#" -gt 0 ]; then printf '%s\000' "$@" >&2; fi
printf '\n' >&2
case "$tool" in
    linger)
        if [ "$1" = ls ]; then
            printf '%s' "$RECIPE_LISTING"
            exit "$RECIPE_LIST_RC"
        fi
        [ "$attaches" -eq 1 ] || exit 5
        exit "$RECIPE_ATTACH_RC"
        ;;
    ssh) printf '%s' "$RECIPE_LISTING"; exit "$RECIPE_LIST_RC" ;;
    kitten) exit "$RECIPE_LAUNCH_RC" ;;
    clear)
        if [ -n "$RECIPE_CLEAR_OUT" ]; then printf '%s' "$RECIPE_CLEAR_OUT"; fi
        exit "$RECIPE_CLEAR_RC"
        ;;
    sleep) exit "$RECIPE_SLEEP_RC" ;;
esac
"#
  for name in ["linger", "ssh", "kitten", "clear", "sleep"] do
    let file := root / name
    IO.FS.writeFile file recorder
    Linger.Posix.chmod file.toString 0o700
  let defaults :=
    #[("RECIPE_LISTING", "name\twork\n"), ("RECIPE_LIST_RC", "0"), ("RECIPE_ATTACH_RC", "7"),
      ("RECIPE_SLEEP_RC", "7"), ("RECIPE_LAUNCH_RC", "0"), ("RECIPE_CLEAR_RC", "0"),
      ("RECIPE_CLEAR_OUT", "")]
  let script := ((← IO.currentDir) / "recipes" / s!"{recipe}.sh").toString
  let command := if direct then script else "/bin/sh"
  let arguments := if direct then args else #[script] ++ args
  let path := s!"{root}:{(← IO.getEnv "PATH").getD ""}"
  let child? ←
    try
      some <$>
          IO.Process.spawn
            { cmd := if closeOutput then "/bin/sh" else command,
              args :=
                if closeOutput then #["-c", "exec \"$@\" >&-", "--", command] ++ arguments
                else arguments,
              env :=
                (defaults ++ settings).map (fun (key, value) => (key, some value)) ++
                  #[("PATH", some path), ("RECIPE_COUNTER", some counter.toString)],
              stdin := .null, stdout := .piped, stderr := .piped }
    catch _ =>
      pure none
  let some child := child? | return (127, "", "")
  let code ← waitProcess child 5000
  if code.isNone then
    child.kill
    discard child.wait
  let stdout ← child.stdout.readToEnd
  let stderr ← child.stderr.readToEnd
  let calls := (stderr.splitOn "\n").filter (·.startsWith "CALL\x00")
  return (code.getD 99, stdout, String.join (calls.map (· ++ "\n")))

private def helperChecks (e : Env) : IO Nat := do
  let mut f := 0
  let target := "work@me@dev-a"
  let attachCall := call ["linger", "attach", target]
  let (attachRc, _, attachCalls) ← probe e "lza" #[target]
  f :=
    f +
      (←
        expect (attachRc == 7 && attachCalls == attachCall)
            "lza returns a non-transport attach failure without retrying")
  for pauseRc in ["0", "7"] do
    let (rc, _, calls) ←
      probe e "lza" #[target] #[("RECIPE_ATTACH_RC", "255"), ("RECIPE_SLEEP_RC", pauseRc)]
    let expected := attachCall ++ call ["sleep", "2"] ++ (if pauseRc == "0" then attachCall else "")
    f :=
      f +
        (←
          expect (rc == (if pauseRc == "0" then 5 else 7) && calls == expected)
              s!"lza retries transport failure only after a successful pause ({pauseRc})")
  for recipe in ["lza", "lzo"] do
    let mut usageOk := true
    for args in [#[], #[""], #["one", "two"]] do
      let (rc, _, calls) ← probe e recipe args
      usageOk := usageOk && rc == 2 && calls.isEmpty
    f := f + (← expect usageOk s!"{recipe} requires exactly one nonempty target")
  let mut attachStatusOk := true
  for status in [0, 1, 9, 130] do
    let (rc, _, calls) ← probe e "lza" #[target] #[("RECIPE_ATTACH_RC", toString status)]
    attachStatusOk := attachStatusOk && rc == status && calls == attachCall
  f := f + (← expect attachStatusOk "lza preserves every tested non-255 status without a pause")
  let (boardRc, _, boardCalls) ← probe e "lzs" #["", "2"]
  f :=
    f +
      (←
        expect
            (boardRc == 7 &&
              boardCalls == call ["linger", "ls", "-r"] ++ call ["clear"] ++ call ["sleep", "2"])
            "lzs uses configured remotes for an empty host and stops on pause failure")
  let (listRc, listOut, listCalls) ← probe e "lzs" #[] #[("RECIPE_LIST_RC", "7")]
  f :=
    f +
      (←
        expect (listRc == 7 && listOut.isEmpty && listCalls == call ["linger", "ls", "-r"])
            "lzs reports listing failure before clearing the screen")
  let (clearRc, clearOut, clearCalls) ← probe e "lzs" #[] #[("RECIPE_CLEAR_RC", "11")]
  f :=
    f +
      (←
        expect
            (clearRc == 11 && clearOut.isEmpty &&
              clearCalls == call ["linger", "ls", "-r"] ++ call ["clear"])
            "lzs stops on clear failure before printing or pausing")
  let (printRc, _, printCalls) ← probe e "lzs" #[] #[] false true
  f :=
    f +
      (←
        expect
            (printRc != 0 && printRc != 99 &&
              printCalls == call ["linger", "ls", "-r"] ++ call ["clear"])
            "lzs stops on output failure before pausing")
  let board := "NAME\tSTATUS\n  a * literal row\nsecond\twaiting\n"
  let (wholeRc, wholeOut, wholeCalls) ←
    probe e "lzs" #["me@one,me@two", ".25"]
        #[("RECIPE_LISTING", board), ("RECIPE_CLEAR_OUT", "CLEARED\n")]
  f :=
    f +
      (←
        expect
            (wholeRc == 7 && wholeOut == "CLEARED\n" ++ board &&
              wholeCalls ==
                call ["linger", "ls", "-r", "me@one,me@two"] ++ call ["clear"] ++
                  call ["sleep", ".25"])
            "lzs clears then prints the complete listing without splitting its rows")
  let mut positiveOk := true
  for seconds in ["1", "0001", "0.25", ".5", "5.", ""] do
    let (rc, _, calls) ← probe e "lzs" #["", seconds]
    positiveOk :=
      positiveOk && rc == 7 &&
        calls ==
          call ["linger", "ls", "-r"] ++ call ["clear"] ++
            call ["sleep", if seconds.isEmpty then "5" else seconds]
  let (defaultRc, _, defaultCalls) ← probe e "lzs"
  positiveOk :=
    positiveOk && defaultRc == 7 &&
      defaultCalls == call ["linger", "ls", "-r"] ++ call ["clear"] ++ call ["sleep", "5"]
  f :=
    f + (← expect positiveOk "lzs accepts positive integer and fractional intervals and defaults")
  let mut intervalOk := true
  for args in
    [#["", "0"], #["", "-1"], #["", "bogus"], #["a", "2", "extra"], #["", "."], #["", "00.000"],
      #["", "1..2"], #["", "..1"], #["", "1e2"], #["", " 2"], #["", "2\n3"]] do
    let (rc, _, calls) ← probe e "lzs" args
    intervalOk := intervalOk && rc == 2 && calls.isEmpty
  f := f + (← expect intervalOk "lzs rejects invalid intervals and extra arguments")
  let host := "me@dev-a"
  let sshCall :=
    call
      ["ssh", "-o", "BatchMode=yes", "-o", "ConnectTimeout=3", "--", host, "linger", "ls",
        "--porcelain"]
  for listing in ["", "name\twork\n"] do
    let (rc, _, calls) ←
      probe e "lzo" #[host] #[("RECIPE_LISTING", listing), ("RECIPE_LIST_RC", "255")]
    f :=
      f +
        (←
          expect (rc == 255 && calls == sshCall)
              s!"lzo preserves failed SSH status before launching (empty output: {listing.isEmpty})")
  let names := ["-live+1", "+saved"].map Linger.Core.Name.sanitize
  let listing := String.join (names.map fun name => s!"name\t{name}\nstate\tlive\n\n")
  let launch := fun name =>
    call
      ["kitten", "@", "launch", "--type=tab", "--tab-title", s!"{name}@{host}", "--", "ssh", "-t",
        "--", host, "linger", "attach", name]
  let (tabsRc, _, tabsCalls) ← probe e "lzo" #[host] #[("RECIPE_LISTING", listing)]
  f :=
    f +
      (←
        expect (tabsRc == 0 && tabsCalls == sshCall ++ String.join (names.map launch))
            "lzo launches each canonical session with exact SSH destination and name")
  let (launchRc, _, launchCalls) ←
    probe e "lzo" #[host] #[("RECIPE_LISTING", listing), ("RECIPE_LAUNCH_RC", "9")]
  f :=
    f +
      (←
        expect (launchRc == 9 && launchCalls == sshCall ++ launch names[0]!)
            "lzo stops after the first failed tab launch")
  let mut namesOk := true
  for name in
    ["bad/name", ".hidden", "a;touch SENTINEL", "", "extra\tfield", "with space", "with\rreturn",
      "nonascii-é", String.ofList (List.replicate (Linger.Core.Name.maxLen + 1) 's')] do
    let (rc, _, calls) ← probe e "lzo" #[host] #[("RECIPE_LISTING", listing ++ s!"name\t{name}\n")]
    namesOk := namesOk && rc != 0 && calls == sshCall
  f := f + (← expect namesOk "lzo validates every name before opening the first tab")
  let mut recordsOk := true
  for invalid in ["name\n", s!"name\t{names[0]!}\n"] do
    let (rc, _, calls) ← probe e "lzo" #[host] #[("RECIPE_LISTING", listing ++ invalid)]
    recordsOk := recordsOk && rc == 1 && calls == sshCall
  f := f + (← expect recordsOk "lzo rejects missing and duplicate name fields before all launches")
  let (emptyRc, _, emptyCalls) ← probe e "lzo" #[host] #[("RECIPE_LISTING", "")]
  f :=
    f +
      (←
        expect (emptyRc == 0 && emptyCalls == sshCall)
            "lzo accepts an empty successful listing without opening an empty tab")
  let boundaryNames := ["-", "+", String.ofList (List.replicate Linger.Core.Name.maxLen 's')]
  let boundaryListing := String.join (boundaryNames.map fun name => s!"name\t{name}\n")
  let (boundaryRc, _, boundaryCalls) ← probe e "lzo" #[host] #[("RECIPE_LISTING", boundaryListing)]
  f :=
    f +
      (←
        expect
            (boundaryRc == 0 && boundaryCalls == sshCall ++ String.join (boundaryNames.map launch))
            "lzo accepts one-character punctuation and the canonical maximum name length")
  let literal := "-work@me@host [ab]*; '$HOME' \\ literal"
  let (literalRc, _, literalCalls) ← probe e "lza" #[literal]
  let (hostsRc, _, hostsCalls) ← probe e "lzs" #[literal, "2"]
  let (hostRc, _, hostCalls) ← probe e "lzo" #[literal]
  f :=
    f +
      (←
        expect
            (literalRc == 7 && literalCalls == call ["linger", "attach", literal] && hostsRc == 7 &&
              hostsCalls ==
                call ["linger", "ls", "-r", literal] ++ call ["clear"] ++ call ["sleep", "2"] &&
              hostRc == 0 &&
              hostCalls ==
                call
                    ["ssh", "-o", "BatchMode=yes", "-o", "ConnectTimeout=3", "--", literal,
                      "linger", "ls", "--porcelain"] ++
                  call
                    ["kitten", "@", "launch", "--type=tab", "--tab-title", s!"work@{literal}", "--",
                      "ssh", "-t", "--", literal, "linger", "attach", "work"])
            "POSIX recipes preserve spaces, glob characters and shell punctuation as literal arguments")
  for (recipe, args, expectedRc, expectedCalls) in
    [("lza", #[target], 7, attachCall),
      ("lzs", #[], 7, call ["linger", "ls", "-r"] ++ call ["clear"] ++ call ["sleep", "5"]),
      ("lzo", #[host], 0, sshCall ++ launch "work")] do
    let (rc, _, calls) ← probe e recipe args #[] true
    f :=
      f +
        (←
          expect (rc == expectedRc && calls == expectedCalls)
              s!"{recipe} executes directly with its portable shebang")
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

/-- Invoke the optional Lean executable. The built linger binary leads PATH;
HOME and XDG data are fixture-owned so defaults cannot read user saves. -/
def runImport (e : Env) (home data : String) (args : Array String)
    (extra : Array (String × Option String) := #[]) : IO (UInt32 × String × String) := do
  let cwd ← IO.currentDir
  let path := s!"{(cwd / ".lake" / "build" / "bin").toString}:{(← IO.getEnv "PATH").getD ""}"
  let out ←
    IO.Process.output
        { cmd := (cwd / ".lake/build/bin/lz").toString, args := #["import-resurrect"] ++ args,
          env :=
            e.procEnv ++
              #[("HOME", some home), ("XDG_DATA_HOME", some data), ("PATH", some path)] ++
              extra }
  return (out.exitCode, out.stdout, out.stderr)

private def relativePathChecks (e : Env) : IO Nat := do
  let root := System.FilePath.mk e.dir
  let origin := root / "relative" / "from"
  let pane := root / "relative" / "to" / "inner"
  let binDir := origin / "bin"
  IO.FS.createDirAll binDir
  IO.FS.createDirAll pane
  IO.FS.writeBinFile (binDir / "linger") (← IO.FS.readBinFile e.bin)
  Linger.Posix.chmod (binDir / "linger").toString 0o700
  discard <|
      IO.Process.run
        { cmd := "ln", args := #["-s", (root / "relative").toString, (origin / "link").toString] }
  let importer := ((← IO.currentDir) / ".lake/build/bin/lz").toString
  let wrongDir := { e with dir := (root / "relative").toString }
  let wrongSymlinkDir := { e with dir := origin.toString }
  let mut f := 0
  for (label, path, state) in
    [("binary", "bin:/usr/bin:/bin", e.dir), ("state", s!"{binDir}:/usr/bin:/bin", "../.."),
      ("symlink-state", s!"{binDir}:/usr/bin:/bin", "link/..")] do
    let name := s!"relative-{label}-w1-p0"
    let save := root / s!"relative-{label}-save"
    IO.FS.writeFile save (paneLine s!"relative-{label}" "1" "0" pane.toString "")
    try
      let out ←
        IO.Process.output
            { cmd := importer, args := #["import-resurrect", save.toString],
              cwd := some origin.toString,
              env := e.procEnv ++ #[("PATH", some path), ("LINGER_DIR", some state)] }
      f :=
        f +
          (←
            expect (out.exitCode == 0 && (← e.info name "start_dir") == some pane.toString)
                s!"lz import-resurrect keeps a relative {label} path anchored to the invocation directory")
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
            { cmd := importer, args := #["import-resurrect", save.toString], cwd := some deepOrigin,
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
                s!"lz import-resurrect resolves a long relative state path before spawning (already exists: {preexisting})")
    finally
      owned.killAll #[name]
  return f

private def importBoundaryChecks (e : Env) (home data : String) : IO Nat := do
  let root := System.FilePath.mk e.dir / "import-boundary"
  IO.FS.createDirAll root
  let save := root / "save"
  let callsFile := root / "calls"
  let executable := root / "linger"
  IO.FS.writeFile executable
      r#"#!/bin/sh
printf 'CALL\000linger\000' >> "$LZR_CALLS"
printf '%s\000' "$@" >> "$LZR_CALLS"
printf '\n' >> "$LZR_CALLS"
if [ "$1" = ls ]; then
    printf '%s' "$LZR_LISTING"
    exit "$LZR_LIST_RC"
fi
if [ "$LZR_FAIL" = create ] && [ "$3" = true ]; then exit 7; fi
if [ "$LZR_FAIL" = restore ] && [ "$3" != true ]; then exit 9; fi
exit 0
"#
  Linger.Posix.chmod executable.toString 0o700
  let command := "tail -n 1 'a b' | tee -a 'c d'"
  let panes :=
    paneLine "live" "1" "0" home command ++ paneLine "resume" "1" "0" home command ++
      paneLine "first" "2" "0" home command ++
      paneLine "second" "2" "1" home ""
  let listing := "name\tlive-w1-p0\nstate\tlive\n\nname\tresume-w1-p0\nstate\tresumable\n\n"
  let invoke := fun (text failure listRc : String) (args : Array String) => do
    IO.FS.writeFile save text
    IO.FS.writeFile callsFile ""
    let (rc, _, err) ←
      runImport e home data args
          #[("PATH", some root.toString), ("LZR_CALLS", some callsFile.toString),
            ("LZR_LISTING", some listing), ("LZR_LIST_RC", some listRc), ("LZR_FAIL", some failure)]
    return (rc, err, ← IO.FS.readFile callsFile)
  let args := #["--restore-processes", save.toString]
  let listCall := call ["linger", "ls", "--porcelain"]
  let createCall := call ["linger", "run", "first-w2-p0", "true"]
  let restoreCall := call ["linger", "run", "first-w2-p0", command]
  let (rc, _, calls) ← invoke panes "" "0" args
  let mut f ←
    expect
        (rc == 0 &&
          calls ==
            listCall ++ createCall ++ restoreCall ++ call ["linger", "run", "second-w2-p1", "true"])
        "lz import-resurrect skips every existing identity and sends an unchanged saved command as one argument"
  let (rc, err, calls) ← invoke panes "" "7" args
  f :=
    f +
      (←
        expect (rc == 1 && has err "could not list" && calls == listCall)
            "lz import-resurrect rejects a failed listing even when it contains existing names")
  let (rc, err, calls) ← invoke panes "create" "0" args
  f :=
    f +
      (←
        expect (rc == 1 && has err "could not create" && calls == listCall ++ createCall)
            "lz import-resurrect stops on the first creation failure before restoring or creating another pane")
  let (rc, err, calls) ← invoke panes "restore" "0" args
  f :=
    f +
      (←
        expect
            (rc == 1 && has err "could not restore" &&
              calls == listCall ++ createCall ++ restoreCall)
            "lz import-resurrect stops on the first command failure before creating another pane")
  let mut preflightOk := true
  let valid := paneLine "valid" "3" "0" home ""
  for invalid in
    ["pane\tshort\n", valid, paneLine "nul" "1" "0" home "tail\x00 -f log",
      paneLine "nul" "1" "0" (home ++ "\x00ignored") ""] do
    let (rc, _, calls) ← invoke (valid ++ invalid) "" "0" args
    preflightOk := preflightOk && rc == 1 && calls.isEmpty
  f :=
    f +
      (←
        expect preflightOk
            "lz import-resurrect rejects malformed, duplicate and NUL-bearing saves before invoking linger")
  let (rc, _, calls) ← invoke panes "" "0" #[save.toString, "extra"]
  f :=
    f +
      (←
        expect (rc == 2 && calls.isEmpty)
            "lz import-resurrect rejects extra arguments before invoking linger")
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
  let executable := bin / "linger"
  IO.FS.writeFile executable
      r#"#!/bin/sh
printf 'CALL\000linger\000' >> "$LZR_CALLS"
printf '%s\000' "$@" >> "$LZR_CALLS"
printf '\nCALL\000cwd\000%s\000\n' "$(pwd -P)" >> "$LZR_CALLS"
if [ "$LZR_CHECK_HOME" = 1 ]; then
    printf 'CALL\000home\000%s\000\n' "${HOME-}" >> "$LZR_CALLS"
fi
"#
  Linger.Posix.chmod executable.toString 0o700
  let importer := ((← IO.currentDir) / ".lake/build/bin/lz").toString
  let env :=
    e.procEnv ++
      #[("PATH", some "bin:/usr/bin:/bin"), ("HOME", some home), ("XDG_DATA_HOME", some data),
        ("LZR_CALLS", some callsFile.toString), ("LZR_CHECK_HOME", some "0")]
  let listCalls := call ["linger", "ls", "--porcelain"] ++ call ["cwd", origin.toString]
  -- Parent traversal follows the saved symlink physically, so the pane starts
  -- in paneDir rather than the lexical parent of saved-link.
  IO.FS.writeFile save (paneLine "lookup" "1" "0" "saved-link/.." "")
  let mut f := 0
  for impostor in [false, true] do
    if impostor then
      IO.FS.writeFile (origin / "linger")
          "#!/bin/sh\nprintf 'CALL\\000impostor\\000\\n' >> \"$LZR_CALLS\"\n"
      Linger.Posix.chmod (origin / "linger").toString 0o700
    let present ← (origin / "linger").pathExists
    IO.FS.writeFile callsFile ""
    let out ←
      IO.Process.output
          { cmd := "/bin/bash",
            args :=
              #["--noprofile", "--norc", "-c",
                "linger() { printf 'FUNCTION\\n' >> \"$LZR_CALLS\"; }; export -f linger || exit 98; exec \"$@\"",
                "--", importer, "import-resurrect", save.toString],
            cwd := some origin, env }
    f :=
      f +
        (←
          expect
              (present == impostor && out.exitCode == 0 &&
                (← IO.FS.readFile callsFile) ==
                  listCalls ++ call ["linger", "run", "lookup-w1-p0", "true"] ++
                    call ["cwd", paneDir.toString])
              s!"lz import-resurrect resolves PATH past an exported Bash function (cwd impostor: {impostor})")
  IO.FS.removeFile (origin / "linger")
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
          { cmd := importer, args := #["import-resurrect", "--restore-processes", save.toString],
            cwd := some origin, env := env ++ #[("HOME", value), ("LZR_CHECK_HOME", some "1")] }
    let lines := (← IO.FS.readFile callsFile).splitOn "\n"
    let homes :=
      lines.filterMap fun line =>
        match line.splitOn "\x00" with
        | ["CALL", "home", value, ""] => some value
        | _ => none
    let homeOk ←
      match homes with
      | [listed, created, restored] =>
        if
            listed.isEmpty || listed != created || listed != restored ||
              !(System.FilePath.mk listed).isAbsolute then
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
                    call ["cwd", accountHome.toString] ++
                    call ["linger", "run", "fallback-w1-p0", command] ++
                    call ["cwd", origin.toString])
              s!"lz import-resurrect uses account home for saved tilde and every child (HOME {label})")
  return f

def run : IO UInt32 := do
  let e ← Env.make "recipes"
  let root := System.FilePath.mk e.dir
  let home := root / "home"
  let data := root / "data"
  IO.FS.createDirAll home
  IO.FS.createDirAll data
  let mut f ← helperChecks e
  f := f + (← importBoundaryChecks e home.toString data.toString)
  f := f + (← importEnvironmentChecks e home.toString data.toString)
  f := f + (← relativePathChecks e)
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
  let (drc, _, _) ← runImport e home.toString data.toString #[]
  f :=
    f +
      (←
        expect (drc == 0 && (← e.info "desk-w1-p0" "start_dir") == some defaultDir.toString)
            "lz import-resurrect reads the default XDG save and restores an escaped cwd")
  IO.sleep 700 -- negative assertion: give a wrongly-started command time to run
  f :=
    f +
      (←
        expect (!(← System.FilePath.pathExists defaultSink))
            "lz import-resurrect does not execute a saved command by default")
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
            "lz import-resurrect treats an empty XDG data home as unset")
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
            "lz import-resurrect prefers the legacy default save directory when it exists")
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
    runImport e home.toString data.toString #["--restore-processes", processSave.toString]
  f :=
    f +
      (←
        expect
            (prc == 0 && (← e.info "dev-w1-p0" "start_dir") == some processDir.toString &&
              (← e.info "dev-w1-p1" "start_dir") == some processDir.toString &&
              (← e.info "dev-w1-p2" "start_dir") == some processDir.toString)
            "lz import-resurrect projects every pane into a named linger session")
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
            "lz import-resurrect --restore-processes keeps commands aligned and runs an allowlisted one")
  IO.sleep 700 -- negative assertion after the import process itself has exited
  f :=
    f +
      (←
        expect (!(← System.FilePath.pathExists blockedSink))
            "lz import-resurrect --restore-processes skips a command outside the allowlist")
  let (rrc, _, _) ←
    runImport e home.toString data.toString #["--restore-processes", processSave.toString]
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
            "lz import-resurrect skips existing sessions on a sequential rerun")
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
    runImport e home.toString data.toString #["--restore-processes", resumableSave.toString]
  IO.sleep 700
  let resumableState ← e.status "resumable-w1-p0"
  f :=
    f +
      (←
        expect
            (checkpointed && crashed && src == 0 && resumableState == .resumable &&
              !(← System.FilePath.pathExists resumableSink))
            "lz import-resurrect skips a resumable checkpoint instead of reviving and replaying it")
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
            "lz import-resurrect validates every cwd before creating any session")
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
            "lz import-resurrect rejects names that linger would rewrite or truncate")
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
            "lz import-resurrect validates directory access before creating any session")
  let malformedSave := root / "malformed-save"
  IO.FS.writeFile malformedSave "pane\tshort\n"
  let (mrc, _, merr) ← runImport e home.toString data.toString #[malformedSave.toString]
  f :=
    f +
      (←
        expect (mrc == 1 && has merr "malformed pane record")
            "lz import-resurrect rejects a malformed pane record")
  let emptySave := root / "empty-save"
  IO.FS.writeFile emptySave "window\tignored\nstate\tignored\t\n"
  let (erc, _, eerr) ← runImport e home.toString data.toString #[emptySave.toString]
  f :=
    f +
      (←
        expect (erc == 1 && has eerr "no pane records")
            "lz import-resurrect rejects a save with no pane records")
  let (nrc, _, nerr) ← runImport e home.toString data.toString #[s!"{e.dir}/missing-save"]
  f :=
    f +
      (←
        expect (nrc == 1 && has nerr "save not found") "lz import-resurrect reports a missing save")
  e.killAll
      #["desk-w1-p0", "emptyxdg-w3-p0", "legacy-w2-p0", "dev-w1-p0", "dev-w1-p1", "dev-w1-p2",
        "resumable-w1-p0", "prevalid-w1-p0", "prevalid-w1-p1", "bad_name-w1-p0",
        "accessvalid-w1-p0", "inaccessible-w1-p0"]
  verdict e f

end E2E.Recipes
