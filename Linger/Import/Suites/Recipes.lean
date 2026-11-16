module

public import Verify.Harness
import Linger.Import.CoreCode.Resurrect
import Linger.Os.CoreCode.Answer
import Linger.Session.CoreCode.Checkpoint
import Linger.Target.CoreCode.Name

public section

/-! # Linger.Import.Suites.Recipes — native launch settings, fish and zsh prompts and the default save

`ls` lists the panes of the latest tmux-resurrect save, found where tmux-resurrect keeps it, and
`resume` runs a fresh shell on one. This suite drives the actual CLI against real daemons and
synthetic saves at the default locations.
Native configuration assertions inspect their effective settings; they do not
claim to launch or exercise any terminal GUI. The prompt checks execute the
native examples in fish and zsh with recorded command calls.
-/

namespace Linger.Import.Suites.Recipes

open Verify.Harness

private def call (args : List String) : String :=
  "CALL\x00" ++ String.intercalate "\x00" args ++ "\x00\n"

/-- The directory the checkpoint of session `name` in state directory `dir` resumes in, as it
records it: `none` without a readable checkpoint. -/
def savedCwd (dir name : String) : IO (Option String) := do
  match ← (IO.FS.readBinFile s!"{dir}/{name}.ckpt").toBaseIO with
  | .ok bytes =>
    return (Linger.Session.Checkpoint.loadBytes bytes).map (·.cwd)
  | .error _ =>
    return none

/-- Session `name` in state directory `dir` has a checkpoint that resumes in `expected`, a
daemon running it or not, as one a resume of a saved tmux pane wrote. Paths compare physically. -/
def savedIn' (dir name : String) (expected : System.FilePath) : IO Bool := do
  let some cwd ← savedCwd dir name | return false
  try
    return (← IO.FS.realPath cwd) == (← IO.FS.realPath expected)
  catch _ =>
    return false

/-- Session `name` in state directory `dir` is saved, with no daemon, to resume in `expected`:
the import that wrote it started nothing. Paths compare physically. -/
def savedIn (dir name : String) (expected : System.FilePath) : IO Bool := do
  let some cwd ← savedCwd dir name | return false
  if ← System.FilePath.pathExists s!"{dir}/{name}.sock" then
    return false
  try
    return (← IO.FS.realPath cwd) == (← IO.FS.realPath expected)
  catch _ =>
    return false

/-- A recipe's effective lines: trimmed, without blank or `comment` lines. A
missing file has none, so its check fails rather than throwing. -/
private def recipeLines (file : System.FilePath) (comment : String) : IO (List String) := do
  let content ←
    try
      IO.FS.readFile file
    catch _ =>
      pure ""
  return (content.splitOn "\n").map (·.trimAscii.toString) |>.filter fun line =>
      !line.isEmpty && !line.startsWith comment

private def configChecks : IO Unit := do
  let root := (← IO.currentDir) / "recipes"
  for (file, comment, setting, label) in
    [("ghostty_config", "#", "command = direct:linger attach", "Ghostty"),
      ("kitty.conf", "#", "shell linger attach", "Kitty"),
      ("wezterm.lua", "--", "return { default_prog = { 'linger', 'attach' } }", "WezTerm")] do
    let settings ← recipeLines (root / file) comment
    expect (settings == [setting]) s!"{label} native configuration launches linger attach"

/-- The recipe only wires a native prompt to the CLI. The recorder supplies
already rendered bytes; all assertions and case selection stay in Lean. -/
private def fishPromptChecks (e : Env) (home data : String) : IO Unit := do
  let recipe := (← IO.currentDir) / "recipes" / "fish_prompt.fish"
  let settings ← recipeLines recipe "#"
  expect
      (settings ==
        ["function fish_right_prompt", "set -l last_status $status", "command -q linger",
          "and command linger ls --summary 2>/dev/null", "return $last_status", "end"])
      "fish prompt delegates the standard attention suffix to linger ls --summary"
  let root := System.FilePath.mk e.dir / "fish prompt"
  let bin := root / "bin"
  let emptyPath := root / "empty"
  let callsFile := root / "calls"
  IO.FS.createDirAll bin
  IO.FS.createDirAll emptyPath
  let env :=
    e.procEnv ++
      #[("HOME", some home), ("XDG_CONFIG_HOME", some (root / "config").toString),
        ("XDG_DATA_HOME", some data), ("FISH_PROMPT_CALLS", some callsFile.toString)]
  -- Resolve fish before restricting PATH. The recipe suite already requires
  -- fish for its account-home regression; none of this adds a runtime dependency.
  let found ←
    IO.Process.output { cmd := "fish", args := #["--no-config", "-c", "status fish-path"], env }
  let fish := found.stdout.trimAscii.toString
  unless found.exitCode == 0 && !fish.isEmpty do
    throw (IO.userError "could not resolve fish for the native prompt checks")
  IO.FS.writeFile (bin / "linger")
      r#"#!/bin/sh
printf 'CALL\000' >> "$FISH_PROMPT_CALLS"
printf '%s\000' "$@" >> "$FISH_PROMPT_CALLS"
printf '\n' >> "$FISH_PROMPT_CALLS"
printf '%s' "$FISH_PROMPT_STDOUT"
printf '%s' "$FISH_PROMPT_STDERR" >&2
exit "$FISH_PROMPT_RC"
"#
  Os.Shell.chmod (bin / "linger").toString 0o700
  let setup :=
    r#"function fish_prompt
    printf 'LEFT'
end
function fish_title
    printf 'TITLE'
    printf 'TITLE\n' >> "$FISH_PROMPT_CALLS"
end
function linger
    printf 'SHADOW'
    return 97
end
function prompt_probe_previous
    return $FISH_PROMPT_PREVIOUS
end
source "$argv[1]"; or exit 98
"#
  let draw := "prompt_probe_previous\nfish_right_prompt\nexit $status\n"
  let invoke := fun (path : System.FilePath) (body text err rc previous : String) => do
    IO.FS.writeFile callsFile ""
    let out ←
      IO.Process.output
          { cmd := fish, args := #["--no-config", "-c", setup ++ body, "--", recipe.toString],
            env :=
              env ++
                #[("PATH", some path.toString), ("FISH_PROMPT_STDOUT", some text),
                  ("FISH_PROMPT_STDERR", some err), ("FISH_PROMPT_RC", some rc),
                  ("FISH_PROMPT_PREVIOUS", some previous)] }
    return (out, ← IO.FS.readFile callsFile)
  let (loaded, calls) ← invoke bin "fish_prompt\nfish_title\n" "" "" "0" "0"
  expect
      (loaded.exitCode == 0 && loaded.stdout == "LEFTTITLE" && loaded.stderr.isEmpty &&
        calls == "TITLE\n")
      "fish recipe preserves the left prompt and title hook and samples nothing when sourced"
  let attention :=
    Linger.Display.Status.summary [.wantsYou, .unknown, .exitedBad, .wantsYou, .working] ++ "\n"
  let unknown := Linger.Display.Status.summary [.unknown] ++ "\n"
  for (context, contextSetup) in
    [("outside", "set -e LINGER_SESSION\n"), ("inside", "set -gx LINGER_SESSION work\n")] do
    for (label, text, err, rc, previous) in
      [("attention", attention, "hidden diagnostic\n", "0", "23"), ("empty", "", "", "0", "0"),
        ("failure", "", "status unavailable\n", "7", "42")] do
      let (out, calls) ← invoke bin (contextSetup ++ draw) text err rc previous
      expect
          (out.exitCode.toNat == previous.toNat?.getD 99 && out.stdout == text &&
            out.stderr.isEmpty &&
            calls == call ["ls", "--summary"])
          s!"fish attention keeps shared bytes and status without calling fish_title ({label}, {context})"
  let (missing, calls) ← invoke emptyPath draw "" "" "0" "19"
  expect
      (missing.exitCode == 19 && missing.stdout.isEmpty && missing.stderr.isEmpty && calls.isEmpty)
      "fish prompt is quiet and preserves status when linger is absent from PATH"
  let redraw :=
    "prompt_probe_previous\nfish_right_prompt\nset -gx FISH_PROMPT_STDOUT '" ++ unknown ++ "'\n" ++
      draw
  let (out, calls) ← invoke bin redraw attention "" "0" "23"
  expect
      (out.exitCode == 23 && out.stdout == attention ++ unknown && out.stderr.isEmpty &&
        calls == call ["ls", "--summary"] ++ call ["ls", "--summary"])
      "fish prompt samples again on each redraw without retaining old counts"
  -- Check the real command as well as the prompt, since prompt stderr suppression
  -- must not conceal a missing CLI route.
  let actual ← IO.Process.output { cmd := e.bin, args := #["ls", "--summary"], env }
  let (prompt, _) ← invoke ((System.FilePath.mk e.bin).parent.getD root) draw "" "" "0" "23"
  expect
      (actual.exitCode == 0 && actual.stdout.isEmpty && actual.stderr.isEmpty &&
        prompt.exitCode == 23 &&
        prompt.stdout.isEmpty &&
        prompt.stderr.isEmpty)
      "fish prompt composes with real linger ls --summary in an empty session directory"

/-- The zsh recipe, checked as the fish one is: it only wires a native prompt to the CLI, through
`precmd`. The recorder supplies already rendered bytes; all assertions and case selection stay in
Lean. A draw runs the `precmd` hooks in order, as zsh does before each prompt, then expands
`RPROMPT`, as zsh's `PROMPT_SUBST` does, which a command substitution leaves without the summary's
line feed. -/
private def zshPromptChecks (e : Env) (home data : String) : IO Unit := do
  let recipe := (← IO.currentDir) / "recipes" / "zsh_prompt.zsh"
  let settings ← recipeLines recipe "#"
  expect
      (settings ==
        ["linger_attention_sample() {", "local last_status=$?", "linger_attention=",
          "(( $+commands[linger] )) && linger_attention=$(command linger ls --summary 2>/dev/null)",
          "return $last_status", "}", "autoload -Uz add-zsh-hook",
          "add-zsh-hook precmd linger_attention_sample", "setopt prompt_subst",
          "RPROMPT+='${linger_attention}'"])
      "zsh prompt delegates the standard attention suffix to linger ls --summary"
  let root := System.FilePath.mk e.dir / "zsh prompt"
  let bin := root / "bin"
  let emptyPath := root / "empty"
  let callsFile := root / "calls"
  IO.FS.createDirAll bin
  IO.FS.createDirAll emptyPath
  let env :=
    e.procEnv ++
      #[("HOME", some home), ("ZDOTDIR", some (root / "config").toString),
        ("XDG_DATA_HOME", some data), ("ZSH_PROMPT_CALLS", some callsFile.toString)]
  -- Resolve zsh before restricting PATH; none of this adds a runtime dependency.
  let found ←
    IO.Process.output { cmd := "zsh", args := #["-f", "-c", "print -r -- $commands[zsh]"], env }
  let zsh := found.stdout.trimAscii.toString
  unless found.exitCode == 0 && !zsh.isEmpty do
    throw (IO.userError "could not resolve zsh for the native prompt checks")
  IO.FS.writeFile (bin / "linger")
      r#"#!/bin/sh
printf 'CALL\000' >> "$ZSH_PROMPT_CALLS"
printf '%s\000' "$@" >> "$ZSH_PROMPT_CALLS"
printf '\n' >> "$ZSH_PROMPT_CALLS"
printf '%s' "$ZSH_PROMPT_STDOUT"
printf '%s' "$ZSH_PROMPT_STDERR" >&2
exit "$ZSH_PROMPT_RC"
"#
  Os.Shell.chmod (bin / "linger").toString 0o700
  let setup :=
    r#"PROMPT='LEFT'
title_hook() {
  local last_status=$?
  print -rn -- 'TITLE'
  print -r -- 'TITLE' >> "$ZSH_PROMPT_CALLS"
  return $last_status
}
precmd_functions=(title_hook)
linger() {
  print -rn -- 'SHADOW'
  return 97
}
prompt_probe_previous() {
  return $ZSH_PROMPT_PREVIOUS
}
prompt_status() {
  return $1
}
source "$1" || exit 98
"#
  -- each hook hears the last command's status, as zsh gives it; the title hook is not the
  -- recipe's, and the recipe must not call it
  let drawOnce :=
    "prompt_probe_previous\ndrawn=$?\nfor hook in $precmd_functions; do\n" ++
      "  [[ $hook == title_hook ]] && continue\n  prompt_status $drawn\n  $hook\n  drawn=$?\n" ++
      "done\nprint -rnP -- \"$RPROMPT\"\n"
  let draw := drawOnce ++ "exit $drawn\n"
  let invoke := fun (path : System.FilePath) (body text err rc previous : String) => do
    IO.FS.writeFile callsFile ""
    let out ←
      IO.Process.output
          { cmd := zsh, args := #["-f", "-c", setup ++ body, "zsh", recipe.toString],
            env :=
              env ++
                #[("PATH", some path.toString), ("ZSH_PROMPT_STDOUT", some text),
                  ("ZSH_PROMPT_STDERR", some err), ("ZSH_PROMPT_RC", some rc),
                  ("ZSH_PROMPT_PREVIOUS", some previous)] }
    return (out, ← IO.FS.readFile callsFile)
  let (loaded, calls) ←
    invoke bin
        "print -rnP -- \"$PROMPT\"\ntitle_hook\n[[ ${precmd_functions[1]} == title_hook ]] || exit 9\n"
        "" "" "0" "0"
  expect
      (loaded.exitCode == 0 && loaded.stdout == "LEFTTITLE" && loaded.stderr.isEmpty &&
        calls == "TITLE\n")
      "zsh recipe preserves the left prompt and title hook and samples nothing when sourced"
  let attention :=
    Linger.Display.Status.summary [.wantsYou, .unknown, .exitedBad, .wantsYou, .working] ++ "\n"
  let unknown := Linger.Display.Status.summary [.unknown] ++ "\n"
  let shown := fun (text : String) =>
    String.ofList (text.toList.reverse.dropWhile (· == '\n')).reverse
  for (context, contextSetup) in
    [("outside", "unset LINGER_SESSION\n"), ("inside", "export LINGER_SESSION=work\n")] do
    for (label, text, err, rc, previous) in
      [("attention", attention, "hidden diagnostic\n", "0", "23"), ("empty", "", "", "0", "0"),
        ("failure", "", "status unavailable\n", "7", "42")] do
      let (out, calls) ← invoke bin (contextSetup ++ draw) text err rc previous
      expect
          (out.exitCode.toNat == previous.toNat?.getD 99 && out.stdout == shown text &&
            out.stderr.isEmpty &&
            calls == call ["ls", "--summary"])
          s!"zsh attention keeps shared bytes and status without calling the title hook ({label}, {context})"
  let (missing, calls) ← invoke emptyPath draw "" "" "0" "19"
  expect
      (missing.exitCode == 19 && missing.stdout.isEmpty && missing.stderr.isEmpty && calls.isEmpty)
      "zsh prompt is quiet and preserves status when linger is absent from PATH"
  let redraw := drawOnce ++ "export ZSH_PROMPT_STDOUT='" ++ unknown ++ "'\n" ++ draw
  let (out, calls) ← invoke bin redraw attention "" "0" "23"
  expect
      (out.exitCode == 23 && out.stdout == shown attention ++ shown unknown && out.stderr.isEmpty &&
        calls == call ["ls", "--summary"] ++ call ["ls", "--summary"])
      "zsh prompt samples again on each redraw without retaining old counts"
  -- Check the real command as well as the prompt, since prompt stderr suppression
  -- must not conceal a missing CLI route.
  let actual ← IO.Process.output { cmd := e.bin, args := #["ls", "--summary"], env }
  let (prompt, _) ← invoke ((System.FilePath.mk e.bin).parent.getD root) draw "" "" "0" "23"
  expect
      (actual.exitCode == 0 && actual.stdout.isEmpty && actual.stderr.isEmpty &&
        prompt.exitCode == 23 &&
        prompt.stdout.isEmpty &&
        prompt.stderr.isEmpty)
      "zsh prompt composes with real linger ls --summary in an empty session directory"

/-- tmux-resurrect prefixes the saved directory and full command with `:` and
escapes spaces in the directory field. The other fields are present only to
exercise the real eleven-field pane shape. -/
def paneLine (session window pane dir command : String) : String :=
  let savedDir := String.intercalate "\\ " (dir.splitOn " ")
  String.intercalate "\t"
      ["pane", session, window, "0", ":", pane, "title", ":" ++ savedDir, "1", "sh",
        ":" ++ command] ++
    "\n"

/-- Only this fixture's tmux can answer discovery. Restricted-PATH checks may
override PATH, so an empty private socket directory and unset TMUX also isolate
any accidentally reached system executable from the user's servers. -/
def tmuxFixtureEnv (root : System.FilePath) : IO (Array (String × Option String)) := do
  let bin := root / "tmux-bin"
  let sockets := root / "tmux-sockets"
  IO.FS.createDirAll bin
  IO.FS.createDirAll sockets
  IO.FS.writeFile (root / "tmux-calls") ""
  IO.FS.writeFile (bin / "tmux")
      (r#"#!/bin/sh
printf 'CALL\000' >> "$LINGER_TMUX_CALLS"
printf '%s\000' "$@" >> "$LINGER_TMUX_CALLS"
printf '\n' >> "$LINGER_TMUX_CALLS"
if [ "$#" -ne 3 ] || [ "$1" != show-options ] || [ "$2" != -gqv ] || [ "$3" != @resurrect-dir ]; then
    exit 97
fi
if [ "$LINGER_TMUX_WAIT" = 1 ]; then
"# ++
        -- past `hangMs`, so a command that waited for this query, rather than retiring it, would
        -- outlast its check's ceiling
        s!"    exec /bin/sleep {2 * hangMs / 1000}\n" ++
        r#"fi
printf '%s\n' "$LINGER_TMUX_DIRECTORY"
exit "$LINGER_TMUX_RC"
"#)
  Os.Shell.chmod (bin / "tmux").toString 0o700
  let path := (← IO.getEnv "PATH").getD "/usr/bin:/bin"
  return #[("PATH", some s!"{bin}:{path}"), ("TMUX", none), ("TMUX_TMPDIR", some sockets.toString),
      ("LINGER_TMUX_CALLS", some (root / "tmux-calls").toString),
      ("LINGER_TMUX_DIRECTORY", some ""), ("LINGER_TMUX_RC", some "0"), ("LINGER_TMUX_WAIT", none)]

/-- Run linger with the suite's state directory, the fixture's tmux (`tmuxFixtureEnv`), and
`home` and `data` as HOME and XDG_DATA_HOME, so it reads only the fixture's saves. -/
def runLinger (e : Env) (home data : String) (args : Array String)
    (extra : Array (String × Option String) := #[]) : IO (UInt32 × String × String) := do
  let isolated ← tmuxFixtureEnv (System.FilePath.mk e.dir)
  let out ←
    IO.Process.output
        { cmd := e.bin, args,
          env :=
            e.procEnv ++ isolated ++ #[("HOME", some home), ("XDG_DATA_HOME", some data)] ++ extra }
  return (out.exitCode, out.stdout, out.stderr)

/-- The names of the saved tmux panes `ls --porcelain` lists, as their `source` field marks
them, in its order. -/
def sourceNames (listing : String) : List String :=
  (listing.splitOn "\n\n").filterMap fun record =>
    let fields := records record
    if fields.lookup "source" == some Linger.Import.Resurrect.sourceName then fields.lookup "name"
    else none

/-- The recipes suite: native launch settings, the fish and zsh prompts and the saved tmux panes `ls`
lists. -/
def run : IO UInt32 :=
  Env.suite "recipes" fun e => do
    let e := { e with bin := (← IO.getEnv "LINGER_EXE").getD e.bin }
    let root := System.FilePath.mk e.dir
    let home := root / "home"
    let data := root / "data"
    IO.FS.createDirAll home
    IO.FS.createDirAll data
    configChecks
    fishPromptChecks e home.toString data.toString
    zshPromptChecks e home.toString data.toString
    -- Default path, escaped cwd, and ignored saved command.
    let defaultDir := root / "work space"
    let defaultSource := root / "default-source"
    let defaultSink := root / "default-sink"
    let resurrectDir := data / "tmux" / "resurrect"
    IO.FS.createDirAll defaultDir
    IO.FS.createDirAll resurrectDir
    IO.FS.writeFile defaultSource "DEFAULT-RAN\n"
    IO.FS.writeFile (resurrectDir / "last")
        (paneLine "desk" "1" "0" defaultDir.toString
            s!"tail -n 1 {defaultSource} >> {defaultSink}" ++
          "window\tdesk\t1\t:ignored\nstate\tdesk\t\n")
    let ls := fun (data : String) => runLinger e home.toString data #["ls", "--porcelain"]
    let resume := fun (data name : String) => runLinger e home.toString data #["resume", name]
    let (drc, dout, derr) ← ls data.toString
    let listed := sourceNames dout
    let (rrc, _, _) ← resume data.toString "desk-w1-p0"
    expect
        (drc == 0 && derr.isEmpty && listed == ["desk-w1-p0"] &&
          has dout s!"directory\t{defaultDir}" &&
          rrc == 0 &&
          (← savedIn' e.dir "desk-w1-p0" defaultDir))
        "ls lists the default XDG save's pane with its escaped cwd, and resume runs a shell there"
    IO.sleep 700 -- negative assertion: give a wrongly-started command time to run
    expect (!(← System.FilePath.pathExists defaultSink))
        "a resumed tmux pane never executes the default save's command"
    -- An explicitly empty XDG value has the documented shell `:-` semantics.
    let emptyXdgDir := root / "empty-xdg"
    let fallbackResurrectDir := home / ".local" / "share" / "tmux" / "resurrect"
    IO.FS.createDirAll emptyXdgDir
    IO.FS.createDirAll fallbackResurrectDir
    IO.FS.writeFile (fallbackResurrectDir / "last")
        (paneLine "emptyxdg" "3" "0" emptyXdgDir.toString "")
    let (xrc, xout, _) ← ls ""
    expect (xrc == 0 && sourceNames xout == ["emptyxdg-w3-p0"])
        "ls treats an empty XDG data home as unset"
    -- Once the legacy last save exists, it takes precedence over the XDG path.
    let legacyDir := root / "legacy"
    let legacyResurrectDir := home / ".tmux" / "resurrect"
    IO.FS.createDirAll legacyDir
    IO.FS.createDirAll legacyResurrectDir
    IO.FS.writeFile (legacyResurrectDir / "last") (paneLine "legacy" "2" "0" legacyDir.toString "")
    let (lrc, lout, _) ← ls data.toString
    expect (lrc == 0 && sourceNames lout == ["legacy-w2-p0"])
        "ls prefers the legacy last save when it exists"
    -- Empty commands, pipelines and other shell syntax all leave ordinary shells.
    let processDir := root / "processes"
    let processSource := root / "process-source"
    let processSink := root / "process-sink"
    let blockedSink := root / "blocked-sink"
    IO.FS.createDirAll processDir
    IO.FS.writeFile processSource "RESTORED-ONCE\n"
    IO.FS.writeFile (legacyResurrectDir / "last")
        (paneLine "dev" "1" "0" processDir.toString "" ++
          paneLine "dev" "1" "1" processDir.toString
            s!"tail -n 1 {processSource} | tee -a {processSink}" ++
          paneLine "dev" "1" "2" processDir.toString s!"printf BLOCKED > {blockedSink}")
    let names := ["dev-w1-p0", "dev-w1-p1", "dev-w1-p2"]
    let (prc, pout, _) ← ls data.toString
    let mut resumed := true
    for name in names do
      resumed :=
        resumed && (← resume data.toString name).1 == 0 && (← savedIn' e.dir name processDir)
    let (_, after, _) ← ls data.toString
    expect (prc == 0 && sourceNames pout == names && resumed && sourceNames after == [])
        "every pane of the save is listed under its projected name, and resumes as its own session"
    IO.sleep 700 -- negative assertion after the shells have started
    expect (!(← System.FilePath.pathExists processSink))
        "a resumed tmux pane ignores a saved pipeline"
    expect (!(← System.FilePath.pathExists blockedSink))
        "a resumed tmux pane ignores arbitrary saved shell syntax"
    -- A checkpoint-only identity is a record of its name: the pane is not listed, and a resume
    -- revives the checkpoint, never the pane or its command.
    let resumableSource := root / "resumable-source"
    let resumableSink := root / "resumable-sink"
    IO.FS.writeFile resumableSource "MUST-NOT-RUN\n"
    let owner ← e.spawn #["attach", "resumable-w1-p0"]
    owner.type "echo CHECKPOINTED\n"
    -- Capture only once the socket exists: an offline capture holds the session
    -- lock, and a daemon starting at that moment cannot claim the name.
    let echoed ←
      waitFor 5000 do
          if !(← System.FilePath.pathExists s!"{e.dir}/resumable-w1-p0.sock") then
            return false
          return has (← e.out #["capture", "resumable-w1-p0"]) "CHECKPOINTED"
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
    IO.FS.writeFile (legacyResurrectDir / "last")
        (paneLine "resumable" "1" "0" processDir.toString
          s!"tail -n 1 {resumableSource} >> {resumableSink}")
    let (src, sout, _) ← ls data.toString
    let resumableState ← e.status "resumable-w1-p0"
    let (rsrc, _, _) ← resume data.toString "resumable-w1-p0"
    IO.sleep 700
    expect
        (echoed && checkpointed && crashed && src == 0 && sourceNames sout == [] &&
          resumableState == .resumable &&
          rsrc == 0 &&
          has (← e.out #["capture", "resumable-w1-p0"]) "CHECKPOINTED" &&
          !(← System.FilePath.pathExists resumableSink))
        "a resumable checkpoint hides the pane of its name, and resume revives it, not the pane"
    -- A save linger cannot read lists no pane and says why, and the listing still answers.
    let longName := String.ofList (List.replicate 80 'a')
    let mut unreadable := true
    for (text, cause) in
      [(paneLine "bad/name" "1" "0" processDir.toString "", "not a valid linger name"),
        (paneLine longName "1" "0" processDir.toString "", "not a valid linger name"),
        ("pane\tshort\n", "malformed pane record"),
        ("window\tignored\nstate\tignored\t\n", "no pane records")] do
      IO.FS.writeFile (legacyResurrectDir / "last") text
      let (rc, out, err) ← ls data.toString
      let (krc, _, _) ← runLinger e home.toString data.toString #["kill", "bad_name-w1-p0"]
      unreadable := unreadable && rc == 0 && sourceNames out == [] && has err cause && krc == 127
    expect (unreadable && !(← System.FilePath.pathExists s!"{e.dir}/bad_name-w1-p0.end"))
        "a save with an invalid name, a malformed record or no pane lists none and says why"
    IO.FS.removeFile (legacyResurrectDir / "last")
    IO.FS.removeFile (fallbackResurrectDir / "last")
    IO.FS.removeFile (resurrectDir / "last")
    let (nrc, nout, nerr) ← ls data.toString
    expect (nrc == 0 && sourceNames nout == [] && nerr.isEmpty)
        "with no save, ls lists no pane and says nothing of one"
    e.killAll #["desk-w1-p0", "dev-w1-p0", "dev-w1-p1", "dev-w1-p2", "resumable-w1-p0"]

end Linger.Import.Suites.Recipes
