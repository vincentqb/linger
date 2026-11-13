module

public import Verify.Harness
import Linger.App.CoreCode.Entry
import Linger.Target.CoreCode.Remote
public import Linger.Target.CoreSpec
import Linger.Target.Suites.Remote

public section

/-! # Remote command lines through every login shell here

SSH hands the command line `Remote.command` builds to the login shell of the remote account,
which runs it as `<shell> -c <line>`. This suite does the same with each shell this host has,
with a fake `linger` that records the words it receives, and checks that the shell passes the
line's plain words on as they are (`Remote.Shell.Literal`), that the remote entry routes exactly
the verb and words the local linger sent, for words a shell would otherwise expand, quote,
escape or split, and that no shell runs a command a word holds. Two checks run the real binary:
it refuses an encoded command line that does not decode, and runs exactly the words of one that
does. -/

namespace Linger.Target.Suites.Shells

open Verify.Harness
open Linger.Target.Remote (encodeWord marker)

/-- The shells an account may log in with. Each one this host has is tried. -/
def candidates : List String :=
  ["sh", "bash", "zsh", "fish", "dash", "ksh", "mksh", "yash", "posh", "tcsh", "csh"]

/-- Words a shell would expand, quote, escape, split or run: quotes, the escape that fish reads
inside single quotes, substitutions, globs, operators, controls, option-like words and Unicode. -/
def hostile : List String :=
  ["", " ", "two words", "\\' ; id ; \\'", "'\\''", "a'b\"c", "back\\slash \\\\ \\", "$(id)",
    "`id`", "${HOME} $HOME ~ ~root", "* ? [ab] {a,b}", "!! !$ %self ^x #hash",
    "; & | > out < in ( ) &&", "line\nbreak", "tab\there", "\r", "\x01\x1b[31m\x7f", "--", "-n",
    "=x", "a=b", "ünïcödé ✓ 🎉 界"]

/-- The first file called `name` in a directory of `path`. -/
def onPath (path name : String) : IO (Option String) := do
  for dir in path.splitOn ":" do
    if !dir.isEmpty && (← System.FilePath.pathExists s!"{dir}/{name}") then
      return some s!"{dir}/{name}"
  return none

/-- Run `line` as `shell -c line` in an empty directory, with `bin` first on `PATH` and a home
of its own, and return the words the fake `linger` received, whether the fake `id` ran, and
the files the run left in its directory. -/
def through (root bin shell line : String) : IO (List String × Bool × Array IO.FS.DirEntry) := do
  let argv := s!"{root}/argv"
  let injected := s!"{root}/injected"
  let cwd := s!"{root}/cwd"
  for path in [argv, injected] do
    if ← System.FilePath.pathExists path then
      IO.FS.removeFile path
  if ← System.FilePath.pathExists cwd then
    IO.FS.removeDirAll cwd
  IO.FS.createDirAll cwd
  let path := s!"{bin}:{(← IO.getEnv "PATH").getD "/usr/bin:/bin"}"
  let _ ←
    IO.Process.output
        { cmd := shell, args := #["-c", line], cwd := some cwd,
          env :=
            #[("PATH", some path), ("HOME", some root), ("XDG_CONFIG_HOME", some root),
              ("ZDOTDIR", some root), ("ENV", none), ("BASH_ENV", none), ("LINGER_ARGV", some argv),
              ("LINGER_INJECTED", some injected)] }
  return (← Linger.Target.Suites.Remote.readArgs argv, ← System.FilePath.pathExists injected,
      ← System.FilePath.readDir cwd)

/-- The shells suite: the encoded command line of `send` through each shell this host has, then
the real binary on encoded command lines. -/
def run : IO UInt32 :=
  Env.suite "shells" fun e => do
    let root := s!"{e.dir}/shells"
    let bin := s!"{root}/bin"
    IO.FS.createDirAll bin
    IO.FS.writeFile s!"{bin}/linger" "#!/bin/sh\nprintf '%s\\000' \"$@\" > \"$LINGER_ARGV\"\n"
    IO.FS.writeFile s!"{bin}/id" "#!/bin/sh\n: > \"$LINGER_INJECTED\"\n"
    for name in ["linger", "id"] do
      Os.Shell.chmod s!"{bin}/{name}" 0o755
    let path := (← IO.getEnv "PATH").getD "/usr/bin:/bin"
    let shells ←
      candidates.filterMapM fun name => do
          return (← onPath path name).map (name, ·)
    let names := String.intercalate " " (shells.map (·.1))
    -- every word in one line, and each word in a line of its own: a shell that misreads one word
    -- can refuse a whole line, which would hide what it does with that word alone
    let verb := "send"
    let commands := ("work" :: hostile) :: hostile.map (["work", ·])
    let mut changed : List String := []
    let mut misrouted : List String := []
    let mut ran : List String := []
    for (name, shell) in shells do
      for words in commands do
        let line := Linger.Target.Remote.command verb words
        let (received, injected, left) ← through root bin shell line
        unless received == (line.splitOn " ").tail do
          changed := changed ++ [s!"{name}: {repr received}"]
        unless Linger.App.Entry.route received == Linger.App.Entry.route (verb :: words) do
          misrouted := misrouted ++ [s!"{name}: {repr received}"]
        if injected || !left.isEmpty then
          ran := ran ++ [s!"{name}: {repr words}"]
    expect (!shells.isEmpty && changed.isEmpty)
        s!"each shell here passes linger the plain words of an encoded command line as they are \
          ({names}){if changed.isEmpty then "" else s!": not {changed.take 3}"}"
    expect (!shells.isEmpty && misrouted.isEmpty)
        s!"the remote entry routes exactly the verb and words linger sent, through each shell here \
          ({names}){if misrouted.isEmpty then "" else s!": not {misrouted.take 3}"}"
    expect ran.isEmpty
        s!"no shell here runs a command or opens a file a word names \
          ({names}){if ran.isEmpty then "" else s!": {ran.take 3} did"}"
    -- the real binary: a word that does not decode refuses the whole line, which starts nothing
    let refused ←
      [["x6"], ["xff"], ["x6A"], ["61"],
              [encodeWord "start", encodeWord "made", encodeWord "/bin/sh", "xzz"]].mapM
          fun encoded => do
          return (← e.cli (marker :: encoded).toArray)
    let (madeRc, _, _) ← e.cli #["info", "made"]
    expect (refused.all (fun (rc, _, err) => rc == 2 && has err "malformed") && madeRc == 127)
        s!"linger refuses an encoded command line that does not decode with status 2 and starts \
          nothing ({refused.map (·.1)}, info {madeRc})"
    let written := s!"{root}/written"
    let word := "\\' ; id ; \\'"
    let line :=
      Linger.Target.Remote.command "start"
        ["made", "/bin/sh", "-c", "printf '%s' \"$1\" > \"$2\"", "sh", word, written]
    let (startRc, _, _) ← e.cli ((line.splitOn " ").tail.toArray)
    let readWritten : IO String := do
      return ((← (IO.FS.readFile written).toBaseIO).toOption).getD ""
    let wrote ← waitFor patienceMs (return (← readWritten) == word)
    expect (startRc == 0 && wrote)
        s!"linger runs exactly the words of an encoded command line \
          ({startRc}, {repr (← readWritten)})"
    e.killAll #["made"]

end Linger.Target.Suites.Shells
