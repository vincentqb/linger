module

public import Linger.Target.WorldSpec
import Linger.Target.CoreCode.Remote
import Os.WorldCode
import SoftwareChallenge.Commands

/-! # The checks of the remote commands' world claims

`Shell.Literal` says that every login shell passes `linger` and then plain words, one space
apart, to `linger` as exactly those words, and `Transport.Delivers` that a transport runs a
`linger` with exactly the plain words after its own, or nothing. Each claim takes the world's
reading as a parameter, which no Lean term computes: `split` and `deliver` name them, and the
checks observe them through every login shell this host has and through the transports that run
linger here, with no host to reach. No program module imports this one. -/

namespace Linger.Target.Checks

/-- The words the program a login shell runs for a command line receives, its own name first:
the observation `Shell.Literal` constrains. -/
opaque split : String → List String

/-- The words the program a transport runs receives when linger runs the transport's words and
then the given ones, its own name first, or `none` when it runs nothing: the observation
`Transport.Delivers` constrains. -/
opaque deliver : List String → List String → Option (List String)

/-- The shells an account may log in with. Each one this host has is tried, here and by the
shells suite. -/
public def shells : List String :=
  ["sh", "bash", "zsh", "fish", "dash", "ksh", "mksh", "yash", "posh", "tcsh", "csh"]

/-- Words a shell would expand, quote, escape, split or run: quotes, the escape fish reads inside
single quotes, substitutions, globs, operators, controls, option-like words and Unicode. -/
public def hostile : List String :=
  ["", " ", "two words", "\\' ; id ; \\'", "'\\''", "a'b\"c", "back\\slash \\\\ \\", "$(id)",
    "`id`", "${HOME} $HOME ~ ~root", "* ? [ab] {a,b}", "!! !$ %self ^x #hash",
    "; & | > out < in ( ) &&", "line\nbreak", "tab\there", "\r", "\x01\x1b[31m\x7f", "--", "-n",
    "=x", "a=b", "ünïcödé ✓ 🎉 界"]

-- Every login shell this host has passes `linger` the plain words of a command line as they
-- are: run as `<shell> -c <line>`, as SSH runs a remote account's command line, with a `linger`
-- of the check's own first on `PATH` that writes the words it receives to a file, each shell
-- passes on exactly the words of the lines `Remote.command` makes of words a shell would
-- otherwise expand, quote, escape, split or run, every word in one line and each in a line of
-- its own.
Check Remote.Shell.Literal split := do
  IO.FS.withTempDir fun dir => do
      let bin := dir / "bin"
      IO.FS.createDirAll bin
      IO.FS.writeFile (bin / "linger") "#!/bin/sh\nprintf '%s\\000' \"$@\" > \"$LINGER_ARGV\"\n"
      Os.Shell.chmod (bin / "linger").toString 0o755
      let path := (← IO.getEnv "PATH").getD "/usr/bin:/bin"
      let mut found : List String := []
      for name in shells do
        for place in path.splitOn ":" do
          if !place.isEmpty && (← System.FilePath.pathExists s!"{place}/{name}") then
            found := found ++ [s!"{place}/{name}"]
            break
      if found.isEmpty then
        throw (IO.userError "no login shell was found on PATH")
      let argv := (dir / "argv").toString
      for shell in found do
        for words in ("work" :: hostile) :: hostile.map (["work", ·]) do
          let line := Linger.Target.Remote.command "send" words
          if ← System.FilePath.pathExists argv then
            IO.FS.removeFile argv
          let _ ←
            IO.Process.output
                { cmd := shell, args := #["-c", line], cwd := some dir,
                  env :=
                    #[("PATH", some s!"{bin}:{path}"), ("HOME", some dir.toString),
                      ("XDG_CONFIG_HOME", some dir.toString), ("ZDOTDIR", some dir.toString),
                      ("ENV", none), ("BASH_ENV", none), ("LINGER_ARGV", some argv)] }
          let received ←
            if ← System.FilePath.pathExists argv then
              pure (((← IO.FS.readFile argv).splitOn "\x00").dropLast)
            else
              pure []
          unless received == (line.splitOn " ").tail do
            throw (IO.userError s!"{shell} passed linger {repr received} for the line {line}")

/-- Run each of `transport`'s commands, then `Remote.commandWords` for `send` with each set of words
a shell would otherwise expand, quote, escape, split or run, every word at once and each alone,
with a `linger` of the check's own first on `PATH` that writes the words it receives to a file,
and throw unless that `linger` received exactly those words each time. -/
def runsLinger (transport : Linger.Target.Remote.Transport) : IO Unit := do
  IO.FS.withTempDir fun dir => do
      let bin := dir / "bin"
      IO.FS.createDirAll bin
      IO.FS.writeFile (bin / "linger") "#!/bin/sh\nprintf '%s\\000' \"$@\" > \"$LINGER_ARGV\"\n"
      Os.Shell.chmod (bin / "linger").toString 0o755
      let path := (← IO.getEnv "PATH").getD "/usr/bin:/bin"
      let argv := (dir / "argv").toString
      for command in [transport.query, transport.attach] do
        let some program := command.head? | throw (IO.userError "a command names a program")
        for words in ("work" :: hostile) :: hostile.map (["work", ·]) do
          let sent := Linger.Target.Remote.commandWords "send" words
          if ← System.FilePath.pathExists argv then
            IO.FS.removeFile argv
          let _ ←
            IO.Process.output
                { cmd := program, args := (command.tail ++ sent).toArray, cwd := some dir,
                  env :=
                    #[("PATH", some s!"{bin}:{path}"), ("HOME", some dir.toString), ("ENV", none),
                      ("BASH_ENV", none), ("LINGER_ARGV", some argv)] }
          let received ←
            if ← System.FilePath.pathExists argv then
              pure (some ("linger" :: ((← IO.FS.readFile argv).splitOn "\x00").dropLast))
            else
              pure none
          unless received == some sent do
            throw (IO.userError s!"{command} ran linger with {repr received} for {repr sent}")

-- `env`, a command that runs its words here, passes `linger` the plain words after it as they
-- are, as `docker exec` and `kubectl exec` pass theirs: the words `Remote.commandWords` spells
-- for words a shell would otherwise expand, quote, escape, split or run.
Check Remote.Transport.Delivers deliver { query := ["env"], attach := ["env"] } :=
  runsLinger { query := ["env"], attach := ["env"] }

-- Commands shaped as ssh's are, which join the words after them with spaces and hand the line to
-- a login shell, as sshd hands it to the remote account's: `sh -c 'exec sh -c "$*"'` passes
-- `linger` the same words, for a query and for an attach.
Check
  Remote.Transport.Delivers deliver
    { query := ["sh", "-c", "exec sh -c \"$*\"", "ssh"],
      attach := ["sh", "-c", "exec sh -c \"$*\"", "ssh-t"] } :=
  runsLinger
    { query := ["sh", "-c", "exec sh -c \"$*\"", "ssh"],
      attach := ["sh", "-c", "exec sh -c \"$*\"", "ssh-t"] }

end Linger.Target.Checks
