module

import Os.WorldCode
import Linger.Os.CoreCode.Env
import Linger.Session.WorldCode.Paths
import Linger.Target.CoreCode.Remote
import Terminal.CoreCode.Render
import Linger.Display.CoreCode.Listing
import Linger.Display.CoreCode.View
import Linger.Os.CoreCode.Answer
public import Linger.Os.CoreSpec
public import Linger.App.WorldCode.Api
import Linger.App.CoreCode.Api
import Linger.App.CoreCode.Commands
import Linger.App.CoreCode.Fields
import Linger.Session.CoreCode.Handoff
import Terminal.CoreCode.Mediation
import Linger.Display.CoreCode.Status

public section

/-! # Linger.App.Shell — the command line, a renderer of the Lean API

A session command line is a request: `Api.parse` reads its words as the typed request of its
command's operation, `Api.perform` performs it, and this module renders the reply: what the
command says as it goes to standard error, what it shows to standard output, and what it found as
the exit status (`Api.answer`). Words no request reads are a usage error. The command line passes
the API the namespace the environment names (`Paths.dirs`), this executable, the
tmux-resurrect source and the remote hosts of the remotes file, whose transports it runs on this
process's own standard streams. `main` routes terminal selection and import before entering this
session backend. Bare invocation reaches help. `__daemon` and its kin are the internal re-exec
targets of the detached spawn, and `__dirs` names the namespace they work in.
-/

namespace Linger.App.Shell

open Linger.Session.Shell
open Os.Shell
open Linger.Os (Answer)

/-- One line per command, from the command table, printed by help and bare invocation, or to
stderr for a word that names no command. -/
private def usage : String := Linger.App.Commands.helpText

/-- What `linger --help` prints after the commands: the program's two options, the legend's two
blocks, a row's attention and its state, which marks titles and `ls --summary` count, and the exit
statuses every command shares: a program's and a signal's, then one line per answer of linger's
own (`Answer.legend`). -/
private def helpFooter : String :=
  let glyphs :=
    String.intercalate " "
      (Linger.Display.Status.counted.map fun a => String.singleton (Linger.Display.Status.mark a))
  String.intercalate "\n"
    (["",
        s!"{Linger.App.Commands.helpOption} shows this; {Linger.App.Commands.versionOption} \
          prints the version and state paths",
        ""] ++
      Linger.Display.Status.legend.map
        (fun line => if line == "Attention" || line == "State" then line else "  " ++ line) ++
      [s!"Titles and ls --summary count {glyphs}", "",
        "Exit statuses: the program's own, when the command waits for it to end; 128+N when",
        "signal N stops the command, or the session it attaches to or waits for; otherwise"] ++
      Answer.legend.map ("  " ++ ·))

/-- The remotes file's hosts, each with its transport (`Remote.config`): none when
`Env.remotesFile` names no file, as for an unset or empty HOME, or the file does not exist. A line
with no one meaning refuses the whole file, before any command runs. -/
private def remoteConfig : IO (List (String × Linger.Target.Remote.Transport)) := do
  let lines ←
    match Linger.Os.Env.remotesFile (← IO.getEnv "HOME") with
    | none =>
      pure []
    | some path =>
      if ← System.FilePath.pathExists path then
        pure ((← IO.FS.readFile path).splitOn "\n")
      else
        pure []
  match Linger.Target.Remote.config lines with
  | .ok config =>
    return config
  | .error e =>
    throw (IO.userError e)

/-- Run one transport command line on this process's standard streams and give its status, the
remote command's; an attach's hands the terminal back after it. -/
private def runRemote (interactive : Bool) : List String → IO UInt32
  | [] => pure Answer.failed.code
  | cmd :: argv => do
    let child ← IO.Process.spawn { cmd, args := argv.toArray, stdin := .inherit }
    try
      child.wait
    finally
      if interactive then
        writeAll stdoutFd (ByteArray.mk Terminal.Render.leaveAnsi.toArray)

/-- The width a human listing fits: the terminal's columns when standard output is one with a
size, else none. -/
private def humanWidth : IO (Option Nat) := do
  unless ← (← IO.getStdout).isTty do
    return none
  try
    let (cols, _) ← winsizeGet stdoutFd
    return if cols == 0 then none else some cols.toNat
  catch _ =>
    return none

/-- Print listing rows: as `k<TAB>v` records each followed by a blank line (`porcelain`), or as
the terminal listing. -/
private def printRows (porcelain : Bool) (rows : List (List (String × String))) : IO Unit := do
  if porcelain then
    for info in rows do
      for (k, v) in info do
        IO.println s!"{k}\t{v}"
      IO.println ""
  else
    -- The selector consumes these same row pieces. Only the status badge has
    -- a palette style, and only where `Env.withColor` allows color. What asks for
    -- someone comes first, as in the selector (`View.sort`). A terminal's rows fit its width, and
    -- a directory under the account's home shows as `~`. A host that did not answer has no
    -- session name, so its row shows `@host`. A row is built only of the fields whose kind and
    -- owner the field table gives (`Fields.table`), every field a row reads among them.
    let withColor :=
      Linger.Os.Env.withColor (← (← IO.getStdout).isTty) (← IO.getEnv "NO_COLOR")
        (← IO.getEnv "TERM")
    let named :=
      rows.map fun info =>
        (match info.lookup "name", info.lookup "host" with
            | none, some host => ("name", "@" ++ host) :: info
            | _, _ => info).filter
          fun kv => (Linger.App.Fields.table.map Linger.App.Fields.Field.key).contains kv.1
    let ordered := Linger.Display.View.sort Linger.Display.Listing.statusOf named
    let width ← humanWidth
    let home ← accountHome
    writeAll stdoutFd
        (ByteArray.mk
          (Linger.Display.Listing.terminalListing withColor width
              (ordered.map (Linger.Display.Listing.atHome home))).toArray)

/-- Write what a request shows to standard output: a capture's bytes; a listing's records, a
named listing's only when there are any; the attention counts, on a line, when any session needs
attention; a save as it is; and a line for each session an upgrade carried over. -/
private def render (request : Linger.App.Api.Request) : Linger.App.Api.Shown → IO Unit
  | .nothing => pure ()
  | .bytes bytes => writeAll stdoutFd bytes
  | .rows porcelain rows =>
    match request with
    | .list (.named ..) =>
      unless rows.isEmpty do
        printRows porcelain rows
    | _ => printRows porcelain rows
  | .text text =>
    match request with
    | .list .summary =>
      unless text.isEmpty do
        IO.println text
    | _ => IO.print text
  | .upgraded names => names.forM fun name => IO.println s!"upgraded {name}"

/-- `--version`: print `linger` and `Mediation.versionNumber`, which sessions also see as
`TERM_PROGRAM_VERSION`, then the socket and state directories this environment resolves. -/
private def cmdVersion : IO Answer := do
  IO.println s!"linger {Terminal.Mediation.versionNumber}"
  IO.println s!"sockets: {← Paths.socketDir}"
  IO.println s!"state:   {← Paths.stateDir}"
  return .done

/-- Run one session command and give its answer, whose code is its exit status: the program's two
options, `--help` and `--version`, stand alone; any other command line is a request
(`Api.parse`), which `Api.perform` performs in the namespace the environment names, rendering
what it says, what it shows and, as the answer, what it found (`Api.answer`), or a usage error,
quoting its command's usage line (`Commands.usageLine`) when its first word names one and the
command table otherwise. `main` routes interactive selection and tmux interchange elsewhere;
`__daemon` and its kin run a session's daemon in this process, in the namespace a leading
`__dirs` names. -/
def main (source : Linger.App.Api.Source) (args : List String) : IO Answer := do
  match args with
  | "__dirs" :: sockets :: state :: rest =>
    Paths.withDirs { sockets, state } (main source rest)
  | "__daemon" :: id :: name :: cwd :: cmd =>
    Linger.App.Api.serveDaemon id name cwd cmd
    return .done
  | "__start" :: report :: id :: name :: cwd :: argv =>
    Linger.App.Api.serveStart report id name cwd argv
    return .done
  | ["__resume", report, id, name, cwd] =>
    Linger.App.Api.serveResume report id name cwd
    return .done
  | ["__upgraded", id, path, pid] =>
    -- an older image names the session's ID too: a name, which was every session's ID
    match pid.toNat? with
    | some pid =>
      Linger.App.Api.serveUpgraded id path (UInt32.ofNat pid)
      return .done
    | none =>
      return .usage
  | ["__handoff-formats"] =>
    IO.println Linger.Session.Upgrade.formatsText
    return .done
  | args =>
    if args.isEmpty || args == [Linger.App.Commands.helpOption] then
      IO.println (usage ++ "\n" ++ helpFooter)
      return .done
    if args == [Linger.App.Commands.versionOption] then
      return ← cmdVersion
    match Linger.App.Api.parse args with
    | some request =>
      let env : Linger.App.Api.Env :=
        { dirs := ← Paths.dirs, exe := (← IO.appPath).toString, source,
          remote := some { config := remoteConfig, run := runRemote },
          say := fun said => IO.eprint said.render }
      let reply ← Linger.App.Api.perform env request
      render request reply.shown
      return Linger.App.Api.answer reply.found
    | none =>
      match Linger.App.Commands.lookup (args.headD "") with
      | some command =>
        if let some why := Linger.App.Api.complaint command.op args.tail then
          IO.eprintln s!"linger: {why}"
        IO.eprintln (Linger.App.Commands.usageLine command)
      | none =>
        IO.eprintln usage
      return .usage

end Linger.App.Shell
