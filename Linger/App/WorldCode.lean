module

import Os.WorldCode
import Linger.Os.CoreCode.Env
import Linger.Session.WorldCode.Paths
import Linger.Session.WorldCode.Names
import Linger.Session.WorldCode.Daemon
import Linger.Session.WorldCode.Client
import Linger.Session.WorldCode.Inventory
import Linger.Target.CoreCode.Remote
import Linger.Target.CoreCode.Name
import Terminal.CoreCode.Render
import Linger.Display.CoreCode.Listing
import Linger.Display.CoreCode.View
import Linger.Os.CoreCode.Answer
import Linger.App.CoreCode.Capture
public import Linger.Os.CoreSpec
public import Linger.Session.CoreSpec
import Linger.App.CoreCode.Recovery
import Linger.App.CoreCode.Commands
import Linger.App.CoreCode.Wait
import Os.WorldCode.Command
import Linger.Session.WorldCode.Resume
import Linger.Session.WorldCode.Record
import Linger.Session.CoreCode.Handoff
import Terminal.CoreCode.Mediation
import Std.Async.Signal
import Linger.Display.CoreCode.Status
import Linger.Display.CoreCode.Alert

public section

/-! # Linger.App.Shell — session argv dispatch

Verb surface: attach creates if needed; read-only attach and capture also
read offline checkpoints. Every session verb accepts an exact name or name@host.
`main` routes terminal selection and import before
entering this session backend. Bare invocation reaches help; `ls` prints an
overview and exits. `__daemon` is the internal re-exec target of the detached
spawn.
-/

namespace Linger.App.Shell

open Linger.Session.Shell
open Linger.Session.Shell.Inventory
open Os.Shell
open Linger.Session.Wire (Msg)
open Linger.Os (Answer)

/-- A source of saved sessions linger reads and never writes, a tmux-resurrect save, as `main`
supplies it: the session library imports no reader of one. `rows` lists its panes no record of
`Records` names, `row` the pane of a name no record names, `adopt` writes a pane's checkpoint
where no record is, answering whether a record named the pane by then, so that nothing was
written, `dismiss` writes the end record a kill leaves for a pane no record names, answering
whether it did, and `writeSave` writes the sessions as a save to standard output. -/
structure Source where
  /-- The listing rows of the panes no record names. -/
  rows : Linger.Session.Records → IO (List (List (String × String)))
  /-- The listing row of the pane of a name no record names. -/
  row : String → IO (Option (List (String × String)))
  /-- Write the pane's checkpoint where no record is: whether a record named it by then. -/
  adopt : String → IO Bool
  /-- Write the end record a kill leaves for a pane no record names: whether it did. -/
  dismiss : String → IO Bool
  /-- Write the local sessions' names and directories as a save to standard output. -/
  writeSave : IO Unit

/-- No source: no pane is listed, adopted or dismissed, and an export writes nothing. -/
def Source.none : Source :=
  { rows := fun _ => pure [], row := fun _ => pure Option.none, adopt := fun _ => pure false,
    dismiss := fun _ => pure false, writeSave := pure () }

/-- One line per command, from the command table, printed by help and bare invocation, or to
stderr when `overview` cannot parse the arguments as listing options. -/
private def usage : String := Linger.App.Commands.helpText

/-- A command's usage error, its row of the command table (`Commands.usageLine`), and the
answer `usage`. -/
private def usageError (word : String) : IO Answer := do
  if let some command := Linger.App.Commands.lookup word then
    IO.eprintln (Linger.App.Commands.usageLine command)
  return .usage

/-- What `linger --help` prints after the commands: the program's two options, the eight statuses
a session can show, which of them titles and `ls --summary` count, and the exit statuses every
command shares: a program's and a signal's, then one line per answer of linger's own
(`Answer.legend`). -/
private def helpFooter : String :=
  let glyphs :=
    String.intercalate " "
      (Linger.Display.Status.attention.map fun status =>
        String.singleton (Linger.Display.Status.icon status))
  String.intercalate "\n"
    (["",
        s!"{Linger.App.Commands.helpOption} shows this; {Linger.App.Commands.versionOption} \
          prints the version and state paths",
        "", "Statuses"] ++
      Linger.Display.Status.legend.map ("  " ++ ·) ++
      [s!"Titles and ls --summary count {glyphs}", "",
        "Exit statuses: the program's own, when the command waits for it to end; 128+N when",
        "signal N stops the command, or the session it attaches to or waits for; otherwise"] ++
      Answer.legend.map ("  " ++ ·))

/-- Start `name`'s daemon detached, running this executable as `__daemon name cwd cmd...`
with its output appended to `Paths.logPath`. Returns the daemon's pid once that program
has started, without waiting for it to listen; `connectUpsert` waits for the socket. -/
private def spawnDaemon (s : Names.Ref) (cwd : String) (cmd : List String) : IO UInt32 := do
  let self ← IO.appPath
  let log ← Paths.logPath s.id
  spawnDetached self.toString (⟨["__daemon", s.id, s.name, cwd] ++ cmd⟩ : Array String) log

/-- How long `connectUpsert` waits for the socket whether or not the daemon it spawned
still lives: a concurrent start whose daemon lost the name to another one still loading
connects within it. -/
private abbrev socketWaitFloorMs : Nat := 3000

/-- The longest `connectUpsert` waits for the socket of a daemon it spawned. -/
private abbrev socketWaitCapMs : Nat := 30000

/-- The name's end record on disk, as a daemon keeps it. -/
private def recordFile (name : String) : Daemon.RecordFile :=
  { load := Record.load name, save := Record.save name, restore := Record.restore name }

/-- A command named a session that does not exist: say so and answer `notFound`, as a shell
does for a command it cannot find. -/
private def noSession (name : String) : IO Answer := do
  IO.eprintln s!"linger: no session '{name}'"
  return .notFound

/-- Why nothing starts over the name's checkpoint when its bytes do not decode
(`Recovery.decide`): it is damaged, it stays as it is, and `linger kill` discards it. -/
private def undecodedText (s : Names.Ref) : IO String := do
  return s!"its checkpoint {← Paths.ckptPath s.id} is damaged and does not decode, so it stays \
    as it is; linger kill {s.name} discards it"

/-- Why a command that found no live session starts nothing, as `Recovery.decide` answered: no
session holds the name, or its checkpoint does not decode. -/
private def refusalText (s : Names.Ref) (answer : Answer) : IO String := do
  if answer == .notFound then
    return s!"no session '{s.name}'"
  return s!"session '{s.name}': {← undecodedText s}"

/-- Say why a command that found no live session starts nothing, as `Recovery.decide`
answered, and give that answer: no session holds the name, or its checkpoint does not decode. -/
private def refused (s : Names.Ref) (answer : Answer) : IO Answer := do
  IO.eprintln s!"linger: {← refusalText s answer}"
  return answer

/-- What the daemon of `name` starts from, as `Recovery.decide` says from the name's checkpoint
file, `create` when a new session may start: a refusal is the status its command answers, and
why. -/
private def recoverFor (s : Names.Ref) (create : Bool) : IO Daemon.Recovered := do
  match Linger.App.Recovery.decide create (← Resume.readCkpt s.id) with
  | .fresh =>
    return .ok none
  | .resume ck =>
    return .ok (some (ck.vt, ck.cwd, ck.fields))
  | .refuse answer =>
    let why ←
      if answer == .notFound then
        pure s!"no session '{s.name}'"
      else
        undecodedText s
    return .error (answer.code.toUInt8, why)

/-- Write what the daemon did to the report `start` named, whole, through a temporary sibling. -/
private def writeReport (path : String) (report : Linger.Session.Start.Report) : IO Unit := do
  IO.FS.writeBinFile s!"{path}.tmp" (ByteArray.mk report.encode.toArray)
  IO.FS.rename s!"{path}.tmp" path

/-- The ticket of the request whose report is at `report`. The command makes it before it begins
the daemon; whoever removes it, the daemon at its commit point or the command once its wait ran
out, decides whether the program runs. -/
private def ticketPath (report : String) : String := s!"{report}.ticket"

/-- Take the ticket of the request at `report`: `true` when this process removed it, and `false`
when it could not, the other side having removed it first, since of two unlinks of one name only
one succeeds. -/
private def takeTicket (report : String) : IO Bool := do
  try
    IO.FS.removeFile (ticketPath report)
    return true
  catch _ =>
    return false

/-- The daemon's side of the request at `report`: it takes the ticket at most once, and writes the
report only holding it, so a command that took the ticket gets no report after its answer. -/
private def daemonRequest (report : String) : IO Daemon.Request := do
  let took ← IO.mkRef (none : Option Bool)
  let take : IO Bool := do
    if let some held← took.get then
      return held
    let held ← takeTicket report
    took.set (some held)
    return held
  let tell (r : Linger.Session.Start.Report) : IO Unit := do
    if ← take then
      writeReport report r
  return { take, tell }

/-- The daemon `start` began. It reports what it did once, and a failure before that is reported
too: as `running` when a live session took the name first, else as linger's own failure. -/
private def serveStart (report id name cwd : String) (argv : List String) : IO Unit := do
  let req ← daemonRequest report
  let told ← IO.mkRef false
  let tell (r : Linger.Session.Start.Report) : IO Unit := do
    told.set true
    req.tell r
  try
    Daemon.serve id name cwd argv (← Resume.saver id) (Resume.dropCkpt id) (recoverFor { name, id })
        (recordFile id) (some { req with tell })
  catch err =>
    unless ← told.get do
      match ← Client.connect id with
      | some fd =>
        close fd
        tell .running
      | none =>
        tell (.failed Answer.failed.code.toUInt8 err.toString.toUTF8.toList)
    throw err

/-- How long `start` waits for its daemon's report. -/
private abbrev startWaitMs : Nat := 30000

/-- The report `start` named, once its daemon has written it; reading it removes it. -/
private def takeReport (path : String) : IO (Option (Option Linger.Session.Start.Report)) := do
  if !(← System.FilePath.pathExists path) then
    return none
  let bytes ← IO.FS.readBinFile path
  IO.FS.removeFile path
  return some (Linger.Session.Start.Report.decode bytes.toList)

/-- How a command's wait for the daemon it began ended. -/
private inductive Waited where
  /-- The daemon took the ticket and reported: what, or `none` for a report that is no report. -/
  | told (report : Option Linger.Session.Start.Report)
  /-- The command took the ticket, so the daemon starts nothing: once the wait ran out
  (`timedOut`), or once the daemon ended before its commit point. -/
  | took (timedOut : Bool)
  /-- The daemon took the ticket and ended without reporting. -/
  | silent

/-- The report a daemon this command began writes, looked for every 10 ms while that daemon lives.
Once `startWaitMs` has passed, the command takes the request's ticket, and the daemon then starts
nothing; when the daemon took it first, the command waits on while the daemon lives, since what
it does after its commit point never waits: one of the waits with no deadline (`pause`). A daemon
that ended gets one last look, since it may have reported just before. -/
private def awaitReport (pid : UInt32) (report : String) : IO Waited := do
  let deadline := (← monotonicMs) + startWaitMs
  let mut bounded := true
  repeat
    if let some told← takeReport report then
      return .told told
    if !(← alive pid) then
      if let some told← takeReport report then
        return .told told
      return if ← takeTicket report then .took false else .silent
    if bounded then
      unless ← nap deadline 10 do
        if ← takeTicket report then
          return .took true
        bounded := false
    else
      pause 10
  return .silent

/-- Make the ticket of the request at `report`, then begin its daemon with `args`; a daemon that
could not begin leaves no ticket. -/
private def beginRequest (report log : String) (args : List String) : IO UInt32 := do
  IO.FS.withFile (ticketPath report) .writeNew fun _ => pure ()
  try
    spawnDetached (← IO.appPath).toString ⟨args⟩ log
  catch err =>
    discard <| takeTicket report
    throw err

/-- What `start` says when a session holds the name, `notDone`: that it is running; for a saved
one whose checkpoint decodes, whether its program ended; and for one whose checkpoint does not,
which nothing resumes (`Recovery.decide`), that it is damaged and kept, and that `linger kill`
discards it. -/
private def startRefused (s : Names.Ref) (saved : Bool) : IO Answer := do
  unless saved do
    IO.eprintln s!"linger: session '{s.name}' is running"
    return .notDone
  if let .refuse .notDone := Linger.App.Recovery.decide false (← Resume.readCkpt s.id) then
    return ← refused s .notDone
  let record := (← (Record.load s.id).toBaseIO).toOption.join
  match record.bind Linger.Session.Record.decode with
  | some (.ended outcome) =>
    IO.eprintln
        s!"linger: session '{s.name}' ended ({(Client.Ending.outcome outcome).describe}); \
        attach to see it, which discards it, or kill it to discard it"
  | _ =>
    IO.eprintln
        s!"linger: session '{s.name}' is saved; attach to resume it, or kill it to discard it"
  return .notDone

/-- `start`'s answer once its wait ended: `done` exactly when the program runs (`Start.answer`);
`notDone`, saying which session holds the name, for a refusal (`startRefused`); for a program that
could not start, the answer whose status a shell or `env` reports; and `timedOut` when the daemon
did not answer in time, so it starts nothing. A report that is no report, or a daemon that ended
without one, is linger's own failure. -/
private def startStatus (s : Names.Ref) (log : String) (waited : Waited) : IO Answer := do
  match Linger.Session.Start.answer (waited matches .took _) (waited matches .told (some .started)),
    waited with
  | .started, _ =>
    return .done
  | .notStarted, .told (some .running) =>
    startRefused s false
  | .notStarted, .told (some .saved) =>
    startRefused s true
  | .notStarted, .told (some (.failed status why)) =>
    do
      IO.eprintln s!"linger: session '{s.name}' did not start: {Client.replyText "no reason" why}"
      return Answer.ofCode status.toUInt32
  | .notStarted, .told none =>
    do
      IO.eprintln s!"linger: session '{s.name}' did not start: the daemon's report is unreadable"
      return .failed
  | .notStarted, .took true =>
    do
      IO.eprintln
          s!"linger: session '{s.name}' did not start: its daemon did not answer within \
        {startWaitMs / 1000} s, so it starts nothing (see {log})"
      return .timedOut
  | .notStarted, .took false =>
    do
      IO.eprintln s!"linger: session '{s.name}' did not start: its daemon ended first (see {log})"
      return .failed
  | .notStarted, _ =>
    do
      IO.eprintln
          s!"linger: session '{s.name}': its daemon ended without saying whether it started \
        (see {log})"
      return .failed

/-- `start`: run `argv` exactly, with no shell, in a new session named `name`, in this directory
and with this environment, and return once the program runs. A live or saved session, an ended
one included, that holds the name is refused, saying which, and never resumed (`Start.plan`);
the daemon decides again holding the name. A program that cannot start answers as a shell or
`env` reports it, `failed` for its directory, `notFound` when not found and `cannotRun` when not
runnable, and leaves no session, checkpoint or record behind. A daemon that does not answer
within `startWaitMs` starts nothing, and `start` says so, `timedOut`. -/
private def cmdStart (s : Names.Ref) (argv : List String) : IO Answer := do
  let live ←
    match ← Client.connect s.id with
    | some fd =>
      do
        close fd
        pure true
    | none =>
      pure false
  let saved ← System.FilePath.pathExists (← Paths.ckptPath s.id)
  match Linger.Session.Start.plan live saved with
  | .running =>
    startRefused s false
  | .saved =>
    startRefused s true
  | .take =>
    let report ← Paths.startReportPath s.id s!"{← getpid}-{← IO.rand 0 0xFFFFFFFF}"
    let cwd := (← IO.Process.getCurrentDir).toString
    let log ← Paths.logPath s.id
    let pid ← beginRequest report log (["__start", report, s.id, s.name, cwd] ++ argv)
    startStatus s log (← awaitReport pid report)

/-- The daemon `resume` began: `serveStart`'s, running only a saved session's program again. -/
private def serveResume (report id name cwd : String) : IO Unit := do
  let req ← daemonRequest report
  let told ← IO.mkRef false
  let tell (r : Linger.Session.Start.Report) : IO Unit := do
    told.set true
    req.tell r
  try
    Daemon.serve id name cwd [] (← Resume.saver id) (Resume.dropCkpt id) (recoverFor { name, id })
        (recordFile id) (some { req with tell }) (resume := true)
  catch err =>
    unless ← told.get do
      match ← Client.connect id with
      | some fd =>
        close fd
        tell .running
      | none =>
        tell (.failed Answer.failed.code.toUInt8 err.toString.toUTF8.toList)
    throw err

/-- A resumed session whose directory is gone runs in `$HOME`: say where it runs and where it was
saved, from its info fields start_dir and saved_dir. -/
private def sayMoved (s : Names.Ref) : IO Unit := do
  if let some (.ok info)← queryInfo s.id then
    if let some saved := info.lookup "saved_dir" then
      let ran := (info.lookup "start_dir").getD "$HOME"
      IO.eprintln s!"linger: session '{s.name}' resumed in {ran}: its directory {saved} is gone"

/-- `resume`'s answer once its wait ended: `done` exactly when the program runs (`Start.answer`),
again, saying where when its directory is gone, or in a live session that already runs it;
`notFound`, as for a session that does not exist, when no session holds the name; for a saved
session that cannot be read or a program that cannot start, `notDone` or the answer whose status
a shell or `env` reports; and `timedOut` when the daemon did not answer in time, so it starts
nothing. A report that is no report, or a daemon that ended without one, is linger's own
failure. -/
private def resumeStatus (s : Names.Ref) (log : String) (waited : Waited) : IO Answer := do
  let runs := waited matches .told (some .started) || waited matches .told (some .running)
  match Linger.Session.Start.answer (waited matches .took _) runs, waited with
  | .started, .told (some .started) =>
    do
      sayMoved s
      return .done
  | .started, _ =>
    return .done
  | .notStarted, .told (some (.failed status why)) =>
    if Answer.ofCode status.toUInt32 == .notFound then
      noSession s.name
    else
      do
        IO.eprintln
            s!"linger: session '{s.name}' did not resume: {Client.replyText "no reason" why}"
        return Answer.ofCode status.toUInt32
  | .notStarted, .told _ =>
    do
      IO.eprintln s!"linger: session '{s.name}' did not resume: the daemon's report is unreadable"
      return .failed
  | .notStarted, .took true =>
    do
      IO.eprintln
          s!"linger: session '{s.name}' did not resume: its daemon did not answer within \
        {startWaitMs / 1000} s, so it starts nothing (see {log})"
      return .timedOut
  | .notStarted, .took false =>
    do
      IO.eprintln s!"linger: session '{s.name}' did not resume: its daemon ended first (see {log})"
      return .failed
  | .notStarted, .silent =>
    do
      IO.eprintln
          s!"linger: session '{s.name}': its daemon ended without saying whether it resumed \
        (see {log})"
      return .failed

/-- Before an attach or a resume of `name` with no daemon: write the latest tmux-resurrect save's
pane of that name as its checkpoint when no record names it (`Source.adopt`), so the
command resumes it as a saved session; a name a record came to name meanwhile keeps it, and the
command goes on with the session that is there, saying so. -/
private def adoptPane (source : Source) (name : String) : IO Unit := do
  if ← source.adopt name then
    IO.eprintln s!"linger: session '{name}' exists; using it, not the saved tmux pane"

/-- `resume`: run a saved session's program again, an ended session's included, in its saved
directory and on its last screen, without attaching, and return once it runs. A live session is
left as it is, a name no record names resumes the latest tmux-resurrect save's pane of that name
(`adoptPane`), and any other name no session holds starts nothing (`Start.resumePlan`); the
daemon decides again holding the name. A daemon that does not answer within `startWaitMs` starts nothing, and
`resume` says so, `timedOut`. -/
private def cmdResume (source : Source) (s : Names.Ref) : IO Answer := do
  adoptPane source s.name
  let live ←
    match ← Client.connect s.id with
    | some fd =>
      do
        close fd
        pure true
    | none =>
      pure false
  let saved ← System.FilePath.pathExists (← Paths.ckptPath s.id)
  match Linger.Session.Start.resumePlan live saved with
  | .running =>
    return .done
  | .missing =>
    noSession s.name
  | .resume =>
    let report ← Paths.startReportPath s.id s!"{← getpid}-{← IO.rand 0 0xFFFFFFFF}"
    let cwd := (← IO.Process.getCurrentDir).toString
    let log ← Paths.logPath s.id
    let pid ← beginRequest report log ["__resume", report, s.id, s.name, cwd]
    resumeStatus s log (← awaitReport pid report)

/-- The answer of an attach whose daemon ended without listening, when the name's checkpoint
does not decode, so that daemon started nothing over it (`Recovery.decide`). `none` when there
is no checkpoint, it decodes or it cannot be read, which the daemon's log tells. -/
private def undecoded (name : String) : IO (Option Answer) := do
  let file ←
    try
      Resume.readCkpt name
    catch _ =>
      pure none
  match Linger.App.Recovery.decide true file with
  | .refuse answer =>
    return some answer
  | _ =>
    return none

/-- Connect, spawning the daemon first if needed (attach-is-upsert). Without a socket it
gives up no sooner than `socketWaitFloorMs`; after that it keeps waiting only while the
spawned daemon lives, never past `socketWaitCapMs`. A daemon that ends without listening over
a checkpoint that does not decode is answered at once, with the refusal (`undecoded`). -/
private def connectUpsert (s : Names.Ref) (cmd : List String) : IO (Except Answer UInt32) := do
  match ← Client.connect s.id with
  | some fd =>
    return .ok fd
  | none =>
    -- Recovery, including its saved cwd, happens only after the daemon owns
    -- both resources. A parent-side load would race another runtime namespace.
    let cwd := (← IO.Process.getCurrentDir).toString
    let pid ← spawnDaemon s cwd cmd
    let start ← monotonicMs
    let mut fdOpt : Option UInt32 := none
    let mut looked := false
    while fdOpt.isNone && ((← monotonicMs) < start + socketWaitFloorMs || (← alive pid)) do
      unless ← nap (start + socketWaitCapMs) 30 do
        break
      fdOpt ← Client.connect s.id
      if fdOpt.isNone && !looked && !(← alive pid) then
        looked := true
        if let some answer← undecoded s.id then
          return .error answer
    match fdOpt with
    | some fd =>
      sayMoved s
      return .ok fd
    | none =>
      let log ← Paths.logPath s.id
      throw (IO.userError s!"daemon for '{s.name}' did not come up (see {log})")

/-- Reject an operand that is neither an exact name nor a well-formed `name@host` target:
print the name rule and answer `usage`. -/
private def invalidTarget : IO Answer := do
  IO.eprintln s!"linger: invalid session name or malformed name@host target (use {Paths.nameRule})"
  return .usage

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

/-- One transport boundary for all session verbs. The host's transport, which the remotes file
gives it or else ssh (`Remote.transportFor`), runs linger there: its attach command for an attach,
which gives the far end a terminal, and its query command for every other verb. Linger hands it
`linger` and words every shell passes on as they are (`transport_exact`), the verb and every word,
empty ones included, encoded: ssh joins them into the line `Remote.command` spells, and a command
such as `docker exec` runs them as they are. Encoding doubles a word's length, and a Linux host
takes a command line of at most 128 KiB, so `send name@host -`, whose inherited stdin stays
byte-exact, carries longer text. The remote linger reads an attach or capture target with
`targetArgs`, so it travels as `targetOperands`; the other verbs take it by position
(`Remote.operands`). The transport's status, the remote command's, is the answer of a remote
target. -/
private def runTarget (verb : String) (target : Linger.Target.Remote.Target) (args : List String)
    (localAction : String → IO Answer) (options : List String := []) : IO Answer := do
  let interactive := verb == "attach"
  if interactive && (!(← stdinIsTty) || !(← (← IO.getStdout).isTty)) then
    throw
        (IO.userError
          s!"{verb} needs terminal input and output (use `start`, `resume` or `send` for scripting)")
  match target.host with
  | none =>
    localAction target.name
  | some host =>
    let transport := Linger.Target.Remote.transportFor (← remoteConfig) host
    match Linger.Target.Remote.targetArgv transport verb options target.name args with
    | [] =>
      throw (IO.userError s!"remote host '{Linger.Target.Remote.scrub host}' has no command")
    | cmd :: argv =>
      let child ← IO.Process.spawn { cmd, args := argv.toArray, stdin := .inherit }
      try
        return .program (← child.wait)
      finally
        if interactive then
          writeAll stdoutFd (ByteArray.mk Terminal.Render.leaveAnsi.toArray)

/-- Run `verb` through `runTarget` once `Remote.parseTarget` accepts the operand; a
malformed operand answers `usage` (`invalidTarget`) without connecting. -/
private def withTarget (verb target : String) (args : List String)
    (localAction : String → IO Answer) (options : List String := []) : IO Answer :=
  match Linger.Target.Remote.parseTarget target with
  | none => invalidTarget
  | some parsed => runTarget verb parsed args localAction options

/-- `withTarget`, its local action given the session the name leads to now (`Names.find`): every
file of the session is the ID's for the rest of the command, whatever renames follow. A name that
leads to no session's ID is no session (`noSession`). -/
private def withSession (verb target : String) (args : List String)
    (localAction : Names.Ref → IO Answer) (options : List String := []) : IO Answer :=
  withTarget verb target args
    (fun name => do
      match ← Names.find name with
      | some s =>
        localAction s
      | none =>
        noSession name)
    options

/-- `withTarget` for a command that may create a session, its local action given the ID the name
leads to, or a fresh one with an entry for the name when it leads nowhere (`Names.claim`). -/
private def withNew (verb target : String) (args : List String)
    (localAction : Names.Ref → IO Answer) (options : List String := []) : IO Answer :=
  withTarget verb target args
    (fun name => do
      localAction (← Names.claim name))
    options

/-- Maximum simultaneous remote overview commands. -/
abbrev remoteQueryLimit : Nat := 4

/-- All remote overview commands share this polling window. -/
abbrev remoteQueryTimeoutMs : Nat := 3000

/-- Remote hosts for `-r`, each with its transport: the explicit flag list, each host with the
transport the remotes file gives it or else ssh, or, for `-r` with no list, the file's hosts
(`remoteConfig`). Duplicates are a hard error (`Remote.checkHosts`). `none` means no `-r` (local
only); `some []` means `-r` with no arg (read the file). -/
private def resolveRemotes (flag : Option (List String)) :
    IO (List (String × Linger.Target.Remote.Transport)) := do
  match flag with
  | none =>
    return []
  | some given =>
    let config ← remoteConfig
    if given.isEmpty then
      return config
    let hosts :=
      (given.map (·.trimAscii.toString)).filter (fun h => !h.isEmpty && !h.startsWith "#")
    match Linger.Target.Remote.checkHosts hosts with
    | .ok l =>
      return l.map fun host => (host, Linger.Target.Remote.transportFor config host)
    | .error e =>
      throw (IO.userError e)

/-- Four transport commands at most share a three-second command deadline, the bounded wait
linger keeps whatever the transport: a transport's own keepalives alone cannot bound a remote
command that never exits. Each host's answer, in host order, is the complete output of a command
that succeeded, or `none`; stop and join every remaining group. Signal waiters let a cancelled
chooser's listing retire the transports' isolated groups: a watched signal that comes before the
waiters stop, even while the groups are retired, ends the listing, which answers with the first
that came (`Watched.came`). -/
private def listRemotes (hosts : Array (String × Linger.Target.Remote.Transport)) :
    IO (Except UInt8 (Array (Option String))) := do
  let signals ← IO.mkRef (#[] : Array (Std.Async.Signal.Waiter × Std.Async.AsyncTask Int))
  let jobs ← IO.mkRef (#[] : Array (Nat × IO.Ref (Option Command.Job)))
  let listed ←
    try
      for signal in [Std.Async.Signal.sigterm, .sigint, .sighup] do
        let waiter ← Std.Async.Signal.Waiter.mk signal true
        try
          let task ← waiter.wait
          signals.modify (·.push (waiter, task))
        catch e =>
          waiter.stop
          throw e
      let deadline := (← monotonicMs) + remoteQueryTimeoutMs
      let mut outputs := Array.replicate hosts.size none
      let mut next := 0
      while next < hosts.size || !(← jobs.get).isEmpty do
        if let some signal← ({ waiters := ← signals.get } : Watched).came then
          return .error signal
        if (← monotonicMs) ≥ deadline then
          break
        while
          next < hosts.size && (← jobs.get).size < remoteQueryLimit && (← monotonicMs) < deadline do
          let index := next
          next := next + 1
          let pending ← IO.mkRef none
          jobs.modify (·.push (index, pending))
          try
            if let cmd :: args :=
                Linger.Target.Remote.argv hosts[index]!.2 "ls" ["--porcelain"] then
              pending.set (some (← Command.start cmd args.toArray))
          catch _ =>
            pure ()
        let mut running := #[]
        for (index, pending) in ← jobs.get do
          try
            if let some output← Command.poll pending then
              if output.exitCode == 0 then
                outputs := outputs.set! index (some output.stdout)
          catch _ =>
            pure ()
          if (← pending.get).isSome then
            running := running.push (index, pending)
        jobs.set running
        if !running.isEmpty then
          unless ← nap deadline 5 do
            break
      pure outputs
    finally
      for (_, pending) in ← jobs.get do
        try
          Command.stop pending
        catch _ =>
          pure ()
      for (waiter, _) in ← signals.get do
        waiter.stop
  if let some signal← ({ waiters := ← signals.get } : Watched).came then
    return .error signal
  return .ok listed

/-- Local attention counts under one 250 ms reply window: the text `ls --summary`
prints and an attached title shows, computed in the calling process. A daemon whose end record
says what it saw is not asked. -/
private def summaryText : IO String := do
  let rows ← localRows (some ((← monotonicMs) + 250)) (statusOnly := true)
  return Linger.Display.Status.summary
      (rows.map fun info => Linger.Display.Status.ofName ((info.lookup "status").getD "unknown"))

/-- One attention sample for a client attached to `own`: the summary `summaryText` gives, each
local session's status, and a notification for each session that changed into asking since
`previous`, other than `own` (`Alert.announce`), with its notification's text, which only those
sessions are asked for, or `bell`. -/
private def attentionSample (own : String)
    (previous : Option (List (String × Linger.Display.Status.Status))) : IO Client.Sample := do
  let rows ← localRows (some ((← monotonicMs) + 250)) (statusOnly := true)
  let statuses :=
    rows.map fun info =>
      ((info.lookup "name").getD "",
        Linger.Display.Status.ofName ((info.lookup "status").getD "unknown"))
  let announced := Linger.Display.Alert.announce previous statuses own
  let told ←
    if announced.isEmpty then
      pure []
    else
      localRows (some ((← monotonicMs) + 250)) (only := some announced)
  let alerts :=
    announced.map fun name =>
      Linger.Display.Alert.notification name
        (((told.find? (·.lookup "name" == some name)).bind (·.lookup "notice")).getD "")
  return { summary := Linger.Display.Status.summary (statuses.map (·.2)), statuses, alerts }

/-- `ls --summary`: print `summaryText`, or nothing when no local session needs
attention; `done` either way. -/
private def cmdSummary : IO Answer := do
  let summary ← summaryText
  if !summary.isEmpty then
    IO.println summary
  return .done

/-- The answer that tells how a session ended, as its daemon reported it (`Ending.answer`): its
program's, or `saved` with the signal for a session a signal to its daemon saved; an older
daemon's status is the program's. -/
private def endingAnswer : Client.Ending → Answer
  | .outcome outcome => (Linger.Session.Ending.program outcome).answer
  | .saved signal => (Linger.Session.Ending.saved signal).answer
  | .status status => .program status

/-- Attach over `fd` once its daemon has said, in an `info` answer on `fd` within
`Client.replySilenceMs`, that it speaks this version's protocol (`Wire.admits`). Otherwise close
`fd`, say which session and which level its daemon reported, and answer `notDone`: a daemon an
older linger started refuses this version's attach as a message it does not know, one from
before the level was reported drops it without a reply, and one that does not answer would leave
the attach waiting for the detach key. -/
private def attachSpoken (name : String) (fd : UInt32) (readOnly : Bool) :
    IO (Except Answer Client.Outcome) := do
  let heard ←
    (Inventory.readInfo fd (some ((← monotonicMs) + Client.replySilenceMs.toNatClampNeg))).toBaseIO
  let level := (heard.toOption.bind (·.lookup "protocol")).bind String.toNat?
  if Linger.Session.Wire.admits level then
    return .ok (← Client.attach name fd (attentionSample name) readOnly)
  close fd
  match heard, level with
  | .error why, _ =>
    IO.eprintln s!"linger: session '{name}' did not say which protocol it speaks ({why})"
  | .ok _, some level =>
    let which := if level < Linger.Session.Wire.protocol then "an older" else "a newer"
    IO.eprintln
        s!"linger: session '{name}' was started by {which} linger (protocol {level}); restart \
          it, or attach with that linger"
  | .ok _, none =>
    IO.eprintln
        s!"linger: session '{name}' was started by an older linger (no protocol level); restart \
          it, or attach with that linger"
  return .error .notDone

/-- Discard the saved session `name` once a viewer has seen it, as `kill` discards one: delete its
checkpoint while holding the name, when it still holds `shown`, the bytes the viewer was shown, so
that a session resumed or replaced since is never lost. Its end record stays, for `wait` and
`ls`. A name another process holds, or a checkpoint that cannot be read or deleted, keeps the
session and says so. -/
private def discardShown (s : Names.Ref) (shown : ByteArray) : IO Unit := do
  let discarded ←
    try
      Paths.withSessionLock s.id do
          if (← Resume.readCkpt s.id).map (·.data) == some shown.data then
            Resume.dropCkpt s.id
      pure none
    catch err =>
      pure (some err.toString)
  if let some why := discarded then
    IO.eprintln s!"\r\nlinger: session '{s.name}' was seen but not discarded: {why}"

/-- Take the steps `Recovery.visit` names for the saved session `name`, whose checkpoint held
`shown`, decoding to the screen `vt`, under the status the listing shows for it: `none` when the
session is to be resumed, and otherwise how the attach ended. A view a signal interrupts takes no
later step, so a session it may not have shown is kept; a view the viewer leaves goes on to tell
how the program ended and discard the session. -/
private def runVisit (s : Names.Ref) (shown : ByteArray) (vt : Terminal.Vt.Vt)
    (status : Linger.Display.Status.Status) (steps : List Linger.App.Visit.Step) :
    IO (Option Client.Outcome) := do
  let mut result : Client.Outcome := .detached
  for step in steps do
    match step with
    | .resume =>
      return none
    | .show =>
      let viewed ← Client.viewSaved s.name vt status
      if let .detached := viewed then
        pure ()
      else
        return some viewed
    | .tell outcome =>
      result := .ended (.outcome outcome)
    | .discard =>
      discardShown s shown
  return some result

/-- What an attach does with `name` when no daemon answers for it, from its end record and then,
unless the attach resumes it, its checkpoint, both read while holding the name: the result of a
program that ended, shown and then discarded, or a saved session viewed or, `none`, resumed
(`Recovery.visit`), or, when its checkpoint does not decode or there is none, the refusal
`Recovery.decide` answers. The record alone decides a resume, so a resume leaves the checkpoint
unread, to the daemon it starts. -/
private def visitOffline (s : Names.Ref) (readOnly : Bool) :
    IO (Except Answer (Option Client.Outcome)) := do
  let (steps, record, file) ←
    Paths.withSessionLock s.id do
        let record ← (Record.load s.id).toBaseIO
        let steps := Linger.App.Recovery.visit readOnly record.toOption.join
        if steps == [.resume] then
          return (steps, record, none)
        return (steps, record, ← Resume.readCkpt s.id)
  if steps == [.resume] then
    return .ok none
  let status := Linger.Display.Listing.rowStatus (savedRow record).1
  match Linger.App.Recovery.decide false file, file with
  | .resume ck, some shown =>
    return .ok (← runVisit s shown ck.vt status steps)
  | .refuse answer, _ =>
    return .error answer
  | _, _ =>
    return .error .notFound

/-- A live connection is authoritative, once its daemon says it speaks this version's protocol
(`attachSpoken`). With no daemon, an offline checkpoint is loaded with its end record while owning
both resources and displayed after releasing them, under the status the listing shows for it
(`visitOffline`): a session whose program ended is a result, which either mode shows, then tells
how it ended and discards once the viewer leaves, since it has been seen; read-only attachment
views any other saved session, and writable attachment keeps the create/resume path for it. Either
refuses a checkpoint that does not decode, which stays as it is (`Recovery.decide`). A writable
attach to a name no record names resumes the latest tmux-resurrect save's pane of that name
(`adoptPane`). Live titles sample `attentionSample` in this process. -/
private def cmdAttach (source : Source) (s : Names.Ref) (cmd : List String) (readOnly : Bool) :
    IO Answer := do
  let result : Except Answer Client.Outcome ←
    if readOnly then
      match ← Client.connect s.id with
      | some fd =>
        attachSpoken s.name fd true
      | none =>
        match ← visitOffline s true with
        | .ok (some outcome) =>
          pure (.ok outcome)
        | .ok none =>
          -- a watcher's visit never resumes (`visit_result`)
          .error <$> refused s .notDone
        | .error answer =>
          .error <$> refused s answer
    else
      -- a result is shown, not resumed: only a saved session that is no result, or none, takes
      -- the create/resume path, as does a name another process holds
      match ← Client.connect s.id with
      | some fd =>
        attachSpoken s.name fd false
      | none =>
        adoptPane source s.name
        match ← (visitOffline s false).toBaseIO with
        | .ok (.ok (some outcome)) =>
          pure (.ok outcome)
        | _ =>
          match ← connectUpsert s cmd with
          | .ok fd =>
            attachSpoken s.name fd false
          | .error answer =>
            .error <$> refused s answer
  match result with
  | .error answer =>
    return answer
  | .ok (.ended (.saved signal)) =>
    -- the system stopping linger may have hung up this terminal too: the answer says it
    try
      IO.eprintln
          s!"\r\nlinger: session '{s.name}' was saved when signal {signal} stopped its daemon; \
            attach to resume it"
    catch _ =>
      pure ()
    return endingAnswer (.saved signal)
  | .ok (.ended ending) =>
    IO.eprintln s!"\r\nlinger: session '{s.name}' ended ({ending.describe})"
    return endingAnswer ending
  | .ok (.stopped signal) =>
    -- the terminal is handed back, but a hung-up one cannot show why: the answer says it, and
    -- `main` then ends the process by the signal
    try
      IO.eprintln s!"\r\nlinger: signal {signal} stopped the attach; detached from '{s.name}'"
    catch _ =>
      pure ()
    return .stopped signal
  | .ok .detached =>
    IO.eprintln s!"\r\nlinger: detached from '{s.name}'"
    return .done
  | .ok (.refused msg) =>
    IO.eprintln s!"\r\nlinger: {msg}"
    return .notDone
  | .ok (.lost why) =>
    IO.eprintln s!"\r\nlinger: {why} for '{s.name}'"
    return .notDone

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
    -- session name, so its row shows `@host`.
    let withColor :=
      Linger.Os.Env.withColor (← (← IO.getStdout).isTty) (← IO.getEnv "NO_COLOR")
        (← IO.getEnv "TERM")
    let named :=
      rows.map fun info =>
        match info.lookup "name", info.lookup "host" with
        | none, some host => ("name", "@" ++ host) :: info
        | _, _ => info
    let ordered :=
      Linger.Display.View.sort
        (fun info => Linger.Display.Status.ofName ((info.lookup "status").getD "")) named
    let width ← humanWidth
    let home ← accountHome
    writeAll stdoutFd
        (ByteArray.mk
          (Linger.Display.Listing.terminalListing withColor width
              (ordered.map (Linger.Display.Listing.atHome home))).toArray)

/-- `ls`: local rows, then each remote host's rows named `name@host`, then the rows of the latest
tmux-resurrect save's panes no record names (`Source.rows`), printed as `k<TAB>v`
records separated by blank lines (`porcelain`) or as the terminal listing.
Remote rows keep only name, command, state and status, as the host's linger reports them; a host
that does not answer within the bounded wait is one record, its `host` with the status `?` no
answer gives, which the terminal listing names `@host`. Answers `stopped`, with the signal, when
a signal stops it while it queries remote hosts. -/
private def cmdList (source : Source) (porcelain : Bool)
    (remotes : List (String × Linger.Target.Remote.Transport)) : IO Answer := do
  let (locals, remote) ←
    if remotes.isEmpty then
      pure (← localRows, (.ok #[] : Except UInt8 (Array (Option String))))
    else
      do
        let task ← IO.asTask localRows Task.Priority.dedicated
        try
          let remote ← listRemotes remotes.toArray
          let locals ← IO.ofExcept (← IO.wait task)
          pure (locals, remote)
        finally
          discard <| IO.wait task
  let remote ←
    match remote with
    | .ok outputs =>
      pure outputs
    | .error signal =>
      return .stopped signal
  let mut rows := locals
  for ((host, _), output) in remotes.zip remote.toList do
    match output with
    | none =>
      rows := rows ++ [[("host", host), ("status", Linger.Display.Status.name .unknown)]]
    | some output =>
      for row in Linger.Target.Remote.parse output do
        -- a remote row is built from what the peer's porcelain says about identity
        -- and liveness. It also emits `clients` and its record fields; those are dropped
        -- rather than rendered, so a remote row's caption and watcher columns are
        -- blank whatever the peer reports.
        rows :=
          rows ++
            [[("name", s!"{row.name}@{host}"), ("cmd", row.cmd),
                ("state", if row.live then "live" else "resumable"),
                ("status",
                  Linger.Display.Status.name
                    (Linger.Display.Listing.rowStatus (.remote row.live row.status)))]]
  let records : Linger.Session.Records :=
    { sockets := (← Paths.listSocketNames).map (·.name),
      checkpoints := (← Paths.listCkptNames).map (·.name),
      endings := (← Paths.listRecordNames).map (·.name),
      entries := (← Names.load).flatMap fun (name, id) => [name, id] }
  printRows porcelain (rows ++ (← source.rows records))
  return .done

/-- Parse the listing's arguments: an optional `--porcelain`, and either `-r` with its hosts or
the names of the sessions to list, in any order, every word after `--` a name, as
`Remote.targetOperands` places one that starts with `-`. `-r` followed by a `-`-prefixed token
(or nothing) means "use the file"; `-r hosts` is an explicit comma list. Returns `none` on any
other option, and on names with `-r`. -/
def parseLs (args : List String) : Option (Bool × Option (List String) × List String) :=
  let rec go : List String → Option (Bool × Option (List String) × List String)
    | [] => some (false, none, [])
    | "--" :: names => some (false, none, names)
    | "--porcelain" :: rest => (go rest).map fun (_, r, n) => (true, r, n)
    | "-r" :: rest =>
      match rest with
      | h :: more =>
        if h.startsWith "-" then (go (h :: more)).map fun (p, _, n) => (p, some [], n)
        else (go more).map fun (p, _, n) => (p, some (h.splitOn ","), n)
      | [] => some (false, some [], [])
    | word :: rest =>
      if word.startsWith "-" then none else (go rest).map fun (p, r, n) => (p, r, word :: n)
  match go args with
  | some (_, some _, _ :: _) => none
  | parsed => parsed

/-- The answer to a one-shot request: `done` when the daemon completed it with `done`,
otherwise `notDone` after printing why it did not complete. -/
private def requestStatus (name : String) (result : Client.Drained) : IO Answer := do
  match result with
  | .done =>
    return .done
  | .refused why =>
    IO.eprintln s!"linger: {why}"
  | .lost why =>
    IO.eprintln s!"linger: {why} for '{name}'"
  | .exited ending =>
    IO.eprintln s!"linger: session '{name}' ended before the request completed ({ending.describe})"
  | .silent =>
    IO.eprintln s!"linger: no reply from '{name}'"
  return .notDone

/-- One request to a live session, given up after `Client.replySilenceMs` of silence, as every
one-shot request is (`Client.oneShot`). -/
private def requireLive (s : Names.Ref) (m : Msg) : IO Answer := do
  match ← Client.oneShot s.id m with
  | none =>
    noSession s.name
  | some result =>
    requestStatus s.name result

/-- Like `requireLive`, but delivers `ms` without awaiting a reply: `send` text. -/
private def requireLiveSend (s : Names.Ref) (ms : List Msg) : IO Answer := do
  if ← Client.sendOnly s.id ms then
    return .done
  noSession s.name

/-- What `capture` of a saved session has to show once it has rendered: the session, or why
there is none, with the answer that says so. -/
private inductive Shown where
  /-- The saved session, rendered. -/
  | session (bytes : List UInt8)
  /-- None: no session holds the name, or its checkpoint does not decode, as `why` says. -/
  | refusal (answer : Answer) (why : String)

/-- Run the steps of `plan` through `run`, in order, as `Capture.work` reads them: the steps from
an `acquire` to the next `release`, or to the end, inside one `Paths.withSessionLock` of `name`,
which takes both of the name's locks once and lets them go however those steps end, and the
other steps outside it. -/
private def runHolding (s : Names.Ref) (plan : List Linger.App.Capture.Step)
    (run : Linger.App.Capture.Step → IO Unit) : IO Unit := do
  let mut held : Option (Array Linger.App.Capture.Step) := none
  for step in plan do
    match step, held with
    | .acquire, none =>
      held := some #[]
    | .release, some inside =>
      Paths.withSessionLock s.id (inside.forM run)
      held := none
    | .acquire, some _ | .release, none =>
      pure ()
    | step, some inside =>
      held := some (inside.push step)
    | step, none =>
      run step
  if let some inside := held then
    Paths.withSessionLock s.id (inside.forM run)

/-- A connected daemon is authoritative, including its errors. Only an absent connection
followed by successful ownership acquisition permits an offline read, which takes the steps of
`Capture.plan`: it holds both locks through loading and rendering, and lets them go before it
writes what it rendered, so a reader that does not read holds up no attach or resume
(`capture_waits_unlocked`). Never start or modify a session. -/
private def cmdRead (s : Names.Ref) (m : Msg) (render : Terminal.Vt.Vt → List UInt8) : IO Answer :=
  do
  match ← Client.oneShot s.id m with
  | some result =>
    requestStatus s.name result
  | none =>
    let file ← IO.mkRef (none : Option ByteArray)
    let shown ← IO.mkRef (Shown.refusal .notFound (← refusalText s .notFound))
    let answer ← IO.mkRef Answer.failed
    runHolding s Linger.App.Capture.plan fun
        | .load => do
          file.set (← Resume.readCkpt s.id)
        | .render => do
          match Linger.App.Recovery.decide false (← file.get) with
          | .resume ck =>
            shown.set (.session (render ck.vt))
          | .refuse refusal =>
            shown.set (.refusal refusal (← refusalText s refusal))
          | .fresh =>
            shown.set (.refusal .notFound (← refusalText s .notFound))
        | .write => do
          match ← shown.get with
          | .session bytes =>
            writeAll stdoutFd (ByteArray.mk bytes.toArray)
            answer.set .done
          | .refusal said why =>
            IO.eprintln s!"linger: {why}"
            answer.set said
        | .acquire | .release => pure ()
    answer.get

/-- `send <name> -`: stdin to the session's pty, byte-exact, each read (≤ 64 KiB) in the
frames `Wire.inputFrames` cuts, each within the decoder's cap (`inputFrames_exact`). The agent's
raw input path — Enter, ^C, ESC, arrow sequences, exact whitespace: everything argv
cannot carry. Poll-then-read so EOF (`read` = `none`)
is distinguished from would-block (`some #[]`, looped past) without spinning;
no timeout on purpose — a slow producer feeding a pipe is legitimate, and every event the loop
answers, input, a reply or either side closing, wakes the poll. Stdin EOF
answers `done`, and a missing session `notFound`; a refusal, an invalid reply, the session's exit
or a lost connection answers `notDone`. Nothing accumulates (each chunk is sent and dropped), so
no `Buf` is involved. -/
private def cmdSendStdin (s : Names.Ref) : IO Answer := do
  match ← Client.connect s.id with
  | none =>
    noSession s.name
  | some fd =>
    try
      let mut dec : Linger.Session.Wire.Decoder := {}
      let mut go := true
      while go do
        let revs ← poll #[stdinFd, fd] #[POLLIN, POLLIN] (-1)
        if revs[1]! &&& (POLLIN ||| POLLHUP ||| POLLERR) != 0 then
          match ← read fd 65536 with
          | none =>
            IO.eprintln s!"linger: connection lost for '{s.name}'"
            return .notDone
          | some bs =>
            if !bs.isEmpty then
              let (dec', msgs) := dec.feed bs.toList
              dec := dec'
              if dec.errored then
                IO.eprintln s!"linger: invalid response from daemon for '{s.name}'"
                return .notDone
              for m in msgs do
                match m with
                | .err msg =>
                  IO.eprintln s!"linger: {Client.replyText "request refused" msg}"
                  return .notDone
                | .ended outcome =>
                  let ending := Client.Ending.outcome outcome
                  IO.eprintln s!"linger: session '{s.name}' ended while sending ({ending.describe})"
                  return .notDone
                | .exited status =>
                  IO.eprintln s!"linger: session '{s.name}' ended while sending (status {status})"
                  return .notDone
                | .saved signal =>
                  let ending := Client.Ending.saved signal
                  IO.eprintln s!"linger: session '{s.name}' ended while sending ({ending.describe})"
                  return .notDone
                | _ =>
                  pure ()
        if revs[0]! &&& (POLLIN ||| POLLHUP ||| POLLERR) != 0 then
          match ← read stdinFd 65536 with
          | none =>
            go := false
          | some bs =>
            for m in Linger.Session.Wire.inputFrames bs.toList do
              Client.sendMsg fd m
      return .done
    finally
      close fd

/-- Say on stderr how the session ended when a signal killed its program, how its program ended
is unknown, or a signal to its daemon saved it, and that no session has the name when a kill
dismissed its tmux pane; an exit status says the rest. -/
private def sayEnding (name : String) : Linger.Session.Ending → IO Unit
  | .program (.exited _) => pure ()
  | .dismissed => IO.eprintln s!"linger: no session '{name}' (a kill dismissed its tmux pane)"
  | .program outcome =>
    IO.eprintln s!"linger: session '{name}' ended ({(Client.Ending.outcome outcome).describe})"
  | .saved signal =>
    IO.eprintln
      s!"linger: session '{name}' was saved when signal {signal} stopped its daemon; \
          `linger resume {name}` runs it again"

/-- What answers for a name when no daemon does. -/
private inductive Unanswered where
  /-- Another process holds the name, as a daemon does while it starts or ends; `why` says so. -/
  | held (why : String)
  /-- The name's end record says this (`Record.answer`), read while holding the name when the
  answer depends on it (`Record.settled`). -/
  | recorded (ending : Option Linger.Session.Ending)

/-- Read the name's end record. A missing record or one that says how its program ended answers
at once (`Record.settled`); only a running one needs the name held to read, since a reader that
can hold the name knows the record's daemon is gone. A record that cannot be read throws. -/
private def unanswered (name : String) : IO Unanswered := do
  if let some answer := Linger.Session.Record.settled (← Record.load name) then
    return .recorded answer
  let loaded ←
    try
      Paths.withSessionLock name do
          return ← (Record.load name).toBaseIO
    catch err =>
      return .held err.toString
  return .recorded (Linger.Session.Record.answer (← IO.ofExcept loaded))

/-- One look at `name` for `wait` (`Wait.Heard`): its daemon's reply, given up after `silenceMs`
of silence, or, with no daemon to answer, its end record or that another process holds it; with
why, for a refusal or a held name. -/
private def hear (s : Names.Ref) (silenceMs : Int32) : IO (Wait.Heard × String) := do
  match ← Client.oneShot s.id .wait (untilDone := false) (silenceMs := silenceMs) with
  | some (.exited (.outcome outcome)) =>
    return (.ended (.program outcome), "")
  | some (.exited (.saved signal)) =>
    return (.ended (.saved signal), "")
  | some (.exited (.status status)) =>
    return (.status status, "")
  | some .silent =>
    return (.silent, "")
  | some (.refused why) =>
    return (.refused, why)
  | some .done =>
    return (.refused, s!"no exit status from '{s.name}'")
  | some (.lost _) | none =>
    match ← unanswered s.id with
    | .recorded answer =>
      return (.recorded answer, "")
    | .held why =>
      return (.held, why)

/-- `wait`: block until the session ends and answer as `Wait.decide` does with what each look
hears, saying why on stderr when that is not the program's own exit. The ending comes from its
daemon or, with no daemon to answer, from the name's end record once nothing else holds the
name: the program's, or `saved` with the signal for a session a signal to its daemon saved, whose
program did not end by itself, which exits with 128 plus the signal's number, as a shell's `wait`
reports a job that signal stopped; `notFound`, as a shell's `wait` reports an unknown job, when no
session has taken the name. A daemon lost during the wait leaves its own record, never an older
one. With a `deadline` on the monotonic clock, `timedOut` once it has passed and the session is
still running, as `timeout(1)` reports, leaving the session as it is. A refusal answers
`notDone`; that linger could not find out, only for an unknown ending or a name held with no
daemon answering for `Wait.heldNameMs`, from the look that first found it so. -/
private def cmdWait (deadline : Option Nat) (s : Names.Ref) : IO Answer := do
  let mut heldSince : Option Nat := none
  repeat
    -- a silence budget ends a held wait when the time is up; `Int32` bounds one round of it
    let now ← monotonicMs
    let silenceMs : Int32 :=
      match deadline with
      | some limit => Int32.ofNat (min (limit - now) 2147483647)
      | none => -1
    let (heard, why) ← hear s silenceMs
    match Wait.decide deadline heldSince (← monotonicMs) heard with
    | .answer answer =>
      match answer, heard with
      | .timedOut, _ =>
        IO.eprintln s!"linger: timed out waiting for '{s.name}'"
      | _, .ended ending | _, .recorded (some ending) =>
        sayEnding s.name ending
      | _, .recorded none =>
        IO.eprintln s!"linger: no session '{s.name}'"
      | _, .refused =>
        IO.eprintln s!"linger: {why}"
      | _, .held =>
        IO.eprintln s!"linger: no answer for '{s.name}': {why}"
      | _, _ =>
        pure ()
      return answer
    | .again since =>
      heldSince := since
      if let some first := since then
        discard <| nap (first + Wait.heldNameMs) 20

/-- `cmdWait` of the session `name` leads to now (`Names.find`), which it waits for whatever
renames follow; a name that leads to none is no session. -/
private def waitNamed (deadline : Option Nat) (name : String) : IO Answer := do
  match ← Names.find name with
  | some s =>
    cmdWait deadline s
  | none =>
    noSession name

/-- Milliseconds in `text`, a number of seconds such as `timeout(1)` takes: digits, a point and
digits, or both, counting at most three decimals. -/
private def parseSeconds (text : String) : Option Nat :=
  let digits (part : String) := !part.isEmpty && part.all Char.isDigit
  match text.splitOn "." with
  | [whole] => if digits whole then whole.toNat?.map (· * 1000) else none
  | [whole, fraction] =>
    if (whole.isEmpty || digits whole) && digits fraction then
      let millis := (fraction.toList.take 3 ++ List.replicate (3 - fraction.length) '0')
      do
      let seconds ←
        if whole.isEmpty then
          some 0
        else
          whole.toNat?
      let millis ← (String.ofList millis).toNat?
      return seconds * 1000 + millis
    else none
  | _ => none

/-- Milliseconds as seconds, with three decimals, as `parseSeconds` reads them back. -/
private def secondsText (ms : Nat) : String :=
  let millis := toString (ms % 1000)
  s!"{ms / 1000}.{"".pushn '0' (3 - millis.length)}{millis}"

/-- `wait` for each named session in turn and give the last one's answer, as a shell's `wait`
does with several jobs. With a time limit in milliseconds, all of them share one deadline, and
`timedOut` means it passed. -/
private def waitAll (names : List String) (limit : Option Nat) : IO Answer := do
  if names.isEmpty then
    return ← usageError "wait"
  let some targets := names.mapM Linger.Target.Remote.parseTarget | invalidTarget
  let deadline ←
    limit.mapM fun ms => do
        return (← monotonicMs) + ms
  let mut answer : Answer := .done
  for target in targets do
    let now ← monotonicMs
    let options :=
      match deadline with
      | some due => ["--timeout", secondsText (due - now)]
      | none => []
    answer ← runTarget "wait" target [] (waitNamed deadline) options
    -- a remote wait's answer is its status, so the codes tell whether its time ran out
    if let some due := deadline then
      if answer.code == Answer.timedOut.code && (← monotonicMs) ≥ due then
        return answer
  return answer

/-- Whether `name` had a checkpoint, which this discards. -/
private def dropSaved (name : String) : IO Bool := do
  if ← System.FilePath.pathExists (← Paths.ckptPath name) then
    Resume.dropCkpt name
    return true
  return false

/-- Discard the saved session `name` while holding the name: whether it had a checkpoint to
discard, or why another process holds the name. -/
private def discardSaved (name : String) : IO (Except String Bool) := do
  let discarded ←
    try
      Paths.withSessionLock name do
          return ← (dropSaved name).toBaseIO
    catch err =>
      return .error err.toString
  return .ok (← IO.ofExcept discarded)

/-- `kill`: end the session and return once it has ended. Its daemon stops the program (SIGHUP to
its terminal session, then SIGKILL after a second), tells whoever is attached or waiting how it
ended, records that and gives the name up. With no daemon, a saved session is discarded instead,
an ended one included, whose end record stays for `wait` and `ls`, and a name no record names
whose pane the latest tmux-resurrect save has gets the end record a kill leaves, which hides the
pane (`Source.dismiss`). No session answers
`notFound`; a refusal, a name another process holds, or a session that has not ended within
`Wait.heldNameMs`, prints a diagnostic and answers `notDone`. -/
private def cmdKill (source : Source) (s : Names.Ref) : IO Answer := do
  match ← Client.oneShot s.id .kill with
  | some (.refused why) =>
    IO.eprintln s!"linger: {why}"
    return .notDone
  | some _ =>
    -- the session has ended once its daemon gives the name up, which it does after recording
    -- how the program ended and removing its socket
    let deadline := (← monotonicMs) + Wait.heldNameMs
    repeat
      let released ←
        try
          Paths.withSessionLock s.id (pure true)
        catch _ =>
          pure false
      if released then
        return .done
      unless ← nap deadline 20 do
        IO.eprintln s!"linger: session '{s.name}' has not ended"
        return .notDone
  | none =>
    match ← discardSaved s.id with
    | .ok true =>
      return .done
    | .ok false =>
      if ← source.dismiss s.name then
        return .done
      noSession s.name
    | .error why =>
      IO.eprintln s!"linger: {why}"
      return .notDone

/-- Whether a live or saved session holds the ID `id`, an ended one still listed included: a
daemon answers on its socket, or its checkpoint exists. -/
private def held (id : String) : IO Bool := do
  match ← Client.connect id with
  | some fd =>
    close fd
    return true
  | none =>
    System.FilePath.pathExists (← Paths.ckptPath id)

/-- Whether the live session with ID `id` has a daemon an older linger started, which reports no
`renames` in its `info`; `false` for a session with no daemon. A daemon that does not answer
throws. -/
private def olderDaemon (id : String) : IO Bool := do
  match ← queryInfo id (retainUnavailable := false) with
  | none =>
    return false
  | some (.ok info) =>
    return (info.lookup "renames").isNone
  | some (.error err) =>
    throw (IO.userError s!"{err}, so the session cannot be renamed")

/-- `rename old new`: give the session `old` leads to the name `new`, as `Names.Rename.plan`
decides, holding the names lock. It refuses, changing nothing, an invalid new name (`usage`), an
old name no live or saved session has (`notFound`), and, answering `notDone`, a new name a live or
saved session has, an ended one still listed included, and a session whose daemon an older linger
started, which a newer linger's `upgrade` moves onto this one. The session keeps its ID, and with
it its program, its terminal, its clients, its waiters, its description and its status, and its
files stay where they are: only its name changes, the old name's entry moving to the new name, or
an entry made for it, neither replacing a name (`Names.move`, `Names.create`). An entry the new
name has whose session is gone is removed first, holding that session's ID, as is a name that is
its own free ID held, so that no start takes the new name meanwhile; a start that places it first
wins, and the rename then refuses. -/
private def cmdRename (new old : String) : IO Answer := do
  let valid := (Linger.Target.Name.check new).isSome
  let outcome ←
    Names.withLock do
        let table ← Names.load
        let oldId := Linger.Session.Names.resolve table old
        let newId := if valid then Linger.Session.Names.resolve table new else none
        let oldHeld ←
          match oldId with
          | some id =>
            held id
          | none =>
            pure false
        let newHeld ←
          match newId with
          | some id =>
            if oldId == some id then
              pure true
            else
              held id
          | none =>
            pure false
        let older ←
          if valid && oldHeld && !newHeld then
            (oldId.mapM olderDaemon)
          else
            pure none
        match Linger.Session.Names.Rename.plan valid oldHeld (older.getD false) newHeld, oldId with
        | .move, some id =>
          let place : IO Bool :=
            if (table.lookup old).isSome then Names.move old new else Names.create new id
          let placed ←
            match newId with
            | some free =>
              Paths.withSessionLock free do
                  if ← held free then
                    return false
                  if (table.lookup new).isSome then
                    Names.remove new
                  place
            | none =>
              place
          unless placed do
            return .refuse .taken
          -- the name placed, it leads where `Names.rename` says: to the session's ID
          -- (`rename_moves`), which no other rename can change while this one holds the lock
          let after := Linger.Session.Names.rename table old new id
          unless
            Linger.Session.Names.resolve (← Names.load) new ==
              Linger.Session.Names.resolve after new do
            throw (IO.userError s!"the names changed while '{old}' was renamed '{new}'")
          return Linger.Session.Names.Rename.Plan.move
        | .move, none =>
          return .refuse .missing
        | plan, _ =>
          return plan
  match outcome with
  | .move =>
    return .done
  | .refuse .invalid =>
    IO.eprintln s!"linger: invalid session name '{new}' (use {Paths.nameRule})"
    return .usage
  | .refuse .missing =>
    noSession old
  | .refuse .taken =>
    IO.eprintln s!"linger: session '{new}' exists, and rename replaces no session"
    return .notDone
  | .refuse .older =>
    IO.eprintln
        s!"linger: session '{old}' was started by an older linger, which cannot rename it; \
          `linger upgrade {old}` moves it onto this linger, or restart it"
    return .notDone

/-- `--version`: print `linger` and `Mediation.versionNumber`, which sessions also see as
`TERM_PROGRAM_VERSION`, then the socket and state directories this environment resolves. -/
private def cmdVersion : IO Answer := do
  IO.println s!"linger {Terminal.Mediation.versionNumber}"
  IO.println s!"sockets: {← Paths.socketDir}"
  IO.println s!"state:   {← Paths.stateDir}"
  return .done

/-- The worse of two answers to one command's requests, as its exit status should tell: the one
with the higher code. -/
private def worse (a b : Answer) : Answer := if a.code < b.code then b else a

/-- `ls name...`: the named sessions' listing rows, as `ls` lists them, in the order named in
`porcelain` records, each a session's fields as its daemon reports them, then its name, state
and status; with no daemon or checkpoint for a name, its name and how the last session to hold it
ended (`Session.endingFields`), from its end record, or with no record of it, the row of the
latest tmux-resurrect save's pane of that name. A `name@host` target is listed by its host's
linger. A name no session has taken answers `notFound`; one another process holds with no daemon
answering prints why and answers `notDone`. -/
private def cmdListNamed (source : Source) (porcelain : Bool) (names : List String) : IO Answer :=
  do
  let some targets := names.mapM Linger.Target.Remote.parseTarget | invalidTarget
  let rows ←
    localRows (only :=
        some (targets.filterMap fun t => if t.host.isNone then some t.name else none))
  let mut answer : Answer := .done
  let mut shown : List (List (String × String)) := []
  for target in targets do
    let row ←
      if target.host.isSome then
        answer :=
          worse answer
            (←
              runTarget "ls" target [] (fun _ => pure .done)
                  (if porcelain then ["--porcelain"] else []))
        pure none
      else
        match rows.find? (·.lookup "name" == some target.name) with
        | some row =>
          pure (some row)
        | none =>
          match ← (← Names.find target.name).mapM (unanswered ·.id) with
          | none =>
            answer := worse answer (← noSession target.name)
            pure none
          | some (.recorded (some ending)) =>
            pure (some (("name", target.name) :: Linger.Session.endingFields ending))
          | some (.recorded none) =>
            match ← source.row target.name with
            | some row =>
              pure (some row)
            | none =>
              answer := worse answer (← noSession target.name)
              pure none
          | some (.held why) =>
            IO.eprintln s!"linger: no answer for '{target.name}': {why}"
            answer := worse answer .notDone
            pure none
    if let some row := row then
      if porcelain then
        printRows true [row]
      else
        shown := shown ++ [row]
  unless porcelain || shown.isEmpty do
    printRows false shown
  return answer

/-- `ls`'s arguments: `--summary` alone, `--resurrect` alone, which writes the sessions as a
tmux-resurrect save to standard output, or a listing of every session, the remote hosts' too
with `-r`, or of the named ones, as records with `--porcelain`. Any other is a usage error. -/
private def listArgs (source : Source) (args : List String) : IO Answer := do
  if args == ["--summary"] then
    return ← cmdSummary
  if args == ["--resurrect"] then
    source.writeSave
    return .done
  match parseLs args with
  | some (porcelain, remoteFlag, []) =>
    cmdList source porcelain (← resolveRemotes remoteFlag)
  | some (porcelain, _, names) =>
    cmdListNamed source porcelain names
  | none =>
    usageError "ls"

/-- An optional `--read-only`, then the target as `Remote.targetArgs` reads it. -/
private def attachArgs (source : Source) (args : List String) : IO Answer := do
  let readOnly := args.head? == some "--read-only"
  let args := if readOnly then args.tail else args
  let some (name, cmd) := Linger.Target.Remote.targetArgs args |
    do
      return ← usageError "attach"
  if readOnly && !cmd.isEmpty then
    IO.eprintln "linger: read-only attach does not accept a command"
    return .usage
  if readOnly then
    withSession "attach" name cmd (cmdAttach source · cmd true) ["--read-only"]
  else
    withNew "attach" name cmd (cmdAttach source · cmd false)

private def captureArgs (args : List String) : IO Answer := do
  let history := args.head? == some "--history"
  let args := if history then args.tail else args
  let some (name, []) := Linger.Target.Remote.targetArgs args |
    do
      return ← usageError "capture"
  withSession "capture" name []
      (cmdRead · (if history then .history else .screen)
        (if history then Terminal.Render.history else Terminal.Render.screenText))
      (if history then ["--history"] else [])

/-- How long `upgrade` waits for a daemon's answer: its probe of this binary, its saves and the
new image's start, which a loaded host slows. -/
private def upgradeWaitMs : Int32 := 60000

/-- `upgrade` of one live session: ask its daemon to replace its image with this binary, which
carries the session over, its program running on (`Msg.upgrade`). A daemon whose `info` names no
handoff format was started by an older linger, which cannot hand its session over, so it is not
asked, and keeps running; a daemon that refuses keeps running and says why. -/
private def upgradeOne (s : Names.Ref) : IO Answer := do
  match ← queryInfo s.id with
  | none =>
    noSession s.name
  | some (.error err) =>
    IO.eprintln s!"linger: {err} for '{s.name}'"
    return .notDone
  | some (.ok info) =>
    if (info.lookup "handoff").isNone then
      IO.eprintln s!"linger: session '{s.name}' was started by an older linger; it keeps running"
      return .notDone
    let exe := (← IO.appPath).toString
    match ← Client.oneShot s.id (.upgrade exe.toUTF8.toList) (silenceMs := upgradeWaitMs) with
    | none =>
      noSession s.name
    | some result =>
      let answer ← requestStatus s.name result
      if answer == .done then
        IO.println s!"upgraded {s.name}"
      return answer

/-- `upgrade [name...]`: `upgradeOne` of each named session, `name@host` on its host, or of every
local live one when none is named, answering the worst of their answers. -/
private def cmdUpgrade (names : List String) : IO Answer := do
  let names ←
    if names.isEmpty then
      let table ← Names.load
      pure ((← Paths.listSocketNames).filterMap (Linger.Session.Names.nameOf table ·.name))
    else
      pure names
  let mut answer : Answer := .done
  for name in names do
    answer := worse answer (← withSession "upgrade" name [] upgradeOne)
  return answer

/-- Perform `op` with the words after its command's word, and give its answer: `usage` for words
the operation does not take, otherwise the operation's own. Each operation has its one command
(`Commands.table`), and this is the one place a command line reaches it. -/
private def runOp (source : Source) (op : Linger.App.Commands.Op) (args : List String) :
    IO Answer := do
  match op, args with
  | .upgrade, names =>
    cmdUpgrade names
  | .resume, [name] =>
    withSession "resume" name [] (cmdResume source)
  | .resume, _ =>
    usageError "resume"
  | .start, name :: argv =>
    if argv.isEmpty then
      return ← usageError "start"
    withNew "start" name argv (cmdStart · argv)
  | .start, [] =>
    usageError "start"
  | .attach, rest =>
    attachArgs source rest
  | .send, name :: text =>
    if text.isEmpty then
      return ← usageError "send"
    withSession "send" name text fun s =>
        if text == ["-"] then cmdSendStdin s
        else
          requireLiveSend s
            (Linger.Session.Wire.inputFrames (String.intercalate " " text).toUTF8.toList)
  | .send, [] =>
    usageError "send"
  | .detach, [name] =>
    withSession "detach" name [] (requireLive · .detachAll)
  | .detach, _ =>
    usageError "detach"
  | .kill, [name] =>
    withSession "kill" name [] (cmdKill source)
  | .kill, _ =>
    usageError "kill"
  | .rename, [old, new] =>
    withTarget "rename" old [new] (cmdRename new)
  | .rename, _ =>
    usageError "rename"
  | .capture, rest =>
    captureArgs rest
  | .resize, [name, cs, rs] =>
    match cs.toNat?, rs.toNat? with
    | some cols, some rows =>
      -- Accept exactly the sizes the emulator keeps, so the pty cannot disagree.
      if Terminal.Vt.clampDim cols != cols || Terminal.Vt.clampDim rows != rows then
        do
          IO.eprintln "linger: size must be 1..1000 (the emulator clamps at 1000)"
          return .usage
      else
        withSession "resize" name [cs, rs]
            (requireLive · (.resize (UInt32.ofNat cols) (UInt32.ofNat rows)))
    | _, _ =>
      usageError "resize"
  | .resize, _ =>
    usageError "resize"
  | .wait, "--timeout" :: seconds :: names =>
    match parseSeconds seconds with
    | some ms =>
      waitAll names (some ms)
    | none =>
      usageError "wait"
  | .wait, names =>
    waitAll names none
  | .describe, name :: words =>
    -- no words clear the description
    withSession "describe" name words fun s =>
        requireLive s (.describe (String.intercalate " " words).toUTF8.toList)
  | .describe, [] =>
    usageError "describe"
  | .list, rest =>
    listArgs source rest

/-- Run one session command and give its answer, whose code is its exit status: `usage` for a
usage error or invalid target, otherwise the verb's own. The program's two options, `--help` and
`--version`, stand alone; any other first word is a command's (`Commands.lookup`), which performs
its operation (`runOp`), and any other is a usage error. `main` routes interactive selection and tmux interchange elsewhere; `__daemon`
runs a session's daemon in this process. -/
def main (source : Source) (args : List String) : IO Answer := do
  match args with
  | "__daemon" :: id :: name :: cwd :: cmd =>
    Daemon.serve id name cwd cmd (← Resume.saver id) (Resume.dropCkpt id) (recoverFor { name, id })
        (recordFile id)
    return .done
  | "__start" :: report :: id :: name :: cwd :: argv =>
    serveStart report id name cwd argv
    return .done
  | ["__resume", report, id, name, cwd] =>
    serveResume report id name cwd
    return .done
  | ["__upgraded", id, path, pid] =>
    -- an older image names the session's ID too: a name, which was every session's ID
    match pid.toNat? with
    | some pid =>
      Daemon.adopt id path (UInt32.ofNat pid) (← Resume.saver id) (Resume.dropCkpt id)
          (recordFile id)
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
    let word := args.headD ""
    match Linger.App.Commands.lookup word with
    | some command =>
      runOp source command.op args.tail
    | none =>
      IO.eprintln usage
      return .usage

end Linger.App.Shell
