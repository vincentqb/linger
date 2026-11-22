module

import Os.WorldCode
public import Linger.Session.WorldCode.Paths
import Linger.Session.WorldCode.Names
import Linger.Session.WorldCode.Daemon
import Linger.Session.WorldCode.Client
import Linger.Session.WorldCode.Inventory
public import Linger.Target.CoreCode.Remote
import Linger.Target.CoreCode.Name
import Terminal.CoreCode.Render
import Linger.Display.CoreCode.Listing
import Linger.Os.CoreCode.Answer
import Linger.App.CoreCode.Capture
public import Linger.Os.CoreSpec
public import Linger.Session.CoreSpec
public import Linger.App.CoreSpec
public import Linger.App.CoreCode.Api
import Linger.App.CoreCode.Recovery
import Linger.App.CoreCode.Commands
import Linger.App.CoreCode.Kill
import Linger.App.CoreCode.Wait
import Os.WorldCode.Command
import Linger.Session.WorldCode.Resume
import Linger.Session.WorldCode.Record
import Linger.Session.CoreCode.Handoff
import Std.Async.Signal
import Linger.Display.CoreCode.Status
import Linger.Display.CoreCode.Alert

public section

/-! # Linger.App.Api — linger as a Lean library

One function for each operation of the session model (`Commands.Op`), with typed arguments, the
`Request`'s, and typed results: what the command found (`Found`), whose answer is the exit status,
and what it shows, the listing's records or the bytes of a capture. `perform` is the one place a
request reaches its operation, through the transition `plan` gives it (`op_meaning`); the command
line parses its words into a request, performs it here and renders the reply
(`Linger.App.Shell`).

The API writes nothing to standard output or standard error (`scripts/gates.sh`): what a command
says as it goes it tells the caller's `Env.say`, and what it shows it returns. It reads no
`LINGER_DIR`, XDG variable or HOME to find its sessions: the caller names the namespace,
`Env.dirs`, which the daemons it begins work in too, and the linger executable that runs them,
`Env.exe`. It runs no remote transport unless the caller passes one, `Env.remote`. An attach is
the one request that uses a terminal, this process's, as the attach client drives it.
-/

namespace Linger.App.Api

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
whether it did, and `save` gives the sessions as the text of a save. -/
structure Source where
  /-- The listing rows of the panes no record names. -/
  rows : Linger.Session.Records → IO (List (List (String × String)))
  /-- The listing row of the pane of a name no record names. -/
  row : String → IO (Option (List (String × String)))
  /-- Write the pane's checkpoint where no record is: whether a record named it by then. -/
  adopt : String → IO Bool
  /-- Write the end record a kill leaves for a pane no record names: whether it did. -/
  dismiss : String → IO Bool
  /-- The local sessions' names and directories as the text of a save. -/
  save : IO String

/-- No source: no pane is listed, adopted or dismissed, and a save lists no session. -/
def Source.none : Source :=
  { rows := fun _ => pure [], row := fun _ => pure Option.none, adopt := fun _ => pure false,
    dismiss := fun _ => pure false, save := pure "" }

/-- The remote hosts a caller lets the API reach: the hosts of its remotes file, each with its
transport, and how to run one transport command line, its program first, giving its exit status,
on this process's terminal for an attach (`interactive`). -/
structure Remote where
  /-- The remotes file's hosts, each with its transport (`Remote.config`). -/
  config : IO (List (String × Linger.Target.Remote.Transport))
  /-- Run one transport command line and give its exit status. -/
  run : (interactive : Bool) → List String → IO UInt32

/-- Where and how the API works: the namespace its sessions live in, the linger executable that
runs their daemons, the source of saved sessions, the remote hosts it may reach, and where what a
command says as it goes goes. -/
structure Env where
  /-- The namespace: its sockets' directory and its state's. -/
  dirs : Paths.Dirs
  /-- The linger executable that runs a session's daemon, and the image an upgrade carries a
  session over to. -/
  exe : String
  /-- The saved sessions linger reads and never writes. -/
  source : Source := Source.none
  /-- The remote hosts the API may reach: none unless the caller passes them. -/
  remote : Option Remote := none
  /-- What a command says as it goes. -/
  say : Said → IO Unit := fun _ => pure ()
  /-- The bytes a `send -` delivers as its standard input's, when the caller gives them, as
  `serve` gives a request's `data`: none to read this process's standard input. -/
  input : Option ByteArray := none
  /-- The server that `serve` runs, which answers JSON-RPC on standard input and output: none
  unless the caller passes one, since the API writes to no standard stream. -/
  serve : Option (IO Found) := none

/-- What a request shows besides what it found. -/
inductive Shown where
  /-- Nothing. -/
  | nothing
  /-- The bytes of a capture: the session's screen or history. -/
  | bytes (bytes : ByteArray)
  /-- The records of a listing, each a session's fields, as records with `porcelain`, otherwise
  as the terminal listing. -/
  | rows (porcelain : Bool) (rows : List (List (String × String)))
  /-- Text a listing gives as it is: the attention counts or a tmux-resurrect save. -/
  | text (text : String)
  /-- The sessions an upgrade carried over. -/
  | upgraded (names : List String)

/-- What a request gives back: what it found, whose answer is its exit status, and what it
shows. -/
structure Reply where
  /-- What it found. -/
  found : Found
  /-- What it shows. -/
  shown : Shown := .nothing

/-- Say `text`. -/
private def say (env : Env) (text : String) : IO Unit := env.say { text }

/-- Say `text` on a terminal just handed back. -/
private def sayFresh (env : Env) (text : String) : IO Unit := env.say { text, fresh := true }

/-- Start `name`'s daemon detached, running `Env.exe` as `__daemon name cwd cmd...`, in this
namespace (`Paths.childArgs`), with its output appended to `Paths.logPath`. Returns the daemon's
pid once that program has started, without waiting for it to listen; `connectUpsert` waits for
the socket. -/
private def spawnDaemon (env : Env) (s : Names.Ref) (cwd : String) (cmd : List String) :
    IO UInt32 := do
  let log ← Paths.logPath s.id
  spawnDetached env.exe ((← Paths.childArgs) ++ ["__daemon", s.id, s.name, cwd] ++ cmd).toArray log

/-- How long `connectUpsert` waits for the socket whether or not the daemon it spawned
still lives: a concurrent start whose daemon lost the name to another one still loading
connects within it. -/
private abbrev socketWaitFloorMs : Nat := 3000

/-- The longest `connectUpsert` waits for the socket of a daemon it spawned. -/
private abbrev socketWaitCapMs : Nat := 30000

/-- The name's end record on disk, as a daemon keeps it. -/
private def recordFile (name : String) : Daemon.RecordFile :=
  { load := Record.load name, save := Record.save name, restore := Record.restore name }

/-- A command named a session that does not exist: say so; it found the name `missing`, as a
shell answers for a command it cannot find. -/
private def noSession (env : Env) (name : String) : IO Found := do
  say env s!"no session '{name}'"
  return .missing

/-- Why nothing starts over the name's checkpoint when its bytes do not decode
(`Recovery.decide`): it is damaged, it stays as it is, and `linger kill` discards it. -/
private def undecodedText (s : Names.Ref) : IO String := do
  return s!"its checkpoint {← Paths.ckptPath s.id} is damaged and does not decode, so it stays \
    as it is; linger kill {s.name} discards it"

/-- What a refusal of `Recovery.decide` finds: no session holds the name, or its checkpoint does
not decode. -/
private def recoveryFound (answer : Answer) : Found :=
  if answer == .notFound then .missing else .refused

/-- Why a command that found no live session starts nothing, as `Recovery.decide` answered: no
session holds the name, or its checkpoint does not decode. -/
private def refusalText (s : Names.Ref) (answer : Answer) : IO String := do
  if answer == .notFound then
    return s!"no session '{s.name}'"
  return s!"session '{s.name}': {← undecodedText s}"

/-- Say why a command that found no live session starts nothing, as `Recovery.decide`
answered, and find that: no session holds the name, or its checkpoint does not decode. -/
private def refused (env : Env) (s : Names.Ref) (answer : Answer) : IO Found := do
  say env (← refusalText s answer)
  return recoveryFound answer

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

/-- The daemon of the session `name`, with ID `id`, its program `cmd` run in `cwd`, as `__daemon`
runs it. -/
def serveDaemon (id name cwd : String) (cmd : List String) : IO Unit := do
  Daemon.serve id name cwd cmd (← Resume.saver id) (Resume.dropCkpt id) (recoverFor { name, id })
      (recordFile id)

/-- The daemon `start` began. It reports what it did once, and a failure before that is reported
too: as `running` when a live session took the name first, else as linger's own failure. -/
def serveStart (report id name cwd : String) (argv : List String) : IO Unit := do
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

/-- Make the ticket of the request at `report`, then begin its daemon, `Env.exe` with `args` in
this namespace (`Paths.childArgs`); a daemon that could not begin leaves no ticket. -/
private def beginRequest (env : Env) (report log : String) (args : List String) : IO UInt32 := do
  IO.FS.withFile (ticketPath report) .writeNew fun _ => pure ()
  try
    spawnDetached env.exe ((← Paths.childArgs) ++ args).toArray log
  catch err =>
    discard <| takeTicket report
    throw err

/-- What `start` says when a session holds the name, `refused`: that it is running; for a saved
one whose checkpoint decodes, whether its program ended; and for one whose checkpoint does not,
which nothing resumes (`Recovery.decide`), that it is damaged and kept, and that `linger kill`
discards it. -/
private def startRefused (env : Env) (s : Names.Ref) (saved : Bool) : IO Found := do
  unless saved do
    say env s!"session '{s.name}' is running"
    return .refused
  if let .refuse .notDone := Linger.App.Recovery.decide false (← Resume.readCkpt s.id) then
    return ← refused env s .notDone
  let record := (← (Record.load s.id).toBaseIO).toOption.join
  match record.bind Linger.Session.Record.decode with
  | some (.ended outcome) =>
    say env
        s!"session '{s.name}' ended ({(Client.Ending.outcome outcome).describe}); attach to see \
        it, which discards it, or kill it to discard it"
  | _ =>
    say env s!"session '{s.name}' is saved; attach to resume it, or kill it to discard it"
  return .refused

/-- What `start` found once its wait ended: `done` exactly when the program runs (`Start.answer`);
`refused`, saying which session holds the name, for a refusal (`startRefused`); for a program
that could not start, the status a shell or `env` reports; and `late` when the daemon did not
answer in time, so it starts nothing. A report that is no report, or a daemon that ended without
one, is linger's own failure. -/
private def startStatus (env : Env) (s : Names.Ref) (log : String) (waited : Waited) : IO Found :=
  do
  match Linger.Session.Start.answer (waited matches .took _) (waited matches .told (some .started)),
    waited with
  | .started, _ =>
    return .done
  | .notStarted, .told (some .running) =>
    startRefused env s false
  | .notStarted, .told (some .saved) =>
    startRefused env s true
  | .notStarted, .told (some (.failed status why)) =>
    do
      say env s!"session '{s.name}' did not start: {Client.replyText "no reason" why}"
      return if Answer.ofCode status.toUInt32 == .notDone then .refused else .unstarted status
  | .notStarted, .told none =>
    do
      say env s!"session '{s.name}' did not start: the daemon's report is unreadable"
      return .unknown
  | .notStarted, .took true =>
    do
      say env
          s!"session '{s.name}' did not start: its daemon did not answer within \
        {startWaitMs / 1000} s, so it starts nothing (see {log})"
      return .late
  | .notStarted, .took false =>
    do
      say env s!"session '{s.name}' did not start: its daemon ended first (see {log})"
      return .unknown
  | .notStarted, _ =>
    do
      say env s!"session '{s.name}': its daemon ended without saying whether it started (see {log})"
      return .unknown

/-- `start`: run `argv` exactly, with no shell, in a new session named `name`, in this directory
and with this environment, and return once the program runs. A live or saved session, an ended
one included, that holds the name is refused, saying which, and never resumed (`Start.plan`);
the daemon decides again holding the name. A program that cannot start finds the status a shell
or `env` reports, 125 for its directory, 127 when not found and 126 when not runnable, and leaves
no session, checkpoint or record behind. A daemon that does not answer within `startWaitMs`
starts nothing, and `start` says so, `late`. -/
private def cmdStart (env : Env) (s : Names.Ref) (argv : List String) : IO Found := do
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
    startRefused env s false
  | .saved =>
    startRefused env s true
  | .take =>
    let report ← Paths.startReportPath s.id s!"{← getpid}-{← IO.rand 0 0xFFFFFFFF}"
    let cwd := (← IO.Process.getCurrentDir).toString
    let log ← Paths.logPath s.id
    let pid ← beginRequest env report log (["__start", report, s.id, s.name, cwd] ++ argv)
    startStatus env s log (← awaitReport pid report)

/-- The daemon `resume` began: `serveStart`'s, running only a saved session's program again. -/
def serveResume (report id name cwd : String) : IO Unit := do
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

/-- The daemon that takes over the session the image this one replaced handed over at `path`, as
`__upgraded` runs it, its program the process `pid`. -/
def serveUpgraded (id path : String) (pid : UInt32) : IO Unit := do
  Daemon.adopt id path pid (← Resume.saver id) (Resume.dropCkpt id) (recordFile id)

/-- A resumed session whose directory is gone runs in `$HOME`: say where it runs and where it was
saved, from its info fields start_dir and saved_dir. -/
private def sayMoved (env : Env) (s : Names.Ref) : IO Unit := do
  if let some (.ok info)← queryInfo s.id then
    if let some saved := info.lookup "saved_dir" then
      let ran := (info.lookup "start_dir").getD "$HOME"
      say env s!"session '{s.name}' resumed in {ran}: its directory {saved} is gone"

/-- What `resume` found once its wait ended: `done` exactly when the program runs
(`Start.answer`), again, saying where when its directory is gone, or in a live session that
already runs it; `missing`, as for a session that does not exist, when no session holds the name;
for a saved session that cannot be read or a program that cannot start, the status a shell or
`env` reports; and `late` when the daemon did not answer in time, so it starts nothing. A report
that is no report, or a daemon that ended without one, is linger's own failure. -/
private def resumeStatus (env : Env) (s : Names.Ref) (log : String) (waited : Waited) : IO Found :=
  do
  let runs := waited matches .told (some .started) || waited matches .told (some .running)
  match Linger.Session.Start.answer (waited matches .took _) runs, waited with
  | .started, .told (some .started) =>
    do
      sayMoved env s
      return .done
  | .started, _ =>
    return .done
  | .notStarted, .told (some (.failed status why)) =>
    if Answer.ofCode status.toUInt32 == .notFound then
      noSession env s.name
    else
      do
        say env s!"session '{s.name}' did not resume: {Client.replyText "no reason" why}"
        return if Answer.ofCode status.toUInt32 == .notDone then .refused else .unstarted status
  | .notStarted, .told _ =>
    do
      say env s!"session '{s.name}' did not resume: the daemon's report is unreadable"
      return .unknown
  | .notStarted, .took true =>
    do
      say env
          s!"session '{s.name}' did not resume: its daemon did not answer within \
        {startWaitMs / 1000} s, so it starts nothing (see {log})"
      return .late
  | .notStarted, .took false =>
    do
      say env s!"session '{s.name}' did not resume: its daemon ended first (see {log})"
      return .unknown
  | .notStarted, .silent =>
    do
      say env s!"session '{s.name}': its daemon ended without saying whether it resumed (see {log})"
      return .unknown

/-- Before an attach or a resume of `name` with no daemon: write the latest tmux-resurrect save's
pane of that name as its checkpoint when no record names it (`Source.adopt`), so the
command resumes it as a saved session; a name a record came to name meanwhile keeps it, and the
command goes on with the session that is there, saying so. -/
private def adoptPane (env : Env) (name : String) : IO Unit := do
  if ← env.source.adopt name then
    say env s!"session '{name}' exists; using it, not the saved tmux pane"

/-- `resume`: run a saved session's program again, an ended session's included, in its saved
directory and on its last screen, without attaching, and return once it runs. A live session is
left as it is, a name no record names resumes the latest tmux-resurrect save's pane of that name
(`adoptPane`), and any other name no session holds starts nothing (`Start.resumePlan`); the
daemon decides again holding the name. A daemon that does not answer within `startWaitMs` starts
nothing, and `resume` says so, `late`. -/
private def cmdResume (env : Env) (s : Names.Ref) : IO Found := do
  adoptPane env s.name
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
    noSession env s.name
  | .resume =>
    let report ← Paths.startReportPath s.id s!"{← getpid}-{← IO.rand 0 0xFFFFFFFF}"
    let cwd := (← IO.Process.getCurrentDir).toString
    let log ← Paths.logPath s.id
    let pid ← beginRequest env report log ["__resume", report, s.id, s.name, cwd]
    resumeStatus env s log (← awaitReport pid report)

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
private def connectUpsert (env : Env) (s : Names.Ref) (cmd : List String) :
    IO (Except Answer UInt32) := do
  match ← Client.connect s.id with
  | some fd =>
    return .ok fd
  | none =>
    -- Recovery, including its saved cwd, happens only after the daemon owns
    -- both resources. A parent-side load would race another runtime namespace.
    let cwd := (← IO.Process.getCurrentDir).toString
    let pid ← spawnDaemon env s cwd cmd
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
      sayMoved env s
      return .ok fd
    | none =>
      let log ← Paths.logPath s.id
      throw (IO.userError s!"daemon for '{s.name}' did not come up (see {log})")

/-- Reject an operand that is neither an exact name nor a well-formed `name@host` target: say the
name rule; it is `invalid`. -/
private def invalidTarget (env : Env) : IO Found := do
  say env s!"invalid session name or malformed name@host target (use {Paths.nameRule})"
  return .invalid

/-- One transport boundary for all session verbs. The host's transport, which the remotes file
gives it or else ssh (`Remote.transportFor`), runs linger there: its attach command for an attach,
which gives the far end a terminal, and its query command for every other verb. Linger hands it
`linger` and words every shell passes on as they are (`transport_exact`), the verb and every word,
empty ones included, encoded: ssh joins them into the line `Remote.command` spells, and a command
such as `docker exec` runs them as they are. Encoding doubles a word's length, and a Linux host
takes a command line of at most 128 KiB, so `send name@host -`, whose inherited stdin stays
byte-exact, carries longer text. The remote linger reads an attach or capture target with
`targetArgs`, so it travels as `targetOperands`; the other verbs take it by position
(`Remote.operands`). The transport's status, the remote command's, is what a remote target
finds. The caller runs the transport (`Remote.run`), and with no `Env.remote` a remote target is
refused, no transport run. -/
private def runTarget (env : Env) (verb : String) (target : Linger.Target.Remote.Target)
    (args : List String) (localAction : String → IO Found) (options : List String := []) :
    IO Found := do
  let interactive := verb == "attach"
  if interactive && (!(← stdinIsTty) || !(← (← IO.getStdout).isTty)) then
    throw
        (IO.userError
          s!"{verb} needs terminal input and output (use `start`, `resume` or `send` for scripting)")
  match target.host with
  | none =>
    localAction target.name
  | some host =>
    let some remote := env.remote |
      do
        say env s!"no transport reaches '{Linger.Target.Remote.scrub host}': this caller runs none"
        return .refused
    let transport := Linger.Target.Remote.transportFor (← remote.config) host
    match Linger.Target.Remote.targetArgv transport verb options target.name args with
    | [] =>
      throw (IO.userError s!"remote host '{Linger.Target.Remote.scrub host}' has no command")
    | argv =>
      return .status (← remote.run interactive argv)

/-- Run `verb` through `runTarget` once `Remote.parseTarget` accepts the operand; a
malformed operand is `invalid` (`invalidTarget`) without connecting. -/
private def withTarget (env : Env) (verb target : String) (args : List String)
    (localAction : String → IO Found) (options : List String := []) : IO Found :=
  match Linger.Target.Remote.parseTarget target with
  | none => invalidTarget env
  | some parsed => runTarget env verb parsed args localAction options

/-- `withTarget`, its local action given the session the name leads to now (`Names.find`): every
file of the session is the ID's for the rest of the command, whatever renames follow. A name that
leads to no session's ID is no session (`noSession`). -/
private def withSession (env : Env) (verb target : String) (args : List String)
    (localAction : Names.Ref → IO Found) (options : List String := []) : IO Found :=
  withTarget env verb target args
    (fun name => do
      match ← Names.find name with
      | some s =>
        localAction s
      | none =>
        noSession env name)
    options

/-- `withTarget` for a command that may create a session, its local action given the ID the name
leads to, or a fresh one with an entry for the name when it leads nowhere (`Names.claim`). -/
private def withNew (env : Env) (verb target : String) (args : List String)
    (localAction : Names.Ref → IO Found) (options : List String := []) : IO Found :=
  withTarget env verb target args
    (fun name => do
      localAction (← Names.claim name))
    options

/-- Maximum simultaneous remote overview commands. -/
abbrev remoteQueryLimit : Nat := 4

/-- All remote overview commands share this polling window. -/
abbrev remoteQueryTimeoutMs : Nat := 3000

/-- Remote hosts for `-r`, each with its transport: the explicit flag list, each host with the
transport the remotes file gives it or else ssh, or, for `-r` with no list, the file's hosts
(`Remote.config`). Duplicates are a hard error (`Remote.checkHosts`). `none` means no `-r` (local
only); `some []` means `-r` with no arg (read the file). With no `Env.remote`, `-r` is refused. -/
private def resolveRemotes (env : Env) (flag : Option (List String)) :
    IO (Option (List (String × Linger.Target.Remote.Transport))) := do
  match flag, env.remote with
  | none, _ =>
    return some []
  | some _, none =>
    say env "no transport reaches a remote host: this caller runs none"
    return none
  | some given, some remote =>
    let config ← remote.config
    if given.isEmpty then
      return some config
    let hosts :=
      (given.map (·.trimAscii.toString)).filter (fun h => !h.isEmpty && !h.startsWith "#")
    match Linger.Target.Remote.checkHosts hosts with
    | .ok l =>
      return some (l.map fun host => (host, Linger.Target.Remote.transportFor config host))
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
gives and an attached title shows, computed in the calling process. A daemon whose end record
says what it saw is not asked. -/
private def summaryText : IO String := do
  let rows ← localRows (some ((← monotonicMs) + 250)) (statusOnly := true)
  return Linger.Display.Status.summary
      (rows.map fun info => (Linger.Display.Listing.statusOf info).attention)

/-- One attention sample for a client attached to `own`: the summary `summaryText` gives, each
local session's attention, and a notification for each session that changed into asking since
`previous`, other than `own` (`Alert.announce`), with its notification's text, which only those
sessions are asked for, or `bell`. -/
private def attentionSample (own : String)
    (previous : Option (List (String × Linger.Display.Status.Attention))) : IO Client.Sample := do
  let rows ← localRows (some ((← monotonicMs) + 250)) (statusOnly := true)
  let statuses :=
    rows.map fun info =>
      ((info.lookup "name").getD "", (Linger.Display.Listing.statusOf info).attention)
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

/-- What an attach finds that tells how a session ended, as its daemon reported it: its
program's ending, or `saved` with the signal for a session a signal to its daemon saved; an older
daemon's status is the program's. -/
private def endingFound : Client.Ending → Found
  | .outcome outcome => .ended (.program outcome)
  | .saved signal => .ended (.saved signal)
  | .status status => .status status

/-- Attach over `fd` once its daemon has said, in an `info` answer on `fd` within
`Client.replySilenceMs`, that it speaks this version's protocol (`Wire.admits`). Otherwise close
`fd`, say which session and which level its daemon reported, and find `refused`: a daemon an
older linger started refuses this version's attach as a message it does not know, one from
before the level was reported drops it without a reply, and one that does not answer would leave
the attach waiting for the detach key. -/
private def attachSpoken (env : Env) (name : String) (fd : UInt32) (mode : Linger.Session.Mode) :
    IO (Except Found Client.Outcome) := do
  let heard ←
    (Inventory.readInfo fd (some ((← monotonicMs) + Client.replySilenceMs.toNatClampNeg))).toBaseIO
  let level := (heard.toOption.bind (·.lookup "protocol")).bind String.toNat?
  if Linger.Session.Wire.admits level then
    return .ok (← Client.attach name fd (attentionSample name) (mode == .readOnly))
  close fd
  match heard, level with
  | .error why, _ =>
    say env s!"session '{name}' did not say which protocol it speaks ({why})"
  | .ok _, some level =>
    let which := if level < Linger.Session.Wire.protocol then "an older" else "a newer"
    say env
        s!"session '{name}' was started by {which} linger (protocol {level}); restart it, or \
          attach with that linger"
  | .ok _, none =>
    say env
        s!"session '{name}' was started by an older linger (no protocol level); restart it, or \
          attach with that linger"
  return .error .refused

/-- Discard the saved session `name` once a viewer has seen it, as `kill` discards one: delete its
checkpoint while holding the name, when it still holds `shown`, the bytes the viewer was shown, so
that a session resumed or replaced since is never lost. Its end record stays, for `wait` and
`ls`. A name another process holds, or a checkpoint that cannot be read or deleted, keeps the
session and says so. -/
private def discardShown (env : Env) (s : Names.Ref) (shown : ByteArray) : IO Unit := do
  let discarded ←
    try
      Paths.withSessionLock s.id do
          if (← Resume.readCkpt s.id).map (·.data) == some shown.data then
            Resume.dropCkpt s.id
      pure none
    catch err =>
      pure (some err.toString)
  if let some why := discarded then
    sayFresh env s!"session '{s.name}' was seen but not discarded: {why}"

/-- Take the steps `Recovery.visit` names for the saved session `name`, whose checkpoint held
`shown`, decoding to the screen `vt`, under the status the listing shows for it: `none` when the
session is to be resumed, and otherwise how the attach ended. A view a signal interrupts takes no
later step, so a session it may not have shown is kept; a view the viewer leaves goes on to tell
how the program ended and discard the session. -/
private def runVisit (env : Env) (s : Names.Ref) (shown : ByteArray) (vt : Terminal.Vt.Vt)
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
      discardShown env s shown
  return some result

/-- What an attach does with `name` when no daemon answers for it, from its end record and then,
unless the attach resumes it, its checkpoint, both read while holding the name: the result of a
program that ended, shown and then discarded, or a saved session viewed or, `none`, resumed
(`Recovery.visit`), or, when its checkpoint does not decode or there is none, the refusal
`Recovery.decide` answers. The record alone decides a resume, so a resume leaves the checkpoint
unread, to the daemon it starts. -/
private def visitOffline (env : Env) (s : Names.Ref) (readOnly : Bool) :
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
    return .ok (← runVisit env s shown ck.vt status steps)
  | .refuse answer, _ =>
    return .error answer
  | _, _ =>
    return .error .notFound

/-- A live connection is authoritative, once its daemon says it speaks this version's protocol
(`attachSpoken`), and the client attaches in `mode`. With no daemon, an offline checkpoint is
loaded with its end record while owning both resources and displayed after releasing them, under
the status the listing shows for it (`visitOffline`): a session whose program ended is a result,
which either mode shows, then tells how it ended and discards once the viewer leaves, since it has
been seen; read-only attachment views any other saved session, and writable attachment keeps the
create/resume path for it, starting `cmd`. Either refuses a checkpoint that does not decode, which
stays as it is (`Recovery.decide`). A writable attach to a name no record names resumes the latest
tmux-resurrect save's pane of that name (`adoptPane`). Live titles sample `attentionSample` in
this process. -/
private def cmdAttach (env : Env) (s : Names.Ref) (mode : Linger.Session.Mode) (cmd : List String) :
    IO Found := do
  let result : Except Found Client.Outcome ←
    if mode == .readOnly then
      match ← Client.connect s.id with
      | some fd =>
        attachSpoken env s.name fd mode
      | none =>
        match ← visitOffline env s true with
        | .ok (some outcome) =>
          pure (.ok outcome)
        | .ok none =>
          -- a watcher's visit never resumes (`visit_result`)
          .error <$> refused env s .notDone
        | .error answer =>
          .error <$> refused env s answer
    else
      -- a result is shown, not resumed: only a saved session that is no result, or none, takes
      -- the create/resume path, as does a name another process holds
      match ← Client.connect s.id with
      | some fd =>
        attachSpoken env s.name fd mode
      | none =>
        adoptPane env s.name
        match ← (visitOffline env s false).toBaseIO with
        | .ok (.ok (some outcome)) =>
          pure (.ok outcome)
        | _ =>
          match ← connectUpsert env s cmd with
          | .ok fd =>
            attachSpoken env s.name fd mode
          | .error answer =>
            .error <$> refused env s answer
  match result with
  | .error found =>
    return found
  | .ok (.ended (.saved signal)) =>
    -- the system stopping linger may have hung up this terminal too: the answer says it
    try
      sayFresh env
          s!"session '{s.name}' was saved when signal {signal} stopped its daemon; attach to \
            resume it"
    catch _ =>
      pure ()
    return endingFound (.saved signal)
  | .ok (.ended ending) =>
    sayFresh env s!"session '{s.name}' ended ({ending.describe})"
    return endingFound ending
  | .ok (.stopped signal) =>
    -- the terminal is handed back, but a hung-up one cannot show why: the answer says it, and
    -- `main` then ends the process by the signal
    try
      sayFresh env s!"signal {signal} stopped the attach; detached from '{s.name}'"
    catch _ =>
      pure ()
    return .stopped signal
  | .ok .detached =>
    sayFresh env s!"detached from '{s.name}'"
    return .done
  | .ok (.refused msg) =>
    sayFresh env msg
    return .refused
  | .ok (.lost why) =>
    sayFresh env s!"{why} for '{s.name}'"
    return .refused

/-- The rows of `ls`: local rows, then each remote host's rows named `name@host`, then the rows of
the latest tmux-resurrect save's panes no record names (`Source.rows`). Remote rows keep only
name, command, state and status, as the host's linger reports them; a host that does not answer
within the bounded wait is one record, its `host` with the status `?` no answer gives, which the
terminal listing names `@host`. Finds `stopped`, with the signal, when a signal stops it while it
queries remote hosts. -/
private def cmdList (env : Env) (porcelain : Bool)
    (remotes : List (String × Linger.Target.Remote.Transport)) : IO Reply := do
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
      return { found := .stopped signal }
  let mut rows := locals
  for ((host, _), output) in remotes.zip remote.toList do
    match output with
    | none =>
      rows := rows ++ [("host", host) :: Linger.Display.Listing.statusFields default]
    | some output =>
      for row in Linger.Target.Remote.parse output do
        -- a remote row is built from what the peer's porcelain says about identity
        -- and liveness. It also emits `clients` and its record fields; those are dropped
        -- rather than rendered, so a remote row's caption and watcher columns are
        -- blank whatever the peer reports.
        rows :=
          rows ++
            [[("name", s!"{row.name}@{host}"), ("cmd", row.cmd),
                  ("state", if row.live then "live" else "resumable")] ++
                Linger.Display.Listing.statusFields
                  (Linger.Display.Listing.rowStatus (.remote row.live row.attention row.status))]
  let records : Linger.Session.Records :=
    { sockets := (← Paths.listSocketNames).map (·.name),
      checkpoints := (← Paths.listCkptNames).map (·.name),
      endings := (← Paths.listRecordNames).map (·.name),
      entries := (← Names.load).flatMap fun (name, id) => [name, id] }
  return { found := .done, shown := .rows porcelain (rows ++ (← env.source.rows records)) }

/-- What a one-shot request found: `done` when the daemon completed it with `done`, otherwise
`refused` after saying why it did not complete. -/
private def requestStatus (env : Env) (name : String) (result : Client.Drained) : IO Found := do
  match result with
  | .done =>
    return .done
  | .refused why =>
    say env why
  | .lost why =>
    say env s!"{why} for '{name}'"
  | .exited ending =>
    say env s!"session '{name}' ended before the request completed ({ending.describe})"
  | .silent =>
    say env s!"no reply from '{name}'"
  return .refused

/-- Bytes a reply carries that a request does not show. -/
private def unshown (_ : ByteArray) : IO Unit := pure ()

/-- One request to a live session, given up after `Client.replySilenceMs` of silence, as every
one-shot request is (`Client.oneShot`). -/
private def requireLive (env : Env) (s : Names.Ref) (m : Msg) : IO Found := do
  match ← Client.oneShot s.id m unshown with
  | none =>
    noSession env s.name
  | some result =>
    requestStatus env s.name result

/-- Like `requireLive`, but delivers `ms` without awaiting a reply: `send` text. -/
private def requireLiveSend (env : Env) (s : Names.Ref) (ms : List Msg) : IO Found := do
  if ← Client.sendOnly s.id ms then
    return .done
  noSession env s.name

/-- What `capture` of a saved session has to show once it has rendered: the session, or why
there is none, with what it found. -/
private inductive Captured where
  /-- The saved session, rendered. -/
  | session (bytes : List UInt8)
  /-- None: no session holds the name, or its checkpoint does not decode, as `why` says. -/
  | refusal (found : Found) (why : String)

/-- Run the steps of `plan` through `run`, in order, in the phases `Capture.phases` cuts them into,
which hold the locks where `Capture.work` reads them held (`capture_waits_unlocked`): each locked
phase inside one `Paths.withSessionLock` of `name`, which takes both of the name's locks once and
lets them go however its steps end, and the other steps outside it. -/
private def runHolding (s : Names.Ref) (plan : List Linger.App.Capture.Step)
    (run : Linger.App.Capture.Step → IO Unit) : IO Unit := do
  for phase in Linger.App.Capture.phases plan do
    match phase with
    | .locked inside =>
      Paths.withSessionLock s.id (inside.forM run)
    | .unlocked step =>
      run step

/-- A connected daemon is authoritative, including its errors: the output frames of its reply to
`m` are what the capture shows. Only an absent connection followed by successful ownership
acquisition permits an offline read, which takes the steps of `Capture.plan`: it holds both locks
through loading and rendering, and lets them go before it writes what it rendered, to the bytes it
shows, so a reader that does not read holds up no attach or resume (`capture_waits_unlocked`).
Never start or modify a session. -/
private def cmdRead (env : Env) (s : Names.Ref) (m : Msg) (render : Terminal.Vt.Vt → List UInt8) :
    IO Reply := do
  let out ← IO.mkRef ByteArray.empty
  let sink (bytes : ByteArray) : IO Unit := out.modify (· ++ bytes)
  match ← Client.oneShot s.id m sink with
  | some result =>
    let found ← requestStatus env s.name result
    return { found, shown := .bytes (← out.get) }
  | none =>
    let file ← IO.mkRef (none : Option ByteArray)
    let shown ← IO.mkRef (Captured.refusal .missing (← refusalText s .notFound))
    let found ← IO.mkRef Found.unknown
    runHolding s Linger.App.Capture.plan fun
        | .load => do
          file.set (← Resume.readCkpt s.id)
        | .render => do
          match Linger.App.Recovery.decide false (← file.get) with
          | .resume ck =>
            shown.set (.session (render ck.vt))
          | .refuse refusal =>
            shown.set (.refusal (recoveryFound refusal) (← refusalText s refusal))
          | .fresh =>
            shown.set (.refusal .missing (← refusalText s .notFound))
        | .write => do
          match ← shown.get with
          | .session bytes =>
            sink (ByteArray.mk bytes.toArray)
            found.set .done
          | .refusal said why =>
            say env why
            found.set said
        | .acquire | .release => pure ()
    return { found := ← found.get, shown := .bytes (← out.get) }

/-- `send <name> -`: stdin to the session's pty, byte-exact, each read (≤ 64 KiB) in the
frames `Wire.inputFrames` cuts, each within the decoder's cap (`inputFrames_exact`). The agent's
raw input path — Enter, ^C, ESC, arrow sequences, exact whitespace: everything argv
cannot carry. Poll-then-read so EOF (`read` = `none`)
is distinguished from would-block (`some #[]`, looped past) without spinning;
no timeout on purpose — a slow producer feeding a pipe is legitimate, and every event the loop
answers, input, a reply or either side closing, wakes the poll. Stdin EOF
finds `done`, and a missing session `missing`; a refusal, an invalid reply, the session's exit
or a lost connection is `refused`. Nothing accumulates (each chunk is sent and dropped), so
no `Buf` is involved. -/
private def cmdSendStdin (env : Env) (s : Names.Ref) : IO Found := do
  match ← Client.connect s.id with
  | none =>
    noSession env s.name
  | some fd =>
    try
      let mut dec : Linger.Session.Wire.Decoder := {}
      let mut go := true
      while go do
        let revs ← poll #[stdinFd, fd] #[POLLIN, POLLIN] (-1)
        if revs[1]! &&& (POLLIN ||| POLLHUP ||| POLLERR) != 0 then
          match ← read fd 65536 with
          | none =>
            say env s!"connection lost for '{s.name}'"
            return .refused
          | some bs =>
            if !bs.isEmpty then
              let (dec', msgs) := dec.feed bs.toList
              dec := dec'
              if dec.errored then
                say env s!"invalid response from daemon for '{s.name}'"
                return .refused
              for m in msgs do
                match m with
                | .err msg =>
                  say env (Client.replyText "request refused" msg)
                  return .refused
                | .ended outcome =>
                  let ending := Client.Ending.outcome outcome
                  say env s!"session '{s.name}' ended while sending ({ending.describe})"
                  return .refused
                | .exited status =>
                  say env s!"session '{s.name}' ended while sending (status {status})"
                  return .refused
                | .saved signal =>
                  let ending := Client.Ending.saved signal
                  say env s!"session '{s.name}' ended while sending ({ending.describe})"
                  return .refused
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

/-- Say how the session ended when a signal killed its program, how its program ended is
unknown, or a signal to its daemon saved it, and that no session has the name when a kill
dismissed its tmux pane; an exit status says the rest. -/
private def sayEnding (env : Env) (name : String) : Linger.Session.Ending → IO Unit
  | .program (.exited _) => pure ()
  | .dismissed => say env s!"no session '{name}' (a kill dismissed its tmux pane)"
  | .program outcome =>
    say env s!"session '{name}' ended ({(Client.Ending.outcome outcome).describe})"
  | .saved signal =>
    say env
      s!"session '{name}' was saved when signal {signal} stopped its daemon; `linger resume \
          {name}` runs it again"

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

/-- One look at `name` for `wait` (`Wait.Heard`): its daemon's reply to `m`, given up after
`silenceMs` of silence, or, with no daemon to answer, its end record or that another process holds
it; with why, for a refusal or a held name. -/
private def hear (s : Names.Ref) (m : Msg) (silenceMs : Int32) : IO (Wait.Heard × String) := do
  match ← Client.oneShot s.id m unshown (untilDone := false) (silenceMs := silenceMs) with
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

/-- `wait`: block until the session ends and find what `Wait.decide` does with what each look
hears, saying why when that is not the program's own exit. The ending comes from its daemon or,
with no daemon to answer, from the name's end record once nothing else holds the name: the
program's, or `saved` with the signal for a session a signal to its daemon saved, whose program
did not end by itself, which exits with 128 plus the signal's number, as a shell's `wait` reports
a job that signal stopped; `missing`, as a shell's `wait` reports an unknown job, when no session
has taken the name. A daemon lost during the wait leaves its own record, never an older one. With
a `deadline` on the monotonic clock, which only a Lean caller gives, `late` once it has passed and
the session is still running, leaving the session as it is. A refusal is `refused`; linger could
not find out only for an unknown ending or a name held with no daemon answering for
`Wait.heldNameMs`, from the look that first found it so. -/
private def cmdWait (env : Env) (m : Msg) (deadline : Option Nat) (s : Names.Ref) : IO Found := do
  let mut heldSince : Option Nat := none
  repeat
    -- a silence budget ends a held wait when the time is up; `Int32` bounds one round of it
    let now ← monotonicMs
    let silenceMs : Int32 :=
      match deadline with
      | some limit => Int32.ofNat (min (limit - now) 2147483647)
      | none => -1
    let (heard, why) ← hear s m silenceMs
    match Wait.decide deadline heldSince (← monotonicMs) heard with
    | .answer found =>
      match found, heard with
      | .late, _ =>
        say env s!"timed out waiting for '{s.name}'"
      | _, .ended ending | _, .recorded (some ending) =>
        sayEnding env s.name ending
      | _, .recorded none =>
        say env s!"no session '{s.name}'"
      | _, .refused =>
        say env why
      | _, .held =>
        say env s!"no answer for '{s.name}': {why}"
      | _, _ =>
        pure ()
      return found
    | .again since =>
      heldSince := since
      if let some first := since then
        discard <| nap (first + Wait.heldNameMs) 20

/-- `cmdWait` of the session `name` leads to now (`Names.find`), which it waits for whatever
renames follow; a name that leads to none is no session. -/
private def waitNamed (env : Env) (m : Msg) (deadline : Option Nat) (name : String) : IO Found := do
  match ← Names.find name with
  | some s =>
    cmdWait env m deadline s
  | none =>
    noSession env name

/-- `wait` for each named session in turn and find what the last one's wait does, as a shell's
`wait` does with several jobs. A remote session's wait takes no deadline. -/
private def waitAll (env : Env) (m : Msg) (names : List String) (deadline : Option Nat) :
    IO Found := do
  if names.isEmpty then
    say env "wait names no session"
    return .invalid
  let some targets := names.mapM Linger.Target.Remote.parseTarget | invalidTarget env
  let mut found : Found := .done
  for target in targets do
    found ← runTarget env "wait" target [] (waitNamed env m deadline)
    if found == .late then
      return found
  return found

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

/-- What the daemon `kill` reached did with its request to end the session. -/
private inductive Taken where
  /-- It refused the request, saying why. -/
  | refused (why : String)
  /-- It took the request; `asked` is the start its `info` answer reported (`startOf`), or `none`
  when it reported none `kill` can tell it by. -/
  | took (asked : Option (String × String))

/-- The start a daemon's `info` answer reports, its program's pid and when it started, which tell
its session from every other session's, even one under the same name: `none` without a pid. -/
private def startOf (info : List (String × String)) : Option (String × String) :=
  (info.lookup "pid").map fun pid => (pid, (info.lookup "created").getD "")

/-- What a conversation that asked a daemon to end its session found: a refusal, or, however else
it ended, that the daemon took the request, which it answers by closing the connection. -/
private def tookOf (asked : Option (String × String)) : Client.Drained → Taken
  | .refused why => .refused why
  | _ => .took asked

/-- Ask the daemon of the session `id` which session it serves, `Wire.Msg.info`, and then to end
it, `m`, on one connection, so that what `kill` learns is of the daemon that takes `m`; `none` when
no daemon answers. A daemon that does not answer `info` within the one-shot reply budget is asked
`m` on a connection of its own, and is then one `kill` cannot tell from another. -/
private def askEnd (id : String) (m : Msg) : IO (Option Taken) := do
  let some fd ← Client.connect id | return none
  try
    match
      ← (readInfo fd (some ((← monotonicMs) + Client.replySilenceMs.toNatClampNeg))).toBaseIO with
    | .ok info =>
      return some (tookOf (startOf info) (← Client.oneShotOn fd m unshown))
    | .error _ =>
      pure ()
  finally
    close fd
  return (← Client.oneShot id m unshown).map (tookOf none)

/-- One look at the session `id`'s name for `kill`, once its daemon has taken the request to end
the session (`Kill.Heard`), with why another process holds the name: no process holds it; the
daemon `kill` asked, whose `info` reported the start `asked`, answers for it as itself; another
daemon answers for it; or a process holds it that `kill` cannot tell from the one it asked. -/
private def look (id : String) (asked : Option (String × String)) : IO (Kill.Heard × String) := do
  let held ←
    try
      Paths.withSessionLock id (pure none)
    catch err =>
      pure (some err.toString)
  let some why := held | return (.free, "")
  let some start := asked | return (.held, why)
  match
    ←
      queryInfo id (some ((← monotonicMs) + Client.replySilenceMs.toNatClampNeg))
          (retainUnavailable := false) with
  | some (.ok info) =>
    return (if startOf info == some start then .asked else .newer, why)
  | _ =>
    return (.held, why)

/-- `kill`: send `m` to the session's daemon, and find what `Kill.decide` does with what each look
at the name hears once the daemon has taken it. Its daemon stops the program (SIGHUP to its
terminal session, then SIGKILL after a second), tells whoever is attached or waiting how it ended,
records that and gives the name up, so the session has ended once no process holds the name, or
once a newer session does, which can take it only after that, and it says so. The daemon it asks
is the one that answers its `info` on the same connection (`askEnd`), told by the start it reports
(`startOf`): once that daemon has had `Wait.heldNameMs`, a session it still answers for as itself
has not ended, `refused`, and one whose name a process holds that `kill` cannot tell from it is
`unknown`, each said. With no daemon, a saved session is discarded instead, an ended one included,
whose end record stays for `wait` and `ls`, and a name no record names whose pane the latest
tmux-resurrect save has gets the end record a kill leaves, which hides the pane
(`Source.dismiss`). No session is `missing`; a refusal, or a saved session's name another process
holds, says why and is `refused`. -/
private def cmdKill (env : Env) (m : Msg) (s : Names.Ref) : IO Found := do
  match ← askEnd s.id m with
  | some (.refused why) =>
    say env why
    return .refused
  | some (.took asked) =>
    let taken ← monotonicMs
    repeat
      let (heard, why) ← look s.id asked
      match Kill.decide taken (← monotonicMs) heard with
      | .answer found =>
        match heard with
        | .newer =>
          say env s!"session '{s.name}' ended; the name now belongs to a newer session"
        | .asked =>
          say env s!"session '{s.name}' has not ended"
        | .held =>
          say env s!"could not find out whether session '{s.name}' ended: {why}"
        | .free =>
          pure ()
        return found
      | .again =>
        discard <| nap (taken + Wait.heldNameMs) 20
  | none =>
    match ← discardSaved s.id with
    | .ok true =>
      return .done
    | .ok false =>
      if ← env.source.dismiss s.name then
        return .done
      noSession env s.name
    | .error why =>
      say env why
      return .refused

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
decides, holding the names lock. It refuses, changing nothing, an invalid new name (`invalid`), an
old name no live or saved session has (`missing`), and, `refused`, a new name a live or saved
session has, an ended one still listed included, and a session whose daemon an older linger
started, which a newer linger's `upgrade` moves onto this one. The session keeps its ID, and with
it its program, its terminal, its clients, its waiters, its description and its status, and its
files stay where they are: only its name changes, the old name's entry moving to the new name, or
an entry made for it, neither replacing a name (`Names.move`, `Names.create`). An entry the new
name has whose session is gone is removed first, holding that session's ID, as is a name that is
its own free ID held, so that no start takes the new name meanwhile; a start that places it first
wins, and the rename then refuses. -/
private def cmdRename (env : Env) (new old : String) : IO Found := do
  -- a new name is clean text; an older key that starts with `-` stays reachable, but is no new name
  let valid := Linger.Target.Name.usable new
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
    say env s!"invalid session name '{new}' (use {Paths.nameRule})"
    return .invalid
  | .refuse .missing =>
    noSession env old
  | .refuse .taken =>
    say env s!"session '{new}' exists, and rename replaces no session"
    return .refused
  | .refuse .older =>
    say env
        s!"session '{old}' was started by an older linger, which cannot rename it; `linger \
          upgrade {old}` moves it onto this linger, or restart it"
    return .refused

/-- `ls name...`: the named sessions' listing rows, as `ls` lists them, in the order named, each a
session's fields as its daemon reports them, then its name, state and status; with no daemon or
checkpoint for a name, its name and how the last session to hold it ended
(`Session.endingFields`), from its end record, or with no record of it, the row of the latest
tmux-resurrect save's pane of that name. A `name@host` target is listed by its host's linger. A
name no session has taken is `missing`; one another process holds with no daemon answering says
why and is `refused`. -/
private def cmdListNamed (env : Env) (porcelain : Bool) (names : List String) : IO Reply := do
  let some targets := names.mapM Linger.Target.Remote.parseTarget |
    do
      return { found := ← invalidTarget env }
  let rows ←
    localRows (only :=
        some (targets.filterMap fun t => if t.host.isNone then some t.name else none))
  let mut found : Found := .done
  let mut shown : List (List (String × String)) := []
  for target in targets do
    if target.host.isSome then
      found :=
        worse found
          (←
            runTarget env "ls" target [] (fun _ => pure .done)
                (if porcelain then ["--porcelain"] else []))
    else
      match rows.find? (·.lookup "name" == some target.name) with
      | some row =>
        shown := shown ++ [row]
      | none =>
        match ← (← Names.find target.name).mapM (unanswered ·.id) with
        | none =>
          found := worse found (← noSession env target.name)
        | some (.recorded (some ending)) =>
          shown := shown ++ [("name", target.name) :: Linger.Session.endingFields ending]
        | some (.recorded none) =>
          match ← env.source.row target.name with
          | some row =>
            shown := shown ++ [row]
          | none =>
            found := worse found (← noSession env target.name)
        | some (.held why) =>
          say env s!"no answer for '{target.name}': {why}"
          found := worse found .refused
  return { found, shown := .rows porcelain shown }

/-- How long `upgrade` waits for a daemon's answer: its probe of the new binary, its saves and the
new image's start, which a loaded host slows. -/
private def upgradeWaitMs : Int32 := 60000

/-- `upgrade` of one live session: ask its daemon to replace its image with `Env.exe`, which
carries the session over, its program running on (`Msg.upgrade`). A daemon whose `info` names no
handoff format was started by an older linger, which cannot hand its session over, so it is not
asked, and keeps running; a daemon that refuses keeps running and says why. -/
private def upgradeOne (env : Env) (s : Names.Ref) : IO Found := do
  match ← queryInfo s.id with
  | none =>
    noSession env s.name
  | some (.error err) =>
    say env s!"{err} for '{s.name}'"
    return .refused
  | some (.ok info) =>
    if (info.lookup "handoff").isNone then
      say env s!"session '{s.name}' was started by an older linger; it keeps running"
      return .refused
    let request := Msg.upgrade env.exe.toUTF8.toList
    match ← Client.oneShot s.id request unshown (silenceMs := upgradeWaitMs) with
    | none =>
      noSession env s.name
    | some result =>
      requestStatus env s.name result

/-- `upgrade [name...]`: `upgradeOne` of each named session, `name@host` on its host, or of every
local live one when none is named, finding the worst of what they found and showing the sessions
it carried over. -/
private def cmdUpgrade (env : Env) (names : List String) : IO Reply := do
  let names ←
    if names.isEmpty then
      let table ← Names.load
      pure ((← Paths.listSocketNames).filterMap (Linger.Session.Names.nameOf table ·.name))
    else
      pure names
  let mut found : Found := .done
  let mut upgraded : List String := []
  for name in names do
    let one ← withSession env "upgrade" name [] (upgradeOne env)
    if one == .done && (Linger.Target.Remote.parseTarget name).any (·.host.isNone) then
      upgraded := upgraded ++ [name]
    found := worse found one
  return { found, shown := .upgraded upgraded }

/-- `ls`: the attention counts, the sessions as a tmux-resurrect save, or a listing of every
session, the remote hosts' too with `-r`, or of the named ones. -/
private def cmdView (env : Env) : View → IO Reply
  | .summary => do
    return { found := .done, shown := .text (← summaryText) }
  | .resurrect => do
    return { found := .done, shown := .text (← env.source.save) }
  | .every porcelain hosts => do
    match ← resolveRemotes env hosts with
    | some remotes =>
      cmdList env porcelain remotes
    | none =>
      return { found := .refused }
  | .named porcelain names => cmdListNamed env porcelain names

/-- A reply that shows nothing, once `action` has found what it found. -/
private def reply (action : IO Found) : IO Reply := do
  return { found := ← action }

/-- **Perform a request**: take the transition `plan` gives it (`op_meaning`), in the namespace
`Env.dirs`, through the one command of its operation, and give back what it found and what it
shows. This is the one place a request reaches its operation. A `deadline` on the monotonic
clock bounds a wait, for a Lean caller, which cannot run `timeout(1)` around a call. An error the
operation throws is said, and found `refused`. -/
def perform (env : Env) (request : Request) (deadline : Option Nat := none) : IO Reply :=
  Paths.withDirs env.dirs do
    try
      match request, plan request with
      | .attach _ target _, .attach mode command =>
        if mode == .readOnly then
          reply
              (withSession env "attach" target command (cmdAttach env · mode command)
                ["--read-only"])
        else
          reply (withNew env "attach" target command (cmdAttach env · mode command))
      | .list _, .list view =>
        cmdView env view
      | .start target _ _, .start program args =>
        reply (withNew env "start" target (program :: args) (cmdStart env · (program :: args)))
      | .resume target, .resume =>
        reply (withSession env "resume" target [] (cmdResume env))
      | .send target (.text words), .deliver bytes =>
        reply
            (withSession env "send" target words
              (requireLiveSend env · (Linger.Session.Wire.inputFrames bytes)))
      | .send target .stdin, .pipe =>
        match env.input with
        | some bytes =>
          reply
              (withSession env "send" target ["-"]
                (requireLiveSend env · (Linger.Session.Wire.inputFrames bytes.toList)))
        | none =>
          reply (withSession env "send" target ["-"] (cmdSendStdin env))
      | .detach target, .ask m =>
        reply (withSession env "detach" target [] (requireLive env · m))
      | .kill target, .ask m =>
        reply (withSession env "kill" target [] (cmdKill env m))
      | .rename target _, .rename new =>
        reply (withTarget env "rename" target [new] (cmdRename env new))
      | .capture history target, .ask m =>
        let shown ← IO.mkRef Shown.nothing
        let found ←
          withSession env "capture" target []
              (fun s => do
                let captured ←
                  cmdRead env s m
                      (if history then Terminal.Render.history else Terminal.Render.screenText)
                shown.set captured.shown
                return captured.found)
              (if history then ["--history"] else [])
        return { found, shown := ← shown.get }
      | .resize target cols rows, .ask m =>
        reply (withSession env "resize" target [toString cols, toString rows] (requireLive env · m))
      | .wait targets, .ask m =>
        reply (waitAll env m targets deadline)
      | .upgrade targets, .upgrade =>
        cmdUpgrade env targets
      | .serve, .serve =>
        match env.serve with
        | some server =>
          reply server
        | none =>
          say env "serve needs its caller's server, which the command line passes"
          return { found := .refused }
      | _, _ =>
        -- `plan` gives each request its own operation's transition (`op_meaning`)
        return { found := .unknown }
    catch err =>
      say env err.toString
      return { found := .refused }

/-- `attach`: connect this process's terminal to the session `target`, read-only on request,
starting it with `command`, or the shell, when none holds the name; how the attach ended. -/
def attach (env : Env) (target : String) (readOnly : Bool := false) (command : List String := []) :
    IO Found := (·.found) <$> perform env (.attach readOnly target command)

/-- `ls`: the sessions as `view` reports them, and what the listing found. -/
def list (env : Env) (view : View) : IO Reply := perform env (.list view)

/-- `start`: run `program` with `args`, exactly, in a new session `target`. -/
def start (env : Env) (target program : String) (args : List String := []) : IO Found :=
  (·.found) <$> perform env (.start target program args)

/-- `resume`: run the saved or ended session `target`'s program again. -/
def resume (env : Env) (target : String) : IO Found := (·.found) <$> perform env (.resume target)

/-- `send`: deliver `input` to the session `target`'s program. -/
def send (env : Env) (target : String) (input : Input) : IO Found :=
  (·.found) <$> perform env (.send target input)

/-- `detach`: disconnect every client attached to the session `target`. -/
def detach (env : Env) (target : String) : IO Found := (·.found) <$> perform env (.detach target)

/-- `kill`: end the session `target`, or discard a saved one, and return once it has ended. -/
def kill (env : Env) (target : String) : IO Found := (·.found) <$> perform env (.kill target)

/-- `rename`: give the session `target` the name `new`. -/
def rename (env : Env) (target new : String) : IO Found :=
  (·.found) <$> perform env (.rename target new)

/-- `capture`: what the read of the session `target`'s screen, or history, found, and its
bytes. -/
def capture (env : Env) (target : String) (history : Bool := false) : IO (Found × ByteArray) := do
  let reply ← perform env (.capture history target)
  match reply.shown with
  | .bytes bytes =>
    return (reply.found, bytes)
  | _ =>
    return (reply.found, ByteArray.empty)

/-- `resize`: set the size of the session `target`, which no client is attached to. -/
def resize (env : Env) (target : String) (cols rows : Nat) : IO Found :=
  (·.found) <$> perform env (.resize target cols rows)

/-- `wait`: wait for the sessions' programs to end, and find how the last one ended; with a
`deadline` on the monotonic clock, `late` once it has passed. -/
def wait (env : Env) (targets : List String) (deadline : Option Nat := none) : IO Found :=
  (·.found) <$> perform env (.wait targets) deadline

/-- `upgrade`: carry the live sessions named, or every local one, over to `Env.exe`; what it
found, and the local sessions it carried over. -/
def upgrade (env : Env) (targets : List String := []) : IO (Found × List String) := do
  let reply ← perform env (.upgrade targets)
  match reply.shown with
  | .upgraded names =>
    return (reply.found, names)
  | _ =>
    return (reply.found, [])

end Linger.App.Api
