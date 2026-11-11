module

import Linger.Os.Shell
import Linger.Os.Env
import Linger.Session.Shell.Paths
import Linger.Session.Shell.Daemon
import Linger.Session.Shell.Client
import Linger.Session.Shell.Inventory
import Linger.Target.Remote
import Terminal.Render
import Linger.Display.Listing
import Linger.Display.View
import Linger.App.Commands
import Linger.Os.Shell.Command
import Linger.Session.Shell.Resume
import Linger.Session.Shell.Record
import Terminal.Mediation
import Std.Async.Signal
import Linger.Display.Status

public section

/-! # Linger.App.Shell — session argv dispatch

Verb surface: attach creates if needed; read-only attach and capture also
read offline checkpoints. Every session verb accepts an exact name or name@host.
`Main` routes terminal selection and import before
entering this session backend. Bare invocation reaches help; `ls` prints an
overview and exits. `__daemon` is the internal re-exec target of the detached
spawn.
-/

namespace Linger.App.Shell

open Linger.Session.Shell
open Linger.Session.Shell.Inventory
open Linger.Os.Shell
open Linger.Session.Wire (Msg)

/-- One line per command, from the command table, printed by help and bare invocation, or to
stderr when `overview` cannot parse the arguments as listing options. -/
private def usage : String := Linger.App.Commands.helpText

/-- A command's usage error, its row of the command table (`Commands.usageLine`), and exit
status 2. -/
private def usageError (word : String) : IO UInt32 := do
  if let some command := Linger.App.Commands.lookup word then
    IO.eprintln (Linger.App.Commands.usageLine command)
  return 2

/-- A removed command's word: what to use instead (`Commands.retired`), and exit status 2. -/
private def retiredCommand (word : String) : IO UInt32 := do
  if let some advice := Linger.App.Commands.retired.lookup word then
    IO.eprintln s!"linger: {word} was removed: {advice}"
  return 2

/-- What `linger help` prints after the commands: the seven statuses a session can show, which
of them titles and `ls --summary` count, and the exit statuses every command shares. -/
private def helpFooter : String :=
  let glyphs :=
    String.intercalate " "
      (Linger.Display.Status.attention.map fun status =>
        String.singleton (Linger.Display.Status.icon status))
  String.intercalate "\n"
    (["", "Statuses"] ++ Linger.Display.Status.legend.map ("  " ++ ·) ++
      [s!"Titles and ls --summary count {glyphs}", "",
        "Exit status: the program's own, when the command waits for it to end; otherwise",
        "0 done, 1 refused or failed, 2 usage, 124 timed out, 125 linger failed, 126 cannot run,",
        "127 not found, 130 interrupted"])

/-- Start `name`'s daemon detached, running this executable as `__daemon name cwd cmd...`
with its output appended to `Paths.logPath`. Returns the daemon's pid once that program
has started, without waiting for it to listen; `connectUpsert` waits for the socket. -/
private def spawnDaemon (name cwd : String) (cmd : List String) : IO UInt32 := do
  let self ← IO.appPath
  let log ← Paths.logPath name
  spawnDetached self.toString (⟨["__daemon", name, cwd] ++ cmd⟩ : Array String) log

/-- How long `connectUpsert` waits for the socket whether or not the daemon it spawned
still lives: a concurrent start whose daemon lost the name to another one still loading
connects within it. -/
private abbrev socketWaitFloorMs : Nat := 3000

/-- The longest `connectUpsert` waits for the socket of a daemon it spawned. -/
private abbrev socketWaitCapMs : Nat := 30000

/-- The name's end record on disk, as a daemon keeps it. -/
private def recordFile (name : String) : Daemon.RecordFile :=
  { load := Record.load name, save := Record.save name, restore := Record.restore name }

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
too: as `running` when a live session took the name first, else as a failure, 125. -/
private def serveStart (report name cwd : String) (argv : List String) : IO Unit := do
  let req ← daemonRequest report
  let told ← IO.mkRef false
  let tell (r : Linger.Session.Start.Report) : IO Unit := do
    told.set true
    req.tell r
  try
    Daemon.serve name cwd argv (← Resume.saver name) (Resume.dropCkpt name) (Resume.loadCkpt name)
        (recordFile name) (some { req with tell })
  catch err =>
    unless ← told.get do
      match ← Client.connect name with
      | some fd =>
        close fd
        tell .running
      | none =>
        tell (.failed 125 err.toString.toUTF8.toList)
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

/-- A command named a session that does not exist: say so and return 127, which a shell reports
for a command it cannot find. -/
private def noSession (name : String) : IO UInt32 := do
  IO.eprintln s!"linger: no session '{name}'"
  return 127

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

/-- What `start` says when a session holds the name, 1: that it is running, or for a saved one
whether its program ended. -/
private def startRefused (name : String) (saved : Bool) : IO UInt32 := do
  if saved then
    let record := (← (Record.load name).toBaseIO).toOption.join
    match record.bind Linger.Session.Record.decode with
    | some (.ended outcome) =>
      IO.eprintln
          s!"linger: session '{name}' ended ({(Client.Ending.outcome outcome).describe}); \
          kill it to discard it, or attach to resume it"
    | _ =>
      IO.eprintln
          s!"linger: session '{name}' is saved; attach to resume it, or kill it to discard it"
  else
    IO.eprintln s!"linger: session '{name}' is running"
  return 1

/-- `start`'s status once its wait ended: 0 exactly when the program runs (`Start.answer`); 1,
saying which session holds the name, for a refusal (`startRefused`); for a program that could not
start, the status a shell or `env` reports; and 124 when the daemon did not answer in time, so it
starts nothing. A report that is no report, or a daemon that ended without one, is linger's own
failure, 125. -/
private def startStatus (name log : String) (waited : Waited) : IO UInt32 := do
  match Linger.Session.Start.answer (waited matches .took _) (waited matches .told (some .started)),
    waited with
  | .started, _ =>
    return 0
  | .notStarted, .told (some .running) =>
    startRefused name false
  | .notStarted, .told (some .saved) =>
    startRefused name true
  | .notStarted, .told (some (.failed status why)) =>
    do
      IO.eprintln s!"linger: session '{name}' did not start: {Client.replyText "no reason" why}"
      return status.toUInt32
  | .notStarted, .told none =>
    do
      IO.eprintln s!"linger: session '{name}' did not start: the daemon's report is unreadable"
      return 125
  | .notStarted, .took true =>
    do
      IO.eprintln
          s!"linger: session '{name}' did not start: its daemon did not answer within \
        {startWaitMs / 1000} s, so it starts nothing (see {log})"
      return 124
  | .notStarted, .took false =>
    do
      IO.eprintln s!"linger: session '{name}' did not start: its daemon ended first (see {log})"
      return 125
  | .notStarted, _ =>
    do
      IO.eprintln
          s!"linger: session '{name}': its daemon ended without saying whether it started \
        (see {log})"
      return 125

/-- `start`: run `argv` exactly, with no shell, in a new session named `name`, in this directory
and with this environment, and return once the program runs. A live or saved session, an ended
one included, that holds the name is refused, saying which, and never resumed (`Start.plan`);
the daemon decides again holding the name. A program that cannot start returns what a shell or
`env` reports, 125 for its directory, 127 when not found and 126 when not runnable, and leaves
no session, checkpoint or record behind. A daemon that does not answer within `startWaitMs`
starts nothing, and `start` says so, 124. -/
private def cmdStart (name : String) (argv : List String) : IO UInt32 := do
  let live ←
    match ← Client.connect name with
    | some fd =>
      do
        close fd
        pure true
    | none =>
      pure false
  let saved ← System.FilePath.pathExists (← Paths.ckptPath name)
  match Linger.Session.Start.plan live saved with
  | .running =>
    startRefused name false
  | .saved =>
    startRefused name true
  | .take =>
    let report ← Paths.startReportPath name s!"{← getpid}-{← IO.rand 0 0xFFFFFFFF}"
    let cwd := (← IO.Process.getCurrentDir).toString
    let log ← Paths.logPath name
    let pid ← beginRequest report log (["__start", report, name, cwd] ++ argv)
    startStatus name log (← awaitReport pid report)

/-- The daemon `resume` began: `serveStart`'s, running only a saved session's program again. -/
private def serveResume (report name cwd : String) : IO Unit := do
  let req ← daemonRequest report
  let told ← IO.mkRef false
  let tell (r : Linger.Session.Start.Report) : IO Unit := do
    told.set true
    req.tell r
  try
    Daemon.serve name cwd [] (← Resume.saver name) (Resume.dropCkpt name) (Resume.loadCkpt name)
        (recordFile name) (some { req with tell }) (resume := true)
  catch err =>
    unless ← told.get do
      match ← Client.connect name with
      | some fd =>
        close fd
        tell .running
      | none =>
        tell (.failed 125 err.toString.toUTF8.toList)
    throw err

/-- A resumed session whose directory is gone runs in `$HOME`: say where it runs and where it was
saved, from its info fields start_dir and saved_dir. -/
private def sayMoved (name : String) : IO Unit := do
  if let some (.ok info)← queryInfo name then
    if let some saved := info.lookup "saved_dir" then
      let ran := (info.lookup "start_dir").getD "$HOME"
      IO.eprintln s!"linger: session '{name}' resumed in {ran}: its directory {saved} is gone"

/-- `resume`'s status once its wait ended: 0 exactly when the program runs (`Start.answer`), again,
saying where when its directory is gone, or in a live session that already runs it; 127, as for
a session that does not exist, when no session holds the name; for a saved session that cannot
be read or a program that cannot start, 1 or what a shell or `env` reports; and 124 when the
daemon did not answer in time, so it starts nothing. A report that is no report, or a daemon that
ended without one, is linger's own failure, 125. -/
private def resumeStatus (name log : String) (waited : Waited) : IO UInt32 := do
  let runs := waited matches .told (some .started) || waited matches .told (some .running)
  match Linger.Session.Start.answer (waited matches .took _) runs, waited with
  | .started, .told (some .started) =>
    do
      sayMoved name
      return 0
  | .started, _ =>
    return 0
  | .notStarted, .told (some (.failed 127 _)) =>
    noSession name
  | .notStarted, .told (some (.failed status why)) =>
    do
      IO.eprintln s!"linger: session '{name}' did not resume: {Client.replyText "no reason" why}"
      return status.toUInt32
  | .notStarted, .told _ =>
    do
      IO.eprintln s!"linger: session '{name}' did not resume: the daemon's report is unreadable"
      return 125
  | .notStarted, .took true =>
    do
      IO.eprintln
          s!"linger: session '{name}' did not resume: its daemon did not answer within \
        {startWaitMs / 1000} s, so it starts nothing (see {log})"
      return 124
  | .notStarted, .took false =>
    do
      IO.eprintln s!"linger: session '{name}' did not resume: its daemon ended first (see {log})"
      return 125
  | .notStarted, .silent =>
    do
      IO.eprintln
          s!"linger: session '{name}': its daemon ended without saying whether it resumed \
        (see {log})"
      return 125

/-- `resume`: run a saved session's program again, an ended session's included, in its saved
directory and on its last screen, without attaching, and return once it runs. A live session is
left as it is, and a name no session holds starts nothing (`Start.resumePlan`); the daemon decides
again holding the name. A daemon that does not answer within `startWaitMs` starts nothing, and
`resume` says so, 124. -/
private def cmdResume (name : String) : IO UInt32 := do
  let live ←
    match ← Client.connect name with
    | some fd =>
      do
        close fd
        pure true
    | none =>
      pure false
  let saved ← System.FilePath.pathExists (← Paths.ckptPath name)
  match Linger.Session.Start.resumePlan live saved with
  | .running =>
    return 0
  | .missing =>
    noSession name
  | .resume =>
    let report ← Paths.startReportPath name s!"{← getpid}-{← IO.rand 0 0xFFFFFFFF}"
    let cwd := (← IO.Process.getCurrentDir).toString
    let log ← Paths.logPath name
    let pid ← beginRequest report log ["__resume", report, name, cwd]
    resumeStatus name log (← awaitReport pid report)

/-- Connect, spawning the daemon first if needed (attach-is-upsert). Without a socket it
gives up no sooner than `socketWaitFloorMs`; after that it keeps waiting only while the
spawned daemon lives, never past `socketWaitCapMs`. -/
private def connectUpsert (name : String) (cmd : List String) : IO UInt32 := do
  match ← Client.connect name with
  | some fd =>
    return fd
  | none =>
    -- Recovery, including its saved cwd, happens only after the daemon owns
    -- both resources. A parent-side load would race another runtime namespace.
    let cwd := (← IO.Process.getCurrentDir).toString
    let pid ← spawnDaemon name cwd cmd
    let start ← monotonicMs
    let mut fdOpt : Option UInt32 := none
    while fdOpt.isNone && ((← monotonicMs) < start + socketWaitFloorMs || (← alive pid)) do
      unless ← nap (start + socketWaitCapMs) 30 do
        break
      fdOpt ← Client.connect name
    match fdOpt with
    | some fd =>
      sayMoved name
      return fd
    | none =>
      let log ← Paths.logPath name
      throw (IO.userError s!"daemon for '{name}' did not come up (see {log})")

/-- Reject an operand that is neither an exact name nor a well-formed `name@host` target:
print the name rule and return exit status 2. -/
private def invalidTarget : IO UInt32 := do
  IO.eprintln s!"linger: invalid session name or malformed name@host target (use {Paths.nameRule})"
  return 2

/-- One transport boundary for all session verbs. SSH interprets a command string
with a shell; `Remote.command` preserves the original argv, including empty words.
The remote linger reads an attach or capture target with `targetArgs`, so it travels
as `targetOperands`; the other verbs take it by position.
Inherited stdin keeps `send name@host -` byte-exact. -/
private def runTarget (verb : String) (target : Linger.Target.Remote.Target) (args : List String)
    (localAction : String → IO UInt32) (options : List String := []) : IO UInt32 := do
  let interactive := verb == "attach"
  if interactive && (!(← stdinIsTty) || !(← (← IO.getStdout).isTty)) then
    throw
        (IO.userError
          s!"{verb} needs terminal input and output (use `start`, `resume` or `send` for scripting)")
  match target.host with
  | none =>
    localAction target.name
  | some host =>
    let operands :=
      if verb == "attach" || verb == "capture" then Linger.Target.Remote.targetOperands target.name
      else [target.name]
    let child ←
      IO.Process.spawn
          { cmd := "ssh",
            args :=
              #[if interactive then "-t" else "-T", "--", host,
                Linger.Target.Remote.command verb (options ++ operands ++ args)],
            stdin := .inherit }
    try
      child.wait
    finally
      if interactive then
        writeAll stdoutFd (ByteArray.mk Terminal.Render.leaveAnsi.toArray)

/-- Run `verb` through `runTarget` once `Remote.parseTarget` accepts the operand; a
malformed operand returns `invalidTarget`'s status 2 without connecting. -/
private def withTarget (verb target : String) (args : List String)
    (localAction : String → IO UInt32) (options : List String := []) : IO UInt32 :=
  match Linger.Target.Remote.parseTarget target with
  | none => invalidTarget
  | some parsed => runTarget verb parsed args localAction options

/-- Maximum simultaneous remote overview commands. -/
abbrev remoteQueryLimit : Nat := 4

/-- All remote overview commands share this polling window. -/
abbrev remoteQueryTimeoutMs : Nat := 3000

/-- Remote hosts for `-r`: explicit flag list, else `Env.remotesFile`, which an
unset or empty HOME leaves unconfigured. Duplicates are a hard error
(`Remote.checkHosts`). `none` means no `-r` (local only); `some []` means `-r`
with no arg (read the file). -/
private def resolveRemotes (flag : Option (List String)) : IO (List String) := do
  match flag with
  | none =>
    return []
  | some given =>
    let raw ←
      if given.isEmpty then
        match Linger.Os.Env.remotesFile (← IO.getEnv "HOME") with
        | none =>
          pure []
        | some path =>
          if ← System.FilePath.pathExists path then
            pure ((← IO.FS.readFile path).splitOn "\n")
          else
            pure []
      else
        pure given
    let hosts := (raw.map (·.trimAscii.toString)).filter (fun h => !h.isEmpty && !h.startsWith "#")
    match Linger.Target.Remote.checkHosts hosts with
    | .ok l =>
      return l
    | .error e =>
      throw (IO.userError e)

/-- Four SSH jobs at most share a three-second command deadline. Transport
keepalives alone cannot bound a remote command that never exits. Collect only
complete successful outputs, in host order; stop and join every remaining group.
Signal waiters let a cancelled chooser's listing retire its isolated SSH groups. -/
private def listRemotes (hosts : Array String) : IO (Option (Array String)) := do
  let signals ← IO.mkRef (#[] : Array (Std.Async.Signal.Waiter × Std.Async.AsyncTask Int))
  let jobs ← IO.mkRef (#[] : Array (Nat × IO.Ref (Option Command.Job)))
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
    let mut outputs := Array.replicate hosts.size ""
    let mut next := 0
    while next < hosts.size || !(← jobs.get).isEmpty do
      for (_, signal) in ← signals.get do
        if (← signal.getState) == .finished then
          return none
      if (← monotonicMs) ≥ deadline then
        break
      while
        next < hosts.size && (← jobs.get).size < remoteQueryLimit && (← monotonicMs) < deadline do
        let index := next
        next := next + 1
        let pending ← IO.mkRef none
        jobs.modify (·.push (index, pending))
        try
          pending.set
              (some
                (←
                  Command.start "ssh"
                      #["-o", "BatchMode=yes", "-o", "ConnectTimeout=3", "-o",
                        "ServerAliveInterval=2", "-o", "ServerAliveCountMax=2", "--", hosts[index]!,
                        "linger", "ls", "--porcelain"]))
        catch _ =>
          pure ()
      let mut running := #[]
      for (index, pending) in ← jobs.get do
        try
          if let some output← Command.poll pending then
            if output.exitCode == 0 then
              outputs := outputs.set! index output.stdout
        catch _ =>
          pure ()
        if (← pending.get).isSome then
          running := running.push (index, pending)
      jobs.set running
      if !running.isEmpty then
        unless ← nap deadline 5 do
          break
    return some outputs
  finally
    for (_, pending) in ← jobs.get do
      try
        Command.stop pending
      catch _ =>
        pure ()
    for (waiter, _) in ← signals.get do
      waiter.stop

/-- Local attention counts under one 250 ms reply window: the text `ls --summary`
prints and an attached title shows, computed in the calling process. A daemon whose end record
says what it saw is not asked. -/
private def summaryText : IO String := do
  let rows ← localRows (some ((← monotonicMs) + 250)) (statusOnly := true)
  return Linger.Display.Status.summary
      (rows.map fun info => Linger.Display.Status.ofName ((info.lookup "status").getD "unknown"))

/-- `ls --summary`: print `summaryText`, or nothing when no local session needs
attention; exit 0 either way. -/
private def cmdSummary : IO UInt32 := do
  let summary ← summaryText
  if !summary.isEmpty then
    IO.println summary
  return 0

/-- The exit status when no daemon answered for `name` and nothing saved could be read: 1 if a
checkpoint exists that will not load, else 127, as for a session that does not exist. -/
private def missingOrUnreadable (name : String) : IO UInt32 := do
  return if ← System.FilePath.pathExists (← Paths.ckptPath name) then 1 else 127

/-- A live connection is authoritative. Only read-only attachment can view an
offline checkpoint, loaded with its end record while owning both resources and displayed after
releasing them, under the status the listing shows for it. Writable attachment keeps the
create/resume path, which resumes an ended session too. Live titles sample `summaryText` in this
process. -/
private def cmdAttach (name : String) (cmd : List String) (readOnly : Bool) : IO UInt32 := do
  let result ←
    if readOnly then
      match ← Client.connect name with
      | some fd =>
        some <$> Client.attach name fd summaryText true
      | none =>
        let (checkpoint, record) ←
          Paths.withSessionLock name do
              return (← Resume.loadCkpt name, ← (Record.load name).toBaseIO)
        let status := Linger.Display.Listing.rowStatus (savedRow record).1
        checkpoint.mapM fun (vt, _, _) => Client.viewSaved name vt status
    else
      let fd ← connectUpsert name cmd
      some <$> Client.attach name fd summaryText
  let some result := result
    |
    IO.eprintln s!"linger: no live session or readable checkpoint for '{name}'"
    return ← missingOrUnreadable name
  match result with
  | .ended ending =>
    IO.eprintln s!"\r\nlinger: session '{name}' ended ({ending.describe})"
    return ending.exitStatus
  | .detached =>
    IO.eprintln s!"\r\nlinger: detached from '{name}'"
    return 0
  | .refused msg =>
    IO.eprintln s!"\r\nlinger: {msg}"
    return 1
  | .lost why =>
    IO.eprintln s!"\r\nlinger: {why} for '{name}'"
    return 1

/-- `ls`: local rows, then each remote host's rows named `name@host`, printed as
`k<TAB>v` records separated by blank lines (`porcelain`) or as the terminal listing.
Remote rows keep only name, command, state and status. Returns 130 when a signal
cancels the remote queries. -/
private def cmdList (porcelain : Bool) (remotes : List String) : IO UInt32 := do
  let (locals, remote) ←
    if remotes.isEmpty then
      pure (← localRows, some #[])
    else
      do
        let task ← IO.asTask localRows Task.Priority.dedicated
        try
          let remote ← listRemotes remotes.toArray
          let locals ← IO.ofExcept (← IO.wait task)
          pure (locals, remote)
        finally
          discard <| IO.wait task
  let some remote := remote | return 130
  let mut rows := locals
  for (host, output) in remotes.zip remote.toList do
    for row in Linger.Target.Remote.parse output do
      -- a remote row is built from what the peer's porcelain says about identity
      -- and liveness. It also emits `clients` and `label.*`; those are dropped
      -- rather than rendered, so a remote row's label and watcher columns are
      -- blank whatever the peer reports — see SCRATCHPAD 2026-09-15.
      rows :=
        rows ++
          [[("name", s!"{row.name}@{host}"), ("cmd", row.cmd),
              ("state", if row.live then "live" else "resumable"),
              ("status",
                Linger.Display.Status.name
                  (Linger.Display.Listing.rowStatus (.remote row.live row.status)))]]
  if porcelain then
    for info in rows do
      for (k, v) in info do
        IO.println s!"{k}\t{v}"
      IO.println ""
  else
    -- The selector consumes these same row pieces. Only the status badge has
    -- a palette style; redirected output and NO_COLOR retain the plain row. What asks for
    -- someone comes first, as in the selector (`View.sort`).
    let withColor := (← (← IO.getStdout).isTty) && (← IO.getEnv "NO_COLOR").isNone
    let ordered :=
      Linger.Display.View.sort
        (fun info => Linger.Display.Status.ofName ((info.lookup "status").getD "")) rows
    writeAll stdoutFd
        (ByteArray.mk (Linger.Display.Listing.terminalListing withColor ordered).toArray)
  return 0

/-- Parse the `ls` argument set: an optional `--porcelain` and an
optional `-r`/`--remote [hosts]`, in any order. `-r` followed by a
`-`-prefixed token (or nothing) means "use the file"; `-r hosts` is an
explicit comma list. Returns `none` on any unrecognized token. -/
def parseLs : List String → Option (Bool × Option (List String))
  | [] => some (false, none)
  | "--porcelain" :: rest => (parseLs rest).map (fun (_, r) => (true, r))
  | "-r" :: rest | "--remote" :: rest =>
    match rest with
    | h :: more =>
      if h.startsWith "-" then (parseLs (h :: more)).map (fun (p, _) => (p, some []))
      else (parseLs more).map (fun (p, _) => (p, some (h.splitOn ",")))
    | [] => some (false, some [])
  | _ => none

/-- Exit status of a one-shot request: 0 when the daemon completed it with `done`,
otherwise 1 after printing why it did not complete. -/
private def requestStatus (name : String) (result : Client.Drained) : IO UInt32 := do
  match result with
  | .done =>
    return 0
  | .refused why =>
    IO.eprintln s!"linger: {why}"
  | .lost why =>
    IO.eprintln s!"linger: {why} for '{name}'"
  | .exited ending =>
    IO.eprintln s!"linger: session '{name}' ended before the request completed ({ending.describe})"
  | .silent =>
    IO.eprintln s!"linger: no reply from '{name}'"
  return 1

/-- One request to a live session, given up after `Client.replySilenceMs` of silence, as every
one-shot request is (`Client.oneShot`). -/
private def requireLive (name : String) (m : Msg) : IO UInt32 := do
  match ← Client.oneShot name m with
  | none =>
    noSession name
  | some result =>
    requestStatus name result

/-- Like `requireLive`, but delivers `m` without awaiting a reply: `send` text and `kill`. -/
private def requireLiveSend (name : String) (m : Msg) : IO UInt32 := do
  if ← Client.sendOnly name m then
    return 0
  noSession name

/-- A connected daemon is authoritative, including its errors. Only an absent
connection followed by successful ownership acquisition permits an offline read.
Hold both locks through loading and rendering; never start or modify a session. -/
private def cmdRead (name : String) (m : Msg) (render : Terminal.Vt.Vt → List UInt8) : IO UInt32 :=
  do
  match ← Client.oneShot name m with
  | some result =>
    requestStatus name result
  | none =>
    Paths.withSessionLock name do
        match ← Resume.loadCkpt name with
        | some (vt, _, _) =>
          writeAll stdoutFd (ByteArray.mk (render vt).toArray)
          return 0
        | none =>
          IO.eprintln s!"linger: no live session or readable checkpoint for '{name}'"
          missingOrUnreadable name

/-- `send <name> -`: stdin to the session's pty, byte-exact, one `.input`
frame per read (≤ 64 KiB, so every frame satisfies `Msg.WF`). The agent's raw input
path — Enter, ^C, ESC, arrow sequences, exact whitespace: everything argv
cannot carry (agent-cli Decision 5). Poll-then-read so EOF (`read` = `none`)
is distinguished from would-block (`some #[]`, looped past) without spinning;
no timeout on purpose — a slow producer feeding a pipe is legitimate, and every event the loop
answers, input, a reply or either side closing, wakes the poll. Stdin EOF
returns 0, and a missing session 127; a refusal, an invalid reply, the session's exit or a
lost connection returns 1. Nothing accumulates (each chunk is sent and dropped), so no
`Buf` is involved. -/
private def cmdSendStdin (name : String) : IO UInt32 := do
  match ← Client.connect name with
  | none =>
    noSession name
  | some fd =>
    try
      let mut dec : Linger.Session.Wire.Decoder := {}
      let mut go := true
      while go do
        let revs ← poll #[stdinFd, fd] #[POLLIN, POLLIN] (-1)
        if revs[1]! &&& (POLLIN ||| POLLHUP ||| POLLERR) != 0 then
          match ← read fd 65536 with
          | none =>
            IO.eprintln s!"linger: connection lost for '{name}'"
            return 1
          | some bs =>
            if !bs.isEmpty then
              let (dec', msgs) := dec.feed bs.toList
              dec := dec'
              if dec.errored then
                IO.eprintln s!"linger: invalid response from daemon for '{name}'"
                return 1
              for m in msgs do
                match m with
                | .err msg =>
                  IO.eprintln s!"linger: {Client.replyText "request refused" msg}"
                  return 1
                | .ended outcome =>
                  let ending := Client.Ending.outcome outcome
                  IO.eprintln s!"linger: session '{name}' ended while sending ({ending.describe})"
                  return 1
                | .exited status =>
                  IO.eprintln s!"linger: session '{name}' ended while sending (status {status})"
                  return 1
                | _ =>
                  pure ()
        if revs[0]! &&& (POLLIN ||| POLLHUP ||| POLLERR) != 0 then
          match ← read stdinFd 65536 with
          | none =>
            go := false
          | some bs =>
            if !bs.isEmpty then
              Client.sendMsg fd (.input bs.toList)
      return 0
    finally
      close fd

/-- Return the status a shell would report for the ending, saying on stderr when a signal killed
the program or how it ended is unknown. -/
private def reportEnding (name : String) (ending : Client.Ending) : IO UInt32 := do
  match ending with
  | .outcome (.exited _) | .status _ =>
    pure ()
  | .outcome _ =>
    IO.eprintln s!"linger: session '{name}' ended ({ending.describe})"
  return ending.exitStatus

/-- What answers for a name when no daemon does. -/
private inductive Unanswered where
  /-- Another process holds the name, as a daemon does while it starts or ends; `why` says so. -/
  | held (why : String)
  /-- The name's end record says this (`Record.answer`), read while holding the name when the
  answer depends on it (`Record.settled`). -/
  | recorded (outcome : Option Linger.Session.Outcome)

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

/-- How long `wait` keeps trying a name that another process holds while no daemon answers on
it, as while a daemon starts or ends: past an ending daemon's drain and its program's stop. -/
private def heldNameMs : Nat := Daemon.drainTimeoutMs + 5000

/-- `wait`: block until the session's program ends and return the status a shell would report
for it (`reportEnding`). With no daemon to answer, the name's end record does once nothing else
holds the name: how the last session's program ended, or 127, as a shell's `wait` reports an
unknown job, when no session has taken the name. A daemon lost during the wait leaves its own
record, never an older one. With a `deadline` on the monotonic clock, 124 once it has passed and
the session is still running, as `timeout(1)` reports, leaving the session as it is. linger's
own failures, a refusal, a reply without a status or a name held past `heldNameMs`, print a
diagnostic and return 125. -/
private def cmdWait (deadline : Option Nat) (name : String) : IO UInt32 := do
  let heldUntil := (← monotonicMs) + heldNameMs
  repeat
    -- a silence budget ends a held wait when the time is up; `Int32` bounds one round of it
    let now ← monotonicMs
    let silenceMs : Int32 :=
      match deadline with
      | some limit => Int32.ofNat (min (limit - now) 2147483647)
      | none => -1
    match ← Client.oneShot name .wait (untilDone := false) (silenceMs := silenceMs) with
    | some (.exited ending) =>
      return ← reportEnding name ending
    | some .silent =>
      pure ()
    | some (.refused why) =>
      IO.eprintln s!"linger: {why}"
      return 125
    | some .done =>
      IO.eprintln s!"linger: no exit status from '{name}'"
      return 125
    | some (.lost _) | none =>
      match ← unanswered name with
      | .recorded none =>
        IO.eprintln s!"linger: no session '{name}'"
        return 127
      | .recorded (some outcome) =>
        return ← reportEnding name (.outcome outcome)
      | .held why =>
        unless ← nap heldUntil 20 do
          IO.eprintln s!"linger: no answer for '{name}': {why}"
          return 125
    if let some limit := deadline then
      if (← monotonicMs) ≥ limit then
        IO.eprintln s!"linger: timed out waiting for '{name}'"
        return 124

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

/-- `wait` for each named session in turn and return the last one's status, as a shell's `wait`
does with several jobs. With a time limit in milliseconds, all of them share one deadline, and
124 means it passed. -/
private def waitAll (names : List String) (limit : Option Nat) : IO UInt32 := do
  if names.isEmpty then
    return ← usageError "wait"
  let some targets := names.mapM Linger.Target.Remote.parseTarget | invalidTarget
  let deadline ←
    limit.mapM fun ms => do
        return (← monotonicMs) + ms
  let mut rc : UInt32 := 0
  for target in targets do
    let now ← monotonicMs
    let options :=
      match deadline with
      | some due => ["--timeout", secondsText (due - now)]
      | none => []
    rc ← runTarget "wait" target [] (cmdWait deadline) options
    if let some due := deadline then
      if rc == 124 && (← monotonicMs) ≥ due then
        return 124
  return rc

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
its terminal session, then SIGKILL after a second), records how it ended and gives the name up.
With no daemon, a saved session is discarded instead, an ended one included, whose end record
stays for `wait` and `info`. No session returns 127; a refusal, a name another process holds,
or a session that has not ended within `heldNameMs`, prints a diagnostic and returns 1. -/
private def cmdKill (name : String) : IO UInt32 := do
  match ← Client.oneShot name .kill with
  | some (.refused why) =>
    IO.eprintln s!"linger: {why}"
    return 1
  | some _ =>
    -- the session has ended once its daemon gives the name up, which it does after recording
    -- how the program ended and removing its socket
    let deadline := (← monotonicMs) + heldNameMs
    repeat
      let released ←
        try
          Paths.withSessionLock name (pure true)
        catch _ =>
          pure false
      if released then
        return 0
      unless ← nap deadline 20 do
        IO.eprintln s!"linger: session '{name}' has not ended"
        return 1
  | none =>
    match ← discardSaved name with
    | .ok true =>
      return 0
    | .ok false =>
      noSession name
    | .error why =>
      IO.eprintln s!"linger: {why}"
      return 1

/-- `info`: the live session's fields; with no daemon to answer, the name and how the program of
the last session to hold it ended, from the name's end record. No session returns 127; a refusal
or a failed reply prints a diagnostic and returns 1. -/
private def cmdInfo (name : String) : IO UInt32 := do
  match ← Client.oneShot name .info with
  | some result =>
    requestStatus name result
  | none =>
    match ← unanswered name with
    | .recorded (some outcome) =>
      for (k, v) in ("name", name) :: Linger.Session.outcomeFields outcome do
        IO.println s!"{k}\t{v}"
      return 0
    | .recorded none =>
      noSession name
    | .held why =>
      IO.eprintln s!"linger: no answer for '{name}': {why}"
      return 1

/-- `get`: print the session's labels as `key=value` lines from one info reply. No session
returns 127, and a failed reply prints a diagnostic and returns 1. -/
private def cmdGet (name : String) : IO UInt32 := do
  match ← queryInfo name with
  | none =>
    noSession name
  | some (.error err) =>
    IO.eprintln s!"linger: {err} for '{name}'"
    return 1
  | some (.ok info) =>
    for (k, v) in info do
      if k.startsWith "label." then
        IO.println s!"{(k.drop 6).toString}={v}"
    return 0

/-- `version`: print `linger` and `Mediation.versionNumber`, which sessions also see as
`TERM_PROGRAM_VERSION`, then the socket and state directories this environment resolves. -/
private def cmdVersion : IO UInt32 := do
  IO.println s!"linger {Terminal.Mediation.versionNumber}"
  IO.println s!"sockets: {← Paths.socketDir}"
  IO.println s!"state:   {← Paths.stateDir}"
  return 0

/-- Execute a validated listing request. -/
private def overview (args : List String) : IO UInt32 := do
  match parseLs args with
  | some (porcelain, remoteFlag) =>
    cmdList porcelain (← resolveRemotes remoteFlag)
  | none =>
    IO.eprintln usage
    return 2

/-- An optional `--read-only`, then the target as `Remote.targetArgs` reads it. -/
private def attachArgs (args : List String) : IO UInt32 := do
  let readOnly := args.head? == some "--read-only"
  let args := if readOnly then args.tail else args
  let some (name, cmd) := Linger.Target.Remote.targetArgs args |
    do
      return ← usageError "attach"
  if readOnly && !cmd.isEmpty then
    IO.eprintln "linger: read-only attach does not accept a command"
    return 2
  withTarget "attach" name cmd (cmdAttach · cmd readOnly) (if readOnly then ["--read-only"] else [])

private def captureArgs (args : List String) : IO UInt32 := do
  let history := args.head? == some "--history"
  let args := if history then args.tail else args
  let some (name, []) := Linger.Target.Remote.targetArgs args |
    do
      return ← usageError "capture"
  withTarget "capture" name []
      (cmdRead · (if history then .history else .screen)
        (if history then Terminal.Render.history else Terminal.Render.screenText))
      (if history then ["--history"] else [])

/-- Run one session command and return its exit status: 2 for a usage error or invalid
target, otherwise the verb's own status. `Main` routes interactive selection and tmux
interchange elsewhere; `__daemon` runs a session's daemon in this process. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | "__daemon" :: name :: cwd :: cmd =>
    Daemon.serve name cwd cmd (← Resume.saver name) (Resume.dropCkpt name) (Resume.loadCkpt name)
        (recordFile name)
    return 0
  | "__start" :: report :: name :: cwd :: argv =>
    serveStart report name cwd argv
    return 0
  | ["__resume", report, name, cwd] =>
    serveResume report name cwd
    return 0
  | ["resume", name] =>
    withTarget "resume" name [] cmdResume
  | "resume" :: _ =>
    return ← usageError "resume"
  | "start" :: name :: argv =>
    if argv.isEmpty then
      return ← usageError "start"
    withTarget "start" name argv (cmdStart · argv)
  | "attach" :: rest | "a" :: rest =>
    attachArgs rest
  | "run" :: _ | "r" :: _ =>
    retiredCommand "run"
  | "send" :: name :: text | "s" :: name :: text =>
    if text.isEmpty then
      return ← usageError "send"
    withTarget "send" name text fun name =>
        if text == ["-"] then cmdSendStdin name
        else requireLiveSend name (.input (String.intercalate " " text).toUTF8.toList)
  | ["detach", name] | ["d", name] =>
    withTarget "detach" name [] (requireLive · .detachAll)
  | ["kill", name] | ["k", name] =>
    withTarget "kill" name [] cmdKill
  | ["info", name] | ["i", name] =>
    withTarget "info" name [] cmdInfo
  | "capture" :: rest | "c" :: rest =>
    captureArgs rest
  | ["resize", name, cs, rs] =>
    match cs.toNat?, rs.toNat? with
    | some cols, some rows =>
      -- Accept exactly the sizes the emulator keeps, so the pty cannot disagree.
      if Terminal.Vt.clampDim cols != cols || Terminal.Vt.clampDim rows != rows then
        do
          IO.eprintln "linger: size must be 1..1000 (the emulator clamps at 1000)"
          return 2
      else
        withTarget "resize" name [cs, rs]
            (requireLive · (.resize (UInt32.ofNat cols) (UInt32.ofNat rows)))
    | _, _ =>
      do
        return ← usageError "resize"
  | "wait" :: "--timeout" :: seconds :: names | "w" :: "--timeout" :: seconds :: names =>
    match parseSeconds seconds with
    | some ms =>
      waitAll names (some ms)
    | none =>
      return ← usageError "wait"
  | "wait" :: names | "w" :: names =>
    waitAll names none
  | ["get", name] | ["g", name] =>
    withTarget "get" name [] cmdGet
  | "set" :: name :: kvs =>
    if kvs.isEmpty || kvs.any (fun pair => !pair.contains '=' || pair.startsWith "=") then
      return ← usageError "set"
    withTarget "set" name kvs fun name => do
        let mut rc : UInt32 := 0
        for kvp in kvs do
          rc := max rc (← requireLive name (.labelSet kvp.toUTF8.toList))
        return rc
  | "unset" :: name :: ks | "un" :: name :: ks =>
    if ks.isEmpty || ks.any (·.isEmpty) then
      return ← usageError "unset"
    withTarget "unset" name ks fun name => do
        let mut rc : UInt32 := 0
        for k in ks do
          rc := max rc (← requireLive name (.labelUnset k.toUTF8.toList))
        return rc
  | ["clear", name] | ["cl", name] =>
    withTarget "clear" name [] (requireLive · .labelClear)
  | ["ls", "--summary"] | ["list", "--summary"] | ["l", "--summary"] =>
    cmdSummary
  | ["version"] | ["v"] =>
    cmdVersion
  | ["help"] | ["h"] | ["--help"] | ["-h"] =>
    IO.println (usage ++ "\n" ++ helpFooter)
    return 0
  -- Explicit listing forms reach this backend.
  | "ls" :: rest | "list" :: rest | "l" :: rest =>
    overview rest
  | other =>
    overview other

end Linger.App.Shell
