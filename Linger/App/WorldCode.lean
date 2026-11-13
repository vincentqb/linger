module

import Os.WorldCode
import Linger.Os.CoreCode.Env
import Linger.Session.WorldCode.Paths
import Linger.Session.WorldCode.Daemon
import Linger.Session.WorldCode.Client
import Linger.Session.WorldCode.Inventory
import Linger.Target.CoreCode.Remote
import Terminal.CoreCode.Render
import Linger.Display.CoreCode.Listing
import Linger.Display.CoreCode.View
import Linger.Os.CoreCode.Answer
import Linger.App.CoreCode.Capture
public import Linger.Os.CoreSpec
import Linger.App.CoreCode.Recovery
import Linger.App.CoreCode.Commands
import Linger.App.CoreCode.Wait
import Os.WorldCode.Command
import Linger.Session.WorldCode.Resume
import Linger.Session.WorldCode.Record
import Terminal.CoreCode.Mediation
import Std.Async.Signal
import Linger.Display.CoreCode.Status

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

/-- One line per command, from the command table, printed by help and bare invocation, or to
stderr when `overview` cannot parse the arguments as listing options. -/
private def usage : String := Linger.App.Commands.helpText

/-- A command's usage error, its row of the command table (`Commands.usageLine`), and the
answer `usage`. -/
private def usageError (word : String) : IO Answer := do
  if let some command := Linger.App.Commands.lookup word then
    IO.eprintln (Linger.App.Commands.usageLine command)
  return .usage

/-- A removed command's word: what to use instead (`Commands.retired`), and the answer
`usage`. -/
private def retiredCommand (word : String) : IO Answer := do
  if let some advice := Linger.App.Commands.retired.lookup word then
    IO.eprintln s!"linger: {word} was removed: {advice}"
  return .usage

/-- What `linger help` prints after the commands: the seven statuses a session can show, which
of them titles and `ls --summary` count, and the exit statuses every command shares, one line
per answer (`Answer.legend`). -/
private def helpFooter : String :=
  let glyphs :=
    String.intercalate " "
      (Linger.Display.Status.attention.map fun status =>
        String.singleton (Linger.Display.Status.icon status))
  String.intercalate "\n"
    (["", "Statuses"] ++ Linger.Display.Status.legend.map ("  " ++ ·) ++
      [s!"Titles and ls --summary count {glyphs}", "",
        "Exit statuses: the program's own, when the command waits for it to end; otherwise"] ++
      Answer.legend.map ("  " ++ ·))

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

/-- A command named a session that does not exist: say so and answer `notFound`, as a shell
does for a command it cannot find. -/
private def noSession (name : String) : IO Answer := do
  IO.eprintln s!"linger: no session '{name}'"
  return .notFound

/-- Why nothing starts over the name's checkpoint when its bytes do not decode
(`Recovery.decide`): it is damaged, it stays as it is, and `linger kill` discards it. -/
private def undecodedText (name : String) : IO String := do
  return s!"its checkpoint {← Paths.ckptPath name} is damaged and does not decode, so it stays \
    as it is; linger kill {name} discards it"

/-- Why a command that found no live session starts nothing, as `Recovery.decide` answered: no
session holds the name, or its checkpoint does not decode. -/
private def refusalText (name : String) (answer : Answer) : IO String := do
  if answer == .notFound then
    return s!"no session '{name}'"
  return s!"session '{name}': {← undecodedText name}"

/-- Say why a command that found no live session starts nothing, as `Recovery.decide`
answered, and give that answer: no session holds the name, or its checkpoint does not decode. -/
private def refused (name : String) (answer : Answer) : IO Answer := do
  IO.eprintln s!"linger: {← refusalText name answer}"
  return answer

/-- What the daemon of `name` starts from, as `Recovery.decide` says from the name's checkpoint
file, `create` when a new session may start: a refusal is the status its command answers, and
why. -/
private def recoverFor (name : String) (create : Bool) : IO Daemon.Recovered := do
  match Linger.App.Recovery.decide create (← Resume.readCkpt name) with
  | .fresh =>
    return .ok none
  | .resume ck =>
    return .ok (some (ck.vt, ck.cwd, ck.labels))
  | .refuse answer =>
    let why ←
      if answer == .notFound then
        pure s!"no session '{name}'"
      else
        undecodedText name
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
private def serveStart (report name cwd : String) (argv : List String) : IO Unit := do
  let req ← daemonRequest report
  let told ← IO.mkRef false
  let tell (r : Linger.Session.Start.Report) : IO Unit := do
    told.set true
    req.tell r
  try
    Daemon.serve name cwd argv (← Resume.saver name) (Resume.dropCkpt name) (recoverFor name)
        (recordFile name) (some { req with tell })
  catch err =>
    unless ← told.get do
      match ← Client.connect name with
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
private def startRefused (name : String) (saved : Bool) : IO Answer := do
  unless saved do
    IO.eprintln s!"linger: session '{name}' is running"
    return .notDone
  if let .refuse .notDone := Linger.App.Recovery.decide false (← Resume.readCkpt name) then
    return ← refused name .notDone
  let record := (← (Record.load name).toBaseIO).toOption.join
  match record.bind Linger.Session.Record.decode with
  | some (.ended outcome) =>
    IO.eprintln
        s!"linger: session '{name}' ended ({(Client.Ending.outcome outcome).describe}); \
        kill it to discard it, or attach to resume it"
  | _ =>
    IO.eprintln s!"linger: session '{name}' is saved; attach to resume it, or kill it to discard it"
  return .notDone

/-- `start`'s answer once its wait ended: `done` exactly when the program runs (`Start.answer`);
`notDone`, saying which session holds the name, for a refusal (`startRefused`); for a program that
could not start, the answer whose status a shell or `env` reports; and `timedOut` when the daemon
did not answer in time, so it starts nothing. A report that is no report, or a daemon that ended
without one, is linger's own failure. -/
private def startStatus (name log : String) (waited : Waited) : IO Answer := do
  match Linger.Session.Start.answer (waited matches .took _) (waited matches .told (some .started)),
    waited with
  | .started, _ =>
    return .done
  | .notStarted, .told (some .running) =>
    startRefused name false
  | .notStarted, .told (some .saved) =>
    startRefused name true
  | .notStarted, .told (some (.failed status why)) =>
    do
      IO.eprintln s!"linger: session '{name}' did not start: {Client.replyText "no reason" why}"
      return Answer.ofCode status.toUInt32
  | .notStarted, .told none =>
    do
      IO.eprintln s!"linger: session '{name}' did not start: the daemon's report is unreadable"
      return .failed
  | .notStarted, .took true =>
    do
      IO.eprintln
          s!"linger: session '{name}' did not start: its daemon did not answer within \
        {startWaitMs / 1000} s, so it starts nothing (see {log})"
      return .timedOut
  | .notStarted, .took false =>
    do
      IO.eprintln s!"linger: session '{name}' did not start: its daemon ended first (see {log})"
      return .failed
  | .notStarted, _ =>
    do
      IO.eprintln
          s!"linger: session '{name}': its daemon ended without saying whether it started \
        (see {log})"
      return .failed

/-- `start`: run `argv` exactly, with no shell, in a new session named `name`, in this directory
and with this environment, and return once the program runs. A live or saved session, an ended
one included, that holds the name is refused, saying which, and never resumed (`Start.plan`);
the daemon decides again holding the name. A program that cannot start answers as a shell or
`env` reports it, `failed` for its directory, `notFound` when not found and `cannotRun` when not
runnable, and leaves no session, checkpoint or record behind. A daemon that does not answer
within `startWaitMs` starts nothing, and `start` says so, `timedOut`. -/
private def cmdStart (name : String) (argv : List String) : IO Answer := do
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
    Daemon.serve name cwd [] (← Resume.saver name) (Resume.dropCkpt name) (recoverFor name)
        (recordFile name) (some { req with tell }) (resume := true)
  catch err =>
    unless ← told.get do
      match ← Client.connect name with
      | some fd =>
        close fd
        tell .running
      | none =>
        tell (.failed Answer.failed.code.toUInt8 err.toString.toUTF8.toList)
    throw err

/-- A resumed session whose directory is gone runs in `$HOME`: say where it runs and where it was
saved, from its info fields start_dir and saved_dir. -/
private def sayMoved (name : String) : IO Unit := do
  if let some (.ok info)← queryInfo name then
    if let some saved := info.lookup "saved_dir" then
      let ran := (info.lookup "start_dir").getD "$HOME"
      IO.eprintln s!"linger: session '{name}' resumed in {ran}: its directory {saved} is gone"

/-- `resume`'s answer once its wait ended: `done` exactly when the program runs (`Start.answer`),
again, saying where when its directory is gone, or in a live session that already runs it;
`notFound`, as for a session that does not exist, when no session holds the name; for a saved
session that cannot be read or a program that cannot start, `notDone` or the answer whose status
a shell or `env` reports; and `timedOut` when the daemon did not answer in time, so it starts
nothing. A report that is no report, or a daemon that ended without one, is linger's own
failure. -/
private def resumeStatus (name log : String) (waited : Waited) : IO Answer := do
  let runs := waited matches .told (some .started) || waited matches .told (some .running)
  match Linger.Session.Start.answer (waited matches .took _) runs, waited with
  | .started, .told (some .started) =>
    do
      sayMoved name
      return .done
  | .started, _ =>
    return .done
  | .notStarted, .told (some (.failed status why)) =>
    if Answer.ofCode status.toUInt32 == .notFound then
      noSession name
    else
      do
        IO.eprintln s!"linger: session '{name}' did not resume: {Client.replyText "no reason" why}"
        return Answer.ofCode status.toUInt32
  | .notStarted, .told _ =>
    do
      IO.eprintln s!"linger: session '{name}' did not resume: the daemon's report is unreadable"
      return .failed
  | .notStarted, .took true =>
    do
      IO.eprintln
          s!"linger: session '{name}' did not resume: its daemon did not answer within \
        {startWaitMs / 1000} s, so it starts nothing (see {log})"
      return .timedOut
  | .notStarted, .took false =>
    do
      IO.eprintln s!"linger: session '{name}' did not resume: its daemon ended first (see {log})"
      return .failed
  | .notStarted, .silent =>
    do
      IO.eprintln
          s!"linger: session '{name}': its daemon ended without saying whether it resumed \
        (see {log})"
      return .failed

/-- `resume`: run a saved session's program again, an ended session's included, in its saved
directory and on its last screen, without attaching, and return once it runs. A live session is
left as it is, and a name no session holds starts nothing (`Start.resumePlan`); the daemon decides
again holding the name. A daemon that does not answer within `startWaitMs` starts nothing, and
`resume` says so, `timedOut`. -/
private def cmdResume (name : String) : IO Answer := do
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
    return .done
  | .missing =>
    noSession name
  | .resume =>
    let report ← Paths.startReportPath name s!"{← getpid}-{← IO.rand 0 0xFFFFFFFF}"
    let cwd := (← IO.Process.getCurrentDir).toString
    let log ← Paths.logPath name
    let pid ← beginRequest report log ["__resume", report, name, cwd]
    resumeStatus name log (← awaitReport pid report)

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
private def connectUpsert (name : String) (cmd : List String) : IO (Except Answer UInt32) := do
  match ← Client.connect name with
  | some fd =>
    return .ok fd
  | none =>
    -- Recovery, including its saved cwd, happens only after the daemon owns
    -- both resources. A parent-side load would race another runtime namespace.
    let cwd := (← IO.Process.getCurrentDir).toString
    let pid ← spawnDaemon name cwd cmd
    let start ← monotonicMs
    let mut fdOpt : Option UInt32 := none
    let mut looked := false
    while fdOpt.isNone && ((← monotonicMs) < start + socketWaitFloorMs || (← alive pid)) do
      unless ← nap (start + socketWaitCapMs) 30 do
        break
      fdOpt ← Client.connect name
      if fdOpt.isNone && !looked && !(← alive pid) then
        looked := true
        if let some answer← undecoded name then
          return .error answer
    match fdOpt with
    | some fd =>
      sayMoved name
      return .ok fd
    | none =>
      let log ← Paths.logPath name
      throw (IO.userError s!"daemon for '{name}' did not come up (see {log})")

/-- Reject an operand that is neither an exact name nor a well-formed `name@host` target:
print the name rule and answer `usage`. -/
private def invalidTarget : IO Answer := do
  IO.eprintln s!"linger: invalid session name or malformed name@host target (use {Paths.nameRule})"
  return .usage

/-- One transport boundary for all session verbs. SSH hands a command string to the login
shell of the remote account, whichever shell that is; `Remote.command` spells the verb and every
word, empty ones included, in plain words that every shell passes on as they are, and the
remote linger routes exactly the original argv (`command_exact`). Encoding doubles a word's
length, and a Linux host takes a command line of at most 128 KiB, so `send name@host -`,
whose inherited stdin stays byte-exact, carries longer text. The remote linger reads an attach
or capture target with `targetArgs`, so it travels as `targetOperands`; the other verbs take it
by position. SSH's status, the remote command's, is the answer of a remote target. -/
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
attention; `done` either way. -/
private def cmdSummary : IO Answer := do
  let summary ← summaryText
  if !summary.isEmpty then
    IO.println summary
  return .done

/-- The answer that tells how a session ended, as its daemon reported it (`Ending.answer`): its
program's, or `interrupted` for a session a signal to its daemon saved; an older daemon's status
is the program's. -/
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
    return .ok (← Client.attach name fd summaryText readOnly)
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

/-- A live connection is authoritative, once its daemon says it speaks this version's protocol
(`attachSpoken`). Only read-only attachment can view an offline checkpoint, loaded with its end
record while owning both resources and displayed after releasing them, under the status the
listing shows for it. Writable attachment keeps the create/resume path, which resumes an ended
session too. Either refuses a checkpoint that does not decode, which stays as it is
(`Recovery.decide`). Live titles sample `summaryText` in this process. -/
private def cmdAttach (name : String) (cmd : List String) (readOnly : Bool) : IO Answer := do
  let result : Except Answer Client.Outcome ←
    if readOnly then
      match ← Client.connect name with
      | some fd =>
        attachSpoken name fd true
      | none =>
        let (recovery, record) ←
          Paths.withSessionLock name do
              return (Linger.App.Recovery.decide false (← Resume.readCkpt name),
                  ← (Record.load name).toBaseIO)
        let status := Linger.Display.Listing.rowStatus (savedRow record).1
        match recovery with
        | .resume ck =>
          pure (.ok (← Client.viewSaved name ck.vt status))
        | .refuse answer =>
          .error <$> refused name answer
        | .fresh =>
          .error <$> refused name .notFound
    else
      match ← connectUpsert name cmd with
      | .ok fd =>
        attachSpoken name fd false
      | .error answer =>
        .error <$> refused name answer
  match result with
  | .error answer =>
    return answer
  | .ok (.ended (.saved signal)) =>
    -- the system stopping linger may have hung up this terminal too: the answer says it
    try
      IO.eprintln
          s!"\r\nlinger: session '{name}' was saved when signal {signal} stopped its daemon; \
            attach to resume it"
    catch _ =>
      pure ()
    return endingAnswer (.saved signal)
  | .ok (.ended ending) =>
    IO.eprintln s!"\r\nlinger: session '{name}' ended ({ending.describe})"
    return endingAnswer ending
  | .ok .interrupted =>
    -- the terminal is handed back, but a hung-up one cannot show why: the answer says it
    try
      IO.eprintln s!"\r\nlinger: interrupted; detached from '{name}'"
    catch _ =>
      pure ()
    return .interrupted
  | .ok .detached =>
    IO.eprintln s!"\r\nlinger: detached from '{name}'"
    return .done
  | .ok (.refused msg) =>
    IO.eprintln s!"\r\nlinger: {msg}"
    return .notDone
  | .ok (.lost why) =>
    IO.eprintln s!"\r\nlinger: {why} for '{name}'"
    return .notDone

/-- `ls`: local rows, then each remote host's rows named `name@host`, printed as
`k<TAB>v` records separated by blank lines (`porcelain`) or as the terminal listing.
Remote rows keep only name, command, state and status. Answers `interrupted` when a signal
cancels the remote queries. -/
private def cmdList (porcelain : Bool) (remotes : List String) : IO Answer := do
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
  let some remote := remote | return .interrupted
  let mut rows := locals
  for (host, output) in remotes.zip remote.toList do
    for row in Linger.Target.Remote.parse output do
      -- a remote row is built from what the peer's porcelain says about identity
      -- and liveness. It also emits `clients` and `label.*`; those are dropped
      -- rather than rendered, so a remote row's label and watcher columns are
      -- blank whatever the peer reports.
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
  return .done

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
private def requireLive (name : String) (m : Msg) : IO Answer := do
  match ← Client.oneShot name m with
  | none =>
    noSession name
  | some result =>
    requestStatus name result

/-- Like `requireLive`, but delivers `ms` without awaiting a reply: `send` text. -/
private def requireLiveSend (name : String) (ms : List Msg) : IO Answer := do
  if ← Client.sendOnly name ms then
    return .done
  noSession name

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
private def runHolding (name : String) (plan : List Linger.App.Capture.Step)
    (run : Linger.App.Capture.Step → IO Unit) : IO Unit := do
  let mut held : Option (Array Linger.App.Capture.Step) := none
  for step in plan do
    match step, held with
    | .acquire, none =>
      held := some #[]
    | .release, some inside =>
      Paths.withSessionLock name (inside.forM run)
      held := none
    | .acquire, some _ | .release, none =>
      pure ()
    | step, some inside =>
      held := some (inside.push step)
    | step, none =>
      run step
  if let some inside := held then
    Paths.withSessionLock name (inside.forM run)

/-- A connected daemon is authoritative, including its errors. Only an absent connection
followed by successful ownership acquisition permits an offline read, which takes the steps of
`Capture.plan`: it holds both locks through loading and rendering, and lets them go before it
writes what it rendered, so a reader that does not read holds up no attach or resume
(`capture_waits_unlocked`). Never start or modify a session. -/
private def cmdRead (name : String) (m : Msg) (render : Terminal.Vt.Vt → List UInt8) : IO Answer :=
  do
  match ← Client.oneShot name m with
  | some result =>
    requestStatus name result
  | none =>
    let file ← IO.mkRef (none : Option ByteArray)
    let shown ← IO.mkRef (Shown.refusal .notFound (← refusalText name .notFound))
    let answer ← IO.mkRef Answer.failed
    runHolding name Linger.App.Capture.plan fun
        | .load => do
          file.set (← Resume.readCkpt name)
        | .render => do
          match Linger.App.Recovery.decide false (← file.get) with
          | .resume ck =>
            shown.set (.session (render ck.vt))
          | .refuse refusal =>
            shown.set (.refusal refusal (← refusalText name refusal))
          | .fresh =>
            shown.set (.refusal .notFound (← refusalText name .notFound))
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
private def cmdSendStdin (name : String) : IO Answer := do
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
            return .notDone
          | some bs =>
            if !bs.isEmpty then
              let (dec', msgs) := dec.feed bs.toList
              dec := dec'
              if dec.errored then
                IO.eprintln s!"linger: invalid response from daemon for '{name}'"
                return .notDone
              for m in msgs do
                match m with
                | .err msg =>
                  IO.eprintln s!"linger: {Client.replyText "request refused" msg}"
                  return .notDone
                | .ended outcome =>
                  let ending := Client.Ending.outcome outcome
                  IO.eprintln s!"linger: session '{name}' ended while sending ({ending.describe})"
                  return .notDone
                | .exited status =>
                  IO.eprintln s!"linger: session '{name}' ended while sending (status {status})"
                  return .notDone
                | .saved signal =>
                  let ending := Client.Ending.saved signal
                  IO.eprintln s!"linger: session '{name}' ended while sending ({ending.describe})"
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
is unknown, or a signal to its daemon saved it; an exit status says the rest. -/
private def sayEnding (name : String) : Linger.Session.Ending → IO Unit
  | .program (.exited _) => pure ()
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
private def hear (name : String) (silenceMs : Int32) : IO (Wait.Heard × String) := do
  match ← Client.oneShot name .wait (untilDone := false) (silenceMs := silenceMs) with
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
    return (.refused, s!"no exit status from '{name}'")
  | some (.lost _) | none =>
    match ← unanswered name with
    | .recorded answer =>
      return (.recorded answer, "")
    | .held why =>
      return (.held, why)

/-- `wait`: block until the session ends and answer as `Wait.decide` does with what each look
hears, saying why on stderr when that is not the program's own exit. The ending comes from its
daemon or, with no daemon to answer, from the name's end record once nothing else holds the
name: the program's, or `interrupted` for a session a signal to its daemon saved, whose program
did not end by itself; `notFound`, as a shell's `wait` reports an unknown job, when no session
has taken the name. A daemon lost during the wait leaves its own record, never an older
one. With a `deadline` on the monotonic clock, `timedOut` once it has passed and the session is
still running, as `timeout(1)` reports, leaving the session as it is. A refusal answers
`notDone`; that linger could not find out, only for an unknown ending or a name held with no
daemon answering for `Wait.heldNameMs`, from the look that first found it so. -/
private def cmdWait (deadline : Option Nat) (name : String) : IO Answer := do
  let mut heldSince : Option Nat := none
  repeat
    -- a silence budget ends a held wait when the time is up; `Int32` bounds one round of it
    let now ← monotonicMs
    let silenceMs : Int32 :=
      match deadline with
      | some limit => Int32.ofNat (min (limit - now) 2147483647)
      | none => -1
    let (heard, why) ← hear name silenceMs
    match Wait.decide deadline heldSince (← monotonicMs) heard with
    | .answer answer =>
      match answer, heard with
      | .timedOut, _ =>
        IO.eprintln s!"linger: timed out waiting for '{name}'"
      | _, .ended ending | _, .recorded (some ending) =>
        sayEnding name ending
      | _, .recorded none =>
        IO.eprintln s!"linger: no session '{name}'"
      | _, .refused =>
        IO.eprintln s!"linger: {why}"
      | _, .held =>
        IO.eprintln s!"linger: no answer for '{name}': {why}"
      | _, _ =>
        pure ()
      return answer
    | .again since =>
      heldSince := since
      if let some first := since then
        discard <| nap (first + Wait.heldNameMs) 20

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
    answer ← runTarget "wait" target [] (cmdWait deadline) options
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
an ended one included, whose end record stays for `wait` and `info`. No session answers
`notFound`; a refusal, a name another process holds, or a session that has not ended within
`Wait.heldNameMs`, prints a diagnostic and answers `notDone`. -/
private def cmdKill (name : String) : IO Answer := do
  match ← Client.oneShot name .kill with
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
          Paths.withSessionLock name (pure true)
        catch _ =>
          pure false
      if released then
        return .done
      unless ← nap deadline 20 do
        IO.eprintln s!"linger: session '{name}' has not ended"
        return .notDone
  | none =>
    match ← discardSaved name with
    | .ok true =>
      return .done
    | .ok false =>
      noSession name
    | .error why =>
      IO.eprintln s!"linger: {why}"
      return .notDone

/-- `info`: the live session's fields; with no daemon to answer, the name and how the last session
to hold it ended (`Session.endingFields`), from the name's end record: how its program ended, or
the signal that stopped its daemon, which saved it. No session answers `notFound`; a
refusal or a failed reply prints a diagnostic and answers `notDone`. -/
private def cmdInfo (name : String) : IO Answer := do
  match ← Client.oneShot name .info with
  | some result =>
    requestStatus name result
  | none =>
    match ← unanswered name with
    | .recorded (some ending) =>
      for (k, v) in ("name", name) :: Linger.Session.endingFields ending do
        IO.println s!"{k}\t{v}"
      return .done
    | .recorded none =>
      noSession name
    | .held why =>
      IO.eprintln s!"linger: no answer for '{name}': {why}"
      return .notDone

/-- `get`: print the session's labels as `key=value` lines from one info reply. No session
answers `notFound`, and a failed reply prints a diagnostic and answers `notDone`. -/
private def cmdGet (name : String) : IO Answer := do
  match ← queryInfo name with
  | none =>
    noSession name
  | some (.error err) =>
    IO.eprintln s!"linger: {err} for '{name}'"
    return .notDone
  | some (.ok info) =>
    for (k, v) in info do
      if k.startsWith "label." then
        IO.println s!"{(k.drop 6).toString}={v}"
    return .done

/-- `version`: print `linger` and `Mediation.versionNumber`, which sessions also see as
`TERM_PROGRAM_VERSION`, then the socket and state directories this environment resolves. -/
private def cmdVersion : IO Answer := do
  IO.println s!"linger {Terminal.Mediation.versionNumber}"
  IO.println s!"sockets: {← Paths.socketDir}"
  IO.println s!"state:   {← Paths.stateDir}"
  return .done

/-- Execute a validated listing request. -/
private def overview (args : List String) : IO Answer := do
  match parseLs args with
  | some (porcelain, remoteFlag) =>
    cmdList porcelain (← resolveRemotes remoteFlag)
  | none =>
    IO.eprintln usage
    return .usage

/-- An optional `--read-only`, then the target as `Remote.targetArgs` reads it. -/
private def attachArgs (args : List String) : IO Answer := do
  let readOnly := args.head? == some "--read-only"
  let args := if readOnly then args.tail else args
  let some (name, cmd) := Linger.Target.Remote.targetArgs args |
    do
      return ← usageError "attach"
  if readOnly && !cmd.isEmpty then
    IO.eprintln "linger: read-only attach does not accept a command"
    return .usage
  withTarget "attach" name cmd (cmdAttach · cmd readOnly) (if readOnly then ["--read-only"] else [])

private def captureArgs (args : List String) : IO Answer := do
  let history := args.head? == some "--history"
  let args := if history then args.tail else args
  let some (name, []) := Linger.Target.Remote.targetArgs args |
    do
      return ← usageError "capture"
  withTarget "capture" name []
      (cmdRead · (if history then .history else .screen)
        (if history then Terminal.Render.history else Terminal.Render.screenText))
      (if history then ["--history"] else [])

/-- The worse of two answers to one command's requests, as its exit status should tell: the one
with the higher code. -/
private def worse (a b : Answer) : Answer := if a.code < b.code then b else a

/-- Run one session command and give its answer, whose code is its exit status: `usage` for a
usage error or invalid target, otherwise the verb's own. `main` routes interactive selection and
tmux interchange elsewhere; `__daemon` runs a session's daemon in this process. -/
def main (args : List String) : IO Answer := do
  match args with
  | "__daemon" :: name :: cwd :: cmd =>
    Daemon.serve name cwd cmd (← Resume.saver name) (Resume.dropCkpt name) (recoverFor name)
        (recordFile name)
    return .done
  | "__start" :: report :: name :: cwd :: argv =>
    serveStart report name cwd argv
    return .done
  | ["__resume", report, name, cwd] =>
    serveResume report name cwd
    return .done
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
        else
          requireLiveSend name
            (Linger.Session.Wire.inputFrames (String.intercalate " " text).toUTF8.toList)
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
          return .usage
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
        let mut answer : Answer := .done
        for kvp in kvs do
          answer := worse answer (← requireLive name (.labelSet kvp.toUTF8.toList))
        return answer
  | "unset" :: name :: ks | "un" :: name :: ks =>
    if ks.isEmpty || ks.any (·.isEmpty) then
      return ← usageError "unset"
    withTarget "unset" name ks fun name => do
        let mut answer : Answer := .done
        for k in ks do
          answer := worse answer (← requireLive name (.labelUnset k.toUTF8.toList))
        return answer
  | ["clear", name] | ["cl", name] =>
    withTarget "clear" name [] (requireLive · .labelClear)
  | ["ls", "--summary"] | ["list", "--summary"] | ["l", "--summary"] =>
    cmdSummary
  | ["version"] | ["v"] =>
    cmdVersion
  | ["help"] | ["h"] | ["--help"] | ["-h"] =>
    IO.println (usage ++ "\n" ++ helpFooter)
    return .done
  -- Explicit listing forms reach this backend.
  | "ls" :: rest | "list" :: rest | "l" :: rest =>
    overview rest
  | other =>
    overview other

end Linger.App.Shell
