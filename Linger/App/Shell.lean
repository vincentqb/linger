module

import Linger.Os.Shell
import Linger.Os.Env
import Linger.Session.Shell.Paths
import Linger.Session.Shell.Daemon
import Linger.Session.Shell.Client
import Linger.Session.Shell.Inventory
import Linger.Target.Remote
import Linger.Terminal.Render
import Linger.Display.Listing
import Linger.Os.Shell.Command
import Linger.Session.Shell.Resume
import Linger.Session.Shell.Record
import Linger.Terminal.Mediation
import Std.Async.Signal

public section

/-! # Linger.App.Shell — session argv dispatch

Verb surface: attach and run create if needed; read-only attach and capture also
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

/-- One line per command, printed by help and bare invocation, or to stderr when
`overview` cannot parse the arguments as listing options. -/
private def usage : String :=
  "attach [--read-only] [name] [command...]  Choose, create or attach to a session
ls [-r [hosts]] [--summary|--porcelain]   List sessions or attention counts
tmux <command> [SAVE]                     Saved tmux panes; see tmux help
run <name> <command...>                   Deprecated: type into a shell; use start, send
start <name> <program> [args...]          Start a program, exactly, in a new session
send <name> <text...|->                   Send raw input; - reads stdin
detach <name>                             Detach all clients from a session
kill <name>                               End a session, or discard a saved one
info <name>                               Print session details
capture [--history] <name>                Print the live or saved screen
resize <name> <cols> <rows>               Resize a detached session
wait [--timeout SECONDS] <name>...        Wait for programs to end; 124 on timeout
get <name>                                Print session labels
set <name> <k=v>...                       Set labels
unset <name> <key>...                     Remove labels
clear <name>                              Remove all labels
version                                   Print version and state paths
help                                      Show commands"

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

/-- The daemon `start` began. It reports what it did once, and a failure before that is reported
too: as `running` when a live session took the name first, else as a failure, 125. -/
private def serveStart (report name cwd : String) (argv : List String) : IO Unit := do
  let told ← IO.mkRef false
  let tell (r : Linger.Session.Start.Report) : IO Unit := do
    told.set true
    writeReport report r
  try
    Daemon.serve name cwd argv (Resume.saveCkpt name) (Resume.dropCkpt name) (Resume.loadCkpt name)
        (recordFile name) (some tell)
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

/-- `start`'s status for its daemon's report: 0 once the program runs; 1, saying which session
holds the name, for a refusal; and for a program that could not start, the status a shell or
`env` reports. A report that is no report is linger's own failure, 125. -/
private def startStatus (name : String) : Option Linger.Session.Start.Report → IO UInt32
  | some .started => return 0
  | some .running => do
    IO.eprintln s!"linger: session '{name}' is running"
    return 1
  | some .saved => do
    IO.eprintln s!"linger: session '{name}' is saved; attach to resume it, or kill it to discard it"
    return 1
  | some (.failed status why) => do
    IO.eprintln s!"linger: session '{name}' did not start: {Client.replyText "no reason" why}"
    return status.toUInt32
  | none => do
    IO.eprintln s!"linger: session '{name}' did not start: the daemon's report is unreadable"
    return 125

/-- `start`: run `argv` exactly, with no shell, in a new session named `name`, in this directory
and with this environment, and return once the program runs. A live or saved session that holds
the name is refused, saying which, and never resumed (`Start.plan`); the daemon decides again
holding the name. A program that cannot start returns what a shell or `env` reports, 125 for its
directory, 127 when not found and 126 when not runnable, and leaves no session, checkpoint or
record behind. -/
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
    startStatus name (some .running)
  | .saved =>
    startStatus name (some .saved)
  | .take =>
    let report ← Paths.startReportPath name s!"{← getpid}-{← IO.rand 0 0xFFFFFFFF}"
    let cwd := (← IO.Process.getCurrentDir).toString
    let log ← Paths.logPath name
    let pid ←
      spawnDetached (← IO.appPath).toString
          (⟨["__start", report, name, cwd] ++ argv⟩ : Array String) log
    let deadline := (← monotonicMs) + startWaitMs
    repeat
      if let some told← takeReport report then
        return ← startStatus name told
      if !(← alive pid) || (← monotonicMs) ≥ deadline then
        -- one last look: the daemon may have reported just before it ended
        if let some told← takeReport report then
          return ← startStatus name told
        IO.eprintln
            s!"linger: session '{name}' did not start: its daemon did not report (see {log})"
        return 125
      IO.sleep 10

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
    while
      fdOpt.isNone && (← monotonicMs) < start + socketWaitCapMs &&
        ((← monotonicMs) < start + socketWaitFloorMs || (← alive pid)) do
      IO.sleep 30
      fdOpt ← Client.connect name
    match fdOpt with
    | some fd =>
      -- a resume whose directory is gone runs in $HOME, and says where it was saved
      if let some (.ok info)← queryInfo name then
        if let some saved := info.lookup "saved_dir" then
          let ran := (info.lookup "start_dir").getD "$HOME"
          IO.eprintln s!"linger: session '{name}' resumed in {ran}: its directory {saved} is gone"
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
    throw (IO.userError s!"{verb} needs terminal input and output (use `run`/`send` for scripting)")
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
        writeAll stdoutFd (ByteArray.mk Linger.Terminal.Render.leaveAnsi.toArray)

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
        IO.sleep 5
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
prints and an attached title shows, computed in the calling process. -/
private def summaryText : IO String := do
  let rows ← localRows (some ((← monotonicMs) + 250))
  return Linger.Display.Status.summary
      (rows.map fun info => Linger.Display.Status.ofName ((info.lookup "status").getD "unknown"))

/-- `ls --summary`: print `summaryText`, or nothing when no local session needs
attention; exit 0 either way. -/
private def cmdSummary : IO UInt32 := do
  let summary ← summaryText
  if !summary.isEmpty then
    IO.println summary
  return 0

/-- A live connection is authoritative. Only read-only attachment can view an
offline checkpoint, loaded while owning both resources and displayed after
releasing them. Writable attachment keeps the create/resume path. Live titles
sample `summaryText` in this process. -/
private def cmdAttach (name : String) (cmd : List String) (readOnly : Bool) : IO UInt32 := do
  let result ←
    if readOnly then
      match ← Client.connect name with
      | some fd =>
        Client.attach name fd summaryText true
      | none =>
        let checkpoint ← Paths.withSessionLock name (Resume.loadCkpt name)
        match checkpoint with
        | some (vt, _, _) =>
          Client.viewSaved name vt
        | none =>
          pure (.refused s!"no live session or readable checkpoint for '{name}'")
    else
      let fd ← connectUpsert name cmd
      Client.attach name fd summaryText
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
    -- a palette style; redirected output and NO_COLOR retain the plain row.
    let withColor := (← (← IO.getStdout).isTty) && (← IO.getEnv "NO_COLOR").isNone
    writeAll stdoutFd (ByteArray.mk (Linger.Display.Listing.terminalListing withColor rows).toArray)
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

/-- One request to a live session. Pass `Client.replySilenceMs` for verbs a
pre-upgrade daemon does not know, which would otherwise hang the untimed drain
(spec agent-cli, Decision 4). -/
private def requireLive (name : String) (m : Msg) (silenceMs : Int32 := -1) : IO UInt32 := do
  match ← Client.oneShot name m (silenceMs := silenceMs) with
  | none =>
    IO.eprintln s!"linger: no session '{name}'"
    return 1
  | some result =>
    requestStatus name result

/-- Like `requireLive`, but delivers `m` without awaiting a reply: `send` text and `kill`. -/
private def requireLiveSend (name : String) (m : Msg) : IO UInt32 := do
  if ← Client.sendOnly name m then
    return 0
  IO.eprintln s!"linger: no session '{name}'"
  return 1

/-- A connected daemon is authoritative, including its errors. Only an absent
connection followed by successful ownership acquisition permits an offline read.
Hold both locks through loading and rendering; never start or modify a session. -/
private def cmdRead (name : String) (m : Msg) (render : Linger.Terminal.Vt.Vt → List UInt8) :
    IO UInt32 := do
  match ← Client.oneShot name m (silenceMs := Client.replySilenceMs) with
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
          return 1

/-- `send <name> -`: stdin to the session's pty, byte-exact, one `.input`
frame per read (≤ 64 KiB, so every frame satisfies `Msg.WF`). The agent's raw input
path — Enter, ^C, ESC, arrow sequences, exact whitespace: everything argv
cannot carry (agent-cli Decision 5). Poll-then-read so EOF (`read` = `none`)
is distinguished from would-block (`some #[]`, looped past) without spinning;
no timeout on purpose — a slow producer feeding a pipe is legitimate. Stdin EOF
returns 0; a missing session, a refusal, an invalid reply, the session's exit or a lost
connection returns 1. Nothing accumulates (each chunk is sent and dropped), so no
`Buf` is involved. -/
private def cmdSendStdin (name : String) : IO UInt32 := do
  match ← Client.connect name with
  | none =>
    IO.eprintln s!"linger: no session '{name}'"
    return 1
  | some fd =>
    try
      let mut dec : Linger.Session.Wire.Decoder := {}
      let mut go := true
      while go do
        let revs ← poll #[stdinFd, fd] #[POLLIN, POLLIN] 200
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
        if (← monotonicMs) ≥ heldUntil then
          IO.eprintln s!"linger: no answer for '{name}': {why}"
          return 125
        IO.sleep 20
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
    IO.eprintln "usage: linger wait [--timeout SECONDS] <name>..."
    return 2
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

/-- `kill`: end the session and return once it has ended. Its daemon stops the program (SIGTERM,
then SIGKILL), records how it ended and gives the name up. With no daemon, a saved session is
discarded instead. No session, a refusal, a name another process holds, or a session that has
not ended within `heldNameMs`, prints a diagnostic and returns 1. -/
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
      if (← monotonicMs) ≥ deadline then
        IO.eprintln s!"linger: session '{name}' has not ended"
        return 1
      IO.sleep 20
  | none =>
    match ← discardSaved name with
    | .ok true =>
      return 0
    | .ok false =>
      IO.eprintln s!"linger: no session '{name}'"
      return 1
    | .error why =>
      IO.eprintln s!"linger: {why}"
      return 1

/-- `info`: the live session's fields; with no daemon to answer, the name and how the program of
the last session to hold it ended, from the name's end record. No session, a refusal or a failed
reply prints a diagnostic and returns 1. -/
private def cmdInfo (name : String) : IO UInt32 := do
  match ← Client.oneShot name .info (silenceMs := Client.replySilenceMs) with
  | some result =>
    requestStatus name result
  | none =>
    match ← unanswered name with
    | .recorded (some outcome) =>
      for (k, v) in ("name", name) :: Linger.Session.outcomeFields outcome do
        IO.println s!"{k}\t{v}"
      return 0
    | .recorded none =>
      IO.eprintln s!"linger: no session '{name}'"
      return 1
    | .held why =>
      IO.eprintln s!"linger: no answer for '{name}': {why}"
      return 1

/-- `get`: print the session's labels as `key=value` lines from one info reply. No
session, or a failed reply, prints a diagnostic and returns 1. -/
private def cmdGet (name : String) : IO UInt32 := do
  match ← queryInfo name with
  | none =>
    IO.eprintln s!"linger: no session '{name}'"
    return 1
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
  IO.println s!"linger {Linger.Terminal.Mediation.versionNumber}"
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
      IO.eprintln "usage: linger attach [--read-only] [--] <name> [command...]"
      return 2
  if readOnly && !cmd.isEmpty then
    IO.eprintln "linger: read-only attach does not accept a command"
    return 2
  withTarget "attach" name cmd (cmdAttach · cmd readOnly) (if readOnly then ["--read-only"] else [])

private def captureArgs (args : List String) : IO UInt32 := do
  let history := args.head? == some "--history"
  let args := if history then args.tail else args
  let some (name, []) := Linger.Target.Remote.targetArgs args |
    do
      IO.eprintln "usage: linger capture [--history] [--] <name>"
      return 2
  withTarget "capture" name []
      (cmdRead · (if history then .history else .screen)
        (if history then Linger.Terminal.Render.history else Linger.Terminal.Render.screenText))
      (if history then ["--history"] else [])

/-- Run one session command and return its exit status: 2 for a usage error or invalid
target, otherwise the verb's own status. `Main` routes interactive selection and tmux
interchange elsewhere; `__daemon` runs a session's daemon in this process. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | "__daemon" :: name :: cwd :: cmd =>
    Daemon.serve name cwd cmd (Resume.saveCkpt name) (Resume.dropCkpt name) (Resume.loadCkpt name)
        (recordFile name)
    return 0
  | "__start" :: report :: name :: cwd :: argv =>
    serveStart report name cwd argv
    return 0
  | "start" :: name :: argv =>
    if argv.isEmpty then
      IO.eprintln "usage: linger start <name> <program> [args...]"
      return 2
    withTarget "start" name argv (cmdStart · argv)
  | "attach" :: rest | "a" :: rest =>
    attachArgs rest
  | "run" :: name :: cmd | "r" :: name :: cmd =>
    if cmd.isEmpty then
      IO.eprintln "usage: linger run <name> <command...>"
      return 2
    withTarget "run" name cmd fun name => do
        -- the shell it types into reinterprets the words, and the shell is the session's program
        IO.eprintln
            "linger: run is deprecated and will be removed: it types its words into the session's \
            shell. Use start to run a program in a new session, or send to type into a session."
        let fd ← connectUpsert name []
        try
          Client.sendMsg fd (.input (String.intercalate " " cmd ++ "\n").toUTF8.toList)
          return 0
        finally
          close fd
  | "send" :: name :: text | "s" :: name :: text =>
    if text.isEmpty then
      IO.eprintln "usage: linger send <name> <text...>  (or: linger send <name> -)"
      return 2
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
      if Linger.Terminal.Vt.clampDim cols != cols || Linger.Terminal.Vt.clampDim rows != rows then
        do
          IO.eprintln "linger: size must be 1..1000 (the emulator clamps at 1000)"
          return 2
      else
        withTarget "resize" name [cs, rs]
            (requireLive · (.resize (UInt32.ofNat cols) (UInt32.ofNat rows)) Client.replySilenceMs)
    | _, _ =>
      do
        IO.eprintln "usage: linger resize <name> <cols> <rows>"
        return 2
  | "wait" :: "--timeout" :: seconds :: names | "w" :: "--timeout" :: seconds :: names =>
    match parseSeconds seconds with
    | some ms =>
      waitAll names (some ms)
    | none =>
      IO.eprintln "usage: linger wait [--timeout SECONDS] <name>..."
      return 2
  | "wait" :: names | "w" :: names =>
    waitAll names none
  | ["get", name] | ["g", name] =>
    withTarget "get" name [] cmdGet
  | "set" :: name :: kvs =>
    if kvs.isEmpty || kvs.any (fun pair => !pair.contains '=' || pair.startsWith "=") then
      IO.eprintln "usage: linger set <name> k=v ..."
      return 2
    withTarget "set" name kvs fun name => do
        let mut rc : UInt32 := 0
        for kvp in kvs do
          rc := max rc (← requireLive name (.labelSet kvp.toUTF8.toList))
        return rc
  | "unset" :: name :: ks | "un" :: name :: ks =>
    if ks.isEmpty || ks.any (·.isEmpty) then
      IO.eprintln "usage: linger unset <name> <key>..."
      return 2
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
    IO.println usage
    return 0
  -- Explicit listing forms reach this backend.
  | "ls" :: rest | "list" :: rest | "l" :: rest =>
    overview rest
  | other =>
    overview other

end Linger.App.Shell
