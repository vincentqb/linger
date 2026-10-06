module

public import Linger.Runtime.Daemon
public import Linger.Runtime.Client
public import Linger.Core.Remote
public import Linger.Core.Listing

public section

/-! # Linger.Runtime.Cli — session argv dispatch

Verb surface: attach and run create if needed; history and capture also read
offline checkpoints. Every session verb accepts an exact name or name@host.
`Main` routes terminal selection and import before
entering this session backend. Bare invocation reaches help; `ls` prints an
overview and exits. `__daemon` is the internal re-exec target of the detached
spawn.
-/

namespace Linger.Runtime.Cli

open Linger.Posix
open Linger.Core.Wire (Msg)
open Linger.Runtime
open Linger.Core.Session (State)

def version : String := "linger 0.1.0"

/-- Bound on accumulated `infoReply` bytes, independent of the request deadline.
A peer exceeding the producer's policy has not supplied a usable answer. -/
abbrev infoReplyCap : Nat := Linger.Core.Session.infoReplyCap

def usage : String :=
  "Usage: linger [command] [args...]
       linger tmux <command> [SAVE]

  (no args)                 Show this help
  select                    Create or choose interactively; return after detach
                              (requires terminal input and output)
  ls [-r [hosts]]           List once; -r includes configured remote hosts
                              (or pass a comma-separated host list)
  status                    Print compact local attention counts for a prompt
  attach [name] [command]    Attach, creating if needed (name defaults to 'main')
  tmux ls [SAVE]            List panes in a saved tmux-resurrect snapshot
  tmux select [SAVE]        Choose a saved pane and attach; fresh shell if needed
                              (requires terminal input and output)
  tmux import [SAVE]        Start fresh shells in saved pane directories
  tmux export SAVE          Save local sessions in tmux-resurrect format
                              (requires a new destination file)
  watch <name>              Watch a live session without input or resizing
                              (marks output seen)
  run <name> <command...>    Send a shell command, creating the session if needed
  send <name> <text...>      Send raw input to session pty ('linger send <name> -'
                              sends stdin verbatim: newlines, ^C, escapes...)
  detach <name>             Detach all clients from a session
  kill <name>               Kill session and all attached clients
  info <name>               Print one session's k<TAB>v records (size, cursor,
                              outseq, labels...); ls --porcelain lists all
  capture <name>            Print the live or saved screen as plain text
                              (one line per row; marks live output seen)
  resize <name> <cols> <rows> Set a detached session's size (refused while an
                              attached client owns it)
  history <name>            Print live or saved scrollback as plain text
  wait <name>...            Wait for sessions' programs to exit
  get <name>               Print session labels
  set <name> <k=v>...       Set labels
  unset <name> <key>...     Remove labels
  clear <name>             Remove all labels
  version | help

Session commands accept an exact name or name@host (also name@user@host).
Names: 1–80 ASCII letters, digits, -_.+; no leading dot. Only select uses fuzzy search.
History/capture prefer the live session; an offline read never starts a program.
Saved tmux: ls/select/import default to the last save; pass SAVE for an older snapshot.
Saved commands never run. Saved selection has no Create row.
Native selection: type to filter or name a new session, arrows to move, Enter to choose.
The Create row names the session to create; Esc cancels.
Inside a session, $LINGER_SESSION holds the session name.
Detach key: ctrl-\\ (set LINGER_NO_DETACH_KEY to disable)."

/-- The daemon's checkpoint behaviour, injected: the CLI dispatch takes save/drop/load
as arguments so `Main` supplies the real ones and a test can supply none. Defaults are
no-ops, which is what makes a daemon without recovery a valid configuration rather than
a special case. -/
structure Hooks where
  save : String → State → IO Unit := fun _ _ => pure ()
  drop : String → IO Unit := fun _ => pure ()
  load : String → IO (Option (Linger.Core.Vt.Vt × String × List (String × String))) := fun _ =>
    pure none

def spawnDaemon (name cwd : String) (cmd : List String) : IO Unit := do
  let self ← IO.appPath
  let log ← Paths.logPath name
  spawnDetached self.toString (⟨["__daemon", name, cwd] ++ cmd⟩ : Array String) log

/-- Connect, spawning the daemon first if needed (attach-is-upsert). -/
def connectUpsert (name : String) (cmd : List String) : IO UInt32 := do
  match ← Client.connect name with
  | some fd =>
    return fd
  | none =>
    -- Recovery, including its saved cwd, happens only after the daemon owns
    -- both resources. A parent-side load would race another runtime namespace.
    let cwd := (← IO.Process.getCurrentDir).toString
    spawnDaemon name cwd cmd
    let deadline := (← monotonicMs) + 3000
    let mut fdOpt : Option UInt32 := none
    while fdOpt.isNone && (← monotonicMs) < deadline do
      IO.sleep 30
      fdOpt ← Client.connect name
    match fdOpt with
    | some fd =>
      return fd
    | none =>
      let log ← Paths.logPath name
      throw (IO.userError s!"daemon for '{name}' did not come up (see {log})")

def invalidTarget : IO UInt32 := do
  IO.eprintln
      "linger: invalid session name or malformed name@host target (use 1–80 ASCII letters, digits, -_.+; no leading dot)"
  return 2

/-- One transport boundary for all session verbs. SSH interprets a command string
with a shell; `Remote.command` preserves the original argv, including empty words.
Inherited stdin keeps `send name@host -` byte-exact. -/
def runTarget (verb : String) (target : Linger.Core.Remote.Target) (args : List String)
    (localAction : String → IO UInt32) : IO UInt32 := do
  let interactive := verb == "attach" || verb == "watch"
  if interactive && (!(← stdinIsTty) || !(← (← IO.getStdout).isTty)) then
    throw (IO.userError s!"{verb} needs terminal input and output (use `run`/`send` for scripting)")
  match target.host with
  | none =>
    localAction target.name
  | some host =>
    let child ←
      IO.Process.spawn
          { cmd := "ssh",
            args :=
              #[if interactive then "-t" else "-T", "--", host,
                Linger.Core.Remote.command verb target.name args],
            stdin := .inherit }
    try
      child.wait
    finally
      if interactive then
        writeAll stdoutFd (ByteArray.mk Linger.Core.Render.leaveAnsi.toArray)

def withTarget (verb target : String) (args : List String) (localAction : String → IO UInt32) :
    IO UInt32 :=
  match Linger.Core.Remote.parseTarget target with
  | none => invalidTarget
  | some parsed => runTarget verb parsed args localAction

def cmdAttach (name : String) (cmd : List String) : IO UInt32 := do
  let fd ← connectUpsert name cmd
  match ← Client.attach name fd with
  | .ended status =>
    IO.eprintln s!"\r\nlinger: session '{name}' ended (status {status})"
    return status &&& 0xFF
  | .detached =>
    IO.eprintln s!"\r\nlinger: detached from '{name}'"
    return 0
  | .refused msg =>
    IO.eprintln s!"\r\nlinger: {msg}"
    return 1
  | .lost why =>
    IO.eprintln s!"\r\nlinger: {why} for '{name}'"
    return 1

def cmdWatch (name : String) : IO UInt32 := do
  match ← Client.connect name with
  | none =>
    IO.eprintln s!"linger: no session '{name}'"
    return 1
  | some fd =>
    match ← Client.attach name fd true with
    | .detached =>
      IO.eprintln s!"\r\nlinger: stopped watching '{name}'"
      return 0
    | .ended status =>
      IO.eprintln s!"\r\nlinger: session '{name}' ended (status {status})"
      return status &&& 0xFF
    | .refused msg =>
      IO.eprintln s!"\r\nlinger: {msg}"
      return 1
    | .lost why =>
      IO.eprintln s!"\r\nlinger: {why} for '{name}'"
      return 1

/-- One connected info conversation, bounded by an absolute request window.
Only `done` completes an answer; a failed prefix is never returned as info. -/
def readInfo (fd : UInt32) (stopAt : Option Nat := none) : IO (List (String × String)) := do
  Client.sendMsg fd .info
  let deadline := stopAt.getD ((← monotonicMs) + 2000)
  let mut dec : Linger.Core.Wire.Decoder := {}
  let mut acc : Linger.Core.Buf.Buf := .empty
  let mut go := true
  while go && (← monotonicMs) < deadline do
    let remaining := deadline - (← monotonicMs)
    let revs ← poll #[fd] #[POLLIN] (Int32.ofNat (min 100 remaining))
    if revs[0]! == 0 then
      continue
    match ← read fd 65536 with
    | none =>
      throw (IO.userError "connection lost before info completed")
    | some bs =>
      if bs.isEmpty then
        continue
      let (dec', msgs) := dec.feed bs.toList
      dec := dec'
      if dec.errored then
        throw (IO.userError "invalid response from daemon")
      else
        for m in msgs do
          if !go then
            continue
          match m with
          | .infoReply payload =>
            let (next, dropped) :=
              Linger.Core.Buf.bufOffer infoReplyCap acc (ByteArray.mk payload.toArray)
            if dropped then
              throw (IO.userError "info reply exceeds the byte limit")
            acc := next
          | .done =>
            go := false
          | .err payload =>
            throw (IO.userError (Client.replyText "info request refused" payload))
          | .exited status =>
            throw (IO.userError s!"session ended before info completed (status {status})")
          | _ =>
            throw (IO.userError "unexpected response to info")
  if go then
    throw (IO.userError "no reply completed within the info deadline")
  let some txt :=
    String.fromUTF8?
      (Linger.Core.Buf.writeFrom acc) | throw (IO.userError "invalid UTF-8 in info reply")
  (txt.splitOn "\n").filter (· != "") |>.mapM fun line =>
      match line.splitOn "\t" with
      | [k, v] => pure (k, v)
      | _ => throw (IO.userError "invalid info record")

/-- Keep connection absence separate from an info failure: listing must retain
a connected peer, while `get` must report its unanswered request. -/
def queryInfo (name : String) (stopAt : Option Nat := none) :
    IO (Option (Except IO.Error (List (String × String)))) := do
  if let some deadline := stopAt then
    if (← monotonicMs) ≥ deadline then
      return some (.error (IO.userError "overview deadline reached"))
  match ← Client.connect name stopAt.isSome with
  | none =>
    if stopAt.isSome then
      return some (.error (IO.userError "overview connection unavailable"))
    return none
  | some fd =>
    try
      let info ← (readInfo fd stopAt).toBaseIO
      return some info
    finally
      close fd

def kv (l : List (String × String)) (k : String) : String :=
  (l.find? (·.1 == k)).map (·.2) |>.getD ""

/-- Remote hosts for `-r`: explicit flag list, else `~/.config/linger/remotes`.
Duplicates are a hard error (`Remote.checkHosts`). `none` means no `-r`
(local only); `some []` means `-r` with no arg (read the file). -/
def resolveRemotes (flag : Option (List String)) : IO (List String) := do
  match flag with
  | none =>
    return []
  | some given =>
    let raw ←
      if given.isEmpty then
        do
          let home := (← IO.getEnv "HOME").getD "/tmp"
          let path := s!"{home}/.config/linger/remotes"
          if ← System.FilePath.pathExists path then
            pure ((← IO.FS.readFile path).splitOn "\n")
          else
            pure []
      else
        pure given
    let hosts := (raw.map (·.trimAscii.toString)).filter (fun h => !h.isEmpty && !h.startsWith "#")
    match Linger.Core.Remote.checkHosts hosts with
    | .ok l =>
      return l
    | .error e =>
      throw (IO.userError e)

/-- One remote's sessions over ssh; a failure (host down, no linger,
timeout) yields `[]` so a dead remote never blocks the local overview.
ConnectTimeout bounds a host that is down; ServerAlive bounds one that
is half-up (accepts the connection, then wedges mid-reboot) — either
way the overview proceeds within a few seconds. -/
def listRemote (host : String) : IO (List (String × Bool × String × String)) := do
  let out ←
    try
      IO.Process.output
          { cmd := "ssh",
            args :=
              #["-o", "BatchMode=yes", "-o", "ConnectTimeout=3", "-o", "ServerAliveInterval=2",
                "-o", "ServerAliveCountMax=2", "--", host, "linger", "ls", "--porcelain"] }
    catch _ =>
      pure { exitCode := 1, stdout := "", stderr := "" }
  if out.exitCode != 0 then
    return []
  return (Linger.Core.Remote.parse out.stdout).map (fun r => (r.name, r.live, r.cmd, r.status))

/-- Remove a failed-connect socket only while holding its name lock. `false`
means another owner holds the lock or the probe itself failed; both fail closed. -/
def removeStaleSocket (name : String) : IO Bool := do
  try
    let lockFd ← flock (← Paths.lockPath name)
    if lockFd < 0 then
      return false
    try
      try
        IO.FS.removeFile (← Paths.socketPath name)
      catch _ =>
        pure ()
      return true
    finally
      close lockFd.toUInt64.toUInt32
  catch _ =>
    return false

/-- Common local snapshot for the listing and prompt. An optional shared deadline
keeps a prompt from waiting once per stalled daemon; unqueried peers stay unknown. -/
def localRows (stopAt : Option Nat := none) : IO (List (List (String × String))) := do
  let sockets := (← Paths.listSocketNames).toArray.qsort (· < ·) |>.toList
  let ckpts := (← Paths.listCkptNames).toArray.qsort (· < ·) |>.toList
  let liveRow := fun name info =>
    Linger.Core.Listing.rowFields name info ++
      [("state", "live"),
        ("status", Linger.Core.Status.name (Linger.Core.Listing.rowStatus (.live info)))]
  let mut confirmedLive : List String := []
  let mut rows : List (List (String × String)) := []
  for name in sockets do
    match ← queryInfo name stopAt with
    | some info =>
      confirmedLive := confirmedLive ++ [name]
      rows := rows ++ [liveRow name (info.toOption.getD [])]
    | none =>
      if !(← removeStaleSocket name) then
        -- Failed connect while another process owns (or may own) the name: keep
        -- the rendezvous path and list the identity as live/unknown.
        confirmedLive := confirmedLive ++ [name]
        rows := rows ++ [liveRow name []]
  for name in ckpts do
    if !confirmedLive.contains name then
      let available ←
        try
          Paths.withSessionLock name (pure true)
        catch _ =>
          pure false
      -- Another runtime directory may share this checkpoint namespace.
      -- A busy or unreadable lock cannot establish that the session is offline.
      rows :=
        rows ++
          [if available then
              Linger.Core.Listing.rowFields name
                [("state", "resumable"),
                  ("status", Linger.Core.Status.name (Linger.Core.Listing.rowStatus .stale))]
            else liveRow name []]
  return rows

def cmdStatus : IO UInt32 := do
  let rows ← localRows (some ((← monotonicMs) + 250))
  let summary :=
    Linger.Core.Status.summary
      (rows.map fun info => Linger.Core.Status.ofName ((info.lookup "status").getD "unknown"))
  if !summary.isEmpty then
    IO.println summary
  return 0

def cmdList (porcelain : Bool) (remotes : List String) : IO UInt32 := do
  let mut rows ← localRows
  -- remotes last (per host), so a slow ssh can't reorder local rows
  for host in remotes do
    for (rname, rlive, rcmd, rstatus) in ← listRemote host do
      -- a remote row is built from what the peer's porcelain says about identity
      -- and liveness. It also emits `clients` and `label.*`; those are dropped
      -- rather than rendered, so a remote row's label and watcher columns are
      -- blank whatever the peer reports — see SCRATCHPAD 2026-09-15.
      rows :=
        rows ++
          [[("name", s!"{rname}@{host}"), ("cmd", rcmd),
              ("state", if rlive then "live" else "resumable"),
              ("status",
                Linger.Core.Status.name (Linger.Core.Listing.rowStatus (.remote rlive rstatus)))]]
  if porcelain then
    for info in rows do
      for (k, v) in info do
        IO.println s!"{k}\t{v}"
      IO.println ""
  else
    -- The selector consumes these same row pieces. Only the status badge has
    -- a palette style; redirected output and NO_COLOR retain the plain row.
    let withColor := (← (← IO.getStdout).isTty) && (← IO.getEnv "NO_COLOR").isNone
    writeAll stdoutFd (ByteArray.mk (Linger.Core.Listing.terminalListing withColor rows).toArray)
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

def requestStatus (name : String) (result : Client.Drained) : IO UInt32 := do
  match result with
  | .done =>
    return 0
  | .refused why =>
    IO.eprintln s!"linger: {why}"
  | .lost why =>
    IO.eprintln s!"linger: {why} for '{name}'"
  | .exited status =>
    IO.eprintln s!"linger: session '{name}' ended before the request completed (status {status})"
  | .silent =>
    IO.eprintln s!"linger: no reply from '{name}'"
  return 1

def requireLive (name : String) (m : Msg) : IO UInt32 := do
  match ← Client.oneShot name m with
  | none =>
    IO.eprintln s!"linger: no session '{name}'"
    return 1
  | some result =>
    requestStatus name result

/-- Like `requireLive` but expects no reply (input/labels-fire-and-forget). -/
def requireLiveSend (name : String) (m : Msg) : IO UInt32 := do
  if ← Client.sendOnly name m then
    return 0
  IO.eprintln s!"linger: no session '{name}'"
  return 1

/-- Like `requireLive` but through the bounded drain (`Client.drainBounded`):
for verbs a pre-upgrade daemon does not know, which would otherwise hang the
untimed drain (spec agent-cli, Decision 4). `wait` must NOT use this — waiting
arbitrarily long is its job. -/
def requireLiveBounded (name : String) (m : Msg) : IO UInt32 := do
  match ← Client.connect name with
  | none =>
    IO.eprintln s!"linger: no session '{name}'"
    return 1
  | some fd =>
    let r ←
      try
        Client.sendMsg fd m
        Client.drainBounded fd
      finally
        close fd
    requestStatus name r

/-- A connected daemon is authoritative, including its errors. Only an absent
connection followed by successful ownership acquisition permits an offline read.
Hold both locks through loading and rendering; never start or modify a session. -/
def cmdRead (hooks : Hooks) (name : String) (m : Msg) (render : Linger.Core.Vt.Vt → List UInt8) :
    IO UInt32 := do
  match ← Client.connect name with
  | some fd =>
    let result ←
      try
        Client.sendMsg fd m
        Client.drainBounded fd
      finally
        close fd
    requestStatus name result
  | none =>
    Paths.withSessionLock name do
        match ← hooks.load name with
        | some (vt, _, _) =>
          writeAll stdoutFd (ByteArray.mk (render vt).toArray)
          return 0
        | none =>
          IO.eprintln s!"linger: no live session or readable checkpoint for '{name}'"
          return 1

/-- `send <name> -`: stdin to the session's pty, byte-exact, one `.input`
frame per read (≤ 64 KiB, so every frame is Wire-wf). The agent's raw input
path — Enter, ^C, ESC, arrow sequences, exact whitespace: everything argv
cannot carry (agent-cli Decision 5). Poll-then-read so EOF (`read` = `none`)
is distinguished from would-block (`some #[]`, looped past) without spinning;
no timeout on purpose — a slow producer feeding a pipe is legitimate, and EOF
is the only exit. Nothing accumulates (each chunk is sent and dropped), so no
`Buf` is involved. -/
def cmdSendStdin (name : String) : IO UInt32 := do
  match ← Client.connect name with
  | none =>
    IO.eprintln s!"linger: no session '{name}'"
    return 1
  | some fd =>
    try
      let mut dec : Linger.Core.Wire.Decoder := {}
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

def cmdWait (names : List String) : IO UInt32 := do
  let mut rc : UInt32 := 0
  for name in names do
    match ← Client.connect name with
    | none =>
      pure () -- no session = nothing to wait for
    | some fd =>
      let result ←
        try
          Client.sendMsg fd .wait
          Client.drainReplies fd false
        finally
          close fd
      match result with
      | .exited status =>
        if status != 0 then
          rc := max rc status
      | .refused why =>
        IO.eprintln s!"linger: {why}"
        rc := max rc 1
      | .lost why =>
        IO.eprintln s!"linger: {why} while waiting for '{name}'"
        rc := max rc 1
      | .done | .silent =>
        IO.eprintln s!"linger: no exit status from '{name}'"
        rc := max rc 1
  return rc

def cmdGet (name : String) : IO UInt32 := do
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

def cmdVersion : IO UInt32 := do
  IO.println version
  IO.println s!"sockets: {← Paths.socketDir}"
  IO.println s!"state:   {← Paths.stateDir}"
  return 0

/-- Execute a validated listing request. -/
def overview (args : List String) : IO UInt32 := do
  match parseLs args with
  | some (porcelain, remoteFlag) =>
    cmdList porcelain (← resolveRemotes remoteFlag)
  | none =>
    IO.eprintln usage
    return 2

def main (hooks : Hooks) (args : List String) : IO UInt32 := do
  match args with
  | "__daemon" :: name :: cwd :: cmd =>
    Daemon.serve name cwd cmd (hooks.save name) (hooks.drop name) (hooks.load name)
    return 0
  | ["attach"] | ["a"] =>
    withTarget "attach" Linger.Core.Name.defaultName [] (cmdAttach · [])
  | "attach" :: name :: cmd | "a" :: name :: cmd =>
    withTarget "attach" name cmd (cmdAttach · cmd)
  | ["watch", name] =>
    withTarget "watch" name [] cmdWatch
  | "run" :: name :: cmd | "r" :: name :: cmd =>
    if cmd.isEmpty then
      IO.eprintln "usage: linger run <name> <command...>"
      return 2
    withTarget "run" name cmd fun name => do
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
    withTarget "kill" name [] (requireLiveSend · .kill)
  | ["info", name] | ["i", name] =>
    withTarget "info" name [] (requireLiveBounded · .info)
  | ["capture", name] | ["c", name] =>
    withTarget "capture" name [] (cmdRead hooks · .screen Linger.Core.Render.screenText)
  | ["resize", name, cs, rs] =>
    match cs.toNat?, rs.toNat? with
    | some cols, some rows =>
      -- 1..1000 is `clampDim`'s range: past it the emulator would clamp while
      -- the pty winsize did not, and the two must not be allowed to disagree
      -- from this path (attach trusts the terminal; an agent gets validated)
      if cols == 0 || rows == 0 || cols > 1000 || rows > 1000 then
        do
          IO.eprintln "linger: size must be 1..1000 (the emulator clamps at 1000)"
          return 2
      else
        withTarget "resize" name [cs, rs]
            (requireLiveBounded · (.resize (UInt32.ofNat cols) (UInt32.ofNat rows)))
    | _, _ =>
      do
        IO.eprintln "usage: linger resize <name> <cols> <rows>"
        return 2
  | ["history", name] | ["hi", name] =>
    withTarget "history" name [] (cmdRead hooks · .history Linger.Core.Render.history)
  | "wait" :: names | "w" :: names =>
    if names.isEmpty then
      IO.eprintln "usage: linger wait <name>..."
      return 2
    let some targets := names.mapM Linger.Core.Remote.parseTarget | invalidTarget
    let mut rc : UInt32 := 0
    for target in targets do
      rc := max rc (← runTarget "wait" target [] (fun name => cmdWait [name]))
    return rc
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
  | ["status"] =>
    cmdStatus
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

end Linger.Runtime.Cli
