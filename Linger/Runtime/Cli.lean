module

public import Linger.Runtime.Daemon
public import Linger.Runtime.Client
public import Linger.Core.Remote
public import Linger.Core.Listing

public section

/-! # Linger.Runtime.Cli — argv dispatch

Verb surface: attach is an upsert; one-shot verbs talk to a
live daemon or say so. Bare `linger` — and `linger ls` — print a session
overview and exit; there is no full-screen picker (pick with the `fzf`
recipe in the README, or just `attach`). `__daemon` is the internal
re-exec target of the detached spawn.
-/

namespace Linger.Runtime.Cli

open Linger.Posix
open Linger.Core.Wire (Msg)
open Linger.Runtime
open Linger.Core.Session (State)

def version : String := "linger 0.1.0"

/-- Session name used when `attach` is given none — "just give me my
session" without having to invent a name. -/
def defaultName : String := "main"

/-- Bound on accumulated `infoReply` bytes, independent of the request deadline.
A peer exceeding it has not supplied a usable answer. -/
def infoReplyCap : Nat := 1048576

def usage : String :=
  "Usage: linger [command] [args...]

  (no args) | ls [-r [h,..]]  List sessions; -r also lists remote hosts
                              (from --remote arg, else ~/.config/linger/remotes)
  [a]ttach [name] [command]   Attach, creating if needed (name defaults to 'main')
  watch <name>                Input/resize-read-only attach (marks output seen)
  [r]un <name> <command...>   Run a command in a session without attaching
  [s]end <name> <text...>     Send raw input to session pty ('linger send <name> -'
                              sends stdin verbatim: newlines, ^C, escapes...)
  [d]etach <name>             Detach all clients from a session
  [k]ill <name>               Kill session and all attached clients
  [i]nfo <name>               Print one session's k<TAB>v records (size, cursor,
                              outseq, labels...; the porcelain, for scripts/agents)
  [c]apture <name>            Print the current screen as plain text (one line
                              per row; marks the session seen)
  resize <name> <cols> <rows> Set a detached session's size (refused while an
                              attached client owns it)
  [hi]story <name>            Print session scrollback as plain text
  [w]ait <name>...            Wait for sessions' programs to exit
  [g]et / set / [un]set / [cl]ear <name>   Session labels (k=v)
  [v]ersion | [h]elp

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
def connectUpsert (hooks : Hooks) (name : String) (cmd : List String) : IO UInt32 := do
  match ← Client.connect name with
  | some fd =>
    return fd
  | none =>
    -- no live daemon: resume from checkpoint if one exists (step 7)
    let resumed ← hooks.load name
    let cwd ←
      match resumed with
      | some (_, cwd, _) =>
        pure cwd
      | none =>
        do
          pure (← IO.Process.getCurrentDir).toString
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

def cmdAttach (hooks : Hooks) (name : String) (cmd : List String) : IO UInt32 := do
  if !(← stdinIsTty) then
    throw (IO.userError "attach needs a terminal (use `run`/`send` for scripting)")
  -- `name@host` attaches to a remote session: become `ssh -t host linger
  -- attach name`. Session names never contain `@` (Name.sanitize
  -- reserves it — theorem sanitize_no_at), so any `@` here means remote.
  -- The host is everything after the FIRST `@`, so it may itself be a
  -- `user@host` ssh target. Lets the fzf recipe feed a listed row
  -- (`name@host`) verbatim to `attach`, local or remote.
  match name.splitOn "@" with
  | sess :: rest@(_ :: _) =>
    let host := String.intercalate "@" rest
    if sess.isEmpty || host.isEmpty then
      throw (IO.userError s!"malformed remote target '{name}' (expected name@host)")
    -- SSH joins the remote command arguments for a shell. Use the same name
    -- alphabet as local paths before crossing that boundary.
    let sess := Linger.Core.Name.sanitize sess
    -- Deliberately NO transport policy here (keepalives, timeouts):
    -- `-o` on the command line would silently override the user's
    -- ~/.ssh/config, and how fast a link is declared dead is the
    -- transport's call, not the session manager's. linger's contribution
    -- to flaky links is making death cheap — the session detaches and
    -- restores — which composes with ANY transport policy (ssh config,
    -- an autossh-style loop, mosh). See README "Flaky links".
    exec "ssh" #["-t", "--", host, "linger", "attach", sess] -- replaces us on success
    return 1 -- only reached if exec fails
  | _ =>
    let fd ← connectUpsert hooks name cmd
    match ← Client.attach fd with
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

/-- One connected info conversation, bounded by an absolute request window.
Only `done` completes an answer; a failed prefix is never returned as info. -/
def readInfo (fd : UInt32) : IO (List (String × String)) := do
  Client.sendMsg fd .info
  let deadline := (← monotonicMs) + 2000
  let mut dec : Linger.Core.Wire.Decoder := {}
  let mut acc : Linger.Core.Buf.Buf := .empty
  let mut go := true
  while go && (← monotonicMs) < deadline do
    let revs ← poll #[fd] #[POLLIN] 100
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
def queryInfo (name : String) : IO (Option (Except IO.Error (List (String × String)))) := do
  match ← Client.connect name with
  | none =>
    return none
  | some fd =>
    try
      let info ← (readInfo fd).toBaseIO
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

def cmdList (porcelain : Bool) (remotes : List String) : IO UInt32 := do
  let sockets := (← Paths.listSocketNames).toArray.qsort (· < ·) |>.toList
  let ckpts := (← Paths.listCkptNames).toArray.qsort (· < ·) |>.toList
  let liveRow := fun name info =>
    Linger.Core.Listing.rowFields name info ++
      [("state", "live"),
        ("status", Linger.Core.Status.name (Linger.Core.Listing.rowStatus (.live info)))]
  let mut confirmedLive : List String := []
  let mut rows : List (List (String × String)) := []
  for name in sockets do
    match ← queryInfo name with
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
      -- through `rowFields` like the live rows, so the displayed name is the
      -- sanitized one `attach` accepts and §Row (`rowFields_name`) covers it —
      -- a checkpoint filename is not trusted to name its own row.
      rows :=
        rows ++
          [Linger.Core.Listing.rowFields name
              [("state", "resumable"),
                ("status", Linger.Core.Status.name (Linger.Core.Listing.rowStatus .stale))]]
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
    -- the human listing is rendered in the pure core (`Listing.humanListing`):
    -- every displayed value passes through `utf8s`, so a control byte in a
    -- `cmd`, a label, a checkpoint filename or a `-r` host cannot reach the
    -- terminal as an escape sequence (`Theorems/Listing.lean`
    -- `humanListing_printable`), the columns align, and there is no trailing
    -- whitespace. The empty-state line is part of it.
    writeAll stdoutFd (ByteArray.mk (Linger.Core.Listing.humanListing rows).toArray)
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

/-- Bare `linger` and `linger ls [...]` share this overview path. -/
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
    let restore := (← hooks.load name).map (fun (vt, _, labels) => (vt, labels))
    Daemon.serve name cwd cmd (hooks.save name) (hooks.drop name) restore
    return 0
  | ["attach"] | ["a"] =>
    cmdAttach hooks defaultName []
  | ["attach", name] | ["a", name] =>
    cmdAttach hooks name []
  | "attach" :: name :: cmd | "a" :: name :: cmd =>
    cmdAttach hooks name cmd
  | ["watch", name] =>
    -- read-only mirror: output only, detach key works
    match ← Client.connect name with
    | none =>
      IO.eprintln s!"linger: no session '{name}'"
      return 1
    | some fd =>
      match ← Client.attach fd true with
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
  | "run" :: name :: cmd | "r" :: name :: cmd =>
    if cmd.isEmpty then
      IO.eprintln "usage: linger run <name> <command...>"
      return 2
    let fd ← connectUpsert hooks name []
    Client.sendMsg fd (.input (String.intercalate " " cmd ++ "\n").toUTF8.toList)
    close fd
    return 0
  | "send" :: name :: text | "s" :: name :: text =>
    if text.isEmpty then
      IO.eprintln "usage: linger send <name> <text...>  (or: linger send <name> -)"
      return 2
    if text == ["-"] then
      cmdSendStdin name
    else
      requireLiveSend name (.input (String.intercalate " " text).toUTF8.toList)
  | ["detach", name] | ["d", name] =>
    requireLive name .detachAll
  | ["kill", name] | ["k", name] =>
    requireLiveSend name .kill
  | ["info", name] | ["i", name] =>
    requireLiveBounded name .info
  | ["capture", name] | ["c", name] =>
    requireLiveBounded name .screen
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
        requireLiveBounded name (.resize (UInt32.ofNat cols) (UInt32.ofNat rows))
    | _, _ =>
      do
        IO.eprintln "usage: linger resize <name> <cols> <rows>"
        return 2
  | ["history", name] | ["hi", name] =>
    requireLive name .history
  | "wait" :: names | "w" :: names =>
    if names.isEmpty then
      IO.eprintln "usage: linger wait <name>..."
      return 2
    cmdWait names
  | ["get", name] | ["g", name] =>
    cmdGet name
  | "set" :: name :: kvs =>
    if kvs.isEmpty then
      IO.eprintln "usage: linger set <name> k=v ..."
      return 2
    let mut rc : UInt32 := 0
    for kvp in kvs do
      rc := max rc (← requireLive name (.labelSet kvp.toUTF8.toList))
    return rc
  | "unset" :: name :: ks | "un" :: name :: ks =>
    if ks.isEmpty then
      IO.eprintln "usage: linger unset <name> <key>..."
      return 2
    let mut rc : UInt32 := 0
    for k in ks do
      rc := max rc (← requireLive name (.labelUnset k.toUTF8.toList))
    return rc
  | ["clear", name] | ["cl", name] =>
    requireLive name .labelClear
  | ["version"] | ["v"] =>
    cmdVersion
  | ["help"] | ["h"] | ["--help"] =>
    IO.println usage
    return 0
  -- bare `linger`, `linger ls ...`, `linger -r ...` → the overview
  | "ls" :: rest | "list" :: rest | "l" :: rest =>
    overview rest
  | other =>
    overview other

end Linger.Runtime.Cli
