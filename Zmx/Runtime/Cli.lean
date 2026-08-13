import Zmx.Runtime.Daemon
import Zmx.Runtime.Client
import Zmx.Core.Remote
import Zmx.Core.Listing
/-! # Zmx.Runtime.Cli — argv dispatch

Verb surface mirrors zmx (attach is an upsert; one-shot verbs talk to a
live daemon or say so). Bare `linger` — and `linger ls` — print a session
overview and exit; there is no full-screen picker (pick with the `fzf`
recipe in the README, or just `attach`). `__daemon` is the internal
re-exec target of the detached spawn.
-/

namespace Zmx.Runtime.Cli

open Zmx.Posix
open Zmx.Core.Wire (Msg)
open Zmx.Runtime
open Zmx.Core.Session (State)

def version : String := "linger 0.1.0"

/-- Session name used when `attach` is given none — "just give me my
session" without having to invent a name. -/
def defaultName : String := "main"

def usage : String := "Usage: linger [command] [args...]

  (no args) | ls [-r [h,..]]  List sessions; -r also lists remote hosts
                              (from --remote arg, else ~/.config/linger/remotes)
  [a]ttach [name] [command]   Attach, creating if needed (name defaults to 'main')
  watch <name>                Attach read-only (view without touching)
  [r]un <name> <command...>   Run a command in a session without attaching
  [s]end <name> <text...>     Send raw input to session pty
  [d]etach <name>             Detach all clients from a session
  [k]ill <name>               Kill session and all attached clients
  [hi]story <name>            Print session scrollback as plain text
  [w]ait <name>...            Wait for sessions' programs to exit
  [g]et / set / [un]set / [cl]ear <name>   Session labels (k=v)
  [v]ersion | [h]elp

Inside a session, $LINGER_SESSION holds the session name.
Detach key: ctrl-\\ (set LINGER_NO_DETACH_KEY to disable)."

/-- Step-7 seam: the daemon's checkpoint behavior. -/
structure Hooks where
  save : String → State → IO Unit := fun _ _ => pure ()
  drop : String → IO Unit := fun _ => pure ()
  load : String → IO (Option (Zmx.Core.Vt.Vt × String × List (String × String))) :=
    fun _ => pure none

def spawnDaemon (name cwd : String) (cmd : List String) : IO Unit := do
  let self ← IO.appPath
  let log ← Paths.logPath name
  spawnDetached self.toString (⟨["__daemon", name, cwd] ++ cmd⟩ : Array String) log

/-- Connect, spawning the daemon first if needed (attach-is-upsert). -/
def connectUpsert (hooks : Hooks) (name : String) (cmd : List String) : IO UInt32 := do
  match ← Client.connect name with
  | some fd => return fd
  | none =>
    -- no live daemon: resume from checkpoint if one exists (step 7)
    let resumed ← hooks.load name
    let cwd ← match resumed with
      | some (_, cwd, _) => pure cwd
      | none => do pure (← IO.Process.getCurrentDir).toString
    spawnDaemon name cwd cmd
    let deadline := (← monotonicMs) + 3000
    let mut fdOpt : Option UInt32 := none
    while fdOpt.isNone && (← monotonicMs) < deadline do
      IO.sleep 30
      fdOpt ← Client.connect name
    match fdOpt with
    | some fd => return fd
    | none =>
      let log ← Paths.logPath name
      throw (IO.userError s!"daemon for '{name}' did not come up (see {log})")

def cmdAttach (hooks : Hooks) (name : String) (cmd : List String) : IO UInt32 := do
  if !(← isatty stdinFd) then
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
    -- Deliberately NO transport policy here (keepalives, timeouts):
    -- `-o` on the command line would silently override the user's
    -- ~/.ssh/config, and how fast a link is declared dead is the
    -- transport's call, not the session manager's. linger's contribution
    -- to flaky links is making death cheap — the session detaches and
    -- restores — which composes with ANY transport policy (ssh config,
    -- an autossh-style loop, mosh). See README "Flaky links".
    exec "ssh" #["-t", "--", host, "linger", "attach", sess]  -- replaces us on success
    return 1                                                 -- only reached if exec fails
  | _ =>
    let fd ← connectUpsert hooks name cmd
    match ← Client.attach fd with
    | some status =>
      IO.eprintln s!"\r\nlinger: session '{name}' ended (status {status})"
      return status &&& 0xFF
    | none =>
      IO.eprintln s!"\r\nlinger: detached from '{name}'"
      return 0

/-- Fetch a session's info key-values. -/
partial def queryInfo (name : String) : IO (Option (List (String × String))) := do
  match ← Client.connect name with
  | none => return none
  | some fd =>
    Client.sendMsg fd .info
    let mut dec : Zmx.Core.Wire.Decoder := {}
    let mut acc : ByteArray := .empty
    let mut go := true
    while go do
      let revs ← poll #[fd] #[POLLIN] 2000
      if revs[0]! == 0 then go := false  -- timeout: treat as dead
      else
        match ← read fd 65536 with
        | none => go := false
        | some bs =>
          if bs.isEmpty then continue
          let (dec', msgs) := dec.feed bs.toList
          dec := dec'
          for m in msgs do
            match m with
            | .infoReply payload => acc := acc ++ ByteArray.mk payload.toArray
            | .done => go := false
            | .err _ => go := false
            | _ => pure ()
    close fd
    let txt := String.fromUTF8? acc |>.getD ""
    return some <| txt.splitOn "\n" |>.filterMap (fun line =>
      match line.splitOn "\t" with
      | [k, v] => some (k, v)
      | _ => none)

def kv (l : List (String × String)) (k : String) : String :=
  (l.find? (·.1 == k)).map (·.2) |>.getD ""

/-- Remote hosts for `-r`: explicit flag list, else `~/.config/linger/remotes`.
Duplicates are a hard error (`Remote.checkHosts`). `none` means no `-r`
(local only); `some []` means `-r` with no arg (read the file). -/
def resolveRemotes (flag : Option (List String)) : IO (List String) := do
  match flag with
  | none => return []
  | some given =>
    let raw ← if given.isEmpty then do
        let home := (← IO.getEnv "HOME").getD "/tmp"
        let path := s!"{home}/.config/linger/remotes"
        if ← System.FilePath.pathExists path then pure ((← IO.FS.readFile path).splitOn "\n")
        else pure []
      else pure given
    let hosts := (raw.map (·.trimAscii.toString)).filter
      (fun h => !h.isEmpty && !h.startsWith "#")
    match Zmx.Core.Remote.checkHosts hosts with
    | .ok l => return l
    | .error e => throw (IO.userError e)

/-- One remote's sessions over ssh; a failure (host down, no linger,
timeout) yields `[]` so a dead remote never blocks the local overview.
ConnectTimeout bounds a host that is down; ServerAlive bounds one that
is half-up (accepts the connection, then wedges mid-reboot) — either
way the overview proceeds within a few seconds. -/
def listRemote (host : String) : IO (List (String × Bool × String × String)) := do
  let out ← try
      IO.Process.output {
        cmd := "ssh",
        args := #["-o", "BatchMode=yes", "-o", "ConnectTimeout=3",
                  "-o", "ServerAliveInterval=2", "-o", "ServerAliveCountMax=2",
                  "--", host, "linger", "ls", "--porcelain"] }
    catch _ => pure { exitCode := 1, stdout := "", stderr := "" }
  if out.exitCode != 0 then return []
  return (Zmx.Core.Remote.parse out.stdout).map
    (fun r => (r.name, r.live, r.cmd, r.status))

def cmdList (porcelain : Bool) (remotes : List String) : IO UInt32 := do
  let live ← Paths.listSocketNames
  let ckpts ← Paths.listCkptNames
  let mut rows : List (List (String × String)) := []
  for name in live do
    match ← queryInfo name with
    | some info =>
      -- the name comes from the socket, not from the reply (the §Row
      -- rule, proved in Core.Listing.rowFields): a daemon too busy to
      -- answer still lists with its real name, and a peer can't spoof
      -- another session's identity
      -- the status column goes through `Listing.rowStatus`, so the two facts
      -- that decide whether a row is trustworthy (socket present, daemon
      -- answered) come from here and not from the reply -- §Row, extended
      rows := rows ++ [Zmx.Core.Listing.rowFields name info
        ++ [("state", "live"),
            ("status", Zmx.Core.Status.name
              (Zmx.Core.Listing.rowStatus (.live info)))]]
    | none =>
      -- connect() itself failed: nothing is listening, the file is stale
      try IO.FS.removeFile (← Paths.socketPath name) catch _ => pure ()
  for name in ckpts do
    if !live.contains name then
      rows := rows ++ [[("name", name), ("state", "resumable"),
        ("status", Zmx.Core.Status.name
          (Zmx.Core.Listing.rowStatus .stale))]]
  -- remotes last (per host), so a slow ssh can't reorder local rows
  for host in remotes do
    for (rname, rlive, rcmd, rstatus) in ← listRemote host do
      -- a remote row carries no activity fields (the peer's porcelain does
      -- not forward them), so it reports liveness only
      rows := rows ++ [[("name", s!"{rname}@{host}"), ("cmd", rcmd),
                        ("state", if rlive then "live" else "resumable"),
                        ("status", Zmx.Core.Status.name
                          (Zmx.Core.Listing.rowStatus (.remote rlive rstatus)))]]
  if porcelain then
    for info in rows do
      for (k, v) in info do
        IO.println s!"{k}\t{v}"
      IO.println ""
  else if rows.isEmpty then
    IO.println "no sessions"
  else
    for info in rows do
      let name := kv info "name"
      let state := kv info "state"
      let pid := kv info "pid"
      let cmd := kv info "cmd"
      let labels := info.filterMap (fun (k, v) =>
        if k.startsWith "label." then some s!"{(k.drop 6).toString}={v}" else none)
      let labelStr := if labels.isEmpty then "" else "  [" ++ String.intercalate " " labels ++ "]"
      let detail :=
        if state == "resumable" then "(resumable)"
        else if pid.isEmpty && cmd.isEmpty then "(busy)"
        else if pid.isEmpty then cmd
        else s!"pid {pid}  {cmd}"
      -- one glyph, most-specific-state-wins (Core.Status); the client count
      -- is the separate integer axis, blank when nobody is attached
      let st := Zmx.Core.Status.ofName (kv info "status")
      let watchers := kv info "clients"
      let watch := if watchers.isEmpty || watchers == "0" then "" else s!"  +{watchers}"
      IO.println s!"{Zmx.Core.Status.icon st} {name}\t{detail}{labelStr}{watch}"
  return 0

/-- Parse the `ls` argument set: an optional `--porcelain` and an
optional `-r`/`--remote [hosts]`, in any order. `-r` followed by a
`-`-prefixed token (or nothing) means "use the file"; `-r hosts` is an
explicit comma list. Returns `none` on any unrecognized token. -/
partial def parseLs : List String → Option (Bool × Option (List String))
  | [] => some (false, none)
  | "--porcelain" :: rest => (parseLs rest).map (fun (_, r) => (true, r))
  | "-r" :: rest | "--remote" :: rest =>
    match rest with
    | h :: more =>
      if h.startsWith "-" then (parseLs rest).map (fun (p, _) => (p, some []))
      else (parseLs more).map (fun (p, _) => (p, some (h.splitOn ",")))
    | [] => some (false, some [])
  | _ => none

def requireLive (name : String) (m : Msg) : IO UInt32 := do
  if ← Client.oneShot name m then return 0
  IO.eprintln s!"linger: no session '{name}'"
  return 1

/-- Like `requireLive` but expects no reply (input/labels-fire-and-forget). -/
def requireLiveSend (name : String) (m : Msg) : IO UInt32 := do
  if ← Client.sendOnly name m then return 0
  IO.eprintln s!"linger: no session '{name}'"
  return 1

def cmdWait (names : List String) : IO UInt32 := do
  let mut rc : UInt32 := 0
  for name in names do
    match ← Client.connect name with
    | none => pure ()  -- no session = nothing to wait for
    | some fd =>
      Client.sendMsg fd .wait
      let status ← Client.drainReplies fd false
      close fd
      if let some s := status then
        if s != 0 then rc := s
  return rc

def cmdGet (name : String) : IO UInt32 := do
  match ← queryInfo name with
  | none =>
    IO.eprintln s!"linger: no session '{name}'"
    return 1
  | some info =>
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
  | some (porcelain, remoteFlag) => cmdList porcelain (← resolveRemotes remoteFlag)
  | none =>
    IO.eprintln usage
    return 2

def main (hooks : Hooks) (args : List String) : IO UInt32 := do
  Zmx.Posix.init
  match args with
  | "__daemon" :: name :: cwd :: cmd =>
    let restore := (← hooks.load name).map (fun (vt, _, labels) => (vt, labels))
    Daemon.serve name cwd cmd (hooks.save name) (hooks.drop name) restore
    return 0
  | ["attach"] | ["a"] => cmdAttach hooks defaultName []
  | ["attach", name] | ["a", name] => cmdAttach hooks name []
  | "attach" :: name :: cmd | "a" :: name :: cmd => cmdAttach hooks name cmd
  | ["watch", name] =>
    -- read-only mirror (abduco -r): output only, detach key works
    match ← Client.connect name with
    | none =>
      IO.eprintln s!"linger: no session '{name}'"
      return 1
    | some fd =>
      let _ ← Client.attach fd true
      IO.eprintln s!"\r\nlinger: stopped watching '{name}'"
      return 0
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
      IO.eprintln "usage: linger send <name> <text...>"
      return 2
    requireLiveSend name (.input (String.intercalate " " text).toUTF8.toList)
  | ["detach", name] | ["d", name] => requireLive name .detachAll
  | ["kill", name] | ["k", name] => requireLiveSend name .kill
  | ["history", name] | ["hi", name] => requireLive name .history
  | "wait" :: names | "w" :: names =>
    if names.isEmpty then
      IO.eprintln "usage: linger wait <name>..."
      return 2
    cmdWait names
  | ["get", name] | ["g", name] => cmdGet name
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
  | ["clear", name] | ["cl", name] => requireLive name .labelClear
  | ["version"] | ["v"] => cmdVersion
  | ["help"] | ["h"] | ["--help"] =>
    IO.println usage
    return 0
  -- bare `linger`, `linger ls ...`, `linger -r ...` → the overview
  | "ls" :: rest | "list" :: rest | "l" :: rest => overview rest
  | other => overview other

end Zmx.Runtime.Cli
