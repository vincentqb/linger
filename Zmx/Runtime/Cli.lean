import Zmx.Runtime.Daemon
import Zmx.Runtime.Client
/-! # Zmx.Runtime.Cli — argv dispatch

Verb surface mirrors zmx (attach is an upsert; one-shot verbs talk to
a live daemon or say so). `__daemon` is the internal re-exec target of
the detached spawn. Checkpoint hooks are no-ops here; `Zmx.Runtime.
Resume` (spec step 7) replaces them via `hooksRef`.
-/

namespace Zmx.Runtime.Cli

open Zmx.Posix
open Zmx.Core.Wire (Msg)
open Zmx.Runtime.Paths in
open Zmx.Runtime
open Zmx.Core.Session (State)

def version : String := "lzmx 0.1.0"

def usage : String := "Usage: lzmx <command> [args...]

Commands:
  [a]ttach <name> [command...]   Attach to session, creating if needed
  [r]un <name> <command...>      Run a command in a session without attaching
  [s]end <name> <text...>        Send raw input to session pty
  [d]etach <name>                Detach all clients from a session
  [l]ist|ls [--porcelain]        List sessions (live and resumable)
  [k]ill <name>                  Kill session and all attached clients
  [hi]story <name>               Print session scrollback as plain text
  [w]ait <name>...               Wait for sessions' programs to exit
  [g]et <name>                   Show session labels
  set <name> k=v ...             Set session labels
  [un]set <name> key ...         Remove session labels
  [cl]ear <name>                 Clear all session labels
  [v]ersion                      Show version and paths
  [h]elp                         Show this help

Inside a session, $LZMX_SESSION holds the session name.
Detach key: ctrl-\\ (set LZMX_NO_DETACH_KEY to disable)."

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
  let fd ← connectUpsert hooks name cmd
  match ← Client.attach fd with
  | some status =>
    IO.eprintln s!"\r\nlzmx: session '{name}' ended (status {status})"
    return status &&& 0xFF
  | none =>
    IO.eprintln s!"\r\nlzmx: detached from '{name}'"
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

def cmdList (porcelain : Bool) : IO UInt32 := do
  let live ← Paths.listSocketNames
  let ckpts ← Paths.listCkptNames
  let mut rows : List (List (String × String)) := []
  for name in live do
    match ← queryInfo name with
    | some info => rows := rows ++ [info ++ [("state", "live")]]
    | none =>
      -- stale socket: clean it up quietly
      try IO.FS.removeFile (← Paths.socketPath name) catch _ => pure ()
  for name in ckpts do
    if !live.contains name then
      rows := rows ++ [[("name", name), ("state", "resumable")]]
  if porcelain then
    for info in rows do
      for (k, v) in info do
        IO.println s!"{k}\t{v}"
      IO.println ""
  else
    if rows.isEmpty then
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
        if state == "live" then
          IO.println s!"{name}\tpid {pid}\t{cmd}{labelStr}"
        else
          IO.println s!"{name}\t(resumable)"
  return 0

def requireLive (name : String) (m : Msg) : IO UInt32 := do
  if ← Client.oneShot name m then return 0
  IO.eprintln s!"lzmx: no session '{name}'"
  return 1

/-- Like `requireLive` but expects no reply (input/labels-fire-and-forget). -/
def requireLiveSend (name : String) (m : Msg) : IO UInt32 := do
  if ← Client.sendOnly name m then return 0
  IO.eprintln s!"lzmx: no session '{name}'"
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
    IO.eprintln s!"lzmx: no session '{name}'"
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

def main (hooks : Hooks) (args : List String) : IO UInt32 := do
  Zmx.Posix.init
  match args with
  | "__daemon" :: name :: cwd :: cmd =>
    let restore := (← hooks.load name).map (fun (vt, _, labels) => (vt, labels))
    Daemon.serve name cwd cmd (hooks.save name) (hooks.drop name) restore
    return 0
  | ["attach", name] | ["a", name] => cmdAttach hooks name []
  | "attach" :: name :: cmd | "a" :: name :: cmd => cmdAttach hooks name cmd
  | "run" :: name :: cmd | "r" :: name :: cmd =>
    if cmd.isEmpty then
      IO.eprintln "usage: lzmx run <name> <command...>"
      return 2
    let fd ← connectUpsert hooks name []
    Client.sendMsg fd (.input (String.intercalate " " cmd ++ "\n").toUTF8.toList)
    close fd
    return 0
  | "send" :: name :: text | "s" :: name :: text =>
    if text.isEmpty then
      IO.eprintln "usage: lzmx send <name> <text...>"
      return 2
    requireLiveSend name (.input (String.intercalate " " text).toUTF8.toList)
  | ["detach", name] | ["d", name] => requireLive name .detachAll
  | ["kill", name] | ["k", name] => requireLiveSend name .kill
  | ["list"] | ["ls"] | ["l"] => cmdList false
  | ["list", "--porcelain"] | ["ls", "--porcelain"] => cmdList true
  | ["history", name] | ["hi", name] => requireLive name .history
  | "wait" :: names | "w" :: names =>
    if names.isEmpty then
      IO.eprintln "usage: lzmx wait <name>..."
      return 2
    cmdWait names
  | ["get", name] | ["g", name] => cmdGet name
  | "set" :: name :: kvs =>
    if kvs.isEmpty then
      IO.eprintln "usage: lzmx set <name> k=v ..."
      return 2
    let mut rc : UInt32 := 0
    for kvp in kvs do
      rc := max rc (← requireLive name (.labelSet kvp.toUTF8.toList))
    return rc
  | "unset" :: name :: ks | "un" :: name :: ks =>
    if ks.isEmpty then
      IO.eprintln "usage: lzmx unset <name> <key>..."
      return 2
    let mut rc : UInt32 := 0
    for k in ks do
      rc := max rc (← requireLive name (.labelUnset k.toUTF8.toList))
    return rc
  | ["clear", name] | ["cl", name] => requireLive name .labelClear
  | ["version"] | ["v"] => cmdVersion
  | ["help"] | ["h"] | [] =>
    IO.println usage
    return 0
  | _ =>
    IO.eprintln usage
    return 2

end Zmx.Runtime.Cli
