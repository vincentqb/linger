import Zmx.Posix
import Zmx.Core.Session
import Zmx.Runtime.Paths
/-! # Zmx.Runtime.Daemon — the poll loop around `Session.step`

All decisions live in the pure machine; this file only:
* turns fd readiness into `Session.Event`s,
* executes `Session.Effect`s as syscalls,
* owns the per-client write buffers (bounded: a client that stops
  reading is disconnected at `outbufCap`, so a slow client cannot grow
  the daemon — the runtime half of §Bound; the machine half is proved).

Checkpoint effects are wired to hooks filled by `Zmx.Runtime.Resume`
(spec step 7): the daemon knows *when*, that module knows *what*.
-/

namespace Zmx.Runtime.Daemon

open Zmx.Posix
open Zmx.Core.Session (State Event Effect step)

/-- A stopped-reading client is cut here (runtime §Bound). -/
def outbufCap : Nat := 4194304

structure Conn where
  fd : UInt32
  out : ByteArray := .empty
  off : Nat := 0
  deriving Inhabited

structure Rt where
  st : State
  listenFd : UInt32
  ptyFd : UInt32
  childPid : UInt32
  conns : List Conn := []
  ptyIn : ByteArray := .empty
  ptyInOff : Nat := 0
  exiting : Bool := false
  sockPath : String
  /-- step-7 hooks -/
  saveCkpt : State → IO Unit
  dropCkpt : IO Unit

def Rt.conn? (rt : Rt) (fd : UInt32) : Option Conn :=
  rt.conns.find? (·.fd == fd)

def Rt.setConn (rt : Rt) (c : Conn) : Rt :=
  { rt with conns := rt.conns.map (fun c' => if c'.fd == c.fd then c else c') }

def Rt.dropConn (rt : Rt) (fd : UInt32) : Rt :=
  { rt with conns := rt.conns.filter (·.fd != fd) }

/-- Try to flush one connection's buffer; `none` = peer gone. -/
def flushConn (c : Conn) : IO (Option Conn) := do
  let mut c := c
  while c.off < c.out.size do
    let n ← write c.fd c.out (USize.ofNat c.off)
    if n < 0 then return none
    if n == 0 then break  -- would block; POLLOUT will resume
    c := { c with off := c.off + n.toNatClampNeg }
  if c.off ≥ c.out.size then
    return some { c with out := .empty, off := 0 }
  return some c

def flushPty (rt : Rt) : IO Rt := do
  let mut buf := rt.ptyIn
  let mut off := rt.ptyInOff
  while off < buf.size do
    let n ← write rt.ptyFd buf (USize.ofNat off)
    if n ≤ 0 then break  -- EAGAIN or child gone; POLLOUT/EOF handles it
    off := off + n.toNatClampNeg
  if off ≥ buf.size then
    return { rt with ptyIn := .empty, ptyInOff := 0 }
  return { rt with ptyIn := buf, ptyInOff := off }

/-- Execute one effect. Returns follow-up events (a close feeds
`.closed` back so the machine's roster stays true). -/
def runEffect (rt : Rt) (eff : Effect) : IO (Rt × List Event) := do
  match eff with
  | .send id m =>
    match rt.conn? (UInt32.ofNat id) with
    | none => return (rt, [])
    | some c =>
      let bytes := ByteArray.mk (Zmx.Core.Wire.encode m).toArray
      let c := { c with out := c.out ++ bytes }
      if c.out.size - c.off > outbufCap then
        -- runtime §Bound: cut the slow client rather than grow
        close c.fd
        return (rt.dropConn c.fd, [.closed c.fd.toNat])
      match ← flushConn c with
      | none =>
        close c.fd
        return (rt.dropConn c.fd, [.closed c.fd.toNat])
      | some c => return (rt.setConn c, [])
  | .close id =>
    let fd := UInt32.ofNat id
    if (rt.conn? fd).isSome then
      close fd
      return (rt.dropConn fd, [])
    return (rt, [])
  | .writePty bytes =>
    let rt := { rt with ptyIn := rt.ptyIn ++ ByteArray.mk bytes.toArray }
    return (← flushPty rt, [])
  | .resizePty cols rows =>
    try winsizeSet rt.ptyFd cols rows catch _ => pure ()
    return (rt, [])
  | .killChild =>
    kill rt.childPid 15  -- SIGTERM
    return (rt, [])
  | .checkpoint =>
    rt.saveCkpt rt.st
    return (rt, [])
  | .dropCheckpoint =>
    rt.dropCkpt
    return (rt, [])
  | .exit =>
    return ({ rt with exiting := true }, [])

/-- Feed events through the machine until quiescent, executing effects
as they come. -/
partial def pump (rt : Rt) (evs : List Event) : IO Rt := do
  match evs with
  | [] => return rt
  | ev :: rest =>
    let (st', effs) := step rt.st ev
    let mut rt := { rt with st := st' }
    let mut queue := rest
    for eff in effs do
      let (rt', more) ← runEffect rt eff
      rt := rt'
      queue := queue ++ more
    pump rt queue

/-- One poll round: gather events from fd readiness. -/
partial def pollRound (rt : Rt) : IO (Rt × List Event) := do
  -- snapshot: only these conns are in the poll set; accepts during
  -- this round join the NEXT one (revs stays index-aligned)
  let polled := rt.conns
  let mut fds : Array UInt32 := #[rt.listenFd, rt.ptyFd]
  let mut evts : Array UInt32 := #[POLLIN,
    POLLIN ||| (if rt.ptyIn.size > rt.ptyInOff then POLLOUT else 0)]
  for c in polled do
    fds := fds.push c.fd
    evts := evts.push (POLLIN ||| (if c.out.size > c.off then POLLOUT else 0))
  let revs ← poll fds evts 1000
  let mut rt := rt
  let mut events : List Event := []
  -- listen fd
  if revs[0]! &&& POLLIN != 0 then
    let mut go := true
    while go do
      let a ← accept rt.listenFd
      if a < 0 then
        go := false
      else
        let fd := a.toUInt64.toUInt32
        setNonblock fd
        rt := { rt with conns := rt.conns ++ [{ fd }] }
        events := events ++ [.connected fd.toNat]
  -- pty
  let ptyRev := revs[1]!
  if ptyRev &&& POLLOUT != 0 then
    rt ← flushPty rt
  if ptyRev &&& (POLLIN ||| POLLHUP ||| POLLERR) != 0 then
    match ← read rt.ptyFd 65536 with
    | some bs =>
      if bs.size > 0 then
        events := events ++ [.ptyOut bs.toList]
    | none =>
      -- child gone: reap and report
      let mut status : Int64 := -1
      let deadline := (← monotonicMs) + 3000
      while status == -1 && (← monotonicMs) < deadline do
        status ← waitpidNohang rt.childPid
        if status == -1 then IO.sleep 10
      events := events ++ [.childExited (if status < 0 then 1 else status.toUInt64.toUInt32)]
  -- clients (the polled snapshot only)
  let mut idx := 2
  for c in polled do
    let r := revs[idx]!
    idx := idx + 1
    -- the conn may have been dropped by an earlier iteration's close
    if (rt.conn? c.fd).isNone then
      continue
    if r &&& POLLOUT != 0 then
      match ← flushConn ((rt.conn? c.fd).getD c) with
      | none =>
        close c.fd
        rt := rt.dropConn c.fd
        events := events ++ [.closed c.fd.toNat]
      | some c' => rt := rt.setConn c'
    if r &&& (POLLIN ||| POLLHUP ||| POLLERR) != 0 then
      if (rt.conn? c.fd).isSome then
        match ← read c.fd 65536 with
        | some bs =>
          if bs.size > 0 then
            events := events ++ [.bytes c.fd.toNat bs.toList]
        | none =>
          close c.fd
          rt := rt.dropConn c.fd
          events := events ++ [.closed c.fd.toNat]
  return (rt, events)

/-- Daemon main. Blocks until the session ends. `restore` is a loaded
checkpoint: prior screen + labels (cwd was already consumed by the
spawner). -/
partial def serve (name : String) (cwd : String) (argv : List String)
    (saveCkpt : State → IO Unit) (dropCkpt : IO Unit)
    (restore : Option (Zmx.Core.Vt.Vt × List (String × String))) : IO Unit := do
  Zmx.Posix.init
  ignoreSighup
  let sockPath ← Paths.socketPath name
  -- Claim the *name* before touching the socket path. Without this the
  -- sequence probe → unlink-stale → bind has a window: two daemons can
  -- both pass the probe, and the second unlinks the first's live socket
  -- before binding its own, orphaning a daemon that still holds a shell.
  -- The lock is held for this process's whole life, so the kernel
  -- releases it on exit/crash — no staleness timeout, and holding it is
  -- itself the proof that this daemon owns the name.
  let lockFd ← flock (← Paths.lockPath name)
  if lockFd < 0 then
    -- another daemon owns or is starting this name; the client that
    -- spawned us polls for the socket and will find the winner's
    throw (IO.userError s!"session '{name}' is already owned by another daemon")
  -- Only the lock holder reaches this point, so the stale check and the
  -- bind below cannot interleave with another daemon's.
  match ← unixConnect sockPath with
  | r =>
    if r ≥ 0 then
      close r.toUInt64.toUInt32
      throw (IO.userError s!"session '{name}' already running")
    else if r == -111 then  -- ECONNREFUSED: stale socket, ours to replace
      try IO.FS.removeFile sockPath catch _ => pure ()
  let listenFd ← unixListen sockPath
  setNonblock listenFd
  let shell := (← IO.getEnv "SHELL").getD "sh"
  let (prog, args) := match argv with
    | [] => ((shell, #[]) : String × Array String)
    | p :: rest => (p, rest.toArray)
  let (pid, ptyFd) ← spawnPty 80 24 cwd prog args
    #[s!"LZMX_SESSION={name}"]
  setNonblock ptyFd
  let created ← realtimeS
  let vt0 := (restore.map (·.1)).getD (Zmx.Core.Vt.Vt.init 80 24)
  let st : State := {
    vt := vt0
    labels := (restore.map (·.2)).getD []
    metaKv := [
      ("name", name), ("pid", toString pid),
      ("created", toString created),
      ("cmd", String.intercalate " " (prog :: args.toList)),
      ("start_dir", cwd)]
  }
  let mut rt : Rt := { st, listenFd, ptyFd, childPid := pid, sockPath,
                       saveCkpt, dropCkpt }
  while !rt.exiting do
    let (rt', events) ← pollRound rt
    let now ← monotonicMs
    rt ← pump rt' (events ++ [.tick now])
  -- shutdown: make sure the child is gone, drop the socket
  if ← alive rt.childPid then
    kill rt.childPid 15
    IO.sleep 150
    if ← alive rt.childPid then kill rt.childPid 9
  let _ ← waitpidNohang rt.childPid
  try IO.FS.removeFile sockPath catch _ => pure ()
  -- the lock file stays; the kernel drops the lock as this process exits
  -- (unlinking it would let a newcomer lock a fresh inode while ours
  -- still held the old one)
  let _ := lockFd

end Zmx.Runtime.Daemon
