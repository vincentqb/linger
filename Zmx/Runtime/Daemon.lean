import Zmx.Posix
import Zmx.Core.Session
import Zmx.Runtime.Paths
/-! # Zmx.Runtime.Daemon — the poll loop around `Session.step`

All decisions live in the pure machine; this file only:
* turns fd readiness into `Session.Event`s,
* executes `Session.Effect`s as syscalls,
* owns the runtime's byte buffers, both bounded at 4 MiB so no buffer can
  grow the daemon — the runtime half of §Bound (the machine half is proved).
  A client that stops reading is disconnected at `outbufCap`; a child that
  stops reading has its input dropped at `ptyInCap` (there is nothing to
  disconnect — the child is the session). Both reclaim written bytes on every
  flush, not only on a full drain, so a slow-but-not-stopped consumer cannot
  grow them either.

Checkpoint effects are wired to hooks filled by `Zmx.Runtime.Resume`
(spec step 7): the daemon knows *when*, that module knows *what*.
-/

namespace Zmx.Runtime.Daemon

open Zmx.Posix
open Zmx.Core.Session (State Event Effect step)

/-- A stopped-reading client is cut here (runtime §Bound). -/
def outbufCap : Nat := 4194304

/-- And a stopped-reading *child* cannot grow the daemon either: past this
many unwritten bytes the newest input is dropped. Same number as `outbufCap`,
so the runtime half of §Bound is one sentence — no runtime buffer exceeds
4 MiB — and the same reason: the alternative to dropping is unbounded growth.
Dropping the newest is what a tty does when its own input buffer fills
(`IMAXBEL`); a child on a real terminal loses those keystrokes too. Dropping
whole `.input` frames cuts at a boundary the client already chose (one frame =
one read of the keyboard), so no UTF-8 sequence or escape is split. -/
def ptyInCap : Nat := 4194304

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
  /-- Whether we have already logged that `ptyIn` hit the cap, so the log
  records the *transition* into backpressure rather than one line per dropped
  chunk (which would be the same unbounded-growth defect, in the log file). -/
  ptyInFull : Bool := false
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

/-- Try to flush one connection's buffer; `none` = peer gone. On a partial
write we drop the already-written prefix (`extract`) rather than keep it: the
cap at `runEffect .send` measures `size - off`, but memory is the whole array,
so a peer that drains a little every round — never enough to empty the buffer —
would grow `out` without limit while `size - off` stayed small and the cap
never tripped. Compacting keeps `off` at 0 outside the loop, so pending and
size agree. -/
def flushConn (c : Conn) : IO (Option Conn) := do
  let mut c := c
  while c.off < c.out.size do
    let n ← write c.fd c.out (USize.ofNat c.off)
    if n < 0 then return none
    if n == 0 then break  -- would block; POLLOUT will resume
    c := { c with off := c.off + n.toNatClampNeg }
  if c.off ≥ c.out.size then
    return some { c with out := .empty, off := 0 }
  return some { c with out := c.out.extract c.off c.out.size, off := 0 }

def flushPty (rt : Rt) : IO Rt := do
  let mut buf := rt.ptyIn
  let mut off := rt.ptyInOff
  while off < buf.size do
    let n ← write rt.ptyFd buf (USize.ofNat off)
    if n ≤ 0 then break  -- EAGAIN or child gone; POLLOUT/EOF handles it
    off := off + n.toNatClampNeg
  if off ≥ buf.size then
    return { rt with ptyIn := .empty, ptyInOff := 0, ptyInFull := false }
  -- same compaction as `flushConn`, and the same reason: without it a
  -- partly-draining child grows the array while the pending count stays small.
  return { rt with ptyIn := buf.extract off buf.size, ptyInOff := 0 }

/-- Queue bytes for the child, bounded (runtime §Bound, the input half). Past
`ptyInCap` unwritten bytes the newest frame is dropped and the transition is
logged once — the daemon cannot make the child read faster, and holding the
input unboundedly only trades a wedged child for a wedged daemon. Not the
client-disconnect reaction `outbufCap` uses, because a `.writePty` carries no
client id (it is produced by `.input` from any client AND by the terminal
mediator's own query replies — see `Theorems/Session.lean`), and because the
flooder is usually the human's own paste into a program that stopped reading. -/
def queuePty (rt : Rt) (bytes : List UInt8) : IO Rt := do
  let pending := rt.ptyIn.size - rt.ptyInOff
  if pending + bytes.length > ptyInCap then
    if !rt.ptyInFull then
      IO.eprintln s!"linger: pty input buffer full ({pending} B, cap {ptyInCap}); \
        the child is not reading — dropping input until it does"
    return { rt with ptyInFull := true }
  flushPty { rt with ptyIn := rt.ptyIn ++ ByteArray.mk bytes.toArray }

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
    return (← queuePty rt bytes, [])
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
  -- Resume at the checkpoint's dimensions, not at 80×24. The restored `Vt`
  -- keeps the session's size, so spawning the pty at a fixed 80×24 handed the
  -- child a size that disagreed with the screen it was drawing onto until the
  -- first sizing attach reconciled them — and `linger run`/`send`/`wait` on a
  -- checkpointed-but-not-live session never attaches at all, so a full-screen
  -- app wrote 80 columns into a wider grid and the rest kept stale content.
  -- Matching them here also keeps the same-size-attach guard effective
  -- (`Theorems/Session.lean`'s `onMsg_attach_same_size_vt`): a client of the
  -- session's own size now finds `vt` already that size, so no `Vt.resize`
  -- fires and the scroll region and tab ruler survive the reattach.
  let vt0 := (restore.map (·.1)).getD (Zmx.Core.Vt.Vt.init 80 24)
  -- Clamp only the two numbers handed to the syscall, not `vt0` itself: a
  -- `Vt.resize` here would reset the scroll region and tab ruler (that is
  -- restore-conformance ledger item 1, re-introduced on the resume path where
  -- no theorem watches). `Checkpoint.load` is total on arbitrary bytes and does
  -- not clamp, so a corrupt or foreign checkpoint could carry `cols ≥ 65536`,
  -- which `UInt32.ofNat` then wraps to a 0-column tty in the shim's
  -- `(unsigned short)` cast. `clampDim` bounds it to [1,1000], the same range a
  -- live session is held to. A pathological checkpoint keeps a mismatched
  -- model, exactly as it did at the old fixed 80×24 — the alternative is
  -- mutating the restored screen.
  let (pid, ptyFd) ← spawnPty (UInt32.ofNat (Zmx.Core.Vt.clampDim vt0.cols))
    (UInt32.ofNat (Zmx.Core.Vt.clampDim vt0.rows)) cwd prog args
    #[s!"LINGER_SESSION={name}",
      "TERM=xterm-256color",
      "TERM_PROGRAM=linger",
      "TERM_PROGRAM_VERSION=0.1.0"]
  setNonblock ptyFd
  let created ← realtimeS
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
