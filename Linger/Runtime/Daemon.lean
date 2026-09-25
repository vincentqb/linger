module

public import Linger.Posix
public import Linger.Core.Session
public import Linger.Runtime.Paths

public section

/-! # Linger.Runtime.Daemon — the poll loop around `Session.step`

All decisions live in the pure machine; this file only:
* turns fd readiness into `Session.Event`s,
* executes `Session.Effect`s as syscalls,
* drives the runtime's two byte queues, both bounded at 4 MiB so no buffer can
  grow the daemon. A client that stops reading is disconnected at `outbufCap`;
  a child that stops reading has its input dropped at `ptyInCap` (there is
  nothing to disconnect — the child is the session).

The queues themselves are **not** this file's: they are `Linger.Core.Buf`, whose
`Theorems/Buf.lean` proves the caps and that nothing written is retained. That is
the runtime half of §Bound, and it used to be a paragraph saying "not proved".
What this file still owns is *when* to enqueue and how to react to a short write,
which is `IO` and therefore gated rather than proved: `tests/gates.sh` checks that
`Linger/Runtime/*` declares no byte buffer of its own, because no theorem can see
that this file calls those functions instead of open-coding the same sums.

Checkpoint effects are wired to hooks filled by `Linger.Runtime.Resume`
(spec step 7): the daemon knows *when*, that module knows *what*.
-/

namespace Linger.Runtime.Daemon

open Linger.Posix
open Linger.Core.Session (State Event Effect maxClients step)
open Linger.Core.Buf (Buf owedLen bufOffer bufEnqueue bufAdvance)

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
  /-- The client's backlog. Starts empty and is sealed: every state this field
  can reach is covered by `Buf.reachableOut_bound` — within `outbufCap` for the
  connection's whole life, given the cut discipline below. -/
  out : Buf := .empty
  deriving Inhabited

structure Rt where
  st : State
  listenFd : UInt32
  ptyFd : UInt32
  childPid : UInt32
  conns : List Conn := []
  /-- The pty-input backlog. Starts empty and is sealed: every state it can
  reach is `Buf.ReachableIn ptyInCap`, so `reachableIn_bound` bounds it for the
  daemon's whole life — not per call. -/
  ptyIn : Buf := .empty
  /-- Whether we have already logged that `ptyIn` hit the cap, so the log
  records the *transition* into backpressure rather than one line per dropped
  chunk (which would be the same unbounded-growth defect, in the log file). -/
  ptyInFull : Bool := false
  exiting : Bool := false
  sockPath : String
  /-- step-7 hooks -/
  saveCkpt : State → IO Unit
  dropCkpt : IO Unit

def Rt.conn? (rt : Rt) (fd : UInt32) : Option Conn := rt.conns.find? (·.fd == fd)

def Rt.setConn (rt : Rt) (c : Conn) : Rt :=
  { rt with conns := rt.conns.map (fun c' => if c'.fd == c.fd then c else c') }

def Rt.dropConn (rt : Rt) (fd : UInt32) : Rt := { rt with conns := rt.conns.filter (·.fd != fd) }

/-- Try to flush one connection's queue; `none` = peer gone.

The cursor is a **local** `Nat`, and `bufAdvance` is called once when the loop
stops: a `Buf` holds exactly what is still owed, so the written prefix is never
retained and the cap therefore measures memory rather than a counter
(`Buf.bufNoRetain`, `Buf.bufAdvance_owed`). The two write reactions are the
reason this is not shared with `flushPty`: here `n < 0` means the peer is gone and
the caller must close the fd and feed `.closed` back into the machine, while
`n == 0` is EAGAIN and POLLOUT resumes. -/
def flushConn (c : Conn) : IO (Option Conn) := do
  let mut wrote := 0
  let owed := owedLen c.out
  while wrote < owed do
    let n ← writeBuf c.fd c.out wrote
    if n < 0 then
      return none
    if n == 0 then
      break -- would block; POLLOUT will resume
    wrote := wrote + n.toNatClampNeg
  return some { c with out := bufAdvance c.out wrote }

/-- The same bookkeeping for the child's input queue, with the *other* reaction:
both `n ≤ 0` cases collapse to `break`, because a dead child surfaces as `read`
returning `none` → `.childExited`, and there is nothing to disconnect. Sharing the
loop would invite "fixing" that asymmetry, which would either drop the pty queue
on a transient or leave a dead client's frames queued. -/
def flushPty (rt : Rt) : IO Rt := do
  let mut wrote := 0
  let owed := owedLen rt.ptyIn
  while wrote < owed do
    let n ← writeBuf rt.ptyFd rt.ptyIn wrote
    if n ≤ 0 then
      break -- EAGAIN or child gone; POLLOUT/EOF handles it
    wrote := wrote + n.toNatClampNeg
  let q := bufAdvance rt.ptyIn wrote
  -- clear the backpressure latch exactly when the queue drains, so the log
  -- records the transition once (`robust_test` asserts exactly-once)
  return { rt with
      ptyIn := q, ptyInFull := rt.ptyInFull && owedLen q != 0 }

/-- Queue bytes for the child, bounded (runtime §Bound, the input half). Past
`ptyInCap` unwritten bytes the newest frame is dropped and the transition is
logged once — the daemon cannot make the child read faster, and holding the
input unboundedly only trades a wedged child for a wedged daemon. Not the
client-disconnect reaction `outbufCap` uses, because a `.writePty` carries no
client id (it is produced by `.input` from any client AND by the terminal
mediator's own query replies — see `Theorems/Session.lean`), and because the
flooder is usually the human's own paste into a program that stopped reading. -/
def queuePty (rt : Rt) (bytes : List UInt8) : IO Rt := do
  let pending := owedLen rt.ptyIn
  let (q, dropped) := bufOffer ptyInCap rt.ptyIn (ByteArray.mk bytes.toArray)
  if dropped then
    if !rt.ptyInFull then
      IO.eprintln
          s!"linger: pty input buffer full ({pending} B, cap {ptyInCap}); \
        the child is not reading — dropping input until it does"
    return { rt with ptyInFull := true }
  flushPty { rt with ptyIn := q }

/-- Execute one effect. Returns follow-up events (a close feeds
`.closed` back so the machine's roster stays true). -/
def runEffect (rt : Rt) (eff : Effect) : IO (Rt × List Event) := do
  match eff with
  | .send id m =>
    match rt.conn? (UInt32.ofNat id) with
    | none =>
      return (rt, [])
    | some c =>
      let bytes := ByteArray.mk (Linger.Core.Wire.encode m).toArray
      let (q, cut) := bufEnqueue outbufCap c.out bytes
      let c := { c with out := q }
      if cut then
        -- runtime §Bound: cut the slow client rather than grow
        close c.fd
        return (rt.dropConn c.fd, [.closed c.fd.toNat])
      match ← flushConn c with
      | none =>
        close c.fd
        return (rt.dropConn c.fd, [.closed c.fd.toNat])
      | some c =>
        return (rt.setConn c, [])
  | .close id =>
    let fd := UInt32.ofNat id
    if (rt.conn? fd).isSome then
      close fd
      return (rt.dropConn fd, [.closed id])
    return (rt, [])
  | .writePty bytes =>
    return (← queuePty rt bytes, [])
  | .resizePty cols rows =>
    try
      winsizeSet rt.ptyFd cols rows
    catch _ =>
      pure ()
    return (rt, [])
  | .killChild =>
    kill rt.childPid 15 -- SIGTERM
    return (rt, [])
  | .checkpoint =>
    try
      rt.saveCkpt rt.st
    catch err =>
      IO.eprintln s!"linger: checkpoint save failed: {err}"
    return (rt, [])
  | .dropCheckpoint =>
    try
      rt.dropCkpt
    catch err =>
      IO.eprintln s!"linger: checkpoint delete failed: {err}"
    return (rt, [])
  | .exit =>
    return ({ rt with exiting := true }, [])

/-- Feed events through the machine until quiescent or exited. Events queued
behind exit must not checkpoint a session whose recovery state was deleted. -/
def pump (rt : Rt) (evs : List Event) : IO Rt := do
  let mut rt := rt
  let mut queue := evs
  while !rt.exiting do
    let ev :: rest := queue | break
    let (st', effs) := step rt.st ev
    rt := { rt with st := st' }
    queue := rest
    for eff in effs do
      let (rt', more) ← runEffect rt eff
      rt := rt'
      queue := queue ++ more
  return rt

/-- One poll round: gather events from fd readiness. -/
def pollRound (rt : Rt) : IO (Rt × List Event) := do
  -- snapshot: only these conns are in the poll set; accepts during
  -- this round join the NEXT one (revs stays index-aligned)
  let polled := rt.conns
  let mut fds : Array UInt32 := #[rt.listenFd, rt.ptyFd]
  let mut evts : Array UInt32 :=
    #[POLLIN, POLLIN ||| (if owedLen rt.ptyIn != 0 then POLLOUT else 0)]
  for c in polled do
    fds := fds.push c.fd
    evts := evts.push (POLLIN ||| (if owedLen c.out != 0 then POLLOUT else 0))
  let revs ← poll fds evts 1000
  let mut rt := rt
  let mut events : List Event := []
  -- listen fd
  if revs[0]! &&& POLLIN != 0 then
    -- Bound one round by the pure roster cap. The queued `.connected` events
    -- make the core admit or refuse each fd before the next poll.
    for _ in List.range maxClients do
      let a ← accept rt.listenFd
      if a < 0 then
        break
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
        if status == -1 then
          IO.sleep 10
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
      | some c' =>
        rt := rt.setConn c'
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
def serve (name : String) (cwd : String) (argv : List String) (saveCkpt : State → IO Unit)
    (dropCkpt : IO Unit) (restore : Option (Linger.Core.Vt.Vt × List (String × String))) :
    IO Unit := do
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
    else
      -- Nothing answered, so whatever is at the path is ours to replace.
      -- This used to test `r == -111` for ECONNREFUSED, which is glibc's
      -- number: on macOS it is 61, the branch never fired, and the bind
      -- below failed EADDRINUSE for every daemon replacing a stale socket
      -- (the name-ownership race test caught it). No errno needs
      -- distinguishing here — this daemon already holds the name lock, so no
      -- live owner can be using the path. Listing cannot assume that: it probes
      -- the same lock before removing a failed-connect socket.
      try
        IO.FS.removeFile sockPath
      catch _ =>
        pure ()
  let listenFd ← unixListen sockPath
  setNonblock listenFd
  let shell := (← IO.getEnv "SHELL").getD "sh"
  let (prog, args) :=
    match argv with
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
  let vt0 := (restore.map (·.1)).getD (Linger.Core.Vt.Vt.init 80 24)
  -- Clamp only the two numbers handed to the syscall, not `vt0` itself: a
  -- `Vt.resize` here would reset the scroll region and tab ruler (that is
  -- restore-conformance ledger item 1, re-introduced on the resume path where
  -- no theorem watches).
  --
  -- **This is now belt-and-braces, and it stays.** `Checkpoint.load` no longer accepts
  -- a record whose dimensions are junk: `rVt` hands its decoded fields to
  -- `Vt.ofDecoded`, which refuses anything that is not `Good`, and
  -- `Theorems/Checkpoint.lean`'s `load_good` says so for *any* byte string —
  -- `load l = some c → Good c.vt`, hence `1 ≤ cols ≤ 1000`. So both sources of `vt0`
  -- are already in range: a loaded checkpoint by that theorem, `Vt.init 80 24` by
  -- `clampDim` inside `init`. `clampDim` here cannot change either value.
  --
  -- It is kept for two reasons, neither of them doubt about the theorem. This is the
  -- last line before `UInt32.ofNat` and the shim's `(unsigned short)` cast, where the
  -- old failure was a `cols ≥ 65536` checkpoint wrapping to a 0-column tty — and
  -- `Linger/Runtime/*` is `IO`, so no theorem can see this call site. Deleting the
  -- clamp would move the syscall's safety into a chain of reasoning in another module
  -- with no local evidence, and would silently mis-size the pty the first time
  -- someone adds a third source for `vt0` (a `--size` flag, a second reader) without
  -- re-deriving the argument. Two `min`/`max` per session spawn is the whole cost.
  let (pid, ptyFd) ←
    spawnPty (UInt32.ofNat (Linger.Core.Vt.clampDim vt0.colCount))
        (UInt32.ofNat (Linger.Core.Vt.clampDim vt0.rowCount)) cwd prog args
        #[s!"LINGER_SESSION={name}", "TERM=xterm-256color", "TERM_PROGRAM=linger",
          "TERM_PROGRAM_VERSION=0.1.0"]
  setNonblock ptyFd
  let created ← realtimeS
  let st :=
    State.boot vt0 ((restore.map (·.2)).getD [])
      [("name", name), ("pid", toString pid), ("created", toString created),
        ("cmd", String.intercalate " " (prog :: args.toList)), ("start_dir", cwd)]
  let mut rt : Rt := { st, listenFd, ptyFd, childPid := pid, sockPath, saveCkpt, dropCkpt }
  try
    while !rt.exiting do
      let (rt', events) ← pollRound rt
      let now ← monotonicMs
      rt ← pump rt' (events ++ [.tick now])
  finally
    -- Stop admitting work, close every owned transport, kill/reap the child,
    -- then unlink while the name lock is still held. This runs on normal exit
    -- and on an unexpected poll/effect exception.
    close rt.listenFd
    for c in rt.conns do
      close c.fd
    try
      if ← alive rt.childPid then
        kill rt.childPid 15
        IO.sleep 150
        if ← alive rt.childPid then
          kill rt.childPid 9
    catch err =>
      IO.eprintln s!"linger: child cleanup failed: {err}"
    let _ ← waitpidNohang rt.childPid
    close rt.ptyFd
    try
      IO.FS.removeFile sockPath
    catch _ =>
      pure ()
    close lockFd.toUInt64.toUInt32

end Linger.Runtime.Daemon
