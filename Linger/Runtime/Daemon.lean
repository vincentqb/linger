module

public import Linger.Posix
public import Linger.Core.Driver
public import Linger.Runtime.Paths

public section

/-! # Linger.Runtime.Daemon — the poll loop around `Session.step`

`Session.step` owns protocol and session decisions. This file schedules fd
readiness, executes effects, and drains accepted streams. Each client owns one
immutable replay cursor and two `Buf` byte buffers sharing `outbufCap` in
retained logical byte length: the front buffer precedes the cursor, and the
following buffer holds later output and exit notifications. Replay advances by
at most one new frame per flush. A client is cut if subsequent output exceeds
the shared allowance. The child's separate input buffer drops new input at
`ptyInCap`.

Active and retired client transports share `maxClients`. Logical close reports
`.closed` immediately; accepted bytes may drain until the connection's fixed
deadline. Final shutdown also has a finite drain grace period.

`Theorems/Buf.lean` proves the byte-buffer caps, shared allowance and removal of
written prefixes. `Theorems/Replay.lean` proves the cursor's exact stream,
progress and storage bound. Runtime scheduling and short-write handling are
`IO`, so source gates tie these proved operations to their actual consumers.

Checkpoint effects are wired to hooks filled by `Linger.Runtime.Resume`
(spec step 7): the daemon knows *when*, that module knows *what*.
-/

namespace Linger.Runtime.Daemon

open Linger.Posix
open Linger.Core.Session (State Event Effect maxClients)
open Linger.Core.Buf (Buf owedLen bufOffer bufEnqueue bufAdvance followingCap)
open Linger.Core

/-- A stopped-reading client is cut here (runtime §Bound). -/
def outbufCap : Nat := 4194304

/-- Payload plus the wire encoder's own frame overhead. -/
def replayFrameCap : Nat := Linger.Core.Session.outputChunk + (Wire.encode (.output [])).length

/-- Ordinary close and final shutdown share one finite drain grace period. -/
def drainTimeoutMs : Nat := 3000

/-- Retry admission without spinning on a readable listener under resource pressure. -/
def acceptRetryMs : Nat := 1000

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
  /-- One immutable snapshot cursor, never a queue of rendered effects. -/
  replay : Option Replay.Plan := none
  /-- Bytes accepted after the replay. Shares `outbufCap` with `out`. -/
  after : Buf := .empty
  /-- Logical removal has already been reported. Finish accepted bytes before
  this deadline; repeating a close never extends it. -/
  closeBy : Option Nat := none
  deriving Inhabited

def Conn.closing (c : Conn) : Bool := c.closeBy.isSome

def Conn.pending (c : Conn) : Bool := owedLen c.out != 0 || c.replay.isSome || owedLen c.after != 0

structure Rt where
  st : State
  listenFd : UInt32
  ptyFd : UInt32
  childPid : UInt32
  conns : List Conn := []
  /-- Admission is suspended until this deadline. Keep the failure latched
  until an accept succeeds so continuing pressure produces one diagnostic. -/
  acceptAfter : Option Nat := none
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

/-- A diagnostic write failure must not turn recovery into session loss. -/
def report (message : String) : IO Unit := do
  try
    IO.eprintln message
  catch _ =>
    pure ()

def Rt.conn? (rt : Rt) (fd : UInt32) : Option Conn := rt.conns.find? (·.fd == fd)

def Rt.setConn (rt : Rt) (c : Conn) : Rt :=
  { rt with conns := rt.conns.map (fun c' => if c'.fd == c.fd then c else c') }

def Rt.dropConn (rt : Rt) (fd : UInt32) : Rt := { rt with conns := rt.conns.filter (·.fd != fd) }

/-- Retired transports still own buffers and a snapshot. Their deadline
releases that ownership even while the rest of the session stays alive. -/
def expireConns (rt : Rt) (now : Nat) : IO Rt := do
  let mut rt := rt
  for c in rt.conns do
    if c.closeBy.any (now ≥ ·) then
      close c.fd
      rt := rt.dropConn c.fd
  return rt

/-- Try to flush one connection's queue; `none` = peer gone.

The write offset is a **local** `Nat`, and `bufAdvance` is called once when the
write loop stops: `Buf.bufSize` is the retained logical byte length and equals
what is still owed (`Buf.bufNoRetain`, `Buf.bufAdvance_owed`). Allocator capacity
and physical heap footprint are outside that bound. The two write reactions are the
reason this is not shared with `flushPty`: here `n < 0` means the peer is gone and
the caller must close the fd and feed `.closed` back into the machine, while
`n == 0` is EAGAIN and POLLOUT resumes. -/
def flushConn (c : Conn) : IO (Option Conn) := do
  let mut c := c
  let mut filled := false
  while true do
    if owedLen c.out == 0 then
      if filled then
        break
      match c.replay with
      | some plan =>
        match Replay.next Linger.Core.Session.outputChunk plan with
        | none =>
          c := { c with replay := none }
          continue
        | some (bytes, plan) =>
          c := { c with replay := some plan }
          if bytes.isEmpty then
            continue
          let (q, cut) :=
            bufEnqueue (outbufCap - owedLen c.after) .empty
              (ByteArray.mk (Wire.encode (.output bytes)).toArray)
          if cut then
            return none
          c := { c with out := q }
      | none =>
        if owedLen c.after == 0 then
          break
        c :=
          { c with
            out := c.after, after := .empty }
      -- At most one new frame per call, so a writable replay cannot monopolize
      -- the poll loop. Empty cursor transitions have a proved progress measure.
      filled := true
    let mut wrote := 0
    let owed := owedLen c.out
    while wrote < owed do
      let n ← writeBuf c.fd c.out wrote
      if n < 0 then
        return none
      if n == 0 then
        break
      wrote := wrote + n.toNatClampNeg
    c := { c with out := bufAdvance c.out wrote }
    if wrote < owed then
      break
  return some c

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
      report
          s!"linger: pty input buffer full ({pending} B, cap {ptyInCap}); \
        the child is not reading — dropping input until it does"
    return { rt with ptyInFull := true }
  flushPty { rt with ptyIn := q }

/-- Execute one effect against the world. Its result type admits only the
feedback that the total driver has proved will terminate. Session state is
read-only here; the driver supplies the state after the current event. -/
def executeEffect (st : State) (rt : Rt) : (eff : Effect) → IO (Rt × Driver.Reply eff)
  | .send id m => do
    match rt.conn? (UInt32.ofNat id) with
    | none =>
      return (rt, false)
    | some c =>
      if c.closing then
        return (rt, false)
      let bytes := ByteArray.mk (Linger.Core.Wire.encode m).toArray
      let (c, cut) :=
        if c.replay.isSome || owedLen c.after != 0 then
          let cap := followingCap outbufCap replayFrameCap (owedLen c.out)
          let (q, cut) := bufEnqueue cap c.after bytes
          ({ c with after := q }, cut)
        else
          let (q, cut) := bufEnqueue outbufCap c.out bytes
          ({ c with out := q }, cut)
      if cut then
        -- runtime §Bound: cut the slow client rather than grow
        close c.fd
        return (rt.dropConn c.fd, true)
      match ← flushConn c with
      | none =>
        close c.fd
        return (rt.dropConn c.fd, true)
      | some c =>
        return (rt.setConn c, false)
  | .replay id plan => do
    match rt.conn? (UInt32.ofNat id) with
    | none =>
      return (rt, false)
    | some c =>
      if c.closing then
        return (rt, false)
      if c.replay.isSome then
        close c.fd
        return (rt.dropConn c.fd, true)
      match ← flushConn { c with replay := some plan } with
      | none =>
        close c.fd
        return (rt.dropConn c.fd, true)
      | some c =>
        return (rt.setConn c, false)
  | .close id => do
    let fd := UInt32.ofNat id
    match rt.conn? fd with
    | none =>
      return (rt, false)
    | some c =>
      if c.closing then
        return (rt, false)
      if c.pending then
        let deadline := (← IO.monoMsNow) + drainTimeoutMs
        return (rt.setConn { c with closeBy := some deadline }, true)
      close fd
      return (rt.dropConn fd, true)
  | .writePty bytes => do
    return (← queuePty rt bytes, ())
  | .resizePty cols rows => do
    try
      winsizeSet rt.ptyFd cols rows
    catch _ =>
      pure ()
    return (rt, ())
  | .killChild => do
    kill rt.childPid 15 -- SIGTERM
    return (rt, ())
  | .checkpoint => do
    try
      rt.saveCkpt st
      return (rt, false)
    catch err =>
      report s!"linger: checkpoint save failed: {err}"
      return (rt, true)
  | .dropCheckpoint => do
    try
      rt.dropCkpt
    catch err =>
      report s!"linger: checkpoint delete failed: {err}"
    return (rt, ())
  | .exit => do
    return (rt, ())

/-- Execute an isolated effect, using the driver's typed feedback policy. -/
def runEffect (rt : Rt) (eff : Effect) : IO (Rt × List Event) := do
  let (next, reply) ← executeEffect rt.st rt eff
  return ({ next with exiting := rt.exiting || eff == .exit }, Driver.feedback eff reply)

/-- Feed events through the machine until quiescent or exited. Events queued
behind exit must not checkpoint a session whose recovery state was deleted.
Effect feedback precedes the next queued event, in effect order: a close must
remove its client before already-read bytes from that client are considered. -/
def pump (rt : Rt) (evs : List Event) : IO Rt := do
  let result ← Driver.run executeEffect { st := rt.st, world := rt, exiting := rt.exiting } evs
  return { result.world with
      st := result.st, exiting := result.exiting }

/-- One poll round: gather events from fd readiness. -/
def pollRound (rt : Rt) : IO (Rt × List Event) := do
  let now ← IO.monoMsNow
  let rt ← expireConns rt now
  let mut timeout := 1000
  for c in rt.conns do
    if let some deadline := c.closeBy then
      timeout := min timeout (deadline - now)
  if let some retryAt := rt.acceptAfter then
    if now < retryAt then
      timeout := min timeout (retryAt - now)
  let accepting := rt.conns.length < maxClients && rt.acceptAfter.all (now ≥ ·)
  -- snapshot: only these conns are in the poll set; accepts during
  -- this round join the NEXT one (revs stays index-aligned)
  let polled := rt.conns
  let mut fds : Array UInt32 := #[rt.listenFd, rt.ptyFd]
  let mut evts : Array UInt32 :=
    #[(if accepting then POLLIN else 0), POLLIN ||| (if owedLen rt.ptyIn != 0 then POLLOUT else 0)]
  for c in polled do
    fds := fds.push c.fd
    evts := evts.push ((if c.closing then 0 else POLLIN) ||| (if c.pending then POLLOUT else 0))
  let revs ← poll fds evts (Int32.ofNat timeout)
  let mut rt := rt
  let mut events : List Event := []
  -- listen fd
  if revs[0]! &&& POLLIN != 0 then
    -- The same cap covers every owned transport, including logical closes
    -- whose accepted stream is still draining. Connections beyond it wait in
    -- the kernel backlog until a slot is released.
    for _ in List.range (maxClients - rt.conns.length) do
      try
        let a ← accept rt.listenFd
        if a < 0 then
          break
        let fd := a.toUInt64.toUInt32
        try
          setNonblock fd
        catch err =>
          close fd
          throw err
        rt :=
          { rt with
            conns := rt.conns ++ [{ fd }], acceptAfter := none }
        events := events ++ [.connected fd.toNat]
      catch err =>
        if rt.acceptAfter.isNone then
          report s!"linger: client admission paused; retrying: {err}"
        rt := { rt with acceptAfter := some ((← IO.monoMsNow) + acceptRetryMs) }
        break
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
        if !c.closing then
          events := events ++ [.closed c.fd.toNat]
      | some c' =>
        if c'.closing && !c'.pending then
          close c'.fd
          rt := rt.dropConn c'.fd
        else
          rt := rt.setConn c'
    if r &&& (POLLIN ||| POLLHUP ||| POLLERR) != 0 then
      if let some current := rt.conn? c.fd then
        if current.closing then
          if r &&& (POLLHUP ||| POLLERR) != 0 then
            close c.fd
            rt := rt.dropConn c.fd
          continue
        -- A cancelled request may reset a socket with an unread reply.
        -- Retire that peer through the same transition as EOF.
        let received ←
          try
            read c.fd 65536
          catch _ =>
            pure none
        match received with
        | some bs =>
          if bs.size > 0 then
            events := events ++ [.bytes c.fd.toNat bs.toList]
        | none =>
          close c.fd
          rt := rt.dropConn c.fd
          events := events ++ [.closed c.fd.toNat]
  return (rt, events)

/-- Stop admitting work and drain accepted bytes, with a finite grace period.
Every poll freezes its fd list; no session events execute after `.exit`. -/
def drainConns (rt : Rt) : IO Rt := do
  let mut rt := rt
  let deadline := (← IO.monoMsNow) + drainTimeoutMs
  while !rt.conns.isEmpty do
    let now ← IO.monoMsNow
    rt ← expireConns rt now
    if rt.conns.isEmpty then
      break
    if now ≥ deadline then
      break
    let polled := rt.conns
    let fds := (polled.map (·.fd)).toArray
    let revs ← poll fds (Array.replicate fds.size POLLOUT) (Int32.ofNat (min 100 (deadline - now)))
    for (c, i) in polled.zipIdx do
      if revs[i]! &&& (POLLOUT ||| POLLHUP ||| POLLERR) != 0 then
        match ← flushConn c with
        | some c =>
          if c.pending then
            rt := rt.setConn c
          else
            close c.fd
            rt := rt.dropConn c.fd
        | none =>
          close c.fd
          rt := rt.dropConn c.fd
  for c in rt.conns do
    close c.fd
  return { rt with conns := [] }

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
    rt ← drainConns rt
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
      report s!"linger: child cleanup failed: {err}"
    let _ ← waitpidNohang rt.childPid
    close rt.ptyFd
    try
      IO.FS.removeFile sockPath
    catch _ =>
      pure ()
    close lockFd.toUInt64.toUInt32

end Linger.Runtime.Daemon
