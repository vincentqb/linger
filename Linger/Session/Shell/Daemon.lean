module

import Linger.Os.Shell
public import Linger.Session.Buf
import Linger.Session.Driver
public import Linger.Session
public import Linger.Session.Record
public import Linger.Session.Start
import Linger.Terminal.Mediation
import Linger.Os.Env
import Linger.Session.Shell.Paths

public section

/-! # Linger.Session.Shell.Daemon — the poll loop around `Session.step`

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

The session ends when its program does. The daemon hears a child end through the descriptor
`childEndFd` makes, whether or not a background job still holds the terminal, and then reaps
the program without blocking and reports how it ended; the terminal's end of file ends nothing
by itself. Between events it sleeps until the session's next tick (`State.nextTick`), so an
idle session costs no wakeup.

`Linger/Session/Proofs/Buf.lean` proves the byte-buffer caps, shared allowance and removal of
written prefixes. `Linger/Terminal/Proofs/Replay.lean` proves the cursor's exact stream,
progress and storage bound. Runtime scheduling and short-write handling are
`IO`, so source gates tie these proved operations to their actual consumers.

Checkpoint effects are wired to checkpoint hooks from `Linger.Session.Shell.Resume`:
the daemon knows *when*, that module knows *what*. A save runs on a thread of its own, one at a
time, and a later request replaces any that waits, so a slow disk holds up no answer and no
output (`Offloop`, `collectSave`); before the daemon gives the name up it waits for them
(`finishSaves`). The name's end record is written the same way whenever what the daemon sees of
the output changes (`publish`), so a summary reads the record instead of waking the daemon.
-/

namespace Linger.Session.Shell.Daemon

open Linger.Os.Shell
open Linger.Session (State Event Effect Outcome maxClients)
open Linger.Session.Buf (Buf owedLen bufOffer bufEnqueue bufAdvance followingCap)
open Linger.Terminal
open Linger.Terminal.Replay (Plan)

/-- One write attempt for a `Linger.Session.Buf` queue, skipping the `sent` bytes the
flush loop already got out. The result is `write`'s: `≥ 0` bytes written (0 = would
block, or nothing is owed past `sent`); `-1` = peer gone; other errors throw.
`Buf.writeFrom` is the byte view of the debt, so what reaches `write(2)` here is the debt
and nothing else: `Buf.bufSize_eq_owedLen` shows the queue retains no more, and
`Buf.bufAdvance_writeFrom` gives what the loop leaves after advancing.

`sent` is the flush loop's **transient** cursor, not stored state: a `Buf` holds
exactly the bytes still owed, and the loop calls `Buf.bufAdvance` once when it
stops. Passing the cursor here rather than re-slicing per iteration keeps a flush
to a single copy.

This wraps `Linger.Os.Shell.write`, so it is not a new syscall. It cannot read a `Buf`'s
representation — `bytes` is `private`, and this calls the one API window, `writeFrom`.
`scripts/gates.sh`'s greps still gate the session shell against declaring parallel byte
buffers of its own, the half privacy cannot see. -/
private def writeBuf (fd : UInt32) (b : Buf) (sent : Nat) : IO Int64 :=
  write fd (Linger.Session.Buf.writeFrom b) (USize.ofNat sent)

/-- A stopped-reading client is cut here (`Buf.reachableOut_bound`). -/
def outbufCap : Nat := 4194304

/-- Payload plus the wire encoder's own frame overhead. -/
def replayFrameCap : Nat := Linger.Session.outputChunk + (Wire.encode (.output [])).length

/-- Ordinary close and final shutdown share one finite drain grace period. -/
def drainTimeoutMs : Nat := 3000

/-- Retry admission without spinning on a readable listener under resource pressure. -/
def acceptRetryMs : Nat := 1000

/-- How often a daemon whose checkpoint is being saved looks whether the save has ended. A save
usually ends within milliseconds; its end matters only to start the save that waited for it or
to retry a failure, so the daemon need not hear it at once. -/
def saveCheckMs : Nat := 50

/-- A stopped-reading *child* cannot grow the daemon either: past this many
unwritten bytes the newest whole `.input` frame is dropped, as a tty drops input
when its own buffer fills (`IMAXBEL`). One frame is one read of the keyboard, so
no UTF-8 sequence or escape is split. -/
def ptyInCap : Nat := outbufCap

/-- Writes of one kind that the daemon does off its loop: at most one runs, on a thread of its
own, and a later one replaces any that waits for it. So a slow disk holds up no answer and no
output, and writes are coalesced and never queue. -/
structure Offloop where
  /-- The write running on its own thread, if any. -/
  running : Option (Task (Except IO.Error Unit)) := none
  /-- The latest write asked for while one ran; it runs when that one ends. -/
  waiting : Option (IO Unit) := none

/-- Run `write` on its own thread now, or after the running write in place of any that waits. -/
def Offloop.ask (w : Offloop) (write : IO Unit) : IO Offloop := do
  if w.running.isSome then
    return { w with waiting := some write }
  return { running := some (← IO.asTask write Task.Priority.dedicated) }

/-- How the running write ended, once it has, or after waiting for it with `block`; the write
that waited for it then starts. `none` while it runs, or when none does. -/
def Offloop.collect (w : Offloop) (block : Bool := false) :
    IO (Offloop × Option (Except IO.Error Unit)) := do
  let some task := w.running | return (w, none)
  unless block || (← IO.hasFinished task) do
    return (w, none)
  let ended ← IO.wait task
  match w.waiting with
  | some write =>
    return ({ running := some (← IO.asTask write Task.Priority.dedicated) }, some ended)
  | none =>
    return ({}, some ended)

/-- One accepted client transport: its socket and the output still owed to it. -/
structure Conn where
  /-- The accepted socket, nonblocking; its number is the client's id in the session. -/
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

/-- Whether the session already treats this client as closed: `.closed` has been
reported, and the transport only drains owed output until `closeBy`. -/
def Conn.closing (c : Conn) : Bool := c.closeBy.isSome

/-- Whether output is still owed: bytes queued in either buffer, or an unfinished replay. -/
def Conn.pending (c : Conn) : Bool := owedLen c.out != 0 || c.replay.isSome || owedLen c.after != 0

/-- The daemon's world around the session machine: the machine's state, the session's
descriptors and child, every owned client transport, and the checkpoint hooks. -/
structure Rt where
  /-- The session machine's state; `pump` replaces it with the driver's result. -/
  st : State
  /-- The nonblocking listening socket at the session's path. -/
  listenFd : UInt32
  /-- The nonblocking pty master of the session's terminal. -/
  ptyFd : UInt32
  /-- The session's program, the child on the pty. -/
  childPid : UInt32
  /-- Owned transports, open or draining after a close, in admission order; never more
  than `maxClients`. -/
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
  /-- Whether the pty can still be read. Its end of file is not the session's end: a program
  can exit while its background jobs hold the terminal, and a program can close its terminal and
  keep running. Only the program's own exit ends the session. -/
  ptyOpen : Bool := true
  /-- The descriptor `childEndFd` made readable when a child of the daemon ends, or `none` when
  it could not be made, and every poll round then asks whether the program has ended. -/
  childEnd : Option UInt32 := none
  /-- How the program ended, once a wait has said. The program stays unreaped until `serve` has
  ended the rest of its terminal session, so its pid stays its own until then. -/
  ending : Option Outcome := none
  /-- Without a child-end descriptor, how long the next poll waits for the program's end while
  its terminal is closed. The end usually follows at once, so the wait starts at 10 ms; it
  doubles each round up to a second, so a program that runs on without its terminal wakes the
  daemon once a second. -/
  reapWaitMs : Nat := 10
  /-- Set once the machine emits `.exit`; the poll loop then stops and `drainConns` runs. -/
  exiting : Bool := false
  /-- checkpoint hooks from `Linger.Session.Shell.Resume` -/
  saveCkpt : State → IO Unit
  /-- Delete the session's checkpoint; a failure is reported, not fatal. -/
  dropCkpt : IO Unit
  /-- Checkpoint saves, off the loop. -/
  saves : Offloop := {}
  /-- Replace the name's end record, as `RecordFile.save` does; nothing in a suite that serves
  without one. -/
  saveRecord : Linger.Session.Record → IO Unit := fun _ => pure ()
  /-- Writes of what the daemon saw to the name's end record, off the loop. -/
  records : Offloop := {}
  /-- What the daemon last asked the record to say it saw. -/
  published : Option Linger.Session.Seen := none
  /-- Whether the last record write failed, so the log records the failure once rather than
  once per event. -/
  recordFailed : Bool := false

/-- A diagnostic write failure must not turn recovery into session loss. -/
private def report (message : String) : IO Unit := do
  try
    IO.eprintln message
  catch _ =>
    pure ()

/-- The owned transport whose socket is `fd`, if any. -/
def Rt.conn? (rt : Rt) (fd : UInt32) : Option Conn := rt.conns.find? (·.fd == fd)

/-- Replace the transport on `c`'s fd with `c`; an fd that is not owned leaves `rt` as is. -/
def Rt.setConn (rt : Rt) (c : Conn) : Rt :=
  { rt with conns := rt.conns.map (fun c' => if c'.fd == c.fd then c else c') }

/-- Close `fd` and forget its transport. -/
def Rt.closeConn (rt : Rt) (fd : UInt32) : IO Rt := do
  close fd
  return { rt with conns := rt.conns.filter (·.fd != fd) }

/-- Wait for the running write and the one waiting for it, and give how each ended: no other can
start meanwhile. A write the disk holds up longer than a second says so once, naming `what`. -/
def Offloop.finish (w : Offloop) (what : String) : IO (List (Except IO.Error Unit)) := do
  let mut w := w
  let mut ended : List (Except IO.Error Unit) := []
  let mut told := false
  for _ in [0:2] do
    let some task := w.running | break
    unless told || (← IO.hasFinished task) do
      let timer ← IO.asTask (IO.sleep 1000) Task.Priority.dedicated
      unless ← IO.waitAny [task.map (fun _ => true), timer.map (fun _ => false)] do
        report s!"linger: waiting for {what} to reach the disk"
        told := true
    let (next, result) ← w.collect true
    w := next
    ended := ended ++ result.toList
  return ended

/-- The end of the running save, once it has ended, or after waiting for it when `block`: a
failure is reported and fed back to the session as `.checkpointFailed`, so it retries at its
next cadence, and the state that waited is saved next. -/
def collectSave (rt : Rt) (block : Bool := false) : IO (Rt × List Event) := do
  let (saves, ended) ← rt.saves.collect block
  if let some (.error err) := ended then
    report s!"linger: checkpoint save failed: {err}"
    return ({ rt with saves }, [.checkpointFailed])
  return ({ rt with saves }, [])

/-- Wait for the running save and the one waiting for it, as before giving the name up: what a
session leaves must be on disk while it still holds the name. Failures are reported and not
retried. -/
def finishSaves (rt : Rt) : IO Rt := do
  for ended in ← rt.saves.finish "the session's checkpoint" do
    if let .error err := ended then
      report s!"linger: checkpoint save failed: {err}"
  return { rt with saves := {} }

/-- Ask the name's end record to say what the daemon now sees of the output, when that changed
since it last asked: output arriving, output going stale and someone looking each change it once,
so a burst of output asks at most twice. The write runs off the loop (`records`). -/
def publish (rt : Rt) : IO Rt := do
  let seen := rt.st.seen
  if rt.published == some seen then
    return rt
  let records ← rt.records.ask (rt.saveRecord (.running (some seen)))
  return { rt with
      records, published := some seen }

/-- The end of the running record write, once it has ended, or after waiting for it when
`block`. A failed write is reported once until one succeeds; the record may then say less than
the daemon saw, so the next event asks again. -/
def collectRecord (rt : Rt) (block : Bool := false) : IO Rt := do
  let (records, ended) ← rt.records.collect block
  match ended with
  | some (.error err) =>
    unless rt.recordFailed do
      report s!"linger: writing the session's record failed: {err}"
    return { rt with
        records, published := none, recordFailed := true }
  | some (.ok ()) =>
    return { rt with
        records, recordFailed := false }
  | none =>
    return { rt with records }

/-- Wait for the record write that runs, dropping any that waits, as before the record says how
the program ended: a write still running would replace that. -/
def settleRecord (rt : Rt) : IO Rt := do
  for ended in ← Offloop.finish { rt.records with waiting := none } "the session's record" do
    if let .error err := ended then
      report s!"linger: writing the session's record failed: {err}"
  return { rt with records := {} }

/-- Retired transports still own buffers and a snapshot. Their deadline
releases that ownership even while the rest of the session stays alive. -/
private def expireConns (rt : Rt) (now : Nat) : IO Rt := do
  let mut rt := rt
  for c in rt.conns do
    if c.closeBy.any (now ≥ ·) then
      rt ← rt.closeConn c.fd
  return rt

/-- Try to flush one connection's queue; `none` = peer gone.

The write offset is a **local** `Nat`, and `bufAdvance` is called once when the
write loop stops: `Buf.bufSize` is the retained logical byte length and equals
what is still owed in `Buf.writeFrom` (`Buf.bufSize_eq_owedLen`,
`Buf.bufAdvance_writeFrom`). Allocator capacity
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
        match Replay.next Linger.Session.outputChunk plan with
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
both `n ≤ 0` cases collapse to `break`, because a dead child surfaces through the reap every
poll round makes (`.childExited`), and there is nothing to disconnect. Sharing the
loop would invite "fixing" that asymmetry, which would either drop the pty queue
on a transient or leave a dead client's frames queued. -/
private def flushPty (rt : Rt) : IO Rt := do
  let mut wrote := 0
  let owed := owedLen rt.ptyIn
  while wrote < owed do
    let n ← writeBuf rt.ptyFd rt.ptyIn wrote
    if n ≤ 0 then
      break -- EAGAIN or child gone; POLLOUT/EOF handles it
    wrote := wrote + n.toNatClampNeg
  -- `serve` flushes every round, also while the child is not reading, and
  -- `bufAdvance` copies the bytes it keeps: skip it when nothing was written.
  if wrote == 0 then
    return { rt with ptyInFull := rt.ptyInFull && owed != 0 }
  let q := bufAdvance rt.ptyIn wrote
  -- clear the backpressure latch exactly when the queue drains, so the log
  -- records the transition once (the robust suite's countFull check asserts it)
  return { rt with
      ptyIn := q, ptyInFull := rt.ptyInFull && owedLen q != 0 }

/-- Queue bytes for the child, bounded (`Buf.reachableIn_bound`). Past
`ptyInCap` unwritten bytes the newest frame is dropped and the transition is
logged once — the daemon cannot make the child read faster, and holding the
input unboundedly only trades a wedged child for a wedged daemon. Not the
client-disconnect reaction `outbufCap` uses, because a `.writePty` carries no
client id (it is produced by `.input` from any client AND by the terminal
mediator's own query replies — see `Linger/Session/Proofs/Session.lean`), and because the
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
  return { rt with ptyIn := q }

/-- Execute one effect against the world. Its result type admits only the
feedback that the total driver has proved will terminate. Session state is
read-only here; the driver supplies the state after the current event. -/
private def executeEffect (st : State) (rt : Rt) : (eff : Effect Plan) → IO (Rt × Driver.Reply eff)
  | .send id m => do
    match rt.conn? (UInt32.ofNat id) with
    | none =>
      return (rt, false)
    | some c =>
      if c.closing then
        return (rt, false)
      let bytes := ByteArray.mk (Linger.Session.Wire.encode m).toArray
      let (c, cut) :=
        if c.replay.isSome || owedLen c.after != 0 then
          let cap := followingCap outbufCap replayFrameCap (owedLen c.out)
          let (q, cut) := bufEnqueue cap c.after bytes
          ({ c with after := q }, cut)
        else
          let (q, cut) := bufEnqueue outbufCap c.out bytes
          ({ c with out := q }, cut)
      if cut then
        -- `Buf.reachableOut_bound`: cut the slow client rather than grow
        return (← rt.closeConn c.fd, true)
      match ← flushConn c with
      | none =>
        return (← rt.closeConn c.fd, true)
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
        return (← rt.closeConn c.fd, true)
      match ← flushConn { c with replay := some plan } with
      | none =>
        return (← rt.closeConn c.fd, true)
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
        let deadline := (← monotonicMs) + drainTimeoutMs
        return (rt.setConn { c with closeBy := some deadline }, true)
      return (← rt.closeConn fd, true)
  | .writePty bytes => do
    return (← queuePty rt bytes, ())
  | .resizePty cols rows => do
    try
      winsizeSet rt.ptyFd cols rows
    catch err =>
      report s!"linger: pty resize failed: {err}"
    return (rt, ())
  | .killChild => do
    -- hang up the program's whole terminal session; `serve` ends what outlives that
    if rt.ending.isNone then
      kill rt.childPid 1 -- SIGHUP
    discard <| signalSession rt.childPid 1
    return (rt, ())
  -- a save waits on the disk, which answers and output must never wait on: it runs on its own
  -- thread, one at a time, and a request that finds one running replaces any that waits for
  -- it; `collectSave` feeds a failure back to the session later
  | .checkpoint => do
    return ({ rt with saves := ← rt.saves.ask (rt.saveCkpt st) }, false)
  | .dropCheckpoint => do
    -- a save still running would put the checkpoint back after the delete
    let rt ← finishSaves { rt with saves := { rt.saves with waiting := none } }
    try
      rt.dropCkpt
    catch err =>
      report s!"linger: checkpoint delete failed: {err}"
    return (rt, ())
  | .exit => do
    return (rt, ())

/-- Execute an isolated effect, using the driver's typed feedback policy. -/
def runEffect (rt : Rt) (eff : Effect Plan) : IO (Rt × List Event) := do
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

/-- poll(2) skips a negative descriptor: the pty's slot holds this one after the terminal
closes, so the closed terminal cannot wake every poll. -/
private def closedFd : UInt32 := 0xFFFFFFFF

/-- How many reads of the terminal the program's last output may take once it has ended. -/
private def finalReads : Nat := 16

/-- How the program ended, if it has: its exit code or signal, or `unknown` when it is no longer
ours to wait for. It stays unreaped, so its zombie keeps its pid, which is its session's id,
until `serve` has ended the session's other processes (`signalSession`). -/
private def programEnd (pid : UInt32) : IO (Option Outcome) := do
  match ← peekNohang pid with
  | .running =>
    return none
  | .exited code =>
    return some (.exited code)
  | .signaled signal =>
    return some (.signaled signal)
  | .unreapable =>
    return some .unknown

/-- The earlier of the deadline already set, if any, and `due`. -/
private def soonest (wake : Option Nat) (due : Nat) : Option Nat := some (wake.elim due (min · due))

/-- One poll round: gather events from fd readiness. It sleeps until an event or its first
deadline: the session's next tick, a retired transport's drain, admission's retry, and without
a child-end descriptor a timer that asks whether the program has ended. With none, it waits for
an event however long that takes, unless the caller bounds the wait with `limitMs`, as a suite
that drives the round by hand does. The program's end is asked after only when the child-end
descriptor says a child ended, or every round without one. -/
def pollRound (rt : Rt) (limitMs : Option Nat := none) : IO (Rt × List Event) := do
  let now ← monotonicMs
  let rt ← expireConns rt now
  -- a write that has ended feeds back first, and the one that waited for it starts
  let (rt, saved) ← collectSave rt
  let rt ← collectRecord rt
  let mut wake := rt.st.nextTick
  if rt.saves.running.isSome || rt.records.running.isSome then
    wake := soonest wake (now + saveCheckMs)
  if let some limit := limitMs then
    wake := soonest wake (now + limit)
  -- once the terminal has closed, the program's end usually follows at once
  if rt.childEnd.isNone && rt.ending.isNone then
    wake := soonest wake (now + if rt.ptyOpen then 1000 else rt.reapWaitMs)
  for c in rt.conns do
    if let some deadline := c.closeBy then
      wake := soonest wake deadline
  if let some retryAt := rt.acceptAfter then
    if now < retryAt then
      wake := soonest wake retryAt
  let timeout : Int32 :=
    match wake with
    | some due => Int32.ofNat (min (due - now) 2147483647)
    | none => -1
  let accepting := rt.conns.length < maxClients && rt.acceptAfter.all (now ≥ ·)
  -- snapshot: only these conns are in the poll set; accepts during
  -- this round join the NEXT one (revs stays index-aligned)
  let polled := rt.conns
  let watchEnd := rt.ending.isNone && rt.childEnd.isSome
  let mut fds : Array UInt32 :=
    #[rt.listenFd, if rt.ptyOpen then rt.ptyFd else closedFd,
      if watchEnd then rt.childEnd.getD closedFd else closedFd]
  let mut evts : Array UInt32 :=
    #[(if accepting then POLLIN else 0), POLLIN ||| (if owedLen rt.ptyIn != 0 then POLLOUT else 0),
      POLLIN]
  for c in polled do
    fds := fds.push c.fd
    evts := evts.push ((if c.closing then 0 else POLLIN) ||| (if c.pending then POLLOUT else 0))
  let revs ← poll fds evts timeout
  let mut rt := rt
  let mut events : List Event := saved
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
        rt := { rt with acceptAfter := some ((← monotonicMs) + acceptRetryMs) }
        break
  -- pty
  let ptyRev := revs[1]!
  if ptyRev &&& POLLOUT != 0 then
    rt ← flushPty rt
  if rt.ptyOpen && ptyRev &&& (POLLIN ||| POLLHUP ||| POLLERR) != 0 then
    match ← read rt.ptyFd 65536 with
    | some bs =>
      if bs.size > 0 then
        events := events ++ [.ptyOut bs.toList]
    | none =>
      -- the terminal closed; the session lasts until its program ends
      rt := { rt with ptyOpen := false }
  -- clients (the polled snapshot only)
  let mut idx := 3
  for c in polled do
    let r := revs[idx]!
    idx := idx + 1
    -- the conn may have been dropped by an earlier iteration's close
    if (rt.conn? c.fd).isNone then
      continue
    if r &&& POLLOUT != 0 then
      match ← flushConn ((rt.conn? c.fd).getD c) with
      | none =>
        rt ← rt.closeConn c.fd
        if !c.closing then
          events := events ++ [.closed c.fd.toNat]
      | some c' =>
        if c'.closing && !c'.pending then
          rt ← rt.closeConn c'.fd
        else
          rt := rt.setConn c'
    if r &&& (POLLIN ||| POLLHUP ||| POLLERR) != 0 then
      if let some current := rt.conn? c.fd then
        if current.closing then
          if r &&& (POLLHUP ||| POLLERR) != 0 then
            rt ← rt.closeConn c.fd
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
          rt ← rt.closeConn c.fd
          events := events ++ [.closed c.fd.toNat]
  -- the program's end, whatever still holds its terminal: asked after when a child ended, and
  -- every round when no descriptor says so. The byte is read first, so an end the signal
  -- reports after this read wakes the next round.
  let asked ←
    if watchEnd then
      if revs[2]! &&& (POLLIN ||| POLLHUP ||| POLLERR) != 0 then
        discard <| (read (rt.childEnd.getD closedFd) 65536).toBaseIO
        pure true
      else
        pure false
    else
      pure true
  if rt.ending.isNone && asked then
    match ← programEnd rt.childPid with
    | none =>
      if !rt.ptyOpen then
        rt := { rt with reapWaitMs := min 1000 (2 * rt.reapWaitMs) }
    | some outcome =>
      rt := { rt with ending := some outcome }
      -- the output it left in the terminal comes first, within a bounded number of reads; a
      -- failed read ends them, and the ending is reported all the same
      if rt.ptyOpen then
        try
          for _ in List.range finalReads do
            match ← read rt.ptyFd 65536 with
            | some bs =>
              if bs.isEmpty then
                break
              events := events ++ [.ptyOut bs.toList]
            | none =>
              rt := { rt with ptyOpen := false }
              break
        catch err =>
          report s!"linger: reading the program's last output failed: {err}"
      events := events ++ [.childExited outcome]
  return (rt, events)

/-- Stop admitting work and drain accepted bytes, with a finite grace period.
Every poll freezes its fd list; no session events execute after `.exit`. -/
def drainConns (rt : Rt) : IO Rt := do
  let mut rt := rt
  let deadline := (← monotonicMs) + drainTimeoutMs
  while !rt.conns.isEmpty do
    let now ← monotonicMs
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
            rt ← rt.closeConn c.fd
        | none =>
          rt ← rt.closeConn c.fd
  for c in rt.conns do
    close c.fd
  return { rt with conns := [] }

/-- How long the processes of an ending session have after SIGHUP before SIGKILL. -/
private def hangupGraceMs : Nat := 1000

/-- How long the kernel has to end the processes SIGKILL reached. -/
private def killWaitMs : Nat := 1000

/-- Whether `done` holds within `ms` milliseconds, asked every `step`. -/
private def within (ms step : Nat) (done : IO Bool) : IO Bool := do
  for _ in List.range (ms / step) do
    if ← done then
      return true
    IO.sleep step.toUInt32
  done

/-- How the program ended, ending it first if it still runs: SIGHUP to it and to the rest of its
terminal session, then SIGKILL to them all if it outlives `hangupGraceMs`, and `unknown` if it
has not ended `killWaitMs` after that. The program stays unreaped (`programEnd`). -/
private def stopProgram (rt : Rt) : IO Outcome := do
  if let some outcome := rt.ending then
    return outcome
  let pid := rt.childPid
  let ending ← IO.mkRef (none : Option Outcome)
  let ended : IO Bool := do
    if (← ending.get).isNone then
      ending.set (← programEnd pid)
    return (← ending.get).isSome
  try
    for (sig, ms) in [(1, hangupGraceMs), (9, killWaitMs)] do
      if ← ended then
        break
      kill pid sig
      discard <| signalSession pid sig
      if ← within ms 10 ended then
        break
  catch err =>
    report s!"linger: stopping the program failed: {err}"
  return (← ending.get).getD .unknown

/-- End every other process of the program's terminal session: SIGHUP, then SIGKILL to whatever
outlives `hangupGraceMs`. Run while the program is unreaped, so its pid is still the session's
id and no other session's. A process that left the session with `setsid` is not reached. Each
look at the session lists every process on the host, so it looks every 50 ms. -/
private def endSession (pid : UInt32) : IO Unit := do
  let gone : IO Bool := return (← signalSession pid 0) == 0
  for (sig, ms) in [(1, hangupGraceMs), (9, killWaitMs)] do
    if ← gone then
      return
    discard <| signalSession pid sig
    if ← within ms 50 gone then
      return

/-- How long a starting daemon waits for its locks. An offline reader holds both only
while it loads and prints a checkpoint. `connectUpsert` gives up on the socket no sooner
than 3 s, and after that only once this daemon exits or 30 s have passed. -/
private def claimWaitMs : Nat := 1000

/-- The line a starting daemon logs the first time it finds a lock held. -/
def claimWaitLine (name : String) : String :=
  s!"linger: session '{name}' is busy; waiting up to {claimWaitMs} ms for its locks"

/-- Retry a held startup claim until `deadline`, unless a live daemon answers on the
session's socket and so owns the name for its lifetime. Report the first wait. -/
private def claimRetry (name sockPath : String) (deadline : Nat) (reported : IO.Ref Bool) :
    IO Bool := do
  if (← monotonicMs) ≥ deadline then
    return false
  let live ← unixConnect sockPath
  if live ≥ 0 then
    close live.toUInt64.toUInt32
    return false
  unless ← reported.get do
    reported.set true
    report (claimWaitLine name)
  IO.sleep 10
  return true

/-- How a daemon keeps its name's end record: `Linger.Session.Shell.Record`, or nothing in a suite
that serves without one. -/
structure RecordFile where
  /-- The record's bytes, or `none` when there is no record. -/
  load : IO (Option (List UInt8))
  /-- Replace the record. -/
  save : Linger.Session.Record → IO Unit
  /-- Put back the bytes `load` gave, or remove the record when it gave none. -/
  restore : Option (List UInt8) → IO Unit

/-- Why a program could not start, for a person. -/
private def failureText (failure : SpawnFailure) (prog cwd : String) : String :=
  match failure with
  | .directory why => s!"cannot enter the directory {cwd}: {why}"
  | .notFound _ => s!"{prog}: not found"
  | .notRunnable why => s!"{prog}: cannot be run: {why}"

/-- Hold both ownership locks from before recovery through final cleanup.
Loading under the locks prevents a second runtime namespace from reading or
overwriting a checkpoint that another daemon is still using. The claim waits
out an offline reader (`claimRetry`) but not a live owner. The name's end record says the
program runs before it starts and how it ended before the locks are released; a program that
cannot start leaves the record as it was.

With `start`, the daemon takes the name only when no live or saved session holds it, never
resumes one (`Start.plan`), runs the program in `cwd` or not at all, and tells `start` what it
did. With `resume` as well, it runs only a saved session's program again, an ended one included,
and starts nothing for a live session or a name no session holds (`Start.resumePlan`). -/
def serve (name : String) (cwd : String) (argv : List String) (saveCkpt : State → IO Unit)
    (dropCkpt : IO Unit)
    (loadCkpt : IO (Option (Linger.Terminal.Vt.Vt × String × List (String × String))))
    (record : RecordFile) (start : Option (Start.Report → IO Unit) := none)
    (resume : Bool := false) : IO Unit := do
  let deadline := (← monotonicMs) + claimWaitMs
  let reported ← IO.mkRef false
  let retry := claimRetry name (← Paths.socketPath name) deadline reported
  Paths.withSessionLockRetrying name retry do
      ignoreSighup
      let sockPath ← Paths.socketPath name
      let r ← unixConnect sockPath
      let live := r ≥ 0
      if live then
        close r.toUInt64.toUInt32
      if let some tell := start then
        let saved ← System.FilePath.pathExists (← Paths.ckptPath name)
        if resume then
          match Start.resumePlan live saved with
          | .running =>
            tell .running
            return
          | .missing =>
            tell (.failed 127 s!"no session '{name}'".toUTF8.toList)
            return
          | .resume =>
            pure ()
        else
          match Start.plan live saved with
          | .running =>
            tell .running
            return
          | .saved =>
            tell .saved
            return
          | .take =>
            pure ()
      if live then
        throw (IO.userError s!"session '{name}' already running")
      let saved ←
        if start.isSome && !resume then
          pure none
        else
          loadCkpt
      -- a resume runs a saved session's program again or none: a checkpoint it cannot read
      -- starts nothing
      if resume && saved.isNone then
        if let some tell := start then
          tell (.failed 1 "its saved session cannot be read".toUTF8.toList)
        return
      -- A new session runs in `cwd` or not at all. A resume runs in its saved directory, or in
      -- $HOME when that is gone (`Env.resumeDir`), and then says so in the info field saved_dir
      -- and in the log.
      let mut cwd := cwd
      let mut moved : Option String := none
      if let some (_, dir, _) := saved then
        match Linger.Os.Env.resumeDir (← IO.getEnv "HOME") dir (← System.FilePath.isDir dir) with
        | some run =>
          cwd := run
          if run != dir then
            moved := some dir
            report s!"linger: session '{name}' resumes in {run}: its directory {dir} is gone"
        | none =>
          throw
              (IO.userError
                s!"session '{name}' cannot resume: its directory {dir} is gone, and HOME is unset")
      let restore := saved.map (fun (vt, _, labels) => (vt, labels))
      -- The socket lock excludes another cooperating listener, even if connect
      -- failed for a reason other than a stale socket. Never unlink the lock inode.
      try
        IO.FS.removeFile sockPath
      catch _ =>
        pure ()
      let listenFd ← unixListen sockPath
      try
        setNonblock listenFd
        let shell := Linger.Os.Env.shellOf (← IO.getEnv "SHELL")
        let (prog, args) :=
          match argv with
          | [] => ((shell, #[]) : String × Array String)
          | p :: rest => (p, rest.toArray)
        -- Preserve the checkpoint's terminal state and dimensions. Clamp only at
        -- the syscall boundary; resizing the restored VT would reset its margins.
        let vt0 := Linger.Session.bootVt (restore.map (·.1))
        let created ← realtimeS
        -- before the program starts, so its end always reaches the descriptor; without one, every
        -- poll round asks whether the program has ended
        let childEnd ←
          match ← childEndFd.toBaseIO with
          | .ok fd =>
            pure (some fd)
          | .error err =>
            report s!"linger: waiting for the program's end on a timer: {err}"
            pure none
        -- The name is this session's from here on: should the daemon end without saying how
        -- its program ended, a reader that holds the name hears that the ending is unknown,
        -- never the previous session's. A record that cannot be written starts nothing, and a
        -- program that cannot start puts the previous record back.
        let previous ← record.load
        record.save (.running none)
        let spawned ←
          try
            trySpawnPty (UInt32.ofNat (Linger.Terminal.Vt.clampDim vt0.colCount))
                (UInt32.ofNat (Linger.Terminal.Vt.clampDim vt0.rowCount)) cwd prog args
                #[s!"LINGER_SESSION={name}", "TERM=xterm-256color", "TERM_PROGRAM=linger",
                  s!"TERM_PROGRAM_VERSION={Linger.Terminal.Mediation.versionNumber}"]
          catch err =>
            record.restore previous
            throw err
        if let .error failure := spawned then
          record.restore previous
          let why := failureText failure prog cwd
          match start with
          | some tell =>
            tell (.failed failure.status why.toUTF8.toList)
          | none =>
            throw (IO.userError s!"linger: session '{name}' did not start: {why}")
          return
        let .ok (pid, ptyFd) := spawned | return
        if let some tell := start then
          tell .started
        let st :=
          State.boot vt0 ((restore.map (·.2)).getD [])
            ([("name", name), ("pid", toString pid), ("created", toString created),
                ("cmd", String.intercalate " " (prog :: args.toList)), ("start_dir", cwd)] ++
              (moved.map (fun dir => [("saved_dir", dir)])).getD [])
        -- The cleanup reads the runtime as each round left it, the program's ending included,
        -- whatever fails after that round.
        let latest ←
          IO.mkRef
              ({ st, listenFd, ptyFd, childPid := pid, childEnd, saveCkpt, dropCkpt,
                 saveRecord := record.save } :
                Rt)
        try
          setNonblock ptyFd
          let mut rt ← latest.get
          while !rt.exiting do
            let (rt', events) ← pollRound rt
            latest.set rt'
            let now ← monotonicMs
            rt ← pump rt' (events ++ [.tick now])
            rt ← flushPty rt
            if !rt.exiting then
              rt ← publish rt
            latest.set rt
          rt ← drainConns rt
          latest.set rt
        finally
          let rt ← latest.get
          for c in rt.conns do
            close c.fd
          let outcome ← stopProgram rt
          let rt ← settleRecord rt
          try
            record.save (.ended outcome)
          catch err =>
            report s!"linger: recording how the program ended failed: {err}"
          -- the session's last screen reaches the disk while the name is still this session's
          discard <| finishSaves rt
          -- the program is reaped last: until then its zombie keeps its pid, which is its
          -- session's id, so ending the session's other processes reaches no one else
          try
            endSession rt.childPid
          catch err =>
            report s!"linger: ending the session's processes failed: {err}"
          discard <| reapNohang rt.childPid
          close rt.ptyFd
          if let some fd := rt.childEnd then
            close fd
      finally
        close listenFd
        try
          IO.FS.removeFile sockPath
        catch _ =>
          pure ()

end Linger.Session.Shell.Daemon
