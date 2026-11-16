module

import Os.WorldCode
import Os.CoreCode.Write
public import Linger.Session.CoreCode.Buf
import Linger.Session.CoreCode.Driver
public import Linger.Session.CoreCode
public import Linger.Session.CoreCode.Record
public import Linger.Session.CoreCode.Start
import Linger.Session.CoreCode.Handoff
import Linger.Os.CoreCode.Env
import Linger.Os.CoreCode.Answer
import Linger.Session.WorldCode.Paths

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

The session ends when its program does, or when a stop signal stops the daemon. The daemon hears
both through its signal pipe (`signalPipe`): a child's end, whether or not a background job still
holds the terminal, after which it asks without blocking whether the program ended and reports how,
leaving it unreaped until the rest of its terminal session has ended (`programEnd`), and SIGHUP,
SIGINT, SIGQUIT or SIGTERM, which it reports as the session's event
(`Event.signal`); the terminal's end of file ends nothing by itself. A kill stops the program
first, with each signal of `Session.ending` in turn (`Effect.stopProgram`), and the session then
ends as it does when its program ends by itself; a stop signal stops the program the same way,
and the session then ends saved, with an end record that says which signal stopped it
(`Effect.record`). Between events it sleeps until the session's next tick (`State.nextTick`), so
an idle session costs no wakeup.

`Linger/Session/Proofs/Buf.lean` proves the byte-buffer caps, shared allowance and removal of
written prefixes. `packages/terminal/Terminal/Proofs/Replay.lean` proves the cursor's exact stream,
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

open Os.Shell
open Linger.Session (State Event Effect Outcome maxClients drainTimeoutMs)
open Linger.Session.Buf (Buf owedLen bufOffer bufEnqueue bufAdvance followingCap)
open Terminal
open Terminal.Replay (Plan)

/-- One write attempt for a `Linger.Session.Buf` queue, skipping the `sent` bytes the
flush loop already got out. The result is `write`'s (`Os.Write.Result`): the bytes written,
none when nothing is owed past `sent`; that the descriptor is full; or that the peer is gone;
other errors throw.
`Buf.writeFrom` is the byte view of the debt, so what reaches `write(2)` here is the debt
and nothing else: `Buf.bufSize_eq_owedLen` shows the queue retains no more, and
`Buf.bufAdvance_writeFrom` gives what the loop leaves after advancing.

`sent` is the flush loop's **transient** cursor, not stored state: a `Buf` holds
exactly the bytes still owed, and the loop calls `Buf.bufAdvance` once when it
stops. Passing the cursor here rather than re-slicing per iteration keeps a flush
to a single copy.

This wraps `Os.Shell.write`, so it is not a new syscall. It cannot read a `Buf`'s
representation — `bytes` is `private`, and this calls the one API window, `writeFrom`.
`scripts/gates.sh`'s greps still gate the session shell against declaring parallel byte
buffers of its own, the half privacy cannot see. -/
private def writeBuf (fd : UInt32) (b : Buf) (sent : Nat) : IO Os.Write.Result :=
  write fd (Linger.Session.Buf.writeFrom b) (USize.ofNat sent)

/-- A stopped-reading client is cut here (`Buf.reachableOut_bound`). -/
def outbufCap : Nat := 4194304

/-- Payload plus the wire encoder's own frame overhead. -/
def replayFrameCap : Nat := Linger.Session.outputChunk + (Wire.encode (.output [])).length

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

/-- Writes of one kind that the daemon does off its loop (`Session.Offloop`): at most one runs, on
a thread of its own, and a later one replaces any that waits for it (`Session.Offloop.ask`). So a
slow disk holds up no answer and no output, and writes are coalesced and never queue. -/
abbrev Offloop : Type := Linger.Session.Offloop (Task (Except IO.Error Unit)) (IO Unit)

/-- Run `write` on its own thread now, or after the running write in place of any that waits. -/
def Offloop.ask (w : Offloop) (write : IO Unit) : IO Offloop := do
  match Linger.Session.Offloop.ask w write with
  | (w, none) =>
    return w
  | (w, some write) =>
    return { w with running := some (← IO.asTask write Task.Priority.dedicated) }

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
  /-- The read end of the daemon's signal pipe (`signalPipe`), which carries a 0 when a child of
  the daemon ends and the number of each stop signal the daemon hears, or `none` when it could not
  be made: every poll round then asks whether the program has ended, and a stop signal has its
  default action. -/
  signals : Option UInt32 := none
  /-- The write end of the signal pipe, which a daemon that upgrades keeps open for the image
  that replaces it, with the read end. -/
  signalWrite : Option UInt32 := none
  /-- The descriptors that hold the session's locks, which a daemon that upgrades keeps open for
  the image that replaces it, so the name stays this session's across the exec. -/
  locks : List UInt32 := []
  /-- The upgrades connections asked for since the last round, in order, each with the path of
  the binary it names (`Effect.upgrade`). The daemon carries the first out after the round, and
  refuses the others. -/
  upgrades : List (Nat × List UInt8) := []
  /-- How the program ended, once a wait has said. The program stays unreaped until `serve` has
  ended the rest of its terminal session, so its pid stays its own until then. -/
  ending : Option Outcome := none
  /-- Without a signal pipe, how long the next poll waits for the program's end while its
  terminal is closed. The end usually follows at once, so the wait starts at 10 ms; it
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
  /-- The end record the session asked to leave (`Effect.record`), which `serve` writes before it
  gives the name up; a daemon that ends before the session asks for one records how its program
  ended. -/
  final : Option Linger.Session.Record := none

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
start meanwhile. A write the disk holds up longer than a second says so once, naming `what`, and
is then waited for however long the disk takes: one of the waits with no deadline. -/
def Offloop.finish (w : Offloop) (what : String) : IO (List (Except IO.Error Unit)) := do
  let mut w := w
  let mut ended : List (Except IO.Error Unit) := []
  let mut told := false
  for _ in [0:2] do
    let some task := w.running | break
    unless told do
      let tellAt := (← monotonicMs) + 1000
      repeat
        if ← IO.hasFinished task then
          break
        unless ← nap tellAt 10 do
          report s!"linger: waiting for {what} to reach the disk"
          told := true
          break
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
and physical heap footprint are outside that bound. Each attempt's outcome is decided as
`Os.Write.next` says, and the two reactions to stopping are the reason this is not shared with
`flushPty`: here a gone peer means the caller must close the fd and feed `.closed` back into the
machine, while a full socket waits for the POLLOUT that resumes it. A write that fails for any
other reason loses the peer the same way, reported: a client's broken transport costs that
client alone, never the session. -/
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
      let written ←
        try
          writeBuf c.fd c.out wrote
        catch err =>
          report s!"linger: writing to a client failed; dropping it: {err}"
          pure .gone
      match Os.Write.next owed wrote written with
      | .write to =>
        wrote := to
      | .done =>
        wrote := owed
      | .await =>
        break
      | .gone =>
        return none
    c := { c with out := bufAdvance c.out wrote }
    if wrote < owed then
      break
  return some c

/-- The same bookkeeping for the child's input queue, with the *other* reaction:
a full pty and a gone child both stop the loop, because a dead child surfaces as `.childExited`
when a poll round asks whether the program ended, which it does when the signal pipe carried a
byte, or every round without a pipe, and there is nothing to disconnect. Sharing the
loop would invite "fixing" that asymmetry, which would either drop the pty queue
on a transient or leave a dead client's frames queued. -/
private def flushPty (rt : Rt) : IO Rt := do
  let mut wrote := 0
  let owed := owedLen rt.ptyIn
  while wrote < owed do
    match Os.Write.next owed wrote (← writeBuf rt.ptyFd rt.ptyIn wrote) with
    | .write to =>
      wrote := to
    | .done =>
      wrote := owed
    | .await | .gone =>
      break -- the child is not reading, or is gone; POLLOUT or the program's end handles it
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

/-- Whether `done` holds within `ms` milliseconds, asked every `step`. -/
private def within (ms step : Nat) (done : IO Bool) : IO Bool := do
  let deadline := (← monotonicMs) + ms
  repeat
    if ← done then
      return true
    unless ← nap deadline step do
      break
  done

/-- How the program ended, ending it first if it still runs: each signal of `Session.ending`, to
it and to the rest of its terminal session, until it ends, SIGHUP first and then SIGKILL, and
`unknown` if it has not ended once the last wait is over. A signal that cannot be sent, as to a
program that became another user, is reported, and the next one is sent all the same; a stop that
cannot even look whether the program ended is reported and answers `unknown`. The program stays
unreaped (`programEnd`). -/
private def stopChild (pid : UInt32) : IO Outcome := do
  let ending ← IO.mkRef (none : Option Outcome)
  let ended : IO Bool := do
    if (← ending.get).isNone then
      ending.set (← programEnd pid)
    return (← ending.get).isSome
  try
    for (sig, ms) in Linger.Session.ending do
      if ← ended then
        break
      try
        kill pid sig
      catch err =>
        report s!"linger: signalling the program failed: {err}"
      try
        discard <| signalSession pid sig
      catch err =>
        report s!"linger: signalling the program's terminal session failed: {err}"
      if ← within ms 10 ended then
        break
  catch err =>
    report s!"linger: stopping the program failed: {err}"
  return (← ending.get).getD .unknown

/-- `stopChild` of the session's program, unless a wait already said how it ended. -/
private def stopProgram (rt : Rt) : IO Outcome := do
  if let some outcome := rt.ending then
    return outcome
  stopChild rt.childPid

/-- Execute one effect against the world. Its result type admits only the
feedback that the total driver has proved will terminate. Session state is
read-only here; the driver supplies the state after the current event. Each failure it can meet
is answered as its effect's reply says: a client whose transport fails is gone (`flushConn`), a
resize or a delete that fails changes nothing, and a stop whose signals fail answers how the
program ended as far as it saw (`stopProgram`). -/
private def perform (st : State) (rt : Rt) : (eff : Effect Plan) → IO (Rt × Driver.Reply eff)
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
  -- the program's end is the session's: `serve` ends what of its terminal session outlives it
  | .stopProgram => do
    let outcome ← stopProgram rt
    return ({ rt with ending := some outcome }, outcome)
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
  -- the end record is written last, once the session's processes have ended (`serve`)
  | .record r => do
    return ({ rt with final := some r }, ())
  | .exit => do
    return (rt, ())
  -- the image is replaced after the round, once every effect of it has run (`upgradeAsked`)
  | .upgrade id exe => do
    return ({ rt with upgrades := rt.upgrades ++ [(id, exe)] }, ())

/-- An effect's failure, as its reply says it: its client gone, its transport closed if the daemon
still owns it; its checkpoint unsaved; its program's ending unknown. -/
private def failed (rt : Rt) : (eff : Effect Plan) → BaseIO (Rt × Driver.Reply eff)
  | .send id _ | .replay id _ | .close id => do
    let fd := UInt32.ofNat id
    match ← (rt.closeConn fd).toBaseIO with
    | .ok rt =>
      return (rt, true)
    | .error _ =>
      return ({ rt with conns := rt.conns.filter (·.fd != fd) }, true)
  | .checkpoint => do
    return (rt, true)
  | .stopProgram => do
    return ({ rt with ending := some .unknown }, .unknown)
  | .writePty _ | .resizePty .. | .dropCheckpoint | .record _ | .exit | .upgrade .. => do
    return (rt, ())

/-- The executor the driver runs, which answers every effect and raises nothing
(`Driver.Responds`): `perform`, whose own answers cover each failure it can meet, and for an
error it raises all the same, a report and the effect's failure (`failed`). -/
private def executeEffect (st : State) (rt : Rt) (eff : Effect Plan) :
    BaseIO (Rt × Driver.Reply eff) :=
  (perform st rt eff).catchExceptions fun err => do
    discard <| (report s!"linger: an effect failed: {err}").toBaseIO
    failed rt eff

/-- Execute an isolated effect, using the driver's typed feedback policy. -/
def runEffect (rt : Rt) (eff : Effect Plan) : BaseIO (Rt × List Event) := do
  let (next, reply) ← executeEffect rt.st rt eff
  return ({ next with exiting := rt.exiting || eff == .exit }, Driver.feedback eff reply)

/-- Feed events through the machine until quiescent or exited. Events queued
behind exit must not checkpoint a session whose recovery state was deleted.
Effect feedback precedes the next queued event, in effect order: a close must
remove its client before already-read bytes from that client are considered. Nothing it runs
raises, since its executor answers every effect. -/
def pump (rt : Rt) (evs : List Event) : BaseIO Rt := do
  let result ← Driver.run executeEffect { st := rt.st, world := rt, exiting := rt.exiting } evs
  return { result.world with
      st := result.st, exiting := result.exiting }

/-- A round's events, after what the daemon reads of the world when a connection that has not
attached sent bytes, as a request does: the clocks, whether the session's program is its login
shell, and its terminal's foreground as the operating system reports it (`Os.Shell.foreground`,
whose report the world claim `Pty.Foreground` is about), as one `observed` event ahead of the
round's, which `info` then reports. An attached client's keys read nothing. -/
def observing (rt : Rt) (login : Bool) (events : List Event) : IO (List Event) := do
  let asks :=
    events.any fun
      | .bytes id _ => !((rt.st.client? id).any (·.attached))
      | _ => false
  if !asks then
    return events
  let reported ←
    try
      foreground rt.ptyFd
    catch _ =>
      pure none
  let observation : Linger.Session.Observation :=
    { nowMs := ← monotonicMs, wallS := (← realtimeS).toNat, login,
      foreground := reported.map fun (pid, argv, dir) => { pid := pid.toNat, argv, dir } }
  return .observed observation :: events

/-- poll(2) skips a negative descriptor: the pty's slot holds this one after the terminal
closes, so the closed terminal cannot wake every poll. -/
private def closedFd : UInt32 := 0xFFFFFFFF

/-- How many reads of the terminal the program's last output may take once it has ended. -/
private def finalReads : Nat := 16

/-- One poll round: gather events from fd readiness. It sleeps until an event or its first
deadline (`Session.pollTimeout`): the session's next tick, a retired transport's drain,
admission's retry, and without a signal pipe a timer that asks whether the program has ended.
With none, it waits for an event however long that takes, unless the caller bounds the wait with
`limitMs`, as a suite that drives the round by hand does. The program's end is asked after only
when the signal pipe carried a byte, or every round without one, and a stop signal the pipe
carried is the session's event, before the program's end when it came first
(`Session.stopOf`). -/
def pollRound (rt : Rt) (limitMs : Option Nat := none) : IO (Rt × List Event) := do
  let now ← monotonicMs
  let rt ← expireConns rt now
  -- a write that has ended feeds back first, and the one that waited for it starts
  let (rt, saved) ← collectSave rt
  let rt ← collectRecord rt
  let mut deadlines : List Nat := rt.st.nextTick.toList
  if rt.saves.running.isSome || rt.records.running.isSome then
    deadlines := (now + saveCheckMs) :: deadlines
  if let some limit := limitMs then
    deadlines := (now + limit) :: deadlines
  -- once the terminal has closed, the program's end usually follows at once
  if rt.signals.isNone && rt.ending.isNone then
    deadlines := (now + if rt.ptyOpen then 1000 else rt.reapWaitMs) :: deadlines
  for c in rt.conns do
    if let some deadline := c.closeBy then
      deadlines := deadline :: deadlines
  if let some retryAt := rt.acceptAfter then
    if now < retryAt then
      deadlines := retryAt :: deadlines
  let timeout := Linger.Session.pollTimeout now deadlines
  let accepting := rt.conns.length < maxClients && rt.acceptAfter.all (now ≥ ·)
  -- snapshot: only these conns are in the poll set; accepts during
  -- this round join the NEXT one (revs stays index-aligned)
  let polled := rt.conns
  let watchEnd := rt.ending.isNone && rt.signals.isSome
  let mut fds : Array UInt32 :=
    #[rt.listenFd, if rt.ptyOpen then rt.ptyFd else closedFd,
      if watchEnd then rt.signals.getD closedFd else closedFd]
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
  -- the program's end, whatever still holds its terminal, and the daemon's stop: the pipe
  -- carries them in the order they came, a 0 for a child's end and a stop signal's number. The
  -- end is asked after when the pipe carried a byte, and every round with no pipe. The bytes
  -- are read first, so a signal after this read wakes the next round.
  let mut heard : List UInt8 := []
  let mut asked := !watchEnd
  if watchEnd && revs[2]! &&& (POLLIN ||| POLLHUP ||| POLLERR) != 0 then
    asked := true
    if let .ok (some bytes)← (read (rt.signals.getD closedFd) 65536).toBaseIO then
      heard := bytes.toList
  let mut ended : List Event := []
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
              ended := ended ++ [.ptyOut bs.toList]
            | none =>
              rt := { rt with ptyOpen := false }
              break
        catch err =>
          report s!"linger: reading the program's last output failed: {err}"
      ended := ended ++ [.childExited outcome]
  -- a stop that came before every child's end ends the session even if the program ended too
  match Linger.Session.stopOf heard with
  | some (signal, true) =>
    events := events ++ .signal signal :: ended
  | some (signal, false) =>
    events := events ++ ended ++ [.signal signal]
  | none =>
    events := events ++ ended
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

/-- End every other process of the program's terminal session with the signals of
`Session.ending`: SIGHUP, then SIGKILL to whatever outlives a second of it. Run while the program
is unreaped, so its pid is still the session's id and no other session's. A process that left
the session with `setsid` is not reached. Each look at the session lists every process on the
host, so it looks every 50 ms. -/
private def endSession (pid : UInt32) : IO Unit := do
  let gone : IO Bool := return (← signalSession pid 0) == 0
  for (sig, ms) in Linger.Session.ending do
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
  nap deadline 10

/-- How a daemon keeps its name's end record: `Linger.Session.Shell.Record`, or nothing in a suite
that serves without one. -/
structure RecordFile where
  /-- The record's bytes, or `none` when there is no record. -/
  load : IO (Option (List UInt8))
  /-- Replace the record. -/
  save : Linger.Session.Record → IO Unit
  /-- Put back the bytes `load` gave, or remove the record when it gave none. -/
  restore : Option (List UInt8) → IO Unit

/-- Answer connection `id` that its request is refused, saying `why`, through the session's
driver, so a connection that is gone is the session's event as for any reply. -/
private def refuse (rt : Rt) (id : Nat) (why : String) : IO Rt := do
  let (rt, events) ← runEffect rt (.send id (.err why.toUTF8.toList))
  pump rt events

/-- How long a probe of the binary an upgrade names may take to answer. -/
def probeMs : Nat := 10000

/-- The handoff formats the binary at `exe` reads, as it prints them when run as
`exe __handoff-formats` (`Upgrade.readFormats`) within `probeMs`, or why it named none: it cannot
be run, it did not answer in time, which ends it, it failed, or it printed no list of formats. -/
private def probe (exe : String) : IO (Except String (List Nat)) := do
  let child ←
    try
      IO.Process.spawn
          { cmd := exe, args := #["__handoff-formats"], stdin := .null, stdout := .piped,
            stderr := .null }
    catch err =>
      return .error s!"cannot be run: {err}"
  let printed ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
  let deadline := (← monotonicMs) + probeMs
  let mut status : Option UInt32 := none
  repeat
    status ← child.tryWait
    if status.isSome then
      break
    unless ← nap deadline 10 do
      break
  let some code := status |
    do
      try
        child.kill
        discard child.wait
      catch _ =>
        pure ()
      return .error s!"did not answer within {probeMs} ms"
  let text :=
    match ← IO.wait printed with
    | .ok text => text
    | .error _ => ""
  if code != 0 then
    return .error s!"answered with status {code}"
  match Linger.Session.Upgrade.readFormats text with
  | some formats =>
    return .ok formats
  | none =>
    return .error "names no handoff format"

/-- Every byte the daemon still owes connection `c`, in order and framed as it would send them:
its backlog, the rest of its repaint, then what follows the repaint. -/
private def owedOf (c : Conn) : IO (List UInt8) := do
  let mut chunks : Array (List UInt8) := #[(Linger.Session.Buf.writeFrom c.out).toList]
  let mut rest := c.replay
  repeat
    let some plan := rest | break
    match Replay.next Linger.Session.outputChunk plan with
    | none =>
      rest := none
    | some (bytes, plan) =>
      rest := some plan
      unless bytes.isEmpty do
        chunks := chunks.push (Wire.encode (.output bytes))
  chunks := chunks.push (Linger.Session.Buf.writeFrom c.after).toList
  return chunks.toList.flatten

/-- Why the daemon cannot hand its session over now, if it cannot: the session is ending, its
program's terminal has closed, or the program is partway through a control sequence or a
character, which the handoff's terminal codec would forget (`Vt.quiet`). -/
private def upgradeBlocked (rt : Rt) : Option String :=
  if rt.exiting || rt.ending.isSome then some "the session is ending"
  else
    if !rt.ptyOpen then some "the program's terminal has closed"
    else
      if !rt.st.terminal.quiet then
        some "the program is partway through a control sequence; try again"
      else none

/-- Replace this daemon's image with the binary at `exe`, which carries the session over, for
connection `asker`, as `Effect.upgrade` asks. The binary must name the handoff format this one
writes when probed (`Upgrade.proceeds`). The daemon then waits for its saves and its record
write, saves its checkpoint, which a new image that cannot take the handoff leaves to resume,
writes the handoff (`Handoff.encode`) and execs the binary as `__upgraded name handoff pid`,
keeping its listener, its pty, its signal pipe, its locks and every connection open
(`Os.Shell.execImage`). It closes nothing first. It returns only when it does not replace its
image, with why, and the daemon carries on from the state it kept. -/
private def upgradeTo (name : String) (login : Bool) (rt : Rt) (asker : Nat) (exe : List UInt8) :
    IO (Rt × String) := do
  let some exe :=
    String.fromUTF8? (ByteArray.mk exe.toArray) | return (rt, "the binary's path is not text")
  unless exe.startsWith "/" do
    return (rt, s!"the binary's path {exe} is not absolute")
  if let some why := upgradeBlocked rt then
    return (rt, why)
  let (some sigRead, some sigWrite) :=
    (rt.signals,
      rt.signalWrite) | return (rt, "the daemon hears its program's end on a timer, and cannot hand that over")
  let formats ←
    match ← probe exe with
    | .error why =>
      return (rt, s!"{exe} {why}, so the session keeps running")
    | .ok formats =>
      pure formats
  unless Linger.Session.Upgrade.proceeds (some formats) do
    let why :=
      s!"{exe} reads handoff formats {formats}, not format {Linger.Session.Handoff.version}, so \
        the session keeps running"
    return (rt, why)
  let rt ← finishSaves rt
  let rt ← settleRecord rt
  try
    rt.saveCkpt rt.st
  catch err =>
    report s!"linger: saving the checkpoint before an upgrade failed: {err}"
  let mut conns : List Linger.Session.Handoff.Conn := []
  for c in rt.conns do
    conns := conns ++ [{ fd := c.fd.toNat, owed := ← owedOf c, closeBy := c.closeBy }]
  let world : Linger.Session.Handoff.World :=
    { listenFd := rt.listenFd.toNat, ptyFd := rt.ptyFd.toNat, childPid := rt.childPid.toNat,
      signals := (sigRead.toNat, sigWrite.toNat), locks := rt.locks.map (·.toNat), conns,
      ptyIn := (Linger.Session.Buf.writeFrom rt.ptyIn).toList, login, asker }
  let path ← Paths.handoffPath name
  try
    IO.FS.writeBinFile path (ByteArray.mk (Linger.Session.Handoff.encode rt.st world).toArray)
  catch err =>
    return (rt, s!"writing the handoff failed: {err}, so the session keeps running")
  let keep :=
    #[rt.listenFd, rt.ptyFd, sigRead, sigWrite] ++ rt.locks.toArray ++ (rt.conns.map (·.fd)).toArray
  try
    execImage exe #["__upgraded", name, path, toString rt.childPid] keep
    return (rt, s!"{exe} returned from its exec, so the session keeps running")
  catch err =>
    try
      IO.FS.removeFile path
    catch _ =>
      pure ()
    return (rt, s!"{exe} could not replace the daemon: {err}, so the session keeps running")

/-- Carry out the first upgrade the round asked for, and refuse the others it asked for; the
daemon carries on when it does not replace its image, and the connection that asked hears why. -/
private def upgradeAsked (name : String) (login : Bool) (rt : Rt) : IO Rt := do
  let (asker, exe) :: others := rt.upgrades | return rt
  let mut rt := { rt with upgrades := [] }
  for (other, _) in others do
    rt ← refuse rt other "another upgrade is under way"
  let (rt', why) ← upgradeTo name login rt asker exe
  report s!"linger: session '{name}' did not upgrade: {why}"
  refuse rt' asker why

/-- Serve the session from `latest` until it ends, then end it: what `serve` does once its program
runs, and what an upgraded image does once it has taken the handoff. Each round polls, feeds the
round's events and a tick through the session, carries out an upgrade the round asked for, writes
to the program, and asks the name's end record to say what the daemon sees. Once the session
exits it drains the connections; however the loop ends, it closes every connection, stops the
program if it still runs, writes the end record, waits for the saves, ends what of the program's
terminal session outlives it, reaps the program, and closes the pty and the signal pipe. -/
private def run (name : String) (login : Bool) (record : RecordFile) (latest : IO.Ref Rt) :
    IO Unit := do
  try
    let mut rt ← latest.get
    setNonblock rt.ptyFd
    -- what the record says this daemon sees, before it first sleeps: a summary then reads it
    -- instead of waking the daemon to ask
    rt ← publish rt
    latest.set rt
    while !rt.exiting do
      let (rt', events) ← pollRound rt
      latest.set rt'
      let now ← monotonicMs
      let events ← observing rt' login events
      rt ← pump rt' (events ++ [.tick now])
      rt ← upgradeAsked name login rt
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
      record.save (rt.final.getD (.ended outcome))
    catch err =>
      report s!"linger: recording how the session ended failed: {err}"
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
    if let some fd := rt.signals then
      close fd
    if let some fd := rt.signalWrite then
      close fd

/-- The request of the command that began this daemon, as `start` and `resume` do: the command
waits a bounded time for the answer, and when that wait runs out it races this daemon for the
request's ticket. -/
structure Request where
  /-- Take the ticket, once: `true` when this daemon holds it, `false` when the command took it
  first and so answered that nothing starts. -/
  take : IO Bool
  /-- Tell the command what this daemon did, holding the ticket: it takes the ticket first if
  nobody has, and tells nothing when the command took it. -/
  tell : Start.Report → IO Unit

/-- What a daemon may start from, as its command decided from the name's checkpoint
(`Linger.App.Recovery.decide`): the saved terminal, directory and record fields to resume, `none` for a
new session, or, when it may do neither, the status its command answers and why. -/
abbrev Recovered : Type :=
  Except (UInt8 × String) (Option (Terminal.Vt.Vt × String × List (String × String)))

/-- The spec's name for the operating system's report of a program that could not start. -/
private def failureOf : SpawnFailure → Linger.Session.Spawn.Failure
  | .directory why => .directory why
  | .notFound why => .notFound why
  | .notRunnable why => .notRunnable why

/-- What the operating system resets of a program's start, as linger's request says it. -/
private def resetOf (reset : Linger.Session.Spawn.Reset) : SpawnReset :=
  { dispositions := reset.dispositions, mask := reset.mask, descriptors := reset.descriptors }

/-- Why a program could not start, for a person. -/
private def failureText (failure : Linger.Session.Spawn.Failure) (prog cwd : String) : String :=
  match failure with
  | .directory why => s!"cannot enter the directory {cwd}: {why}"
  | .notFound _ => s!"{prog}: not found"
  | .notRunnable why => s!"{prog}: cannot be run: {why}"

/-- Take over the session the image this one replaced handed over at `path`, as `__upgraded`
asks, and serve it as `serve` does: the session's whole state, and the listener, the pty, the
signal pipe, the locks and every connection, open at the numbers the handoff names
(`Handoff.decode`), with what the old image still owed the program and each connection. The
handoff is read and removed, and the connection that asked hears `done`. A connection whose debt
no longer fits `outbufCap`, as one whose repaint was under way can, is cut, as a slow client is.

A handoff that does not decode, which a probe that named its format makes unlikely but cannot
exclude, leaves no half-session: the session ends as a kill ends it, its program `pid`, which
`__upgraded` names, stopped, the name's end record saying how it ended, and the checkpoint the
replaced image saved just before its exec kept, for the first attach to show; every descriptor
the handoff named closes as the process ends. -/
def adopt (name path : String) (pid : UInt32) (saveCkpt : State → IO Unit) (dropCkpt : IO Unit)
    (record : RecordFile) : IO Unit := do
  ignoreSighup
  let sockPath ← Paths.socketPath name
  let bytes ←
    try
      pure (some (← IO.FS.readBinFile path))
    catch err =>
      report s!"linger: reading the handoff failed: {err}"
      pure none
  try
    IO.FS.removeFile path
  catch _ =>
    pure ()
  let some (st, w) := bytes.bind (Linger.Session.Handoff.decode ·.toList) |
    do
      report
          s!"linger: session '{name}': the handoff from the image this one replaced does not \
            decode; ending the session, whose checkpoint stays"
      let outcome ← stopChild pid
      try
        record.save (.ended outcome)
      catch err =>
        report s!"linger: recording how the session ended failed: {err}"
      try
        endSession pid
      catch err =>
        report s!"linger: ending the session's processes failed: {err}"
      discard <| reapNohang pid
      try
        IO.FS.removeFile sockPath
      catch _ =>
        pure ()
  let listenFd := UInt32.ofNat w.listenFd
  let sigRead := UInt32.ofNat w.signals.1
  let sigWrite := UInt32.ofNat w.signals.2
  let signals ←
    try
      adoptSignalPipe sigRead sigWrite
      pure (some sigRead)
    catch err =>
      report s!"linger: waiting for the program's end on a timer: {err}"
      pure none
  let mut conns : List Conn := []
  let mut cut : List Event := []
  for c in w.conns do
    let (out, over) := bufEnqueue outbufCap .empty (ByteArray.mk c.owed.toArray)
    if over then
      close (UInt32.ofNat c.fd)
      if c.closeBy.isNone then
        cut := cut ++ [.closed c.fd]
    else
      conns := conns ++ [{ fd := UInt32.ofNat c.fd, out, closeBy := c.closeBy }]
  let rt : Rt :=
    { st, listenFd, ptyFd := UInt32.ofNat w.ptyFd, childPid := UInt32.ofNat w.childPid, conns,
      ptyIn := (bufOffer ptyInCap .empty (ByteArray.mk w.ptyIn.toArray)).1, signals,
      signalWrite := signals.map fun _ => sigWrite, locks := w.locks.map UInt32.ofNat, saveCkpt,
      dropCkpt, saveRecord := record.save }
  let (rt, answered) ← runEffect rt (.send w.asker .done)
  let latest ← IO.mkRef (← pump rt (cut ++ answered))
  try
    run name w.login record latest
  finally
    close listenFd
    try
      IO.FS.removeFile sockPath
    catch _ =>
      pure ()
    for fd in (← latest.get).locks do
      close fd

/-- Hold both ownership locks from before recovery through final cleanup.
Loading under the locks prevents a second runtime namespace from reading or
overwriting a checkpoint that another daemon is still using. The claim waits
out an offline reader (`claimRetry`) but not a live owner. The name's end record says the
program runs before it starts and how it ended before the locks are released; a program that
cannot start leaves the record as it was.

Without `start`, as `attach` asks, the daemon resumes the saved session, or starts a new one
when none is saved: `recover true` says which, and a checkpoint that does not decode starts
nothing and stays as it is. With `start`, it takes the name only when no live or saved session
holds it, never resumes one (`Start.plan`), runs the program in `cwd` or not at all, and tells
`start` what it did. With `resume` as well, it runs only a saved session's program again, an
ended one included, as `recover false` decides, and starts nothing for a live session, a name no
session holds (`Start.resumePlan`) or a checkpoint that does not decode. Either way it takes the
request's ticket before the session is visible, and starts nothing when the command took it
first (`Start.proceeds`). -/
def serve (name : String) (cwd : String) (argv : List String) (saveCkpt : State → IO Unit)
    (dropCkpt : IO Unit) (recover : Bool → IO Recovered) (record : RecordFile)
    (start : Option Request := none) (resume : Bool := false) : IO Unit := do
  let deadline := (← monotonicMs) + claimWaitMs
  let reported ← IO.mkRef false
  let retry := claimRetry name (← Paths.socketPath name) deadline reported
  Paths.withSessionLockHeld name retry fun locks => do
      ignoreSighup
      let sockPath ← Paths.socketPath name
      let r ← unixConnect sockPath
      let live := r ≥ 0
      if live then
        close r.toUInt64.toUInt32
      if let some req := start then
        let saved ← System.FilePath.pathExists (← Paths.ckptPath name)
        if resume then
          match Start.resumePlan live saved with
          | .running =>
            req.tell .running
            return
          | .missing =>
            req.tell
                (.failed Linger.Os.Answer.notFound.code.toUInt8
                  s!"no session '{name}'".toUTF8.toList)
            return
          | .resume =>
            pure ()
        else
          match Start.plan live saved with
          | .running =>
            req.tell .running
            return
          | .saved =>
            req.tell .saved
            return
          | .take =>
            pure ()
      if live then
        throw (IO.userError s!"session '{name}' already running")
      -- a start loads no checkpoint; anything else resumes the saved session or, when a new one
      -- may start, starts one when none is saved, and starts nothing over a checkpoint that does
      -- not decode, which stays as it is
      let recovered ←
        if start.isSome && !resume then
          pure (.ok none)
        else
          recover !resume
      if let .error (status, why) := recovered then
        match start with
        | some req =>
          req.tell (.failed status why.toUTF8.toList)
        | none =>
          report s!"linger: session '{name}' did not start: {why}"
        return
      let saved := recovered.toOption.join
      -- A new session runs in `cwd` or not at all. A resume runs in its saved directory, or in
      -- $HOME when that is gone (`Env.resumeDir`), and then says so in the log and, through
      -- `Start.metadata`, in the info field saved_dir.
      let mut cwd := cwd
      if let some (_, dir, _) := saved then
        match Linger.Os.Env.resumeDir (← IO.getEnv "HOME") dir (← System.FilePath.isDir dir) with
        | some run =>
          cwd := run
          if run != dir then
            report s!"linger: session '{name}' resumes in {run}: its directory {dir} is gone"
        | none =>
          throw
              (IO.userError
                s!"session '{name}' cannot resume: its directory {dir} is gone, and HOME is unset")
      let restore := saved.map (fun (vt, _, fields) => (vt, fields))
      -- The socket lock excludes another cooperating listener, even if connect
      -- failed for a reason other than a stale socket. Never unlink the lock inode.
      try
        IO.FS.removeFile sockPath
      catch _ =>
        pure ()
      -- The commit point, before the session is visible: the daemon takes the request's ticket,
      -- and when the command that asked took it first, having stopped waiting, this daemon starts
      -- nothing and tells nothing, as that command answered.
      if let some req := start then
        unless Start.proceeds (← req.take) do
          return
      let listenFd ← unixListen sockPath
      try
        setNonblock listenFd
        let (prog, args) := Start.programOf (Linger.Os.Env.shellOf (← IO.getEnv "SHELL")) argv
        -- Preserve the checkpoint's terminal state and dimensions. Clamp only at
        -- the syscall boundary; resizing the restored VT would reset its margins.
        let vt0 := Linger.Session.bootVt (restore.map (·.1))
        let created ← realtimeS
        -- before the program starts, so its end always reaches the pipe; without one, every poll
        -- round asks whether the program has ended, and a stop signal has its default action
        let signals ←
          match ← signalPipe.toBaseIO with
          | .ok fds =>
            pure (some fds)
          | .error err =>
            report
                s!"linger: waiting for the program's end on a timer, and a stop signal ends the \
                  daemon at once: {err}"
            pure none
        -- The name is this session's from here on: should the daemon end without saying how
        -- its program ended, a reader that holds the name hears that the ending is unknown,
        -- never the previous session's. A record that cannot be written starts nothing, and a
        -- program that cannot start puts the previous record back.
        let previous ← record.load
        record.save (.running none)
        let spawned ←
          try
            trySpawnPty (UInt32.ofNat (Terminal.Vt.clampDim vt0.colCount))
                (UInt32.ofNat (Terminal.Vt.clampDim vt0.rowCount)) cwd prog args
                ((Start.environment name).toArray.map fun (key, value) => s!"{key}={value}")
                (resetOf Start.reset)
          catch err =>
            record.restore previous
            throw err
        if let .error reported := spawned then
          record.restore previous
          let failure := failureOf reported
          let why := failureText failure prog cwd
          match start with
          | some req =>
            req.tell (.failed (Start.failureStatus failure) why.toUTF8.toList)
          | none =>
            throw (IO.userError s!"linger: session '{name}' did not start: {why}")
          return
        let .ok (pid, ptyFd) := spawned | return
        if let some req := start then
          req.tell .started
        let st :=
          State.boot vt0 ((restore.map (·.2)).getD [])
            (Start.metadata name (toString pid) (toString created)
              (String.intercalate " " (prog :: args.toList)) cwd (saved.map fun (_, dir, _) => dir))
        -- The cleanup reads the runtime as each round left it, the program's ending included,
        -- whatever fails after that round.
        let latest ←
          IO.mkRef
              ({ st, listenFd, ptyFd, childPid := pid, signals := signals.map (·.1),
                 signalWrite := signals.map (·.2), locks, saveCkpt, dropCkpt,
                 saveRecord := record.save } :
                Rt)
        run name argv.isEmpty record latest
      finally
        close listenFd
        try
          IO.FS.removeFile sockPath
        catch _ =>
          pure ()

end Linger.Session.Shell.Daemon
