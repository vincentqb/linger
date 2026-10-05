module

public import Linger.Core.Wire
public import Linger.Core.Vt
public import Linger.Core.Render
public import Linger.Core.Replay
public import Linger.Core.Terminal
public import Linger.Core.Name

public section

/-! # Linger.Core.Session — the daemon's brain, as data

One daemon = one session = one pty + one `Vt` + attached clients. This
module is the *entire* decision logic: `step : State → Event → State ×
List Effect`. The runtime (Step 6) is a dumb poll loop that turns fds
into `Event`s and `Effect`s into syscalls.

Tensions carried (THEOREMS.md):
* §Detach — a session with zero clients still advances; detach never
  touches the screen; attach touches only the dimensions (resize).
* §Bound — clients ≤ `maxClients`, labels ≤ `maxLabels`, every stored
  wire decoder stays under the Wire §Bound cap and non-errored (a
  malformed peer is closed, not buffered).
* §Frame (machine half) — an `unknown` message changes nothing.
-/

namespace Linger.Core.Session

open Linger.Core.Wire (Msg)

def maxClients : Nat := 16

def maxLabels : Nat := 64

def outputChunk : Nat := 65536

/-- Maximum encoded info answer, shared by the producer and the CLI accumulator. -/
def infoReplyCap : Nat := 1048576

structure Client where
  id : Nat
  cols : UInt32 := 80
  rows : UInt32 := 24
  attached : Bool := false
  /-- attached with a real size (read-only observers attach 0×0 and
  never influence the pty size). -/
  sizer : Bool := false
  /-- attach order; the highest attached sizer owns the size. -/
  seq : Nat := 0
  /-- `linger wait` parked here until the child exits. -/
  waiting : Bool := false
  decoder : Wire.Decoder := {}
  deriving Repr, Inhabited

/-- The session's whole state. Sealed since lean-modules Step 5: the
bookkeeping fields §Bound and §Unread protect are `private`, which makes the
anonymous constructor private too — outside this module and its friends
(`Theorems/Session.lean`, `Tests/Session.lean`, via `import all`) a `State`
can only be `State.boot`ed and `step`ped, never forged or field-poked, so
`run_wf`'s well-formedness is a fact about every state the daemon can possess
rather than about the states it politely constructs. `vt`, `labels` and
`metaKv` stay public-read: they are exactly what the checkpoint save hook
serializes (`Linger/Runtime/Resume.lean`). -/
structure State where
  vt : Vt.Vt
  /-- One bounded scanner owned by the PTY-facing virtual terminal. -/
  private scan : Terminal.Scan := .ground
  private clients : List Client := []
  labels : List (String × String) := []
  /-- name/pid/created/cwd…, set once by the runtime at boot. -/
  metaKv : List (String × String) := []
  private exited : Option UInt32 := none
  /-- Persistent screen or label changes since the last checkpoint? -/
  private dirty : Bool := false
  private lastCkptMs : Nat := 0
  /-- monotone attach counter, for size ownership. -/
  private attachSeq : Nat := 0
  /-- Monotone output counter: bumped once per pty-output event. A counter
  rather than a timestamp, so "has anything happened since you looked" is
  determined by the event list alone — `.tick` already carries time for the
  checkpoint clock, but this needs no tick to be *correct*, only to be
  reported. -/
  private outSeq : Nat := 0
  /-- The `outSeq` as of the last time somebody looked: set on attach and
  when an attached client leaves. `outSeq > lookSeq` is "unread", which is a
  property of the **session**, not of a viewer — "last looked" is a session
  event, so no per-client bookkeeping is created for a one-off connection. -/
  private lookSeq : Nat := 0
  /-- `outSeq` as of the previous `.tick`, and whether output arrived since
  it. Freshness from a *counter comparison across ticks* rather than a stored
  timestamp: the poll loop already ticks, so "output since the last tick" is
  the signal, and the core needs no clock arithmetic. -/
  private tickOutSeq : Nat := 0
  private freshFlag : Bool := false

-- No `deriving` clause at all. `Inhabited` went in `specs/archive/vt-toolkit.md`
-- Step 3: it needed `Inhabited Vt`, a public door out of the `Vt` seal admitting a
-- zero-column screen. `Repr` went with the seal's read half (the audit's R6): it
-- needed `Repr Vt`, whose removal is what makes the seal actually hide reads.
-- Nothing used either instance. A `State` still has exactly one door, `State.boot`.

/-- The one public door into a `State`: a fresh or restored emulator, the
restored labels, the boot-time metadata. Everything else a `State` ever holds
is `step`'s doing (the private fields above make the constructor private).

Restored labels are capped HERE, which closes the Bounded-at-boot gap this
step's sizing surfaced: `.labelSet` enforces `maxLabels` per message, but
`Checkpoint.load` is deliberately total on arbitrary bytes, so a corrupt or
forged checkpoint could carry any list and boot used to be the bypass. Over
the cap, the first `maxLabels` survive (`.labelSet` appends at the end, so
these are the oldest). `boot_wf` is the claim; composed with `run_wf`
(`run_boot_wf`), every state the daemon can hold is well-formed. -/
def State.boot (vt : Vt.Vt) (labels : List (String × String)) (metaKv : List (String × String)) :
    State := { vt, labels := labels.take maxLabels, metaKv }

/-- What the runtime feeds in. All byte payloads are `List UInt8`; the
runtime converts at the fd boundary. -/
inductive Event where
  | connected (id : Nat)
  | bytes (id : Nat) (chunk : List UInt8)
  | closed (id : Nat)
  | ptyOut (chunk : List UInt8)
  | childExited (status : UInt32)
  | tick (nowMs : Nat)
  | checkpointFailed
  deriving Repr

/-- What the runtime executes. -/
inductive Effect where
  | send (id : Nat) (m : Msg)
  | replay (id : Nat) (plan : Replay.Plan)
  | close (id : Nat)
  | writePty (bytes : List UInt8)
  | resizePty (cols rows : UInt32)
  | killChild
  | checkpoint
  | dropCheckpoint
  | exit
  deriving Repr, DecidableEq

/-- Checkpoint cadence (§ reboot-resume): at most one periodic save per minute.
Natural-number milliseconds keep deadline addition from wrapping. -/
def ckptIntervalMs : Nat := 60000

/-- A label payload decoded as text: a bare key for `.labelUnset`, a `k=v` pair
for `.labelSet`. Invalid UTF-8 becomes `""`, which is the safe direction —
`.labelSet` rejects an empty key, so a corrupt payload can neither set nor unset
anything.

One decode shared by both arms, so they cannot drift about what a key *is*: a
`.labelSet` that decoded differently from `.labelUnset` would leave a label no
`unset` could reach. -/
def labelText (bs : List UInt8) : String := String.fromUTF8? (ByteArray.mk bs.toArray) |>.getD ""

/-! ## Helpers -/

def chunksOf {α : Type} (n : Nat) (l : List α) : List (List α) :=
  if _h : l.length ≤ n ∨ n = 0 then [l]
  else
    let rest := chunksOf n (l.drop n)
    l.take n :: rest
termination_by l.length
decreasing_by
  simp at _h
  simp [List.length_drop]
  omega

def State.client? (s : State) (id : Nat) : Option Client := s.clients.find? (·.id == id)

def State.setClient (s : State) (c : Client) : State :=
  { s with clients := s.clients.map (fun c' => if c'.id == c.id then c else c') }

def State.dropClient (s : State) (id : Nat) : State :=
  { s with clients := s.clients.filter (·.id != id) }

/-- One disconnect transition for EOF and malformed traffic. Decide whether
the last attacher needs a checkpoint before removing its record. -/
def closeClient (s : State) (id : Nat) : State × List Effect :=
  let hadAttached := s.clients.any (fun c => c.id == id && c.attached)
  let s' := s.dropClient id
  if s.dirty && hadAttached && s'.clients.all (fun c => !c.attached) then
    ({ s' with dirty := false }, [.checkpoint])
  else (s', [])

/-- Unread: output arrived while nobody was watching. What
`Status.wantsYou` is derived from — a property of the **session**, since
"last looked" is a session event rather than a viewer attribute, so a one-off
connection creates no state. -/
def unseen (s : State) : Bool := s.lookSeq < s.outSeq

/-- How much arrived unseen — free from the counter, where a boolean would
have thrown it away. -/
def behind (s : State) : Nat := s.outSeq - s.lookSeq

/-- The fields one listing record carries, as a named stage. Split out from
`infoText` because the framing below is only unambiguous if no field contains a
framing byte, and that is a claim about *these* — see `infoText_framing`. -/
def infoFields (s : State) : List (String × String) :=
  s.metaKv ++ [("clients", toString (s.clients.filter (·.attached)).length)]
    -- the observations `Status.classify` needs from the daemon; the rest
    -- (reachability, checkpoint loadability) only the caller can know
    ++
    [("unseen", toString (unseen s)), ("fresh", toString s.freshFlag),
      ("behind", toString (behind s))]
    -- what an agent needs to see the session (specs/archive/agent-cli.md Step 1):
    -- geometry + cursor for `capture`, `alt` for "a full-screen app is live",
    -- `outseq` as the change cursor ("re-capture only when it moved"). Values
    -- are read at reply time, so they are current as of this `.info`.
    ++
    [("cols", toString s.vt.colCount), ("rows", toString s.vt.rowCount),
      ("cursorx", toString s.vt.cursorPos.1), ("cursory", toString s.vt.cursorPos.2),
      ("alt", toString s.vt.inAlt), ("outseq", toString s.outSeq)] ++
    (match s.exited with
    | some st => [("exit", toString st.toNat)]
    | none => []) ++
    s.labels.map (fun (k, v) => (s!"label.{k}", v))

/-- Frame the fields as `k` TAB `v` LF records.

**The two framing bytes are emitted structurally, and nothing else can produce
them.** Every character of a key or a value goes through `Render.utf8s`, which
replaces a C0 control — tab and newline included — with U+FFFD. So a label value
containing a newline shows a replacement character instead of **forging an extra
record**, and in particular cannot forge a `status`/`state` pair that the listing
would then display as a session's state.

Established here rather than at `.labelSet`, for the same reason `Render.gridAnsi`
establishes its own pen instead of trusting its callers: a guard at the emit site
needs no invariant about where the field came from, and it covers fields nobody has
added yet. `Status.name_clean` proves the *status* column carries no framing byte;
this is the same promise for every other column, and labels used to bypass both.

This was `(String.join (fields.map (fun (k, v) => s!"{k}\t{v}\n"))).toUTF8.toList`,
which passed a label's newline through verbatim (`specs/archive/restore-conformance.md`
Step 0 ledger item 2, §Row/§Status integrity). That shape was also what made the
output unprovable — a `String` literal does not reduce in the kernel, so no theorem
could see its bytes, which is exactly the argument in `Linger/Core/Render.lean`'s
header. Building `List UInt8` directly fixes both at once. -/
def infoText (s : State) : List UInt8 :=
  (infoFields s).flatMap
    (fun (k, v) => Render.utf8s k.toList ++ [0x09] ++ Render.utf8s v.toList ++ [0x0A])

/-- Resize the pty only on behalf of the size owner: the most recently
attached client with a real terminal (a read-only observer or an older
mirror must not fight the active user's size). -/
def sizeOwner (s : State) : Option Client :=
  (s.clients.filter (fun c => c.attached && c.sizer)).foldl
    (fun best c =>
      match best with
      | none => some c
      | some b => if c.seq ≥ b.seq then some c else some b)
    none

/-- One geometry transition for attach, attached resize and control resize.
An exact or clamped same size preserves the whole emulator: resetting its
region and tabs without a winsize change would leave the child unaware.
A genuine change marks the screen dirty and sends the pty the emulator's
effective dimensions, never an unclamped wire value. -/
def resize (s : State) (cols rows : UInt32) : State × List Effect :=
  if
      (s.vt.colCount == cols.toNat && s.vt.rowCount == rows.toNat) ||
        (s.vt.colCount == Vt.clampDim cols.toNat && s.vt.rowCount == Vt.clampDim rows.toNat) then
    (s, [])
  else
    let vt := s.vt.resize cols.toNat rows.toNat
    ({ s with
        vt, dirty := true },
      [.resizePty (UInt32.ofNat vt.colCount) (UInt32.ofNat vt.rowCount)])

/-- Only the newest attached sizer can apply a client resize. -/
def resizeOwned (s : State) (c : Client) : State × List Effect :=
  if c.sizer && (sizeOwner s).any (·.id == c.id) then resize s c.cols c.rows else (s, [])

/-- The control-resize decision (`linger resize`, from a NON-attached
connection — agent-cli Decision 3). The size-owner rule extends rather than
bends: while an attached sizer exists it always wins (refuse, loudly — a
silent drop would let an agent believe a size it never got); with nobody
attached there is nobody to fight, and the requested size applies. The
same-size branch leaves the emulator alone for the attach guard's reason:
`Vt.resize` resets the scroll region and tab ruler unconditionally, and at an
unchanged winsize no SIGWINCH nudges the child to re-establish them
(restore-conformance Step 0 ledger 1). Zero is refused — 0×0 is the observer
marker on attach, and a zero dimension is never a size. -/
def controlResize (s : State) (c : Client) (cols rows : UInt32) : State × List Effect :=
  if (sizeOwner s).isSome then
    (s, [.send c.id (.err "an attached client owns the size".toUTF8.toList)])
  else
    if cols == 0 || rows == 0 then (s, [.send c.id (.err "size must be nonzero".toUTF8.toList)])
    else
      let r := resize s cols rows
      (r.1, r.2 ++ [.send c.id .done])

/-- Send a byte payload as ≤ 64 KiB `output` frames (Wire §Bound wf). -/
def outputMsgs (id : Nat) (bytes : List UInt8) : List Effect :=
  (chunksOf outputChunk bytes).map (fun c => .send id (.output c))

/-- Preflight the whole info answer before emitting any bytes. Accepted answers
are a stream of bounded byte chunks followed by `done`; records and UTF-8 may
cross frames, so consumers decode text only after joining the payloads.
Refusals carry no prefix or `done`, and the diagnostic is bounded too. -/
def infoMsgs (id : Nat) (bytes : List UInt8) : List Effect :=
  if bytes.length > infoReplyCap then
    [.send id (.err ("info reply exceeds the byte limit".toUTF8.toList.take outputChunk))]
  else (chunksOf outputChunk bytes).map (fun c => .send id (.infoReply c)) ++ [.send id .done]

/-- Broadcast presentation bytes to the attached clients.

The empty guard is load-bearing, not defensive tidiness: `chunksOf n [] = [[]]`,
so without it a chunk consisting *entirely* of an owned query — whose visible
bytes are empty by design — would push a zero-length `output` frame to every
attached client on every terminal query. Unreachable before the mediator
existed, since the runtime raises `.ptyOut` only for a non-empty read.
Pinned by `broadcast_empty` and by a Session fixture. -/
def broadcast (s : State) (bytes : List UInt8) : List Effect :=
  if bytes.isEmpty then []
  else s.clients.filter (·.attached) |>.flatMap (fun c => outputMsgs c.id bytes)

/-! ## Message handling (client → daemon) -/

def onMsg (s : State) (c : Client) (m : Msg) : State × List Effect :=
  match m with
  | .attach cols rows =>
    if c.attached then (s, [.send c.id (.err "already attached".toUTF8.toList)])
    else
      -- 0×0 marks a read-only observer: it mirrors output
      -- but never owns the size and its input is dropped.
      let sizer := cols != 0 && rows != 0
      let c :=
        { c with
          attached := true, sizer, seq := s.attachSeq, cols, rows }
      let s :=
        { s.setClient c with
          attachSeq := s.attachSeq + 1, lookSeq := s.outSeq }
      let (s, effs) := resizeOwned s c
      -- Capture here: feedMsgs can change the VT again before effects run.
      (s,
        effs ++ [.replay c.id (Replay.start s.vt)] ++
          (match s.exited with
          | some st => [.send c.id (.exited st)]
          | none => []))
  | .input bytes =>
    -- attached observers are read-only; control connections (not
    -- attached, e.g. `linger send`) keep their input rights
    if c.attached && !c.sizer then (s, []) else (s, [.writePty bytes])
  | .resize cols rows =>
    let c :=
      { c with
        cols, rows }
    let s := s.setClient c
    if c.attached then resizeOwned s c
    else
      -- a control connection (`linger resize`): the named stage above owns
      -- the decision, and `controlResize_never_overrides` the invariant
      controlResize s c cols rows
  | .detachAll =>
    (s, (s.clients.filter (·.attached) |>.map (fun c' => Effect.close c'.id)) ++ [.send c.id .done])
  | .kill => (s, [.killChild, .dropCheckpoint, .exit])
  | .info => (s, infoMsgs c.id (infoText s))
  | .history => (s, outputMsgs c.id (Render.history s.vt) ++ [.send c.id .done])
  | .screen =>
    -- `linger capture`: the grid only, plain text. Delivering the current
    -- screen IS a look, so it catches the read mark up — after a capture,
    -- "output arrived while nobody was watching" is false and `behind` counts
    -- from this moment (agent-cli Decision 1). `.info` must never do this
    -- (`ls` polls every daemon; a listing that marks everything read destroys
    -- the status column) and `.history` stays an export, not an observation.
    ({ s with lookSeq := s.outSeq }, outputMsgs c.id (Render.screenText s.vt) ++ [.send c.id .done])
  | .wait =>
    match s.exited with
    | some st => (s, [.send c.id (.exited st)])
    | none => (s.setClient { c with waiting := true }, [])
  | .labelSet kv =>
    let txt := labelText kv
    match txt.splitOn "=" with
    | k :: rest =>
      if k.isEmpty then (s, [.send c.id (.err "empty label key".toUTF8.toList)])
      else
        let v := String.intercalate "=" rest
        let labels := (s.labels.filter (·.1 != k)) ++ [(k, v)]
        if labels.length > maxLabels then (s, [.send c.id (.err "too many labels".toUTF8.toList)])
        else
          ({ s with
              labels, dirty := true },
            [.send c.id .done])
    | [] => (s, [.send c.id (.err "empty label".toUTF8.toList)])
  | .labelUnset k =>
    let txt := labelText k
    ({ s with
        labels := s.labels.filter (·.1 != txt), dirty := true },
      [.send c.id .done])
  | .labelClear =>
    ({ s with
        labels := [], dirty := true },
      [.send c.id .done])
  -- daemon-to-client vocabulary arriving at the daemon, and unknown
  -- tags: dropped without a trace (§Frame, machine half)
  | .output _ | .exited _ | .infoReply _ | .done | .err _ => (s, [])
  | .unknown _ _ => (s, [])

/-! ## The step function -/

/-- Fold decoded messages through `onMsg`, threading state + effects.
The client record is re-read each round (attach mutates it); a message
after a close for this sender or an exit stops affecting state, even before
the runtime executes those effects. Named so the preservation and stopping
theorems can target it. -/
def feedMsgs (id : Nat) (msgs : List Msg) (acc : State × List Effect) : State × List Effect :=
  msgs.foldl
    (fun (acc : State × List Effect) m =>
      if acc.2.contains (.close id) || acc.2.contains .exit then acc
      else
        match acc.1.client? id with
        | none => acc
        | some c' =>
          let r := onMsg acc.1 c' m
          (r.1, acc.2 ++ r.2))
    acc

def step (s : State) (ev : Event) : State × List Effect :=
  match ev with
  | .connected id =>
    if s.clients.length ≥ maxClients then
      (s, [.send id (.err "too many clients".toUTF8.toList), .close id])
    else ({ s with clients := s.clients ++ [{ id }] }, [])
  | .bytes id chunk =>
    match s.client? id with
    | none => (s, []) -- late bytes from a dropped client
    | some c =>
      let (dec, msgs) := c.decoder.feed chunk
      if dec.errored then
        let (s, effs) := closeClient s id
        (s, .close id :: effs)
      else feedMsgs id msgs (s.setClient { c with decoder := dec }, [])
  | .closed id => closeClient s id
  | .ptyOut chunk =>
    let r := Terminal.feed s.vt s.scan chunk
    ({ s with
        vt := r.vt, scan := r.scan, dirty := true, outSeq := s.outSeq + 1,
        lookSeq := if s.clients.any (·.attached) then s.outSeq + 1 else s.lookSeq },
      (if r.replies.isEmpty then [] else [.writePty r.replies]) ++ broadcast s r.visible)
  | .childExited status =>
    let flushed := Terminal.finish s.scan
    let s :=
      { s with
        exited := some status, scan := flushed.2 }
    let flush := if flushed.1.isEmpty then [] else broadcast s flushed.1
    let notify :=
      s.clients.filter (fun c => c.attached || c.waiting) |>.map
        (fun c => Effect.send c.id (.exited status))
    let closes := s.clients.map (fun c => Effect.close c.id)
    (s, flush ++ notify ++ closes ++ [.dropCheckpoint, .exit])
  | .tick now =>
    -- the activity flag is refreshed in both branches as a field value: a
    -- `let` before the `if` would hide the `if` from the proofs that `split`
    -- on this handler
    if s.dirty && now ≥ s.lastCkptMs + ckptIntervalMs then
      ({ s with
          dirty := false, lastCkptMs := now, freshFlag := s.tickOutSeq < s.outSeq,
          tickOutSeq := s.outSeq },
        [.checkpoint])
    else
      ({ s with
          freshFlag := s.tickOutSeq < s.outSeq, tickOutSeq := s.outSeq },
        [])
  | .checkpointFailed =>
    -- Keep the attempt time: retry at the next cadence, without needing more
    -- output and without spinning while storage remains unavailable.
    ({ s with dirty := true }, [])

/-- Disconnect feedback can request persistence, but cannot create more
transport work. Used by the driver's termination argument. -/
theorem closed_effects (s : State) (id : Nat) :
    ∀ eff ∈ (step s (.closed id)).2, eff = .checkpoint := by
  simp only [step, closeClient]
  split <;> simp

/-- A failed checkpoint marks the state dirty without immediately retrying. -/
theorem checkpointFailed_effects (s : State) : (step s .checkpointFailed).2 = [] := by rfl

/-- Fold the supplied event trace through `step`, preserving effect order.
For the runtime this trace consists of the events actually consumed, including
effect feedback: `pump` stops before consuming any event after exit. `run` does
not model that queue or choose its stopping prefix. The state projection is
recursive, so preservation lifts directly from `step`. -/
def run (s : State) : List Event → State × List Effect
  | [] => (s, [])
  | ev :: evs =>
    let r := step s ev
    let rest := run r.1 evs
    (rest.1, r.2 ++ rest.2)

end Linger.Core.Session
