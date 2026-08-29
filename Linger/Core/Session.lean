import Linger.Core.Wire
import Linger.Core.Vt
import Linger.Core.Render
import Linger.Core.Terminal
import Linger.Core.Name
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

structure Client where
  id : Nat
  cols : UInt32 := 80
  rows : UInt32 := 24
  attached : Bool := false
  /-- attached with a real size (read-only observers attach 0×0 and
  never influence the pty size — abduco's `-r`). -/
  sizer : Bool := false
  /-- attach order; the highest attached sizer owns the size
  (abduco's better-resize-handling rule). -/
  seq : Nat := 0
  /-- `linger wait` parked here until the child exits. -/
  waiting : Bool := false
  decoder : Wire.Decoder := {}
  deriving Repr, Inhabited

structure State where
  vt : Vt.Vt
  /-- One bounded scanner owned by the PTY-facing virtual terminal. -/
  scan : Terminal.Scan := .ground
  clients : List Client := []
  labels : List (String × String) := []
  /-- name/pid/created/cwd…, set once by the runtime at boot. -/
  metaKv : List (String × String) := []
  exited : Option UInt32 := none
  /-- pty output since the last checkpoint? -/
  dirty : Bool := false
  lastCkptMs : UInt64 := 0
  /-- monotone attach counter, for size ownership. -/
  attachSeq : Nat := 0
  /-- Monotone output counter: bumped once per pty-output event. A counter
  rather than a timestamp, so "has anything happened since you looked" is
  determined by the event list alone — `.tick` already carries time for the
  checkpoint clock, but this needs no tick to be *correct*, only to be
  reported. -/
  outSeq : Nat := 0
  /-- The `outSeq` as of the last time somebody looked: set on attach and
  when an attached client leaves. `outSeq > lookSeq` is "unread", which is a
  property of the **session**, not of a viewer — "last looked" is a session
  event, so no per-client bookkeeping is created for a one-off connection. -/
  lookSeq : Nat := 0
  /-- `outSeq` as of the previous `.tick`, and whether output arrived since
  it. Freshness from a *counter comparison across ticks* rather than a stored
  timestamp: the poll loop already ticks, so "output since the last tick" is
  the signal, and the core needs no clock arithmetic. -/
  tickOutSeq : Nat := 0
  freshFlag : Bool := false
  deriving Repr, Inhabited

/-- What the runtime feeds in. All byte payloads are `List UInt8`; the
runtime converts at the fd boundary. -/
inductive Event where
  | connected (id : Nat)
  | bytes (id : Nat) (chunk : List UInt8)
  | closed (id : Nat)
  | ptyOut (chunk : List UInt8)
  | childExited (status : UInt32)
  | tick (nowMs : UInt64)
  deriving Repr

/-- What the runtime executes. -/
inductive Effect where
  | send (id : Nat) (m : Msg)
  | close (id : Nat)
  | writePty (bytes : List UInt8)
  | resizePty (cols rows : UInt32)
  | killChild
  | checkpoint
  | dropCheckpoint
  | exit
  deriving Repr, DecidableEq

/-- Checkpoint cadence (§ reboot-resume): at most one per minute. -/
def ckptIntervalMs : UInt64 := 60000

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

def State.client? (s : State) (id : Nat) : Option Client :=
  s.clients.find? (·.id == id)

def State.setClient (s : State) (c : Client) : State :=
  { s with clients := s.clients.map (fun c' => if c'.id == c.id then c else c') }

def State.dropClient (s : State) (id : Nat) : State :=
  { s with clients := s.clients.filter (·.id != id) }

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
  s.metaKv
    ++ [("clients", toString (s.clients.filter (·.attached)).length)]
    -- the observations `Status.classify` needs from the daemon; the rest
    -- (reachability, checkpoint loadability) only the caller can know
    ++ [("unseen", toString (unseen s)), ("fresh", toString s.freshFlag),
        ("behind", toString (behind s))]
    -- what an agent needs to see the session (specs/agent-cli.md Step 1):
    -- geometry + cursor for `capture`, `alt` for "a full-screen app is live",
    -- `outseq` as the change cursor ("re-capture only when it moved"). Values
    -- are read at reply time, so they are current as of this `.info`.
    ++ [("cols", toString s.vt.cols), ("rows", toString s.vt.rows),
        ("cursorx", toString s.vt.cursor.x), ("cursory", toString s.vt.cursor.y),
        ("alt", toString s.vt.altGrid.isSome), ("outseq", toString s.outSeq)]
    ++ (match s.exited with
        | some st => [("exit", toString st.toNat)]
        | none => [])
    ++ s.labels.map (fun (k, v) => (s!"label.{k}", v))

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
which passed a label's newline through verbatim (`specs/restore-conformance.md`
Step 0 ledger item 2, §Row/§Status integrity). That shape was also what made the
output unprovable — a `String` literal does not reduce in the kernel, so no theorem
could see its bytes, which is exactly the argument in `Linger/Core/Render.lean`'s
header. Building `List UInt8` directly fixes both at once. -/
def infoText (s : State) : List UInt8 :=
  (infoFields s).flatMap (fun (k, v) =>
    Render.utf8s k.toList ++ [0x09] ++ Render.utf8s v.toList ++ [0x0A])

/-- Resize the pty only on behalf of the size owner: the most recently
attached client with a real terminal (abduco's rule — a read-only
observer or an older mirror must not fight the active user's size). -/
def sizeOwner (s : State) : Option Client :=
  (s.clients.filter (fun c => c.attached && c.sizer)).foldl
    (fun best c => match best with
      | none => some c
      | some b => if c.seq ≥ b.seq then some c else some b)
    none

def resizeEffects (s : State) (c : Client) : List Effect :=
  if (sizeOwner s).any (·.id == c.id) then [.resizePty c.cols c.rows] else []

/-- Send a byte payload as ≤ 64 KiB `output` frames (Wire §Bound wf). -/
def outputMsgs (id : Nat) (bytes : List UInt8) : List Effect :=
  (chunksOf outputChunk bytes).map (fun c => .send id (.output c))

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
    -- 0×0 marks a read-only observer (abduco `-r`): it mirrors output
    -- but never owns the size and its input is dropped
    let sizer := cols != 0 && rows != 0
    let c := { c with attached := true, sizer, seq := s.attachSeq, cols, rows }
    let s := { s.setClient c with attachSeq := s.attachSeq + 1, lookSeq := s.outSeq }
    -- resize only on a genuine size change. `Vt.resize` resets the scroll
    -- region and tab ruler (top/bot/tabs) unconditionally, so resizing at an
    -- unchanged size wiped a child's DECSTBM and custom tab stops from the
    -- model — and, since the winsize did not change, the kernel sends no
    -- SIGWINCH, so the child is never nudged to re-establish them. A same-size
    -- reattach must therefore leave the emulator alone (restore-conformance
    -- Step 0 ledger item 1).
    let s := if sizer && (s.vt.cols != cols.toNat || s.vt.rows != rows.toNat)
             then { s with vt := s.vt.resize cols.toNat rows.toNat } else s
    (s, resizeEffects s c
          ++ outputMsgs c.id (Render.restore s.vt)
          ++ (match s.exited with
              | some st => [.send c.id (.exited st)]
              | none => []))
  | .input bytes =>
    -- attached observers are read-only; control connections (not
    -- attached, e.g. `linger send`) keep their input rights
    if c.attached && !c.sizer then (s, [])
    else (s, [.writePty bytes])
  | .resize cols rows =>
    let c := { c with cols, rows }
    let s := s.setClient c
    -- only the newest real-terminal attacher owns the pty size
    if c.attached && c.sizer && (sizeOwner s).any (·.id == c.id) then
      ({ s with vt := s.vt.resize cols.toNat rows.toNat },
       [.resizePty cols rows])
    else
      (s, [])
  | .detachAll =>
    (s, (s.clients.filter (·.attached) |>.map (fun c' => Effect.close c'.id))
          ++ [.send c.id .done])
  | .kill => (s, [.killChild, .dropCheckpoint, .exit])
  | .info => (s, [.send c.id (.infoReply (infoText s)), .send c.id .done])
  | .history =>
    (s, outputMsgs c.id (Render.history s.vt false) ++ [.send c.id .done])
  | .wait =>
    match s.exited with
    | some st => (s, [.send c.id (.exited st)])
    | none => (s.setClient { c with waiting := true }, [])
  | .labelSet kv =>
    let txt := String.fromUTF8? (ByteArray.mk kv.toArray) |>.getD ""
    match txt.splitOn "=" with
    | k :: rest =>
      if k.isEmpty then (s, [.send c.id (.err "empty label key".toUTF8.toList)])
      else
        let v := String.intercalate "=" rest
        let labels := (s.labels.filter (·.1 != k)) ++ [(k, v)]
        if labels.length > maxLabels then
          (s, [.send c.id (.err "too many labels".toUTF8.toList)])
        else ({ s with labels }, [.send c.id .done])
    | [] => (s, [.send c.id (.err "empty label".toUTF8.toList)])
  | .labelUnset k =>
    let txt := String.fromUTF8? (ByteArray.mk k.toArray) |>.getD ""
    ({ s with labels := s.labels.filter (·.1 != txt) }, [.send c.id .done])
  | .labelClear => ({ s with labels := [] }, [.send c.id .done])
  -- daemon-to-client vocabulary arriving at the daemon, and unknown
  -- tags: dropped without a trace (§Frame, machine half)
  | .output _ | .exited _ | .infoReply _ | .done | .err _ => (s, [])
  | .unknown _ _ => (s, [])

/-! ## The step function -/

/-- Fold decoded messages through `onMsg`, threading state + effects.
The client record is re-read each round (attach mutates it); a message
that closed the client stops affecting state. Named (not inline) so
the preservation theorems can target it. -/
def feedMsgs (id : Nat) (msgs : List Msg) (acc : State × List Effect) :
    State × List Effect :=
  msgs.foldl
    (fun (acc : State × List Effect) m =>
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
    else
      ({ s with clients := s.clients ++ [{ id }] }, [])
  | .bytes id chunk =>
    match s.client? id with
    | none => (s, [])  -- late bytes from a dropped client
    | some c =>
      let (dec, msgs) := c.decoder.feed chunk
      if dec.errored then
        (s.dropClient id, [.close id])
      else
        feedMsgs id msgs (s.setClient { c with decoder := dec }, [])
  | .closed id =>
    -- checkpoint when the last attached client leaves (reboot-resume's
    -- main save point; detach itself must stay side-effect-free
    -- otherwise — §Detach allows only this)
    let hadAttached := s.clients.any (fun c => c.id == id && c.attached)
    let s' := s.dropClient id
    if s.dirty && hadAttached && s'.clients.all (fun c => !c.attached) then
      ({ s' with dirty := false }, [.checkpoint])
    else
      (s', [])
  | .ptyOut chunk =>
    let r := Terminal.feed s.vt s.scan chunk
    ({ s with vt := r.vt, scan := r.scan, dirty := true,
              outSeq := s.outSeq + 1,
              lookSeq := if s.clients.any (·.attached) then s.outSeq + 1
                         else s.lookSeq },
     (if r.replies.isEmpty then [] else [.writePty r.replies]) ++
       broadcast s r.visible)
  | .childExited status =>
    let flushed := Terminal.finish s.scan
    let s := { s with exited := some status, scan := flushed.2 }
    let flush := if flushed.1.isEmpty then [] else broadcast s flushed.1
    let notify := s.clients.filter (fun c => c.attached || c.waiting)
      |>.map (fun c => Effect.send c.id (.exited status))
    let closes := s.clients.map (fun c => Effect.close c.id)
    (s, flush ++ notify ++ closes ++ [.dropCheckpoint, .exit])
  | .tick now =>
    -- the activity flag is refreshed in both branches as a field value: a
    -- `let` before the `if` would hide the `if` from the proofs that `split`
    -- on this handler
    if s.dirty && now ≥ s.lastCkptMs + ckptIntervalMs then
      ({ s with dirty := false, lastCkptMs := now,
                freshFlag := s.tickOutSeq < s.outSeq, tickOutSeq := s.outSeq },
       [.checkpoint])
    else ({ s with freshFlag := s.tickOutSeq < s.outSeq, tickOutSeq := s.outSeq }, [])

/-- A whole event trace folded through `step`, effects in arrival
order — the specification of the runtime's poll loop (which feeds one
event at a time). Structural recursion, and projection-shaped so
`(run s (e :: es)).1 = (run (step s e).1 es).1` is definitional: the
trace-level theorems (`run_wf`, `run_bytes_isolates`) step through it
directly. -/
def run (s : State) : List Event → State × List Effect
  | [] => (s, [])
  | ev :: evs =>
    let r := step s ev
    let rest := run r.1 evs
    (rest.1, r.2 ++ rest.2)

end Linger.Core.Session
