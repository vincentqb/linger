module

public import Linger.Terminal.Spec
import LeanEvidence.Commands

public section

/-! # What session headlines are stated in

The values a session exchanges with its clients and its runtime (messages, client records,
events and effects), the caps its state keeps, the contract on the effect interpreter, and
predicates over the session's operations, which they take as parameters: the bounds a state
keeps, the reachable states of the daemon's byte queues, and a model of how daemons and
offline readers claim a session's resources. Bodies are exposed: each definition here is its
own specification. -/

namespace Linger.Session.Wire

/-- Largest payload a frame may carry. Reads from the OS are ≤ 64 KiB, so honest senders stay
far below; a frame claiming more is either corruption or an attack, and the decoder turns it
into a connection error rather than memory growth. -/
@[expose]
def maxPayload : Nat := 262144

/-- The message vocabulary. Payload-carrying constructors keep raw
bytes; numeric fields are encoded LE at the payload layer. `unknown`
makes the decoder total (§Frame): a tag from a newer peer is data. -/
inductive Msg where
  /-- client → daemon: bytes for the pty (keystrokes, pastes). -/
  | input (bytes : List UInt8)
  /-- daemon → client: bytes from the pty (also used for history/restore). -/
  | output (bytes : List UInt8)
  /-- client → daemon: my terminal is now cols×rows. -/
  | resize (cols rows : UInt32)
  /-- client → daemon: I am a live client; stream output to me. -/
  | attach (cols rows : UInt32)
  /-- client → daemon: disconnect every attached client (incl. me). -/
  | detachAll
  /-- client → daemon: terminate the session. -/
  | kill
  /-- client → daemon: describe yourself (one-shot). -/
  | info
  /-- daemon → client: `k\tv\n` lines (fields + labels). -/
  | infoReply (bytes : List UInt8)
  /-- client → daemon: send scrollback and the screen as output frames, then `done`. -/
  | history
  /-- daemon → client: the session ended, with the status of its
  `Session.Event.childExited`. -/
  | exited (status : UInt32)
  /-- client → daemon: hold this connection open until the child exits. -/
  | wait
  /-- client → daemon: set one `k=v` label. -/
  | labelSet (kv : List UInt8)
  /-- client → daemon: remove one label by key. -/
  | labelUnset (k : List UInt8)
  /-- client → daemon: remove all labels. -/
  | labelClear
  /-- daemon → client: end of a request/reply exchange. -/
  | done
  /-- daemon → client: request failed, human-readable reason. -/
  | err (msg : List UInt8)
  /-- client → daemon: send the current screen (grid only, plain text) as
  output frames, then `done`. `linger capture` — and it marks the session
  seen (a capture is a look). -/
  | screen
  /-- any tag this version does not know: skipped, never fatal (§Frame). -/
  | unknown (tag : UInt8) (payload : List UInt8)
  deriving Repr, DecidableEq, Inhabited

/-- Decoder state. Both ends drop a connection whose decoder errored, rather than buffer
its input without bound. -/
structure Decoder where
  /-- Bytes of the incomplete frame; decoding keeps them within `4 + maxPayload`. -/
  buf : List UInt8 := []
  /-- An oversize frame arrived. The flag never clears, and no later chunk is decoded. -/
  errored : Bool := false
  deriving Repr, DecidableEq, Inhabited

end Linger.Session.Wire

namespace Linger.Session

open Linger.Session.Wire (Msg)

/-- Most connections a session holds; a session refuses and closes one more. The daemon
stops accepting at the same count. -/
@[expose]
def maxClients : Nat := 16

/-- Most labels a session holds: setting one more is refused, and booting keeps only the
first this many restored labels. -/
@[expose]
def maxLabels : Nat := 64

/-- One connection's record: its identity, terminal size, attach and request state, and
its undecoded input. -/
structure Client where
  /-- The connection's identifier, as in `Event.connected`. -/
  id : Nat
  /-- Terminal width from the latest attach or resize message. -/
  cols : UInt32 := 80
  /-- Terminal height from the latest attach or resize message. -/
  rows : UInt32 := 24
  /-- The connection attached and receives the session's output. -/
  attached : Bool := false
  /-- attached with a real size (read-only observers attach 0×0 and
  never influence the pty size). -/
  sizer : Bool := false
  /-- attach order; the highest attached sizer owns the size. -/
  seq : Nat := 0
  /-- `linger wait` parked here until the child exits. -/
  waiting : Bool := false
  /-- An `info`, `history`, `screen` or control `resize` from the current read
  was answered. One request per read: clients wait for the reply before the
  next request, and later requests decoded from the same read are refused. -/
  answered : Bool := false
  /-- Partial frames from this connection. No session state holds an errored decoder: the
  session closes the connection instead. -/
  decoder : Wire.Decoder := {}
  deriving Repr, Inhabited

/-- What the runtime feeds in. All byte payloads are `List UInt8`; the
runtime converts at the fd boundary. -/
inductive Event where
  /-- A connection was accepted. -/
  | connected (id : Nat)
  /-- A connection sent bytes. -/
  | bytes (id : Nat) (chunk : List UInt8)
  /-- A connection ended, or the runtime retired it. -/
  | closed (id : Nat)
  /-- The child wrote output to the pty. -/
  | ptyOut (chunk : List UInt8)
  /-- The pty reached end of file. `status` is the child's exit code, 128 plus the number of
  the signal that killed it, or 1 when the runtime could not reap it. -/
  | childExited (status : UInt32)
  /-- A poll round ended; `nowMs` is the monotonic clock in milliseconds. -/
  | tick (nowMs : Nat)
  /-- The last `.checkpoint` effect failed to save. -/
  | checkpointFailed
  deriving Repr

/-- What the runtime executes, given the type of a captured repaint. -/
inductive Effect (Plan : Type) where
  /-- Send one message to a connection. -/
  | send (id : Nat) (m : Msg)
  /-- Stream a captured repaint to a connection ahead of its later output. -/
  | replay (id : Nat) (plan : Plan)
  /-- Close a connection. -/
  | close (id : Nat)
  /-- Write bytes to the child through the pty. -/
  | writePty (bytes : List UInt8)
  /-- Set the pty's window size. -/
  | resizePty (cols rows : UInt32)
  /-- Ask the child to terminate (SIGTERM). -/
  | killChild
  /-- Save a checkpoint of the session. -/
  | checkpoint
  /-- Delete the session's checkpoint. -/
  | dropCheckpoint
  /-- Stop the daemon; no later event is handled. -/
  | exit
  deriving Repr, DecidableEq

/-- The session after a trace of events, given its transition: each event starts from the state
the previous one left, and the effects come out in the order the events asked for them. -/
@[expose]
def trace {S E F : Type} (step : S → E → S × List F) (s : S) : List E → S × List F
  | [] => (s, [])
  | ev :: evs =>
    let r := step s ev
    let rest := trace step r.1 evs
    (rest.1, r.2 ++ rest.2)

/-- The session bounds, read through a state's client roster, labels and pty scanner: the
roster and the label store within their caps, every client's frame decoder healthy and
holding at most one frame, and the scanner within its caps. -/
structure Bounds {S : Type} (roster : S → List Client) (labels : S → List (String × String))
    (scanner : S → Terminal.Mediation.Scan) (s : S) : Prop where
  /-- At most `maxClients` clients. -/
  clientsLe : (roster s).length ≤ maxClients
  /-- At most `maxLabels` labels. -/
  labelsLe : (labels s).length ≤ maxLabels
  /-- Every client's decoder is healthy and holds at most one frame. -/
  decOk : ∀ c ∈ roster s, c.decoder.errored = false ∧ c.decoder.buf.length ≤ 4 + Wire.maxPayload
  /-- The pty scanner is within its caps. -/
  scanOk : (scanner s).Bounded

end Linger.Session

namespace Linger.Session.Driver

/-- A transport operation reports whether its target disconnected; a checkpoint
reports whether saving failed. Other effects cannot enqueue feedback. -/
abbrev Reply {Plan : Type} : Effect Plan → Type
  | .send .. | .replay .. | .close .. | .checkpoint => Bool
  | _ => Unit

/-- The reply of an effect that succeeded: its target stayed connected, or the checkpoint was
saved. -/
@[expose]
def success {Plan : Type} : (eff : Effect Plan) → Reply eff
  | .send .. | .replay .. | .close .. | .checkpoint => false
  | .writePty .. | .resizePty .. | .killChild | .dropCheckpoint | .exit => ()

/-- The driver's state between events. -/
structure Result (S World : Type) where
  /-- The session state. -/
  st : S
  /-- The interpreter's world. -/
  world : World
  /-- An event's effects requested exit, so no later event is consumed. -/
  exiting : Bool := false

/-- The external contract excludes unreported exceptions; it permits every
disconnect/checkpoint-failure result. This is a premise about primitive
execution, not an assumption that the event driver succeeds. A primitive that raises
instead of returning a result falsifies it. -/
WorldClaim Responds {S World Plan ε : Type}
  (execute : S → World → (eff : Effect Plan) → Except ε (World × Reply eff)) :=
  ∀ st world eff, ∃ answer, execute st world eff = .ok answer

end Linger.Session.Driver

namespace Linger.Session.Checkpoint

/-- What a checkpoint holds, given the terminal type: the terminal, the working directory and
the labels. It derives no `Inhabited`: a default terminal is a choice, not a state the
emulator reaches. -/
structure Ckpt (V : Type) where
  /-- The terminal state; its parser state is not saved. -/
  vt : V
  /-- The directory the restored session's child starts in. -/
  cwd : String
  /-- The session's labels, as key/value pairs. -/
  labels : List (String × String)

/-- `v` is the terminal of a checkpoint `load` returns for some bytes: a terminal a resumed
session can start from. -/
@[expose]
def Decoded {V : Type} (load : ByteArray → Option (Ckpt V)) (v : V) : Prop :=
  ∃ bytes c, load bytes = some c ∧ c.vt = v

end Linger.Session.Checkpoint

/-! ## Reachable queue states

A queue starts empty and moves only through the given operations, so each predicate covers
every queue a plain importer can hold when the queue type is sealed. -/

namespace Linger.Session.Buf

/-- The pty-input queue's reachable states: it starts `empty` and moves only through capped
`offer`s and flush `advance`s. -/
inductive InputReach {B : Type} (empty : B) (offer : Nat → B → ByteArray → B × Bool)
    (advance : B → Nat → B) (cap : Nat) : B → Prop where
  /-- The queue every session starts with. -/
  | empty : InputReach empty offer advance cap empty
  /-- A capped offer, whether it queued the frame or dropped it. -/
  |
  offer (b : B) (more : ByteArray) :
    InputReach empty offer advance cap b → InputReach empty offer advance cap (offer cap b more).1
  /-- A flush that removes the bytes written. -/
  |
  advance (b : B) (n : Nat) :
    InputReach empty offer advance cap b → InputReach empty offer advance cap (advance b n)

/-- The client-output queue's **retained** states: it starts `empty`, and an `enqueue` that
reports "cut" gets the client dropped from the roster — so a queue the daemon keeps holds only
enqueues that reported `false`, plus flush advances. The not-cut hypothesis on the constructor
IS the append-then-cut discipline. -/
inductive OutputReach {B : Type} (empty : B) (enqueue : Nat → B → ByteArray → B × Bool)
    (advance : B → Nat → B) (cap : Nat) : B → Prop where
  /-- The queue every connection starts with. -/
  | empty : OutputReach empty enqueue advance cap empty
  /-- An append that left the client connected. -/
  |
  enqueue (b : B) (more : ByteArray) :
    OutputReach empty enqueue advance cap b →
      (enqueue cap b more).2 = false → OutputReach empty enqueue advance cap (enqueue cap b more).1
  /-- A flush that removes the bytes written. -/
  |
  advance (b : B) (n : Nat) :
    OutputReach empty enqueue advance cap b → OutputReach empty enqueue advance cap (advance b n)

end Linger.Session.Buf

/-! ## Claiming a session's resources

A resource identifies a stable lock inode, not a pathname string. Successful exclusive
acquisition requires that resource to be free. Failed acquisition leaves the state unchanged,
so a starting daemon that retries a held lock for a short time takes only `unchanged` steps
until it acquires. A daemon or offline reader enters only after holding both resources, and
releases them only after leaving and completing its cleanup.

The model permits acquisition, release and later reuse by different processes. Its
assumptions require cooperating processes, lock files that are never unlinked or replaced, and
a filesystem that implements the locking contract. The runtime correspondence is tested and
source-gated, not proved. -/

namespace Linger.Session.Claim

/-- The socket and checkpoint resources a daemon or offline reader claims together. -/
structure Lease where
  /-- The socket's lock inode. -/
  socket : Nat
  /-- The checkpoint's lock inode. -/
  checkpoint : Nat
  deriving DecidableEq

/-- `resource` is the lease's socket or checkpoint resource. -/
@[expose]
def Lease.Uses (lease : Lease) (resource : Nat) : Prop :=
  resource = lease.socket ∨ resource = lease.checkpoint

/-- `locks` maps each resource to the actor holding its lock; `active` maps each actor to
the lease it has entered. -/
structure State where
  /-- The actor holding each resource's lock. -/
  locks : Nat → Option Nat
  /-- The lease each actor has entered. -/
  active : Nat → Option Lease

/-- No lock is held and no actor has entered. -/
@[expose]
def initial : State := ⟨fun _ => none, fun _ => none⟩

/-- `map` updated at `key` to `value`. -/
@[expose]
def put {α : Type} (map : Nat → α) (key : Nat) (value : α) : Nat → α := fun index =>
  if index = key then value else map index

/-- The OS acquisition contract and the application's lifetime protocol.
`enter` covers both daemon ownership and an offline reader's critical section.
`leave` means all resource access and cleanup have finished. -/
inductive Step : State → State → Prop where
  /-- An actor takes a free resource's lock. -/
  |
  acquire (s : State) (actor resource : Nat) (free : s.locks resource = none) :
    Step s { s with locks := put s.locks resource (some actor) }
  /-- An idle actor holding both of a lease's locks enters it. -/
  |
  enter (s : State) (actor : Nat) (lease : Lease) (idle : s.active actor = none)
    (socket : s.locks lease.socket = some actor)
    (checkpoint : s.locks lease.checkpoint = some actor) :
    Step s { s with active := put s.active actor (some lease) }
  /-- An actor leaves its lease after finishing all access and cleanup. -/
  | leave (s : State) (actor : Nat) : Step s { s with active := put s.active actor none }
  /-- An idle actor releases a lock it holds. -/
  |
  release (s : State) (actor resource : Nat) (owned : s.locks resource = some actor)
    (idle : s.active actor = none) : Step s { s with locks := put s.locks resource none }
  /-- A failed acquisition, or any step that changes nothing. -/
  | unchanged (s : State) : Step s s

/-- The states reached from `initial` by finitely many `Step`s. -/
inductive Reachable : State → Prop where
  /-- The start: nothing held, nobody active. -/
  | initial : Reachable initial
  /-- One more step from a reachable state. -/
  | next {before after} (reached : Reachable before) (step : Step before after) : Reachable after

end Linger.Session.Claim
