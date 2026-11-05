module

public import Linger.Session
public import Linger.Session.Buf
public import Linger.Session.Driver
public import Linger.Terminal.Vt

public section

/-! # What session headlines are stated in

The session bounds and the live terminal every daemon state keeps, the contract on the effect
interpreter, the states the daemon's byte queues can reach, and a model of how daemons and
offline readers claim a session's resources. Bodies are exposed: each definition here is its
own specification. -/

/-! ## Daemon states and the effect interpreter -/

namespace Linger.Session

/-- The session bounds: the client roster and the label store within their caps, every
client's frame decoder healthy and holding at most one frame, and the pty scanner within its
caps. -/
structure Bounded (s : State) : Prop where
  /-- At most `maxClients` clients. -/
  clientsLe : s.clients.length ≤ maxClients
  /-- At most `maxLabels` labels. -/
  labelsLe : s.labels.length ≤ maxLabels
  /-- Every client's decoder is healthy and holds at most one frame. -/
  decOk : ∀ c ∈ s.clients, c.decoder.errored = false ∧ c.decoder.buf.length ≤ 4 + Wire.maxPayload
  /-- The pty scanner is within its caps. -/
  scanOk : s.scan.Bounded

/-- The daemon's terminal is one a live session can hold. -/
@[expose]
def LiveVt (s : State) : Prop := Terminal.Vt.LiveReachableVt s.vt

end Linger.Session

namespace Linger.Session.Driver

/-- The external contract excludes unreported exceptions; it permits every
disconnect/checkpoint-failure result. This is a premise about primitive
execution, not an assumption that the event driver succeeds. -/
@[expose]
def Responds {World ε : Type}
    (execute : State → World → (eff : Effect) → Except ε (World × Reply eff)) : Prop :=
  ∀ st world eff, ∃ answer, execute st world eff = .ok answer

end Linger.Session.Driver

/-! ## Reachable queue states

`Buf.empty` is the only way to make a `Buf` and the operations below the only ways forward, so
each predicate covers every queue a plain importer can hold. -/

namespace Linger.Session.Buf

/-- The pty-input queue's reachable states: `Rt.ptyIn` starts `empty` and moves
only through capped `bufOffer`s (`queuePty`) and flush `bufAdvance`s. -/
inductive ReachableIn (cap : Nat) : Buf → Prop where
  /-- The queue every session starts with. -/
  | empty : ReachableIn cap .empty
  /-- A capped offer, whether it queued the frame or dropped it. -/
  | offer (b : Buf) (more : ByteArray) : ReachableIn cap b → ReachableIn cap (bufOffer cap b more).1
  /-- A flush that removes the bytes written. -/
  | advance (b : Buf) (n : Nat) : ReachableIn cap b → ReachableIn cap (bufAdvance b n)

/-- The client-output queue's **retained** states: `Conn.out` starts `empty`,
and a `bufEnqueue` that reports "cut" gets the client dropped from the roster —
so a queue the daemon keeps holds only enqueues that reported `false`, plus
flush advances. The not-cut hypothesis on the constructor IS the shipped
append-then-cut discipline; drop it and `reachableOut_bound` is refutable. -/
inductive ReachableOut (cap : Nat) : Buf → Prop where
  /-- The queue every connection starts with. -/
  | empty : ReachableOut cap .empty
  /-- An append that left the client connected. -/
  |
  enqueue (b : Buf) (more : ByteArray) :
    ReachableOut cap b →
      (bufEnqueue cap b more).2 = false → ReachableOut cap (bufEnqueue cap b more).1
  /-- A flush that removes the bytes written. -/
  | advance (b : Buf) (n : Nat) : ReachableOut cap b → ReachableOut cap (bufAdvance b n)

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
