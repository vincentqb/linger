module

public section

/-! # Linger.Core.Buf — a bounded byte queue, as a value

The daemon's socket output buffers and pty input backlog share this value type.
It carries the cap, the policy when it is reached, and the discipline that keeps
the stored byte sequence equal to the unwritten debt. Those decisions lived in
`Linger/Runtime/Daemon.lean`, where nothing could prove them; the runtime half of
§Bound was a paragraph in THEOREMS.md ending "not proved".

This module is the value; `Theorems/Buf.lean` is the proof; the daemon is the
interpreter. That is the same split `Session.step` already uses one layer up (the
machine decides, the runtime performs syscalls) — extended inward.

**There is no write cursor, and that is the design.** The obvious shape is
`bytes` plus an `off` the writer advances, which is what the daemon held. It has
a latent leak: reclaim the written prefix only when the queue *empties*, and a
peer that drains a little each round grows `bytes` without limit while the debt
stays small, so a cap on the debt never trips. That bug was real and was fixed by
compacting on every flush — after which `off` is always `0` between rounds, so the
field only ever held a value *inside* the write loop. Carrying it in the
persistent state bought nothing and cost an invariant (`off ≤ bytes.size`) that no
type enforced and every content proof needed. So the queue stores exactly the bytes
still owed; the write loop keeps its cursor as a local `Nat` and calls `bufAdvance`
once when it stops. Same single copy per flush as before, and the leak is now
**unrepresentable** rather than merely absent.

**The field is `private` (2026-08-19, the module system).** The 2026-08-18
measurement said "not adoptable yet" for two reasons, and the module system
retired both: proofs no longer have to move here — `Theorems/Buf.lean` is a
`module` with `import all Linger.Core.Buf`, the friend import, so the semantic
census in `Theorems/Coverage.lean` sees its private theorem types — and
the write hole is closed, because a private field makes the *constructor*
private, so structure-instance notation can no longer write or forge where it
cannot read (all three refuse from `Linger/Runtime/`, break-verified). The
runtime's discipline is now compiler-enforced at this boundary; `scripts/gates.sh`'s
three greps stay unweakened, because they guard the half privacy cannot see — a
*parallel* `ByteArray` queue declared in the runtime is sealed by nothing here.

**`ByteArray`, not `List UInt8`.** The rest of `Linger/Core` speaks `List UInt8`
because the emitters must reduce in the kernel; a queue must not. A 4 MiB
`List UInt8` costs ~48 bytes per byte and `++` is O(left), so every `.send` would
become a multi-megabyte cons walk. `ByteArray` in `Linger/Core` is house-legal — the
purity gate bans unproved axioms, `partial` definitions and effects, not a choice
of representation — and is not even the first: `Vt.feedBytes` has taken one since
long before this (a `Tests/`-facing convenience, which is all the precedent needs
— it establishes that the gate admits the type, not that the daemon calls it).
Nothing here is stated through
`ByteArray.toList`, which is a `get!` + `reverse` loop.
-/

namespace Linger.Core.Buf

/-- A byte queue: exactly the bytes still owed to the peer, oldest first.
The representation is sealed: `writeFrom` is the one window out, `empty` the
one door in, and `Theorems/Buf.lean` sees inside via `import all`. -/
structure Buf where
  private bytes : ByteArray := .empty
  deriving Inhabited

/-- The empty queue. The public door where `{}` used to be: a private field
makes the anonymous constructor private, which is the point — an importer can
start a queue but not forge one mid-debt. -/
def Buf.empty : Buf := {}

/-- What the caps compare. `owedLen_eq` is the bridge that makes this the length of
`writeFrom`. -/
def owedLen (b : Buf) : Nat := b.bytes.size

/-- Retained logical byte length. It coincides with the debt by construction
(`bufSize_eq_owedLen`); allocator capacity and object overhead are not measured. -/
def bufSize (b : Buf) : Nat := b.bytes.size

/-- Allowance for a following queue that shares a cap with the front queue.
Reserve at least one complete frame, so a full following queue cannot prevent
the front queue from accepting that frame. -/
def followingCap (cap frame front : Nat) : Nat := cap - max frame front

/-- Offer bytes, dropping the whole frame if it would breach the cap — the
**child-input** discipline (`.writePty`). Measures *before* appending, so the bound
is unconditional and no partial frame is ever queued: one `.input` frame is one
read of the user's keyboard, so refusing at that boundary splits no UTF-8 sequence
and no escape. Reports whether the frame was dropped.

Dropping the newest is what a tty does when its own input buffer fills
(`IMAXBEL`); there is nothing to disconnect, because the child *is* the session. -/
def bufOffer (cap : Nat) (b : Buf) (more : ByteArray) : Buf × Bool :=
  if owedLen b + more.size > cap then (b, true) else ({ bytes := b.bytes ++ more }, false)

/-- Append, then report whether the peer must be cut — the **client-output**
discipline (`.send`). Appends *first* and measures after, which is the shipped
behaviour: a client is disconnected once its backlog is past the cap, and the frame
that crossed it is still queued at the moment of the decision. That is why
`bufEnqueue_bound` is guarded by "the peer was not cut" rather than unconditional;
the honest unconditional bound would be `cap` plus one wire frame. Collapsing this
into `bufOffer` would force a theorem that is false of the client path as it ships. -/
def bufEnqueue (cap : Nat) (b : Buf) (more : ByteArray) : Buf × Bool :=
  let b := { bytes := b.bytes ++ more }
  (b, owedLen b > cap)

/-- Drop the `n` bytes the writer got out, clamped to what was owed. Called once
per flush with the loop's total, so the written prefix is never retained. -/
def bufAdvance (b : Buf) (n : Nat) : Buf := { bytes := b.bytes.extract n b.bytes.size }

/-- The byte view of the debt, for the write(2) loop and for decoding the info accumulator. -/
def writeFrom (b : Buf) : ByteArray := b.bytes

/-! ## Reachability — the seal's semantics, as a predicate

Before `bytes` was `private` (2026-08-19), a predicate like these would have
been **decoration by this repo's own standard** (the poll-plan kill in
`specs/archive/runtime-invariants.md`): any importer could forge
`{ bytes := … }` mid-debt, so "reachable from `empty`" described nothing about
the values the runtime could actually hold, and its canonical break — forge a
`Buf` — would not have been caught by anything. Sealed, `Buf.empty` is the one
door in and the operations below are the only ways forward, so each predicate
is **exhaustive over what a plain importer can possess**, and its invariant
(`Theorems/Buf.lean`: `reachableIn_bound` / `reachableOut_bound`) is a
whole-lifetime fact about the daemon's queue — the same lift `LiveReachableVt`
gives the emulator, one layer down. No content twins are needed at this level:
the trace claims are bounds composed of steps that already carry their twins
(`bufOffer_writeFrom`, `bufEnqueue_writeFrom`, `bufAdvance_writeFrom`). -/

/-- The pty-input queue's reachable states: `Rt.ptyIn` starts `empty` and moves
only through capped `bufOffer`s (`queuePty`) and flush `bufAdvance`s. -/
inductive ReachableIn (cap : Nat) : Buf → Prop where
  | empty : ReachableIn cap .empty
  | offer (b : Buf) (more : ByteArray) : ReachableIn cap b → ReachableIn cap (bufOffer cap b more).1
  | advance (b : Buf) (n : Nat) : ReachableIn cap b → ReachableIn cap (bufAdvance b n)

/-- The client-output queue's **retained** states: `Conn.out` starts `empty`,
and a `bufEnqueue` that reports "cut" gets the client dropped from the roster —
so a queue the daemon keeps holds only enqueues that reported `false`, plus
flush advances. The not-cut hypothesis on the constructor IS the shipped
append-then-cut discipline; drop it and `reachableOut_bound` is refutable
(break-verified). -/
inductive ReachableOut (cap : Nat) : Buf → Prop where
  | empty : ReachableOut cap .empty
  |
  enqueue (b : Buf) (more : ByteArray) :
    ReachableOut cap b →
      (bufEnqueue cap b more).2 = false → ReachableOut cap (bufEnqueue cap b more).1
  | advance (b : Buf) (n : Nat) : ReachableOut cap b → ReachableOut cap (bufAdvance b n)

end Linger.Core.Buf
