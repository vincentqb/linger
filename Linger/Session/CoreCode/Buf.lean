module

public import Linger.Session.CoreSpec

public section

/-! # Linger.Session.Buf — a bounded byte queue, as a value

The daemon's socket output buffers and pty input backlog share this value type.
It carries the cap, the policy when it is reached, and the discipline that keeps
the stored byte sequence equal to the unwritten debt. The queues' bounds are
`reachableIn_bound` and `reachableOut_bound` (`Challenge.lean`, part 6).

This module is the value; `Linger/Session/Proofs/Buf.lean` is the proof; the daemon is the
interpreter. That is the same split `Session.step` already uses one layer up (the
machine decides, the runtime performs syscalls) — extended inward.

**There is no write cursor, and that is the design.** The obvious shape is
`bytes` plus an `off` the writer advances. It has
a latent leak: reclaim the written prefix only when the queue *empties*, and a
peer that drains a little each round grows `bytes` without limit while the debt
stays small, so a cap on the debt never trips. Compacting on every flush closes it,
and then `off` is always `0` between rounds, so the
field would only ever hold a value *inside* the write loop. Carrying it in the
persistent state would buy nothing and cost an invariant (`off ≤ bytes.size`) that no
type enforces and every content proof needs. So the queue stores exactly the bytes
still owed; the write loop keeps its cursor as a local `Nat` and calls `bufAdvance`
once when it stops. That is one copy per flush, and the leak is
**unrepresentable** rather than merely absent.

**The field is `private`.** `Linger/Session/Proofs/Buf.lean` is a `module` with
`import all Linger.Session.Buf`, the friend import, and a private field makes the
*constructor* private, so structure-instance notation cannot write or forge where it
cannot read (all three refuse from the runtime, break-verified). The
runtime's discipline is compiler-enforced at this boundary; `scripts/gates.sh`'s
three greps guard the half privacy cannot see — a
*parallel* `ByteArray` queue declared in the runtime is sealed by nothing here.

**`ByteArray`, not `List UInt8`.** The other pure modules speak `List UInt8`
because the emitters must reduce in the kernel; a queue must not. A 4 MiB
`List UInt8` costs ~48 bytes per byte and `++` is O(left), so every `.send` would
become a multi-megabyte cons walk. `ByteArray` in a pure module is house-legal — the
purity gate bans unproved axioms, `partial` definitions and effects, not a choice
of representation — and is not the only one: `Vt.feedBytes` takes one too
(a `Tests/`-facing convenience, which is all the precedent needs
— it establishes that the gate admits the type, not that the daemon calls it).
Nothing here is stated through
`ByteArray.toList`, which is a `get!` + `reverse` loop.
-/

namespace Linger.Session.Buf

/-- A byte queue's representation: exactly the bytes still owed to the peer, oldest first.
It is sealed: `writeFrom` is the one window out, `empty` the one door in, and
`Linger/Session/Proofs/Buf.lean` sees inside via `import all`. -/
structure BufRec where
  private bytes : ByteArray := .empty
  deriving Inhabited

/-- A byte queue, as the headline theorems name it: a definition over the sealed record
`BufRec`, because `Challenge.lean` declares the type as a hole the program fills. -/
abbrev Buf : Type := BufRec

/-- The empty queue, the public door into one: a private field
makes the anonymous constructor private, which is the point — an importer can
start a queue but not forge one mid-debt. -/
def Buf.empty : Buf := {}

/-- What the caps compare. `owedLen_eq` is the bridge that makes this the length of
`writeFrom`. -/
def owedLen (b : Buf) : Nat := b.bytes.size

/-- Retained logical byte length. It coincides with the debt by construction
(`bufSize_eq_owedLen`); allocator capacity and object overhead are not measured. -/
private def bufSize (b : Buf) : Nat := b.bytes.size

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

/-- The pty-input queue's reachable states: `InputReach` (`Linger/Session/CoreSpec.lean`) over this
queue's own operations. With `bytes` sealed it covers every queue an importer can hold, so its
bound (`reachableIn_bound`) is a whole-lifetime fact about the daemon's queue. -/
abbrev ReachableIn (cap : Nat) : Buf → Prop := InputReach Buf.empty bufOffer bufAdvance cap

/-- The client-output queue's retained states: `OutputReach` over this queue's own operations,
bounded by `reachableOut_bound`. -/
abbrev ReachableOut (cap : Nat) : Buf → Prop := OutputReach Buf.empty bufEnqueue bufAdvance cap

end Linger.Session.Buf
