/-! # Zmx.Core.Buf — a bounded byte queue, as a value

The daemon owns two long-lived byte queues: the per-client output backlog and the
pty input backlog. Both are the same shape, and both carry *decisions*, not
plumbing: a cap, what to do when it is reached, and the discipline that keeps the
cap measuring **memory** rather than a counter. Those decisions lived in
`Zmx/Runtime/Daemon.lean`, where nothing could prove them; the runtime half of
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

**Why the field is not `private`, though it should be.** Marking it `private`
does block a cross-module read (Lean 4.32: "Field `bytes` ... is private"), and
reading is what every piece of buffer arithmetic needs — so it would make the
runtime's discipline compiler-enforced rather than grepped. It is not adoptable
yet, for a measured reason: `private` also hides the field from `Theorems/`, so the
proofs would have to live in this file, and `tests/coverage.py` scans `Theorems/**`
only for theorem statements — every def here would become unclaimed surface and
breach a ratchet that must stay monotone. (It is also only half a discipline:
structure-instance notation can still *write* a private field where it cannot read
one.) So the gate is `tests/e2e.sh`'s three greps, and this becomes attractive the
day `coverage.py` also counts theorems in `Zmx/Core`.

**`ByteArray`, not `List UInt8`.** The rest of `Zmx/Core` speaks `List UInt8`
because the emitters must reduce in the kernel; a queue must not. A 4 MiB
`List UInt8` costs ~48 bytes per byte and `++` is O(left), so every `.send` would
become a multi-megabyte cons walk. `ByteArray` in `Zmx/Core` is house-legal (the
purity gate bans `sorry`, `sorryAx`, `partial def` and `IO`, not a representation)
and has precedent in `Vt.feedBytes`. Nothing here is stated through
`ByteArray.toList`, which is a `get!` + `reverse` loop.
-/

namespace Zmx.Core.Buf

/-- A byte queue: exactly the bytes still owed to the peer, oldest first. -/
structure Buf where
  bytes : ByteArray := .empty
  deriving Inhabited

/-- The bytes still owed to the peer. Every claim in `Theorems/Buf.lean` is stated
about this rather than about a counter, which is what stops a bound from being a
fact about an unrelated `Nat`. -/
def owed (b : Buf) : ByteArray := b.bytes

/-- What the caps compare. `owedLen_eq` is the bridge that makes this the length of
`owed`. -/
def owedLen (b : Buf) : Nat := b.bytes.size

/-- The queue's **memory** footprint. It coincides with the debt by construction —
that equation is `bufNoRetain`, and it is the property the write-cursor shape
could only promise. -/
def bufSize (b : Buf) : Nat := b.bytes.size

/-- Offer bytes, dropping the whole frame if it would breach the cap — the
**child-input** discipline (`.writePty`). Measures *before* appending, so the bound
is unconditional and no partial frame is ever queued: one `.input` frame is one
read of the user's keyboard, so refusing at that boundary splits no UTF-8 sequence
and no escape. Reports whether the frame was dropped.

Dropping the newest is what a tty does when its own input buffer fills
(`IMAXBEL`); there is nothing to disconnect, because the child *is* the session. -/
def bufOffer (cap : Nat) (b : Buf) (more : ByteArray) : Buf × Bool :=
  if owedLen b + more.size > cap then (b, true)
  else ({ bytes := b.bytes ++ more }, false)

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
def bufAdvance (b : Buf) (n : Nat) : Buf :=
  { bytes := b.bytes.extract n b.bytes.size }

/-- What the writer hands to `write(2)`: exactly the owed bytes, so the syscall
needs no offset. The **one** sanctioned read of the representation, used only by
`Zmx.Posix.writeBuf`; `writeFrom_owed` pins that it is the debt and nothing else. -/
def writeFrom (b : Buf) : ByteArray := b.bytes

end Zmx.Core.Buf
