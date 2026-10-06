module

public import Linger.Core.Buf
import all Linger.Core.Buf

/-! # §Bound, the runtime half — the daemon's byte queues, proved

This file is the tree's first **friend module**: `import all Linger.Core.Buf`
is what lets these statements and proofs see a representation that is sealed to
every plain importer (`Buf.bytes` is `private`; the runtime cannot read, write,
or forge it — specs/archive/lean-modules.md Step 2). There is deliberately no blanket
`public section` here: these theorems are leaves — nothing imports them as
lemmas (checked; they appear elsewhere only in prose) — and being CHECKED at
build is their whole job, so module-private is their honest visibility. It also
lets the `rfl` proofs elaborate where the sealed definitions still reduce;
`Theorems/Coverage.lean` imports this friend scope and checks the resulting theorem
types semantically.

`Session.run_wf` bounds the *machine*: no event trace grows a client roster, a
label store or the screen. One layer below, the daemon's two byte queues were
bounded only by code review — `THEOREMS.md`'s §Bound bullet said so in as many
words. These are that bullet, turned into theorems about `Linger.Core.Buf`.

**What is proved here is the arithmetic, not the daemon.** `Linger/Runtime/*` is
`IO`; no theorem can see that it calls these functions rather than open-coding the
same sums. Two things carry that gap: `Buf.bytes` is `private`, so the runtime
cannot *read* the representation — nor, since the module system sealed the
constructor, **write or forge** one — and every buffer arithmetic needs to read; and
`scripts/gates.sh` greps that `Linger/Runtime/*` declares no byte buffer of its own — a
source-tree property, and therefore a grep. Anyone who reads this file as "the
runtime is proved" is overclaiming.

**Why each bound has a content twin.** A cap theorem alone is satisfied by a queue
that throws its contents away. So each bound is paired with a claim stated through
`owed` — `owedLen_eq` first of all, without which every `≤ cap` here would be a
fact about an unrelated `Nat`. The pairing is the point; a bound without its twin
is decoration.

**Why several proofs are one word.** They are short because the representation was
chosen to make them short: the queue holds exactly what it owes, so "advancing
drops the first `n` bytes in order" and "the writer is handed the debt" are the same
statement twice. The write-cursor shape needed an `off ≤ bytes.size` invariant that
no type enforced and every content proof had to assume — the doctrine in
`AGENTS.md` ("restructure code for provability rather than weakening a theorem")
says to move the definition, so the definition moved. `bufNoRetain` is where that
shows up as a claim.
-/

namespace Linger.Core.Buf

/-! ## The bridge -/

/-- **The bridge.** The number the caps compare is the length of what is actually
owed. Nothing else in this file means anything without it. -/
theorem owedLen_eq (b : Buf) : (owed b).size = owedLen b := rfl

/-- The one public door in starts with zero debt — `empty`'s anchor, and what
claims it in the census: an importer can begin a queue, never forge one
mid-debt (the constructor is private with the field). -/
theorem owed_empty : owed Buf.empty = ByteArray.empty := rfl

theorem owedLen_empty : owedLen Buf.empty = 0 := rfl

/-- **Nothing written is retained.** Memory footprint *is* the debt — an equation,
not a bound, because an inequality would also hold of a queue that kept its whole
history. This is the property the write-cursor shape could only promise and the
partial-drain regression violated; here it is structural, so re-introducing the
regression means changing the type. -/
theorem bufNoRetain (b : Buf) : bufSize b = owedLen b := rfl

/-! ## Advancing over written bytes -/

/-- Advancing over `n` written bytes reduces the debt by exactly `n`, clamped — so
a short write leaves the rest owed and an over-long one owes nothing. -/
theorem bufAdvance_wf (b : Buf) (n : Nat) : owedLen (bufAdvance b n) = owedLen b - n := by
  show (b.bytes.extract n b.bytes.size).size = b.bytes.size - n
  rw [ByteArray.size_extract, Nat.min_self]

/-- **The no-loss twin.** Advancing drops exactly the first `n` owed bytes and
keeps the rest in order — so the debt cannot be discharged by dropping the *middle*
of a paste, which a length bound alone would permit. -/
theorem bufAdvance_owed (b : Buf) (n : Nat) :
    owed (bufAdvance b n) = (owed b).extract n (owed b).size := rfl

/-! ## The two caps

The disciplines genuinely differ, so they are two functions: `bufOffer` measures
before appending, so its bound is unconditional and no partial frame is queued;
`bufEnqueue` appends and then reports, which is the shipped `.send` behaviour, so
its bound is guarded by "the peer was not cut". -/

/-- **The child-input cap, unconditional.** A queue within the cap stays within the
cap: an offer that would breach it is refused whole. -/
theorem bufOffer_bound (cap : Nat) (b : Buf) (more : ByteArray) (h : owedLen b ≤ cap) :
    owedLen (bufOffer cap b more).1 ≤ cap := by
  unfold bufOffer
  by_cases hc : owedLen b + more.size > cap
  · rw [ite_eq_left hc]; exact h
  · rw [ite_eq_right hc]
    show (b.bytes ++ more).size ≤ cap
    rw [ByteArray.size_append]
    show b.bytes.size + more.size ≤ cap
    have ho : owedLen b = b.bytes.size := rfl
    omega

/-- **The twin.** An accepted offer really is appended, in order — so the cap is
not met by silently discarding what it claimed to accept. -/
theorem bufOffer_owed (cap : Nat) (b : Buf) (more : ByteArray)
    (h : (bufOffer cap b more).2 = false) : owed (bufOffer cap b more).1 = owed b ++ more := by
  unfold bufOffer at h ⊢
  by_cases hc : owedLen b + more.size > cap
  · rw [ite_eq_left hc] at h; exact absurd h (by simp)
  · rw [ite_eq_right hc]; rfl

/-- Refusing a whole input frame leaves all previously queued input unchanged.
The bound alone would also allow discarding or rearranging that input. -/
theorem bufOffer_rejected (cap : Nat) (b : Buf) (more : ByteArray)
    (h : (bufOffer cap b more).2 = true) : (bufOffer cap b more).1 = b := by
  unfold bufOffer at h ⊢
  split at h <;> simp_all

/-- **The client-output cap, guarded.** If the peer was not cut, its backlog is
within the cap. The guard is not a weakening: `.send` appends and *then* decides,
so at the moment of the decision the frame that crossed the cap is queued, and the
honest unconditional bound is `cap` plus one wire frame. Changing that would change
when a slow client is disconnected — a behaviour change, not a proof convenience. -/
theorem bufEnqueue_bound (cap : Nat) (b : Buf) (more : ByteArray)
    (h : (bufEnqueue cap b more).2 = false) : owedLen (bufEnqueue cap b more).1 ≤ cap := by
  unfold bufEnqueue at h ⊢
  simp only [decide_eq_false_iff_not, Nat.not_lt] at h
  exact h

/-- **The twin.** Enqueue really appends, cut or not — the client's frames are not
dropped on the way to the decision to disconnect it. -/
theorem bufEnqueue_owed (cap : Nat) (b : Buf) (more : ByteArray) :
    owed (bufEnqueue cap b more).1 = owed b ++ more := rfl

/-- What the writer hands to `write(2)` is exactly what is owed. This is the only
sanctioned read of the representation, so it is the one place a mismatch between
"what we think is queued" and "what goes out" could hide. -/
theorem writeFrom_owed (b : Buf) : writeFrom b = owed b := rfl

/-- Both queues share the cap even when the front exceeds one frame. -/
theorem followingCap_front {cap frame front : Nat} (h : front ≤ cap) :
    front + followingCap cap frame front ≤ cap := by
  unfold followingCap
  omega

/-- Reserving a complete frame prevents following output from starving it. -/
theorem followingCap_frame {cap frame front : Nat} (h : frame ≤ cap) :
    frame + followingCap cap frame front ≤ cap := by
  unfold followingCap
  omega

/-- The allowance is exactly the largest debt satisfying both reservations. -/
theorem followingCap_iff {cap frame front debt : Nat} (hf : frame ≤ cap) (hp : front ≤ cap) :
    debt ≤ followingCap cap frame front ↔ frame + debt ≤ cap ∧ front + debt ≤ cap := by
  unfold followingCap
  omega

/-! ## §Bound over the queue's whole life

The per-step bounds above compose into lifetime invariants of the reachability
predicates (`Linger/Core/Buf.lean`), and the composition is only meaningful
because the representation is sealed: every `Buf` a plain importer can possess
is `empty` moved forward by the API, so "reachable" is not a subset of the
runtime's states — it IS them. Pre-seal these theorems would have been true of
a predicate that described nothing (the forge escape); that is why they were
not written until specs/archive/lean-modules.md Step 2 landed. -/

/-- **The pty-input queue is bounded for the daemon's whole life**: any
interleaving of capped offers and flush advances, from boot, stays within the
cap. The step facts carry it — `bufOffer_bound` (refuse-before-append) and
`bufAdvance_wf` (advancing only shrinks). -/
theorem reachableIn_bound {cap : Nat} {b : Buf} (h : ReachableIn cap b) : owedLen b ≤ cap := by
  induction h with
  | empty =>
    rw [owedLen_empty]; exact Nat.zero_le cap
  | offer b more _ ih => exact bufOffer_bound cap b more ih
  | advance b n _ ih =>
    rw [bufAdvance_wf]; omega

/-- **Every client backlog the daemon retains is bounded for its whole life.**
The enqueue constructor's not-cut hypothesis is what carries it — exactly the
guard `bufEnqueue_bound` is stated under, because `.send` appends before it
decides and a cut client leaves the roster with its queue. -/
theorem reachableOut_bound {cap : Nat} {b : Buf} (h : ReachableOut cap b) : owedLen b ≤ cap := by
  induction h with
  | empty =>
    rw [owedLen_empty]; exact Nat.zero_le cap
  | enqueue b more _ hcut _ => exact bufEnqueue_bound cap b more hcut
  | advance b n _ ih =>
    rw [bufAdvance_wf]; omega

end Linger.Core.Buf
