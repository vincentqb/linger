import Zmx.Core.Buf
/-! # §Bound, the runtime half — the daemon's byte queues, proved

`Session.run_wf` bounds the *machine*: no event trace grows a client roster, a
label store or the screen. One layer below, the daemon's two byte queues were
bounded only by code review — `THEOREMS.md`'s §Bound bullet said so in as many
words. These are that bullet, turned into theorems about `Zmx.Core.Buf`.

**What is proved here is the arithmetic, not the daemon.** `Zmx/Runtime/*` is
`IO`; no theorem can see that it calls these functions rather than open-coding the
same sums. Two things carry that gap: `Buf.bytes` is `private`, so the runtime
cannot *read* the representation, and every buffer arithmetic needs to read; and
`tests/e2e.sh` greps that `Zmx/Runtime/*` declares no byte buffer of its own — a
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

namespace Zmx.Core.Buf

/-! ## The bridge -/

/-- **The bridge.** The number the caps compare is the length of what is actually
owed. Nothing else in this file means anything without it. -/
theorem owedLen_eq (b : Buf) : (owed b).size = owedLen b := rfl

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
  · rw [if_pos hc]; exact h
  · rw [if_neg hc]
    show (b.bytes ++ more).size ≤ cap
    rw [ByteArray.size_append]
    show b.bytes.size + more.size ≤ cap
    have ho : owedLen b = b.bytes.size := rfl
    omega

/-- **The twin.** An accepted offer really is appended, in order — so the cap is
not met by silently discarding what it claimed to accept. -/
theorem bufOffer_owed (cap : Nat) (b : Buf) (more : ByteArray)
    (h : (bufOffer cap b more).2 = false) :
    owed (bufOffer cap b more).1 = owed b ++ more := by
  unfold bufOffer at h ⊢
  by_cases hc : owedLen b + more.size > cap
  · rw [if_pos hc] at h; exact absurd h (by simp)
  · rw [if_neg hc]; rfl

/-- **The client-output cap, guarded.** If the peer was not cut, its backlog is
within the cap. The guard is not a weakening: `.send` appends and *then* decides,
so at the moment of the decision the frame that crossed the cap is queued, and the
honest unconditional bound is `cap` plus one wire frame. Changing that would change
when a slow client is disconnected — a behaviour change, not a proof convenience. -/
theorem bufEnqueue_bound (cap : Nat) (b : Buf) (more : ByteArray)
    (h : (bufEnqueue cap b more).2 = false) :
    owedLen (bufEnqueue cap b more).1 ≤ cap := by
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

end Zmx.Core.Buf
