import Linger.Core.Buf
/-! # Buf fixtures — the caps and the no-retention property, evaluated

`Theorems/Buf.lean` proves these for all inputs; these evaluate them on concrete
bytes, which is the oracle that would have caught the partial-drain regression the
`Buf` shape now makes unrepresentable. Before this module the only live oracle for
that regression was the daemon's resident-set size under a 16 MiB flood, which
`SCRATCHPAD.md` (2026-08-18) recorded as measured-and-rejected: it is dominated by
transient decode garbage. These reduce, so they cannot be noisy.
`native_decide` is allowed here (it is banned only in `Theorems/`).
-/

namespace Linger.Core.Buf.Tests

open Linger.Core.Buf

def bytes (n : Nat) : ByteArray := ByteArray.mk (Array.replicate n 0x61)

/-- A fresh queue owes nothing. -/
example : owedLen ({} : Buf) = 0 := by native_decide

/-- Memory is the debt, with bytes in flight — the no-retention property. -/
example : bufSize ((bufEnqueue 100 {} (bytes 40)).1) = 40 := by native_decide

/-- Advancing over a partial write keeps memory equal to what is still owed.
**This is the regression oracle**: with a retained prefix, `bufSize` here would be
40 while `owedLen` said 15. -/
example : bufSize (bufAdvance (bufEnqueue 100 {} (bytes 40)).1 25) = 15 := by native_decide
example : owedLen (bufAdvance (bufEnqueue 100 {} (bytes 40)).1 25) = 15 := by native_decide

/-- Repeated partial drains do not accumulate: four rounds of "queue 40, write 25"
leaves the debt bounded, not growing by 15 a round in memory terms. -/
example :
    let step := fun (b : Buf) => bufAdvance (bufEnqueue 1000 b (bytes 40)).1 25
    bufSize (step (step (step (step {})))) = 60 := by native_decide

/-- Advancing past the end owes nothing and keeps nothing. -/
example : bufSize (bufAdvance (bufEnqueue 100 {} (bytes 40)).1 999) = 0 := by native_decide

/-- The child-input discipline: an offer that would breach the cap is refused
**whole**, so the queue is unchanged and the caller is told. -/
example : (bufOffer 50 (bufEnqueue 100 {} (bytes 40)).1 (bytes 20)).2 = true := by native_decide
example : owedLen (bufOffer 50 (bufEnqueue 100 {} (bytes 40)).1 (bytes 20)).1 = 40 := by
  native_decide

/-- An accepted offer is appended in full. -/
example : owedLen (bufOffer 50 (bufEnqueue 100 {} (bytes 40)).1 (bytes 10)).1 = 50 := by
  native_decide
example : (bufOffer 50 (bufEnqueue 100 {} (bytes 40)).1 (bytes 10)).2 = false := by native_decide

/-- The client-output discipline: `.send` appends and *then* reports, so the frame
that crossed the cap is queued at the moment of the decision. That asymmetry with
`bufOffer` is deliberate and is why `bufEnqueue_bound` is hypothesis-guarded. -/
example : (bufEnqueue 30 {} (bytes 40)).2 = true := by native_decide
example : owedLen (bufEnqueue 30 {} (bytes 40)).1 = 40 := by native_decide

end Linger.Core.Buf.Tests
