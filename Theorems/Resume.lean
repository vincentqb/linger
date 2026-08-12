import Theorems.Checkpoint
import Theorems.Render
/-! # §Resume — the end-to-end claim, as one theorem

Everything else in `Theorems/` is a rung. This file states the thing the
program is *for*, by composing them:

> Kill a session's daemon. Reboot the machine. Reattach. The bytes the
> new client's terminal receives are derived from a checkpoint that
> round-trips exactly, and they leave that terminal quiesced — parser in
> `ground`, no half-decoded character — so the session's own next output
> is interpreted correctly.

The two halves:

* **§Restore** (`Checkpoint.load_save`): what `save` writes, `load` reads
  back, modulo the parser state a checkpoint deliberately drops.
* **§Replay** (`Render.restore_quiesced`): the byte stream `restore`
  builds from that state leaves a fresh emulator quiesced.

`resume_quiesced` is their composition, `resume_cursor` adds the cursor —
the first *value* fidelity claim to reach the end-to-end statement — and
what remains carried by tests rather than proof is the replayed **cells**
equalling the saved cells (§Replay stage 3d). Keeping that gap named in
the same file as the claim is deliberate; a reader should not have to hunt
THEOREMS.md to learn what is not yet proved.
-/

namespace Zmx.Core

open Zmx.Core.Checkpoint (Ckpt load save)

/-- **§Resume.** A checkpoint, reloaded and replayed into a fresh
emulator of the same size, leaves that emulator quiesced: the parser is
in `ground` with no pending UTF-8 sequence. Holds for any session state
whatsoever, with no hypotheses — the reattaching client is always left
ready for the application's next byte. -/
theorem resume_quiesced (c : Ckpt) (cols rows : Nat) :
    ∃ c', load (save c) = some c'
      ∧ ((Vt.Vt.init cols rows).feed (Render.restore c'.vt)).pstate = .ground
      ∧ ((Vt.Vt.init cols rows).feed (Render.restore c'.vt)).u8need = 0 := by
  refine ⟨{ c with vt := c.vt.quiesce }, Checkpoint.load_save c, ?_, ?_⟩
  · exact (Render.restore_quiesced _ cols rows).1
  · exact (Render.restore_quiesced _ cols rows).2

/-- The same, in the form the runtime uses it: a *quiescent* checkpoint
(which is what the daemon writes, being taken between poll rounds) comes
back byte-identical, and its replay is quiesced. -/
theorem resume_exact (c : Ckpt) (cols rows : Nat) (h : c.vt.pstate = .ground)
    (h8 : c.vt.u8need = 0) (ha : c.vt.u8acc = 0) :
    load (save c) = some c
      ∧ ((Vt.Vt.init cols rows).feed (Render.restore c.vt)).pstate = .ground
      ∧ ((Vt.Vt.init cols rows).feed (Render.restore c.vt)).u8need = 0 :=
  ⟨Checkpoint.load_save_exact c h h8 ha,
   (Render.restore_quiesced c.vt cols rows).1,
   (Render.restore_quiesced c.vt cols rows).2⟩

/-- **§Resume (cursor).** The end-to-end cursor claim: a quiescent
checkpoint comes back byte-identical, and replaying it into a fresh
emulator of the session's size puts the cursor exactly where the session
had it. `Vt.Good` is the §Bound invariant every live session satisfies;
`origin = false` is the documented DECOM gap (`Render.restore_cursor`). -/
theorem resume_cursor (c : Ckpt) (h : c.vt.pstate = .ground) (h8 : c.vt.u8need = 0)
    (ha : c.vt.u8acc = 0) (hgood : Vt.Good c.vt) (ho : c.vt.modes.origin = false) :
    load (save c) = some c
      ∧ (((Vt.Vt.init c.vt.cols c.vt.rows).feed
          (Render.restore c.vt)).cursor.x = c.vt.cursor.x)
      ∧ (((Vt.Vt.init c.vt.cols c.vt.rows).feed
          (Render.restore c.vt)).cursor.y = c.vt.cursor.y) :=
  ⟨Checkpoint.load_save_exact c h h8 ha,
   (Render.restore_cursor c.vt hgood ho).1,
   (Render.restore_cursor c.vt hgood ho).2⟩

end Zmx.Core
