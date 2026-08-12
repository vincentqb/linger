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

`resume_quiesced` is their composition, and `resume_screen_pending`
records — as a theorem statement rather than as prose — exactly which
part of the claim is still carried by tests instead of proof: that the
replayed *cells* equal the saved cells. Keeping the gap in the same file
as the claim is deliberate; a reader should not have to hunt THEOREMS.md
to learn what is not yet proved.
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

/-- The cursor half, for the common case. `Render.cup_places_cursor` is
the proved core; what it needs to reach a whole restore stream is the
`Quiet` composition recorded in specs/bigger-theorems.md. Stated here so
the shape of the finished claim is on the record next to the part that is
done. -/
theorem resume_cursor_shape (v : Vt.Vt) (row col : Nat)
    (hg : (Vt.Vt.init v.cols v.rows).pstate = .ground)
    (hrow : 1 ≤ row) (hcol : 1 ≤ col) (hr : row ≤ 65535) (hc : col ≤ 65535)
    (hry : row - 1 < (Vt.Vt.init v.cols v.rows).rows)
    (hcx : col - 1 < (Vt.Vt.init v.cols v.rows).cols)
    (ho : (Vt.Vt.init v.cols v.rows).modes.origin = false) :
    (((Vt.Vt.init v.cols v.rows).feed (Render.csiNum2 row col 0x48)).cursor.x = col - 1)
      ∧ (((Vt.Vt.init v.cols v.rows).feed
          (Render.csiNum2 row col 0x48)).cursor.y = row - 1) :=
  Render.cup_places_cursor row col hg hrow hcol hr hc hry hcx ho

end Zmx.Core
