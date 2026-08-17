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
* **§Replay** (`Render.restore_quiesced_any`): the byte stream `restore`
  builds from that state leaves **any** emulator quiesced — the receiver's own
  parser state does not have to be assumed, which is what `restore_quiesced`
  (fresh `Vt.init` only) had to do.

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

/-- **§Resume, receiver-quantified** (Step 2 of `specs/restore-conformance.md`).
The same claim into **any** client's terminal rather than a fresh emulator: a
reattaching client is left ready for the application's next byte whatever state its
terminal was in — mid-escape, mid-OSC, mid-DCS, or holding a half-decoded character.
That is the state a real client is in, and `resume_quiesced` above assumed it away.

It rests on two properties of the stream's ends and nothing in between: `restore`
**leads** with `ESC \` so a receiver in a string state resynchronises
(`Render.restore_grounds`), and **ends** with a `CSI … H` whose final byte cannot
leave a character half-decoded (`Render.restore_u8_zero`). -/
theorem resume_quiesced_any (c : Ckpt) (w : Vt.Vt) :
    ∃ c', load (save c) = some c'
      ∧ ((w.feed (Render.restore c'.vt)).pstate = .ground)
      ∧ ((w.feed (Render.restore c'.vt)).u8need = 0) :=
  ⟨{ c with vt := c.vt.quiesce }, Checkpoint.load_save c,
   (Render.restore_quiesced_any _ w).1, (Render.restore_quiesced_any _ w).2⟩

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

/-- **§Resume (cursor), receiver-quantified.** The end-to-end cursor claim into *any*
client's emulator of the session's size, not only a fresh one. `Good w` is what
`dims_feed` needs of the receiver (see `Render.restore_cursor_any`); every client's
emulator satisfies it. -/
theorem resume_cursor_any (c : Ckpt) (w : Vt.Vt) (h : c.vt.pstate = .ground)
    (h8 : c.vt.u8need = 0) (ha : c.vt.u8acc = 0) (hgood : Vt.Good c.vt)
    (hgw : Vt.Good w) (hcols : w.cols = c.vt.cols) (hrows : w.rows = c.vt.rows)
    (ho : c.vt.modes.origin = false)
    (hmouse : c.vt.modes.mouse = 0 ∨ c.vt.modes.mouse = 1000 ∨ c.vt.modes.mouse = 1002
      ∨ c.vt.modes.mouse = 1003) :
    load (save c) = some c
      ∧ ((w.feed (Render.restore c.vt)).cursor.x = c.vt.cursor.x)
      ∧ ((w.feed (Render.restore c.vt)).cursor.y = c.vt.cursor.y) :=
  ⟨Checkpoint.load_save_exact c h h8 ha,
   (Render.restore_cursor_any c.vt w hgood hgw hcols hrows ho hmouse).1,
   (Render.restore_cursor_any c.vt w hgood hgw hcols hrows ho hmouse).2⟩

end Zmx.Core
