module

public import Theorems.Checkpoint
public import Theorems.Render
import all Linger.Core.Vt
-- Converted from legacy by the `Vt` seal (`specs/archive/vt-toolkit.md` Step 1). The
-- end-to-end claim quantifies over a quiescent `Vt`, so its statement names three
-- now-private fields; module-private declarations may, public ones may not. The
-- rungs it composes are module-private too, hence `import all` on both.
import all Theorems.Checkpoint
import all Theorems.Render

/-! # §Resume — the end-to-end claim, as one theorem

Everything else in `Theorems/` is a rung. This file states the thing the
program is *for*, by composing them:

> Kill a session's daemon. Reboot the machine. Reattach. The bytes the
> new client's terminal receives are derived from a checkpoint that
> round-trips exactly modulo parser quiescence, and replay restores the
> proved screen, ruler and history observations while leaving the receiver's
> parser in `ground` with no half-decoded character.

The two halves:

* **§Restore** (`Checkpoint.load_save`): what `save` writes, `load` reads
  back, modulo the parser state a checkpoint deliberately drops.
* **§Replay** (`Render.restore_quiesced_any`): the byte stream `restore`
  builds from that state leaves **any** emulator quiesced — the receiver's own
  parser state does not have to be assumed, which is what `restore_quiesced`
  (fresh `Vt.init` only) had to do.

`resume_grid`, `resume_tabs`, and `resume_sb` prove value fidelity.
`resume_cursor` covers cursor position with origin mode off. Title and saved
cursor/pen fidelity still rely on fixtures. The fixture equivalence also
compares all three deferred-wrap flags, and socket checks exercise the next
glyph after replay. Decoded flags without a representable margin cell remain
outside that equivalence. Parser quiescence alone does not imply equivalence
under arbitrary future input.

The last section is the same statement with the subject swapped: `load`'s **output**
instead of `save`'s input, i.e. an arbitrary byte string off disk. Those three claims
(`resume_grid_of_load`, `resume_tabs_of_load`, `resume_sb_of_load`) carry no
`Good`/`Renderable`/`TabsOk` hypothesis at all, because the decoder establishes all three —
which it did not before finding R2. That is what validating the shape at the door bought,
and the reason it is a *new* family rather than a weakening of the one above is written
there.
-/

namespace Linger.Core

open Linger.Core.Checkpoint (Ckpt load save)

/-- `Vt.init` at a `Good` state's own dimensions installs exactly those dimensions:
`clampDim` is the identity inside `[1,1000]`, which is what `Good` says. Extracted because
six claims below need one half of it or both, and it was written out four times. -/
theorem init_dims_of_good {v : Vt.Vt} (h : Vt.Good v) :
    (Vt.Vt.init v.cols v.rows).cols = v.cols ∧ (Vt.Vt.init v.cols v.rows).rows = v.rows := by
  constructor
  · show Vt.clampDim v.cols = v.cols
    have := h.colsPos
    have := h.colsLe
    simp only [Vt.clampDim]
    omega
  · show Vt.clampDim v.rows = v.rows
    have := h.rowsPos
    have := h.rowsLe
    simp only [Vt.clampDim]
    omega

/-- **§Resume.** A checkpoint, reloaded and replayed into a fresh
emulator of the same size, leaves that emulator quiesced: the parser is
in `ground` with no pending UTF-8 sequence. The reattaching client is always left
ready for the application's next byte.

`hgood` is the hypothesis that arrived with the checkpoint validation
(`specs/archive/vt-toolkit.md` Step 2): `load` refuses a record that does not describe a
`Good` screen, so `load (save c)` is `none` for a `c` no live session could hold. This
claim used to have no hypotheses and was, for exactly that reason, also true of
`cols := 0`. `Vt.good_init` and the `Pres` machinery give it for every real session.

**`hren` and `htabs` arrived with finding R2**, by the same mirror and for the same kind of
reason: the door now also refuses a record whose grid is not the shape its dimensions
claim, or whose tab ruler is not the width of its screen. This claim does not read the grid
— that is the cost the mirror imposes, named here rather than left for a reader to
discover, and `Vt.renderable_of_liveReachable`/`Vt.tabsOk_of_liveReachable` discharge both
for any live session (`Checkpoint.load_save_live`). -/
theorem resume_quiesced (c : Ckpt) (cols rows : Nat) (hgood : Vt.Good c.vt)
    (hren : Vt.Renderable c.vt) (htabs : Vt.TabsOk c.vt) :
    ∃ c',
      load (save c) = some c' ∧
        ((Vt.Vt.init cols rows).feed (Render.restore c'.vt)).pstate = .ground ∧
        ((Vt.Vt.init cols rows).feed (Render.restore c'.vt)).u8need = 0 := by
  refine ⟨{ c with vt := c.vt.quiesce }, Checkpoint.load_save c hgood hren htabs, ?_, ?_⟩
  · exact (Render.restore_quiesced _ cols rows).1
  · exact (Render.restore_quiesced _ cols rows).2

/-- **§Resume, receiver-quantified** (Step 2 of `specs/archive/restore-conformance.md`).
The same claim into **any** client's terminal rather than a fresh emulator: a
reattaching client is left ready for the application's next byte whatever state its
terminal was in — mid-escape, mid-OSC, mid-DCS, or holding a half-decoded character.
That is the state a real client is in, and `resume_quiesced` above assumed it away.

It composes the stream's grounding prefix and stage guarantees: `restore`
**leads** with `ESC \` so a receiver in a string state resynchronises
(`Render.restore_grounds`). Cursor addressing clears partial UTF-8, and the
optional deferred-wrap stage finishes with complete SGR sequences
(`Render.restore_u8_zero`).

`hren`/`htabs` are `resume_quiesced`'s — the round-trip conjunct's, not the replay's; see
there. -/
theorem resume_quiesced_any (c : Ckpt) (w : Vt.Vt) (hgood : Vt.Good c.vt)
    (hren : Vt.Renderable c.vt) (htabs : Vt.TabsOk c.vt) :
    ∃ c',
      load (save c) = some c' ∧
        ((w.feed (Render.restore c'.vt)).pstate = .ground) ∧
        ((w.feed (Render.restore c'.vt)).u8need = 0) :=
  ⟨{ c with vt := c.vt.quiesce }, Checkpoint.load_save c hgood hren htabs,
    (Render.restore_quiesced_any _ w).1, (Render.restore_quiesced_any _ w).2⟩

/-- A checkpoint whose parser is already quiescent comes back as the same
record, and its replay is quiesced. A poll boundary does not itself establish
these parser hypotheses. `hren`/`htabs`: see `resume_quiesced`. -/
theorem resume_exact (c : Ckpt) (cols rows : Nat) (hgood : Vt.Good c.vt) (hren : Vt.Renderable c.vt)
    (htabs : Vt.TabsOk c.vt) (h : c.vt.pstate = .ground) (h8 : c.vt.u8need = 0)
    (ha : c.vt.u8acc = 0) :
    load (save c) = some c ∧
      ((Vt.Vt.init cols rows).feed (Render.restore c.vt)).pstate = .ground ∧
      ((Vt.Vt.init cols rows).feed (Render.restore c.vt)).u8need = 0 :=
  ⟨Checkpoint.load_save_exact c hgood hren htabs h h8 ha,
    (Render.restore_quiesced c.vt cols rows).1, (Render.restore_quiesced c.vt cols rows).2⟩

/-- **§Resume (cursor).** The end-to-end cursor claim: a quiescent
checkpoint comes back as the same record, and replaying it into a fresh
emulator of the session's size puts the cursor exactly where the session
had it. `Vt.Good` is the §Bound invariant every live session satisfies;
`origin = false` is the documented DECOM gap (`Render.restore_cursor`).
`hren`/`htabs` are the round trip's, not the cursor's: see `resume_quiesced`. -/
theorem resume_cursor (c : Ckpt) (h : c.vt.pstate = .ground) (h8 : c.vt.u8need = 0)
    (ha : c.vt.u8acc = 0) (hgood : Vt.Good c.vt) (hren : Vt.Renderable c.vt)
    (htabs : Vt.TabsOk c.vt) (ho : c.vt.modes.origin = false) :
    load (save c) = some c ∧
      (((Vt.Vt.init c.vt.cols c.vt.rows).feed (Render.restore c.vt)).cursor.x = c.vt.cursor.x) ∧
      (((Vt.Vt.init c.vt.cols c.vt.rows).feed (Render.restore c.vt)).cursor.y = c.vt.cursor.y) :=
  ⟨Checkpoint.load_save_exact c hgood hren htabs h h8 ha, (Render.restore_cursor c.vt hgood ho).1,
    (Render.restore_cursor c.vt hgood ho).2⟩

/-- **§Resume (cursor), receiver-quantified.** The end-to-end cursor claim into *any*
client's emulator of the session's size, not only a fresh one. `Good w` is what
`dims_feed` needs of the receiver (see `Render.restore_cursor_any`); every client's
emulator satisfies it. `hren`/`htabs` are the round trip's: see `resume_quiesced`. -/
theorem resume_cursor_any (c : Ckpt) (w : Vt.Vt) (h : c.vt.pstate = .ground) (h8 : c.vt.u8need = 0)
    (ha : c.vt.u8acc = 0) (hgood : Vt.Good c.vt) (hren : Vt.Renderable c.vt)
    (htabs : Vt.TabsOk c.vt) (hgw : Vt.Good w) (hcols : w.cols = c.vt.cols)
    (hrows : w.rows = c.vt.rows) (ho : c.vt.modes.origin = false)
    (hmouse :
      c.vt.modes.mouse = 0 ∨
        c.vt.modes.mouse = 1000 ∨ c.vt.modes.mouse = 1002 ∨ c.vt.modes.mouse = 1003) :
    load (save c) = some c ∧
      ((w.feed (Render.restore c.vt)).cursor.x = c.vt.cursor.x) ∧
      ((w.feed (Render.restore c.vt)).cursor.y = c.vt.cursor.y) :=
  ⟨Checkpoint.load_save_exact c hgood hren htabs h h8 ha,
    (Render.restore_cursor_any c.vt w hgood hgw hcols hrows ho hmouse).1,
    (Render.restore_cursor_any c.vt w hgood hgw hcols hrows ho hmouse).2⟩

/-- **§Resume (grid) — Definition-of-done item 5, end to end.** A quiescent checkpoint comes
back as the same record, and replaying it into a fresh emulator of the session's size reproduces
the session's screen exactly, cell for cell — on either screen (`Render.restore_grid_any`
dispatches on the alt flag) and for **any** height, the one-row screen included. `Good`/
`Renderable` are the §Bound invariants every live session satisfies.

`hren` was already here, so finding R2 cost this claim **one** binder rather than two:
`htabs`, which the round-trip conjunct now needs (`Checkpoint.load_save_exact`). And the
other direction is where R2 pays: `resume_grid_of_load` below is this claim's conclusion
over an arbitrary byte string with **no** hypotheses at all. -/
theorem resume_grid (c : Ckpt) (h : c.vt.pstate = .ground) (h8 : c.vt.u8need = 0)
    (ha : c.vt.u8acc = 0) (hgood : Vt.Good c.vt) (hren : Vt.Renderable c.vt)
    (htabs : Vt.TabsOk c.vt) :
    load (save c) = some c ∧
      ((Vt.Vt.init c.vt.cols c.vt.rows).feed (Render.restore c.vt)).grid = c.vt.grid := by
  refine ⟨Checkpoint.load_save_exact c hgood hren htabs h h8 ha, ?_⟩
  exact
    Render.restore_grid_any c.vt (Vt.Vt.init c.vt.cols c.vt.rows) (Vt.good_init _ _)
      (Vt.renderable_init _ _) (init_dims_of_good hgood).1 (init_dims_of_good hgood).2 rfl rfl hren

/-- Non-vacuity: a real 80×24 checkpoint satisfies every hypothesis of `resume_grid`, so the
theorem is not vacuously true. -/
example :
    ∃ c : Ckpt,
      c.vt.pstate = .ground ∧
        c.vt.u8need = 0 ∧ c.vt.u8acc = 0 ∧ Vt.Good c.vt ∧ Vt.Renderable c.vt ∧ Vt.TabsOk c.vt :=
  ⟨{ vt := Vt.Vt.init 80 24, cwd := "", labels := [] }, rfl, rfl, rfl, Vt.good_init 80 24,
    Vt.renderable_init 80 24, Vt.tabsOk_init 80 24⟩

/-- **§Resume (tab ruler).** A quiescent checkpoint comes back as the same record, and
replaying it into a fresh emulator of the session's width installs the session's tab
ruler. `hvtabs` is the ruler-length hypothesis `Render.restore_tabs_any` explains:
`Good`/`Renderable` do not carry it. It is no longer *unreachable* from disk, though —
after finding R2 the decoder checks it (`Checkpoint.load_tabsOk`), which is what
`resume_tabs_of_load` below rests on; here it stays a hypothesis because this claim's
subject is `save`'s input.

`hren` is R2's one added binder on this claim, and it is the round trip's rather than the
ruler's (`Checkpoint.load_save_exact`). -/
theorem resume_tabs (c : Ckpt) (h : c.vt.pstate = .ground) (h8 : c.vt.u8need = 0)
    (ha : c.vt.u8acc = 0) (hgood : Vt.Good c.vt) (hren : Vt.Renderable c.vt)
    (hvtabs : c.vt.tabs.size = c.vt.cols) :
    load (save c) = some c ∧
      ((Vt.Vt.init c.vt.cols c.vt.rows).feed (Render.restore c.vt)).tabs = c.vt.tabs := by
  refine ⟨Checkpoint.load_save_exact c hgood hren hvtabs h h8 ha, ?_⟩
  exact
    Render.restore_tabs_any c.vt (Vt.Vt.init c.vt.cols c.vt.rows) (Vt.good_init _ _)
      (init_dims_of_good hgood).1 hvtabs

/-- Non-vacuity at the degenerate height: `resume_grid` genuinely covers a **one-row** screen,
the case `h2 : 0 < rows - 1` used to exclude — the grid of an 80×1 session is reproduced. -/
example :
    ((Vt.Vt.init 80 1).feed (Render.restore (Vt.Vt.init 80 1))).grid = (Vt.Vt.init 80 1).grid :=
  (resume_grid { vt := Vt.Vt.init 80 1, cwd := "", labels := [] } rfl rfl rfl (Vt.good_init 80 1)
      (Vt.renderable_init 80 1) (Vt.tabsOk_init 80 1)).2

/-- **§Resume (scrollback).** A quiescent checkpoint comes back as the same record, and replaying it
into a fresh emulator of the session's size installs the session's history above the screen —
oldest first, each row at the session's width, trimmed from the oldest end to the byte budget.

This is the row `THEOREMS.md`'s A5 anchor could not claim while the scrollback rested on the
round-trip fixtures alone. `.toList`, not `.sb`: a ring that has wrapped and a ring built from
index 0 are the same history in different records, and `Render.restore_sb_any` explains why
comparing the records instead would be a false claim about a true capability.

`hne` is the branch, not a restriction smuggled in: with nothing to replay `restore` emits no
`ED 3` and the client keeps its own scrollback, which is `Render.restore_sb_keeps_of_empty`
rather than a weaker form of this. The exit criterion for this claim is the *first* conjunct —
dropping `wRing` from `save` must break it, since a checkpoint that does not carry history
cannot restore one.

`htabs` is finding R2's one added binder here, and it is the round trip's, not the ring's;
`hren` was already present. Note what R2 did **not** reach: the ring's own rows. `Vt.resize`
leaves them at their old width, so no decoder may demand `RowOk v.cols` of them — see
`Render.restore_sb_exact`'s `hrok`, which stays unreachable from disk by construction. -/
theorem resume_sb (c : Ckpt) (h : c.vt.pstate = .ground) (h8 : c.vt.u8need = 0)
    (ha : c.vt.u8acc = 0) (hgood : Vt.Good c.vt) (hren : Vt.Renderable c.vt)
    (htabs : Vt.TabsOk c.vt) (hne : (Render.sbRows c.vt).isEmpty = false) :
    load (save c) = some c ∧
      ((Vt.Vt.init c.vt.cols c.vt.rows).feed (Render.restore c.vt)).sb.toList =
        (Render.sbRows c.vt).toList := by
  refine ⟨Checkpoint.load_save_exact c hgood hren htabs h h8 ha, ?_⟩
  exact
    Render.restore_sb_any c.vt (Vt.Vt.init c.vt.cols c.vt.rows) (Vt.good_init _ _)
      (Vt.renderable_init _ _) hgood hren (init_dims_of_good hgood).1 (init_dims_of_good hgood).2
      rfl rfl hne

/-! ## §Resume over an arbitrary byte string — what finding R2 bought

The claims above take `save`'s **input** as their subject, so their `Renderable`/`TabsOk`
hypotheses cannot be discharged by the decoder: the only bridge to it is
`Checkpoint.load_save_exact`, whose *conclusion* is the round trip and which is itself
gated on those hypotheses. That circularity is real and was measured by trying it — see
SCRATCHPAD.md. So the payoff of validating the shape at the door is not a weakening of the
family above but a **new** one, whose subject is `load`'s output:

> whatever bytes are on disk, if they load at all then replaying them reproduces the
> screen, the ruler and the history they describe.

No `Good`, no `Renderable`, no `TabsOk`, no quiescence, no `save` — only `load l = some c`,
for an arbitrary `l`. Before R2 the grid and ruler halves of this were not provable at all,
because `load` established nothing about either.

**The `ofDecoded` rung (2026-09-14) adds no statement to this family, and that is a
measurement rather than an omission.** Every claim here is expressible from
`Checkpoint.load_good`/`load_renderable`/`load_tabsOk`, which R2 already provided; what the
rung supplies on top — `Checkpoint.load_live`, i.e. that a decoded screen is in the closure
the `Render.restore_*_reachable` theorems quantify over — is only *needed* where the
closure is the hypothesis of an induction, and the one induction in the tree that takes it
is the daemon's (`Session.run_vt_live`). So the rung's payoff is
`Theorems/Session.lean` §"Resume at the daemon", not another rung here. Where it does help
locally is proof size: with `load_live` the three claims below reach
`Render.restore_grid_reachable` and its siblings directly, receiver-quantified, instead of
threading four hypotheses into the `_any` forms — a change with no effect on any statement,
so it was not made. -/

/-- **§Resume (grid), from disk.** Any byte string that loads, replayed into a fresh
emulator of the checkpoint's size, reproduces the checkpoint's screen cell for cell.
`Checkpoint.load_good` and `Checkpoint.load_renderable` discharge every hypothesis
`resume_grid` has to ask for. -/
theorem resume_grid_of_load {l : List UInt8} {c : Ckpt} (h : load l = some c) :
    ((Vt.Vt.init c.vt.cols c.vt.rows).feed (Render.restore c.vt)).grid = c.vt.grid :=
  Render.restore_grid_any c.vt (Vt.Vt.init c.vt.cols c.vt.rows) (Vt.good_init _ _)
    (Vt.renderable_init _ _) (init_dims_of_good (Checkpoint.load_good h)).1
    (init_dims_of_good (Checkpoint.load_good h)).2 rfl rfl (Checkpoint.load_renderable h)

/-- **§Resume (tab ruler), from disk.** The ruler half, likewise —
`Checkpoint.load_tabsOk` is the hypothesis `resume_tabs` has to ask for, and it did not
exist before R2: a checkpoint could name a ruler of any length at all. -/
theorem resume_tabs_of_load {l : List UInt8} {c : Ckpt} (h : load l = some c) :
    ((Vt.Vt.init c.vt.cols c.vt.rows).feed (Render.restore c.vt)).tabs = c.vt.tabs :=
  Render.restore_tabs_any c.vt (Vt.Vt.init c.vt.cols c.vt.rows) (Vt.good_init _ _)
    (init_dims_of_good (Checkpoint.load_good h)).1 (Checkpoint.load_tabsOk h)

/-- **§Resume (scrollback), from disk.** The history half. `hne` is the same branch
`resume_sb` has (an empty history leaves the client's own scrollback alone,
`Render.restore_sb_keeps_of_empty`) and is not a hypothesis the decoder could discharge —
it is a property of the checkpoint's content, not of its well-formedness. -/
theorem resume_sb_of_load {l : List UInt8} {c : Ckpt} (h : load l = some c)
    (hne : (Render.sbRows c.vt).isEmpty = false) :
    ((Vt.Vt.init c.vt.cols c.vt.rows).feed (Render.restore c.vt)).sb.toList =
      (Render.sbRows c.vt).toList :=
  Render.restore_sb_any c.vt (Vt.Vt.init c.vt.cols c.vt.rows) (Vt.good_init _ _)
    (Vt.renderable_init _ _) (Checkpoint.load_good h) (Checkpoint.load_renderable h)
    (init_dims_of_good (Checkpoint.load_good h)).1 (init_dims_of_good (Checkpoint.load_good h)).2
    rfl rfl hne

end Linger.Core
