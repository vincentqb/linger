module

public import Theorems.Render.Scrollback
import all Linger.Core.Render
import all Linger.Core.Vt
import all Theorems.Render.Scrollback

-- Module-private by default: `Vt`'s fields are sealed (see `Theorems/Vt/State.lean`).

/-! # §Replay — the restore stream, proved (façade)

`Render.restore` is the byte stream a re-attaching client's terminal is fed, and
this ladder proves what it does to that terminal. The proof is one file per rung,
imported in dependency order; this module is the name the rest of `Theorems/`
imports, so splitting the ladder changed no downstream import.

The rungs, in dependency order:

* `Theorems.Render.Ends` — §Replay stage 3b: the parser half. `Ends bs` ("from
  ground, `bs` returns to ground") plus one lemma per emitted construct, and the
  byte facts of the emitters that make them provable.
* `Theorems.Render.Quiet` — stage 3c: the emitted numbers survive the round trip,
  and `Quiet bs` keeps DECOM off.
* `Theorems.Render.Pen` — stage 3d begins: the pen round trip (semantic and parser
  halves) and one glyph placed in one cell.
* `Theorems.Render.Keeps` — `Fixes π` shares nonprinting control-stage proofs
  across projections; `Keeps` specializes it to the screen. Also `Row.mend`'s
  fixed points.
* `Theorems.Render.Modes` — anchor A5, both directions for the modes: the lead-in
  grounds any receiver, `leave_canonical` on the way out, `MMap` and the inbound
  modes and pen on the way in.
* `Theorems.Render.Sticky` — A5 inbound for the sticky bundle (region, charsets,
  shift state, screen) via `SMap`, and the cursor: `cup_feed_eq` is the primitive
  address and `restore_cursor_placed_any` places the session's cursor in any receiver.
* `Theorems.Render.History` — §Row: `linger capture --history`'s framing cannot be forged by
  a cell's contents.
* `Theorems.Render.Row` — the row painter: `Matches` and `rowAnsi_writes_row`.
* `Theorems.Render.PendingGlyph` and `PendingAccumulator` —
  reprinting a canonical margin cell preserves the rest of the terminal;
  separate byte-level cursor frames also cover malformed receiver grids and
  stale UTF-8 accumulators.
* `Theorems.Render.PendingWrap` — complete state equations for the deferred-wrap
  stages, their post-paint frames, the unconditional cell fit, and the original
  cursor guarantees.
* `Theorems.Render.Grid` — the grid: `paint_rows`, `gridAnsi_writes_grid`, and
  `restore_grid_any` on both screens at every height.
* `Theorems.Render.Tabs` — the tab-stop projection and `restore_tabs_any`.
* `Theorems.Render.Scrollback` — the history stage's row half: the unconditional row
  fit (`rowOk_fitRow`, `fitRow_id_of_rowOk`) and the complete byte budget
  (`sbTake_budget`, `sbRows_budget`, `sbTake_prefix`, `scrollbackAnsi_le`). Its
  receiver half, `scrollback_entry`, is in `Grid` beside `paint_entry`. -/

namespace Linger.Core.Render

/-- The compiled row painter emits exactly the logical painter's bytes and final
pen, including arbitrary decoded rows and nondefault starting pens. -/
theorem rowAnsiLinear_exact (row : Vt.Row) (pen : Vt.Pen) :
    rowAnsiLinear row pen = rowAnsi row pen := by rw [rowAnsi_eq_rowAnsiLinear]

end Linger.Core.Render
