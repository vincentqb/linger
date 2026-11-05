module

public import Linger.Terminal.Proofs.Render.Scrollback
import all Linger.Terminal.Render
import all Linger.Terminal.Vt
import all Linger.Terminal.Proofs.Render.Scrollback

-- Module-private by default: `Vt`'s fields are sealed (see `Linger/Terminal/Proofs/Vt/State.lean`).

/-! # §Replay — the restore stream, proved (façade)

`Render.restore` is the byte stream a re-attaching client's terminal is fed, and
this ladder proves what it does to that terminal. The proof is one file per rung,
imported in dependency order. Most modules in `Theorems/` that use the ladder import
this one; `Theorems/Contracts.lean`, `Linger/Terminal/Proofs/Replay.lean` and
`Linger/Terminal/Proofs/Title.lean` instead import rungs directly.

The rungs, in dependency order:

* `Linger.Terminal.Proofs.Render.Ends` — §Replay stage 3b: the parser half. `Ends bs` ("from
  ground, `bs` returns to ground") plus one lemma per emitted construct, and the
  byte facts of the emitters that make them provable.
* `Linger.Terminal.Proofs.Render.Quiet` — stage 3c: the emitted numbers survive the round trip,
  and `Quiet bs` keeps DECOM off.
* `Linger.Terminal.Proofs.Render.Pen` — stage 3d begins: the pen round trip (semantic and parser
  halves) and one glyph placed in one cell.
* `Linger.Terminal.Proofs.Render.Keeps` — `Fixes π` shares nonprinting control-stage proofs
  across projections; `Keeps` specializes it to the screen.
* `Linger.Terminal.Proofs.Render.Modes` — anchor A5, both directions for the modes: the lead-in
  grounds any receiver, `leave_canonical` on the way out, `MMap` and the inbound
  modes and pen on the way in.
* `Linger.Terminal.Proofs.Render.Sticky` — A5 inbound for the sticky bundle (region, charsets,
  shift state, screen) via `SMap`, and the cursor: `cup_feed_eq` is the primitive
  address and `restore_cursor_placed_any` places the session's cursor in any receiver.
* `Linger.Terminal.Proofs.Render.History` — §Row: `linger capture --history`'s framing cannot be forged by
  a cell's contents.
* `Linger.Terminal.Proofs.Render.Row` — the row painter: `Matches` and `rowAnsi_writes_row`.
* `Linger.Terminal.Proofs.Render.PendingGlyph` and `PendingAccumulator` —
  reprinting a canonical margin cell preserves the rest of the terminal;
  separate byte-level cursor frames also cover malformed receiver grids and
  stale UTF-8 accumulators.
* `Linger.Terminal.Proofs.Render.PendingWrap` — complete state equations for the deferred-wrap
  stages, their post-paint frames, the unconditional cell fit, and the original
  cursor guarantees.
* `Linger.Terminal.Proofs.Render.Grid` — the grid: `paint_rows`, `gridAnsi_writes_grid`, and
  `restore_grid_any` on both screens at every height.
* `Linger.Terminal.Proofs.Render.Tabs` — the tab-stop projection and `restore_tabs_any`.
* `Linger.Terminal.Proofs.Render.Scrollback` — the history stage's row half: the unconditional row
  fit (`rowOk_fitRow`, `fitRow_id_of_rowOk`) and the complete byte budget
  (`sbTake_budget`, `sbRows_budget`, `sbTake_prefix`, `scrollbackAnsi_le`). Its
  receiver half, `scrollback_entry`, is in `Grid` beside `paint_entry`. -/
