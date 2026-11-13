module

public import Terminal.Proofs.Render.Scrollback
import all Terminal.Render
import all Terminal.Vt
import all Terminal.Proofs.Render.Scrollback

-- Module-private by default: `Vt`'s fields are sealed (see `packages/terminal/Terminal/Proofs/Vt/State.lean`).

/-! # The restore stream, proved (façade)

`Render.restore` is the byte stream a re-attaching client's terminal is fed, in steps of any
positive budget (`Replay.drain_start`), and this ladder proves what it does to that terminal:
the replay headlines of `packages/terminal/TerminalChallenge.lean`, such as `replay_restores`
and `replay_history`, rest on it. The proof is one file per rung, imported in dependency order.
Most proofs that use the ladder import this one; `Theorems/Solution.lean`,
`packages/terminal/Terminal/Solution.lean` and the toolkit's `Replay`, `Title` and `Vt/History`
proofs import the rungs they need directly.

The rungs, in dependency order:

* `Terminal.Proofs.Render.Ends` — the parser half: `Ends bs` ("from
  ground, `bs` returns to ground") plus one lemma per emitted construct, and the
  byte facts of the emitters that make them provable.
* `Terminal.Proofs.Render.Quiet` — the emitted numbers survive the round trip,
  and `Quiet bs` keeps DECOM off.
* `Terminal.Proofs.Render.Pen` — the pen round trip (semantic and parser
  halves) and one glyph placed in one cell.
* `Terminal.Proofs.Render.Keeps` — `Fixes π` shares nonprinting control-stage proofs
  across projections; `Keeps` specializes it to the screen.
* `Terminal.Proofs.Render.Modes` — the modes in both directions: the lead-in
  grounds any receiver, `leave_canonical` on the way out, `MMap` and the inbound
  modes and pen on the way in.
* `Terminal.Proofs.Render.Sticky` — the sticky bundle on the way in (region, charsets,
  shift state, screen) via `SMap`, and the cursor: `cup_feed_eq` is the primitive
  address and `restore_cursor_placed_any` places the session's cursor in any receiver.
* `Terminal.Proofs.Render.History` — `linger capture --history`'s row framing cannot be forged
  by a cell's contents.
* `Terminal.Proofs.Render.Row` — the row painter: its invariant `Matches`, one step lemma per
  cell shape and the mark loop.
* `Terminal.Proofs.Render.PendingGlyph` and `PendingAccumulator` —
  reprinting a canonical margin cell preserves the rest of the terminal;
  separate byte-level cursor frames also cover malformed receiver grids and
  stale UTF-8 accumulators.
* `Terminal.Proofs.Render.PendingWrap` — complete state equations for the deferred-wrap
  stages, their post-paint frames, the unconditional cell fit, and the original
  cursor guarantees.
* `Terminal.Proofs.Render.Grid` — the grid: `rowAnsi_writes_row`, `paint_rows`,
  `gridAnsi_writes_grid`, and `restore_grid_any` on both screens at every height.
* `Terminal.Proofs.Render.Tabs` — the tab-stop projection and `restore_tabs_any`.
* `Terminal.Proofs.Render.Scrollback` — the history stage: the unconditional row
  fit (`rowOk_fitRow`, `fitRow_id_of_rowOk`), the complete byte budget
  (`sbTake_budget`, `sbRows_budget`, `sbTake_prefix`, `scrollbackAnsi_le`) and the ring a
  receiver ends with (`restore_sb_any`). `scrollback_entry`, which carries the paint's entry
  state across the stage, is in `Grid` beside `paint_entry`. -/
