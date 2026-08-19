import Theorems.Render.Scrollback
/-! # §Replay — the restore stream, proved (façade)

`Render.restore` is the byte stream a re-attaching client's terminal is fed, and
this ladder proves what it does to that terminal. The proof is one file per rung,
imported in dependency order; this module is the name the rest of `Theorems/`
imports, so splitting the ladder changed no downstream import.

The rungs, in the order they are built (each imports the one above):

* `Theorems.Render.Ends` — §Replay stage 3b: the parser half. `Ends bs` ("from
  ground, `bs` returns to ground with no pending UTF-8") plus one lemma per emitted
  construct, and the byte facts of the emitters that make them provable.
* `Theorems.Render.Quiet` — stage 3c: the emitted numbers survive the round trip,
  the cursor lands where the session had it, and DECOM stays off.
* `Theorems.Render.Pen` — stage 3d begins: the pen round trip (semantic and parser
  halves) and one glyph placed in one cell.
* `Theorems.Render.Keeps` — the restore tail leaves the screen alone, so the paint
  is the only writer; and `Row.mend`'s fixed points.
* `Theorems.Render.Modes` — anchor A5, both directions for the modes: the lead-in
  grounds any receiver, `leave_canonical` on the way out, `MMap` and the inbound
  modes and pen on the way in.
* `Theorems.Render.Sticky` — A5 inbound for the sticky bundle (region, charsets,
  shift state, screen) via `SMap`, and the cursor for any receiver.
* `Theorems.Render.History` — §Row: `linger history`'s framing cannot be forged by
  a cell's contents.
* `Theorems.Render.Row` — the row painter: `Matches` and `rowAnsi_writes_row`.
* `Theorems.Render.Grid` — the grid: `paint_rows`, `gridAnsi_writes_grid`, and
  `restore_grid_any` on both screens at every height.
* `Theorems.Render.Tabs` — `Fixes π` (the projection-generic stream predicate that
  `Keeps` and `MMap id` are instances of) and `restore_tabs_any`.
* `Theorems.Render.Scrollback` — the history stage's row half: the unconditional fit
  (`cellOk_cellFit`, `rowOk_fitRow`, `fitRow_id_of_rowOk`) and the byte budget
  (`sbTake_budget`, `sbRows_budget`, `sbTake_prefix`, `rowAnsi_len_le_cost`). Its
  receiver half, `scrollback_entry`, is in `Grid` beside `paint_entry`.

Why it is split: at ~9,900 lines the single file was accretion from
one-commit-per-step, and the boundaries above are the ones its own section headers
already named — so the split is a move, not a rewrite (no statement, proof or
docstring changed). It was done to make the elaborator cost legible: see
`FINDINGS-2026-08-18-factoring-audit.md` for which `maxHeartbeats` raises were
paying for file size and which are the record-width tax `THEOREMS.md` describes. -/
