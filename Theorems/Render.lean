module

public import Theorems.Render.Scrollback
import all Linger.Core.Render
import all Linger.Core.Vt
import all Theorems.Render.Scrollback

-- No `public section`: a **public** declaration's type may not mention a private
-- field, and `Vt`'s are private now (the seal, `specs/archive/vt-toolkit.md` Step 1).
-- Module-private is the default, so consumers reach in with `import all`. See the
-- longer note in `Theorems/Vt.lean`.

/-! # §Replay — the restore stream, proved (façade)

`Render.restore` is the byte stream a re-attaching client's terminal is fed, and
this ladder proves what it does to that terminal. The proof is one file per rung,
imported in dependency order; this module is the name the rest of `Theorems/`
imports, so splitting the ladder changed no downstream import.

The rungs, in dependency order:

* `Theorems.Render.Ends` — §Replay stage 3b: the parser half. `Ends bs` ("from
  ground, `bs` returns to ground with no pending UTF-8") plus one lemma per emitted
  construct, and the byte facts of the emitters that make them provable.
* `Theorems.Render.Quiet` — stage 3c: the emitted numbers survive the round trip,
  `Quiet bs` keeps DECOM off, and `cup_roundtrip` proves the primitive cursor address.
* `Theorems.Render.Pen` — stage 3d begins: the pen round trip (semantic and parser
  halves) and one glyph placed in one cell.
* `Theorems.Render.Keeps` — `Fixes π` shares nonprinting control-stage proofs
  across projections; `Keeps` specializes it to the screen. Also `Row.mend`'s
  fixed points.
* `Theorems.Render.Modes` — anchor A5, both directions for the modes: the lead-in
  grounds any receiver, `leave_canonical` on the way out, `MMap` and the inbound
  modes and pen on the way in.
* `Theorems.Render.Sticky` — A5 inbound for the sticky bundle (region, charsets,
  shift state, screen) via `SMap`.
* `Theorems.Render.History` — §Row: `linger history`'s framing cannot be forged by
  a cell's contents.
* `Theorems.Render.Row` — the row painter: `Matches` and `rowAnsi_writes_row`.
* `Theorems.Render.PendingGlyph`, `PendingPosition` and `PendingAccumulator` —
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
  receiver half, `scrollback_entry`, is in `Grid` beside `paint_entry`.

Why it is split: at ~9,900 lines the single file was accretion from
one-commit-per-step, and the boundaries above are the ones its own section headers
already named — so the split is a move, not a rewrite (no statement, proof or
docstring changed). It was done to make the elaborator cost legible: see
`FINDINGS-2026-08-18-factoring-audit.md` for which `maxHeartbeats` raises were
paying for file size and which are the record-width tax `THEOREMS.md` describes. -/
