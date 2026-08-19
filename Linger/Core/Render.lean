import Linger.Core.Vt
/-! # Linger.Core.Render — Vt state → ANSI bytes

Pure functions from a `Vt` snapshot to the byte stream that reproduces
it on a real terminal: `restore` (what a re-attaching client is sent)
and `history` (scrollback dump for `linger history`).

**Bytes, not Strings** (§Replay, specs/archive/bigger-theorems.md). This module
used to assemble `String`s and UTF-8 them at the end, which made the
output unprovable: a `String` literal does not reduce in the kernel, so
no theorem could see that `csi` is `[0x1B, 0x5B]` (`decide` gets stuck
on `"\x1b[".toUTF8`). Everything here now builds `List UInt8` through
named stages — `digits`, `utf8`, `csiNum`, `penSgr`, `rowAnsi` — each of
which the §Replay ladder in `Theorems/Render.lean` can state a lemma
about. `rowText` (plain text for `history`) was the last holdout and is now
bytes too, which is what let `history_framing`/`history_lines` be stated at all.

Emitted characters pass `safeChar`: a C0/DEL codepoint is replaced by
U+FFFD. That makes the emitter's output provably free of control bytes
for ANY `Vt` — no invariant hypothesis needed — and it is genuinely
defensive, since a control byte written into a repaint (or into an OSC
title payload) would be re-parsed as a command and desync the replay.
-/

namespace Linger.Core.Render

open Linger.Core.Vt

abbrev Bytes := List UInt8

/-! ## Byte primitives -/

def escB : Bytes := [0x1B]
def csiB : Bytes := [0x1B, 0x5B]

/-- Decimal, most significant digit first (`0` → `"0"`). Our own, so
the ladder can prove every emitted digit is in `0x30…0x39`. -/
def digits (n : Nat) : Bytes :=
  if n < 10 then [UInt8.ofNat (0x30 + n)]
  else digits (n / 10) ++ [UInt8.ofNat (0x30 + n % 10)]
termination_by n
decreasing_by omega

/-- A codepoint safe to emit inside a repaint or an OSC payload: never a
C0 control or DEL (which the parser would execute rather than print).
Cells can legitimately hold such a codepoint — an overlong UTF-8
sequence decodes to one — so the guard is on the emit side, where it
needs no hypothesis about the state. -/
def safeChar (c : Char) : Char :=
  if c.toNat < 0x20 || c.toNat == 0x7F then '\uFFFD' else c

/-- UTF-8 encode one codepoint. Ours rather than `String.toUTF8` so the
bytes are visible to the kernel and to proofs. The `min` is a local
clamp for provability (the AGENTS.md idiom): it is the identity on every
`Char` — scalar values are ≤ 0x10FFFF — and it makes each emitted byte's
range an arithmetic fact rather than a `Char.valid` derivation. -/
def utf8 (c : Char) : Bytes :=
  let n := min c.toNat 0x10FFFF
  if n < 0x80 then [UInt8.ofNat n]
  else if n < 0x800 then
    [UInt8.ofNat (0xC0 + n / 64), UInt8.ofNat (0x80 + n % 64)]
  else if n < 0x10000 then
    [UInt8.ofNat (0xE0 + n / 4096), UInt8.ofNat (0x80 + n / 64 % 64),
     UInt8.ofNat (0x80 + n % 64)]
  else
    [UInt8.ofNat (0xF0 + n / 262144), UInt8.ofNat (0x80 + n / 4096 % 64),
     UInt8.ofNat (0x80 + n / 64 % 64), UInt8.ofNat (0x80 + n % 64)]

/-- Encode a char list, control codepoints neutralized. -/
def utf8s (cs : List Char) : Bytes := cs.flatMap (fun c => utf8 (safeChar c))

/-- `CSI <n> <final>`. -/
def csiNum (n : Nat) (final : UInt8) : Bytes := csiB ++ digits n ++ [final]

/-- `CSI <a> ; <b> <final>`. -/
def csiNum2 (a b : Nat) (final : UInt8) : Bytes :=
  csiB ++ digits a ++ [0x3B] ++ digits b ++ [final]

/-- `CSI ? <n> <final>` (private mode set/reset). -/
def csiPriv (n : Nat) (final : UInt8) : Bytes :=
  csiB ++ [0x3F] ++ digits n ++ [final]

/-- `CSI <final>` with no parameters, so the receiver applies its own
defaults. Used for `DECSTBM` (`CSI r`), whose defaults are exactly "the
whole screen" — which is the one scroll region we can name without
knowing the receiver's height. -/
def csiPlain (final : UInt8) : Bytes := csiB ++ [final]

/-- A two-byte `ESC <final>` sequence (DECSC, HTS, app-keypad…). Named so
its bytes stay one syntactic unit: `a ++ escB ++ [b]` would associate as
`(a ++ escB) ++ [b]` and split the sequence in two. -/
def escSeq (final : UInt8) : Bytes := escB ++ [final]

/-- A charset designation, `ESC ( x` / `ESC ) x`. -/
def escCharset (i x : UInt8) : Bytes := escB ++ [i, x]

/-! ## Pen -/

/-- One colour as SGR parameter *numbers* (16-colour, 256-colour and
truecolour forms). Numbers rather than bytes, so the same list can be
emitted either as its own sequence or joined into a longer one. -/
def colorCodes (c : Color) (isFg : Bool) : List Nat :=
  match c with
  | .default => []
  | .idx i =>
    let n := i.toNat
    if n < 8 then [(if isFg then 30 else 40) + n]
    else if n < 16 then [(if isFg then 90 else 100) + n - 8]
    else [if isFg then 38 else 48, 5, n]
  | .rgb r g b => [if isFg then 38 else 48, 2, r.toNat, g.toNat, b.toNat]

/-- The attribute half of a pen, as parameter numbers. Leads with `0`, so
the sequence starts from a clean slate: we diff by "pen changed at all",
not per attribute. -/
def penAttrCodes (p : Pen) : List Nat :=
  0 :: ((if p.bold then [1] else []) ++ (if p.dim then [2] else [])
    ++ (if p.italic then [3] else []) ++ (if p.underline then [4] else [])
    ++ (if p.blink then [5] else []) ++ (if p.reverse then [7] else [])
    ++ (if p.strike then [9] else []))

/-- `<n1>;<n2>;…` — parameters joined by `;`, with no leading separator (a
leading `;` would mean an empty first parameter, which SGR reads as a
*reset*). -/
def joinSemi : List Nat → Bytes
  | [] => []
  | [n] => digits n
  | n :: ns => digits n ++ [0x3B] ++ joinSemi ns

/-- `CSI <codes> m`. -/
def sgrOf (codes : List Nat) : Bytes := csiB ++ joinSemi codes ++ [0x6D]

/-- A colour as its own SGR, or nothing when the colour is the default —
`CSI m` with no parameters is a *reset*, which would wipe the attributes
the previous sequence just set. -/
def sgrColorSeq (c : Color) (isFg : Bool) : Bytes :=
  match colorCodes c isFg with
  | [] => []
  | codes => sgrOf codes

/-- SGR for a pen, as up to three sequences: attributes, then foreground,
then background.

**Why three and not one.** The parser honours at most 16 parameters and
sets `ignore` on the 17th, dropping the whole sequence. A single combined
SGR for a pen with all seven attributes and truecolour foreground *and*
background carries 18 (`0` + 7 + 5 + 5), so such a pen replayed as one
sequence comes back **entirely default** — every attribute and both
colours lost. That pen is reachable: an application sets attributes and
colours in separate SGRs, and nothing merges them.

Split this way each sequence carries at most 8, and no colour triplet can
straddle a boundary. Found by proving §Replay, not by testing (the
`heavyPen` fixture in `Tests/Render.lean` now pins it). -/
def penSgr (p : Pen) : Bytes :=
  sgrOf (penAttrCodes p) ++ sgrColorSeq p.fg true ++ sgrColorSeq p.bg false

/-! ## Grid -/

def cellText (c : Cell) : Bytes := utf8 (safeChar c.base) ++ utf8s c.marks

/-- One cell's slot in the row painter's fold, over
`(bytes so far, the pen already in effect, the next cell index)`.

A width-0 cell is the shadow of the wide char to its left: for a grid the
emulator produced it paints nothing, because `Vt.printMark` keeps marks off
shadows and `Row.mend` canonicalizes them, so a repaint of the base re-creates
it (`Vt.Cell.shadow`). The branch still emits any marks it finds there, which is
dead code for a live grid and the defensive path for a decoded checkpoint, whose
rows carry no such guarantee.

A wide cell's **own** marks need the cursor parked *between* the glyph and
its shadow, or they attach to the shadow instead: `print` puts a mark at
`cursor.x - 1`, and a 2-column advance leaves the cursor two past the glyph
(§Replay fix 8). `CHA` puts it there by absolute column, which is why the fold
carries the column.

The fold's column is a **cell index**, so every cell advances it by one. A
width-2 base advancing it by two double-counted the pair — its shadow advances
it as well — and the emitted `CHA` for the *second* marked wide glyph in a row
then addressed one column too far right, which drifted the rest of the row and
wrapped its last cell into a spurious line feed that scrolled the whole grid.
Latent until marks were normalized onto the base (`Vt.print`), which is what
made this branch fire for an ordinary `漢` plus a combining mark; the fuzzer
found it in the same pass.

Named rather than left as a lambda inside `rowAnsi`, for the reason `modeSet`
gives above: the row-replay theorem has to *mention* the fold body in its own
statement, which is impossible for a lambda, and each branch is then reached by
`rw` on a named equation instead of by reducing a four-way beta-redex per
cell. -/
def rowSlot (acc : Bytes × Pen × Nat) (c : Cell) : Bytes × Pen × Nat :=
  let (s, pen, x) := acc
  if c.width == 0 then (s ++ utf8s c.marks, pen, x + 1)
  else
    let s := if c.pen == pen then s else s ++ penSgr c.pen
    let body :=
      if c.width == 2 && !c.marks.isEmpty then
        utf8 (safeChar c.base) ++ csiNum (x + 2) 0x47 ++ utf8s c.marks
          ++ csiNum (x + 3) 0x47
      else cellText c
    (s ++ body, c.pen, x + 1)

/-- One row as SGR-colored bytes: `rowSlot` folded over the cells, keeping the
bytes and the pen the row leaves in effect. -/
def rowAnsi (row : Row) (startPen : Pen) : Bytes × Pen :=
  let (bs, pen, _) := row.foldl rowSlot ([], startPen, 0)
  (bs, pen)

/-- Join painted rows with CR+LF, no trailing separator (a trailing
CRLF on the last row would scroll the screen). -/
def joinCRLF : List Bytes → Bytes
  | [] => []
  | [b] => b
  | b :: bs => b ++ [0x0D, 0x0A] ++ joinCRLF bs

/-- Paint a full grid: reset the pen, home, then each row.

The leading `CSI 0 m` is load-bearing, not decoration. The fold below seeds
its "pen already in effect" accumulator with the *default* pen, and
`rowAnsi` emits an `SGR` only when a cell's pen differs from that — so a
leading run of default-pen cells emits no `SGR` at all and inherits whatever
pen the terminal happened to be carrying. `screensAnsi` is exactly such a
caller: it sets the stashed main pen immediately before painting the alt
grid, and without this reset the whole leading run of the alt screen came
back in that pen (§Replay fix 9). Establishing the assumption here rather
than trusting each call site is what makes `gridAnsi` self-contained. -/
def gridAnsi (grid : Array Row) : Bytes :=
  let (rows, _) := grid.foldl
    (fun (acc : List Bytes × Pen) row =>
      let (line, pen') := rowAnsi row acc.2
      (acc.1 ++ [line], pen'))
    (([], ({} : Pen)))
  csiNum 0 0x6D ++ (csiB ++ [0x48] ++ joinCRLF rows)

/-! ## Modes -/

/-- One DEC private mode, set **or** reset. Named rather than a local lambda so
that a mode-replay proof matches it structurally instead of reducing a beta-redex
per mode — with a dozen modes the difference is a heartbeat timeout. -/
def modeSet (n : Nat) (on : Bool) : Bytes := csiPriv n (if on then 0x68 else 0x6C)

/-! ## Scrollback

The session's ring, painted into the **receiver's own** scrollback buffer, so
wheel-scroll, search and selection find the history above the screen.

There is exactly one way to put a line into a terminal's native scrollback:
print it inside a whole-screen scroll region and let it scroll off. So the ring
is painted and then pushed — and that push is its own stage, emitted *before*
the screen paint, never fused with it. Painting `sbRows v ++ v.grid` as one tall
array makes the painted-row count exceed the screen height, which deletes
`paint_rows`' no-scroll argument and with it the whole screen-fidelity ladder
(`restore_grid_any`, `Resume.resume_grid`). Staged, the screen paint is
byte-for-byte what it was.

**Text rows only**, named so it is a decision and not a side effect: a sixel or
kitty placement that was in the ring stays gone, consistent with the settled
non-goal on images (AGENTS.md). -/

/-- One CR+LF, as one syntactic unit: the flush is `List.replicate v.rows crlfB`
flattened, and a proof has to name the pushing pair rather than rediscover it
inside a literal. CR **then** LF, which is also why a full-width row does not
push twice — `carriageReturn` clears the wrap-pending flag the last glyph set. -/
def crlfB : Bytes := [0x0D, 0x0A]

/-- A cell as a repaint can reproduce it. Every clause is one field of
`CellOk` (`Theorems/Vt.lean`), so `cellOk_cellFit` needs no hypothesis — which
is the whole point: `sb` rows are the one place in a `Vt` that no stated
invariant covers (`Vt.resize` re-fits the grid and leaves the ring alone), and a
decoded checkpoint's ring is arbitrary bytes' worth of cells.

**The width-0 branch is load-bearing.** A shadow must stay a shadow: collapsing
it to `charWidth ' ' = 1` would shift every pair after it one column left. Same
discipline as `Vt.printableChar` on store, one field further out. -/
def cellFit (c : Cell) : Cell :=
  let base := printableChar c.base
  { base := base,
    width := if c.width == 0 then 0 else charWidth base,
    marks := (c.marks.filter (fun m => charWidth m == 0 && printableChar m == m)).take 8,
    pen := c.pen }

/-- A ring row at the session's width, reproducible unconditionally.

**Not** `Vt.resizeRow`: that copies cells verbatim, so its `RowOk` carries a
`∀ x, CellOk (row.at x)` hypothesis — and the ring is exactly where that
hypothesis is unavailable. `Row.mend` then repairs the pair a truncation can
halve. -/
def fitRow (row : Row) (cols : Nat) : Row :=
  Row.mend ((Array.range cols).map (fun i => cellFit (row.at i)))

/-- The replay budget, as a bound on Σ `sbRowCost` — **not** on emitted bytes.
The emitted stage is bounded by `sbReplayBytes + 2 * v.rows + 19` and does
exceed `sbReplayBytes` by up to that much: measured 262,153 bytes for a full
80×24 ring whose rows each end in a truecolour cell (the 19 is `ED 3` + the
paint's `SGR 0`/`CUP` + the mode tail, less the per-row CRLF credit the
separators do not use).

A row cap would bound nothing that matters. `Cell.erased` emits one space and no
SGR, so a blank 80-column row costs 86 counted (82 emitted); per-cell truecolour
costs 40 bytes a column, 57 with all seven attributes. A full `sbCap = 10000`
ring is therefore 32–46 MB at 80 columns and ~86 MB at 150 — against an
`outbufCap` of 4 MiB that **disconnects** the client (`Linger/Runtime/Daemon.lean`).
Without a byte budget, attach becomes attach-then-instant-drop.

262144 admits 3,048 blank 80-column rows, or 2,383 of a realistic mixed row —
still more than tmux's default 2000-line history. The binding constraint is time
on a slow link (256 KiB over 1 MB/s ssh is a quarter-second stall on every
attach); that has not been measured over a real ssh path, and 131072 is the
safer number if attach latency wins. -/
def sbReplayBytes : Nat := 262144

/-- What one replayed row costs the budget: its paint from the **default** pen,
plus `+2` for the CRLF that pushes it and `+4` for the one `SGR 0` a row can
emit that a default-seeded count does not.

The `+4` is exact and attained, and the reason is not the fit: a width-0 cell
leaves `rowSlot`'s pen accumulator untouched, so the default-seeded fold and the
fold from an arbitrary incoming pen diverge only at the first non-shadow cell
and agree from that cell on. The excess is therefore one optional `SGR`, and the
only shape where the default-seeded fold emits nothing while the other emits is
"that cell's pen is the default", costing exactly `penSgr {}` = 4 bytes
(`rowAnsi_len_seed`, `rowAnsi_len_le_cost`; witness: a blank 80-column row is 80
bytes from the default pen and 84 from a truecolour one). -/
def sbRowCost (row : Row) : Nat := (rowAnsi row {}).1.length + 6

/-- The rows a budget admits, newest first, each fitted to `cols`.

Structural on the list with the fit **fused in**, so the per-cell work touches
only the rows kept. It **stops** at the first row that does not fit rather than
skipping it, so the result is always "the newest N lines" — a contiguous run
(`sbTake_prefix`), which is what licenses "the oldest are dropped first" in the
docs. -/
def sbTake (cols budget : Nat) : List Row → List Row
  | [] => []
  | r :: rs =>
    let f := fitRow r cols
    let c := sbRowCost f
    if c ≤ budget then f :: sbTake cols (budget - c) rs else []

/-- The session's history as the receiver will be given it: oldest first, each
row at the session's width, trimmed from the **oldest** end to `sbReplayBytes`.

`Ring.toList` is oldest-first and oldest-first is the push order, so the budget
walk — which has to start from the newest — runs on the reverse and the result is
reversed back. Both reverses are load-bearing and in opposite ways: dropping the
outer one plays the history backwards, and feeding `v.sb.toList` instead of its
reverse keeps the **oldest** N under a tight budget instead of the newest. -/
def sbRows (v : Vt) : Array Row :=
  (sbTake v.cols sbReplayBytes v.sb.toList.reverse).reverse.toArray

/-- **The history push.** Paint the fitted ring, then scroll it off the top with
`v.rows` CRLFs.

`gridAnsi (sbRows v)` homes and paints `m` rows with `m-1` separators; `v.rows`
further CRLFs push exactly `m` of them into the receiver's ring (pushes
`= C - (rows - 1)` where `C = (m-1) + rows`). `F = v.rows` is not merely
sufficient, it is the **unique** correct count — swept over every
`rows, m ∈ 1…8`, 64 of 64 cells admit exactly one `F`, always `rows`. No `min`
and no special case: for `m < rows` the surplus CRLFs are absorbed by the
non-pushing descent (`cursor.y < bot`), so zero blank rows are pushed, and for
`m > rows` the paint itself pushes and the total is still `m`.

Afterwards the receiver's screen is **fully blank** and the cursor is at `(0,0)`
— `?6l` (DECOM reset) homes it — and every one of those blank cells carries the
pen the ring paint left in effect (`scrollUpIn` vacates with
`blankRow cols v.pen`). Harmless only because the screen paint that follows is
`gridAnsi v.grid`, which leads with `CSI 0 m` and rewrites every column.

`ED 3` (erase-saved-lines) is what stops a second attach stacking a second copy
of the ring. It is **guarded by the same emptiness test as the paint**, and that
guard is a user-facing decision, not an optimization: linger never enters the alt
screen, so the session shares the user's own terminal scrollback — an
unconditional `ED 3` would discard the history of any window a session is
attached in, including the common case of a session with no history to put there.
Guarded, the anti-stacking property is untouched (nothing is pushed when the ring
is empty, so nothing can stack) and the price is stated where it belongs: what
`restore` promises about a receiver's ring is two branches, not one. See
README §Notes and THEOREMS.md's conformance-profile entry 11.

The trailing `4l ?6l ?7h` re-establish what `paint_entry` needs — `insert`,
`wrap`, `origin` — and are **proof-load-bearing ordering**, not cosmetics: an
`MMap` cannot be pushed across the ring's glyph bytes (there is no
`mmap_id_gridAnsi`; `Modes.lean` explains the asymmetry), so the obligation has
to be moved to a chunk where `mmap_irm`/`mmap_modeSet` close it. They must stay
ESC-leading and contiguous at the end, and they buy `u8need = 0` for free through
`abortUtf8`. Behaviourally they are inert in every fixture — which is why their
break-verification is a proof break, never a test. -/
def scrollbackAnsi (v : Vt) : Bytes :=
  (if (sbRows v).isEmpty then []
   else csiNum 3 0x4A ++ gridAnsi (sbRows v) ++ (List.replicate v.rows crlfB).flatten)
    ++ csiNum 4 0x6C ++ modeSet 6 false ++ modeSet 7 true


/-- **Put the receiver in a known state before painting.**

`restore` is fed to a client terminal in whatever state its previous occupant
left it — `Session.onMsg` sends it on attach with nothing before it — so every
mode the repaint depends on has to be established rather than assumed. Each line
below is a hazard that was previously latent:

* `?1049l` — if the client sits on the alt screen, the main-grid repaint would
  land there and `screensAnsi`'s own `?1049h` would then be a no-op, so the main
  screen would never be painted;
* `4l` (IRM) — insert mode shifts the row right at every glyph, so the paint
  would smear;
* `?6l` (DECOM) — under origin mode `CSI H` homes to the region top, not row 0,
  and every absolute address in the stream is reinterpreted;
* `?7h` (DECAWM) — wrap must be **on**: `Vt.printMark` reads wrap-pending to
  attach a combining mark to the margin cell it just wrote (see SCRATCHPAD
  2026-08-15, and the note on `restoreBody`);
* `1;rows r` — a leftover scroll region turns the repaint's line feeds into
  scrolls. Degenerate for one row, where `DECSTBM` is a no-op and the region is
  already whole;
* `(B`, `)B`, `SI` — a leftover DEC line-drawing charset would translate the
  ASCII the painter emits into box glyphs.

It **leads** with `ESC \\` (ST), because a receiver's parser state is part of the
state being assumed. A client caught mid-OSC or mid-DCS swallows every byte until its
terminator — `Vt.stepOsc` accumulates our `ESC` and then our `[`, so the whole restore
stream would vanish into a window title. `ST` closes both, and from any other state
(`ground`, `esc`, `escInter`, `csi`) it lands in `ground` with nothing written that
the `ED 2` two lines later does not erase.

`charsetAnsi` re-emits the charset state afterwards, since the session's own
value may differ from the ASCII default this establishes. -/
def prologueAnsi (v : Vt) : Bytes :=
  escSeq 0x5C
    ++ modeSet 1049 false
    ++ csiNum 4 0x6C
    ++ modeSet 6 false
    ++ modeSet 7 true
    ++ csiNum2 1 v.rows 0x72
    ++ escCharset 0x28 0x42 ++ escCharset 0x29 0x42 ++ [0x0F]

/-- Mode replay: what a fresh terminal must be told so the application
keeps working after reattach. DECOM and IRM are included (§Replay
fix 4): origin mode changes how the final cursor address must be
computed, and insert mode would corrupt the *next* app output if lost.
Emitted after the repaint (insert mode during the repaint would shift
cells) and before the final cursor (setting DECOM homes the cursor).

Every mode is emitted **both ways**. A mode that is only ever *set* leaks the
client's previous state: attaching a session with the mouse off to a terminal that
a crashed program left reporting leaves the mouse on, and the same held for IRM,
DECOM, bracketed paste, focus events, SGR mouse, application cursor and keypad.
`prologueAnsi` already neutralizes the subset that would corrupt the *paint*; this
is the same discipline for the ones that only affect what happens afterwards.

The mouse guard is an **allowlist**, not a denylist, and that is the whole point.
`setMode` only ever stores 1000/1002/1003 in that field, but a `Vt` does not only
come from `setMode`: `Checkpoint.load` reads `mouse` as an arbitrary `Nat` and is
deliberately total on arbitrary bytes, so a corrupt or foreign checkpoint can put
anything there — and this line replays it verbatim. A denylist got the first case
right and the rest wrong: `!= 6` was there because private mode 6 is DECOM, so
replaying a `mouse` of 6 would silently turn origin mode on (§Replay's
`quiet_modesAnsi`), but 47, 1047 and 1049 **switch screens**, which would corrupt
the very grid the restore is rebuilding. Naming the three modes the emulator can
legitimately hold closes both holes at once and cannot grow a third.

The alternative was a reachability invariant on `Vt`; one guarded emit is still
cheaper than a field every constructor must maintain.

Every mode is emitted **both ways**. A mode that is only ever *set* leaks the
client's previous state: attaching a session with the mouse off to a terminal that
a crashed program left reporting leaves the mouse on, and the same held for IRM,
DECOM, bracketed paste, focus events, SGR mouse, application cursor and keypad.
The three mouse modes are mutually exclusive, so all three are cleared before the
live one is set. `prologueAnsi` already neutralizes the subset that would corrupt
the *paint*; this is the same discipline for the ones that only affect what the
application does afterwards. -/
def modesAnsi (v : Vt) : Bytes :=
  modeSet 7 v.modes.wrap
    ++ modeSet 1 v.modes.appCursor
    ++ (if v.modes.appKeypad then escSeq 0x3D else escSeq 0x3E)
    ++ modeSet 25 v.modes.cursorVisible
    ++ modeSet 2004 v.modes.bracketedPaste
    ++ modeSet 1000 false ++ modeSet 1002 false ++ modeSet 1003 false
    ++ (if v.modes.mouse == 1000 || v.modes.mouse == 1002 || v.modes.mouse == 1003
        then modeSet v.modes.mouse true else [])
    ++ modeSet 1006 v.modes.mouseSgr
    ++ modeSet 1004 v.modes.focusEvents
    ++ modeSet 6 v.modes.origin
    ++ csiNum 4 (if v.modes.insert then 0x68 else 0x6C)

/-! ## Restore

Named stages throughout, so §Replay can discharge one at a time and the
top theorem is their composition (`Theorems/Render.lean`).
-/

/-- The history, then the two screens: in alt, paint main, park the stashed
cursor/pen, switch, then paint alt (§Replay fix 7).

`scrollbackAnsi` goes here rather than being a new top-level stage in
`restoreBody` because `screensAnsi v` is what the ladder names *opaquely*:
`restore_split`, `restore_grid_of_paint` and `restore_tabs_split` all quote it as
an atom, so this placement costs five `unfold screensAnsi` repairs instead of
fifty-five rewrites of the `prologueAnsi v ++ csiNum 0 0x6D` prefix. It also
means the flush's evicted rows are the blanks the preceding `ED 2` left rather
than the receiver's junk.

Emitted **identically on both screens**, and before the discarded main paint:
`Vt.sb` is main-screen-only (`scrollUpIn` pushes only when `altGrid.isNone`), the
alt grid is a fresh blank with no history of its own, and a branch-dependent
stage here would make the two `restore_grid_any_*` statements diverge. -/
def screensAnsi (v : Vt) : Bytes :=
  scrollbackAnsi v ++
    match v.altGrid with
    | none => gridAnsi v.grid
    | some (mainGrid, mcur, mpen) =>
      gridAnsi mainGrid
        ++ penSgr mpen ++ csiNum2 (mcur.y + 1) (mcur.x + 1) 0x48
        ++ csiPriv 1049 0x68 ++ gridAnsi v.grid

/-- Scroll region, when it is not the whole screen. -/
def regionAnsi (v : Vt) : Bytes :=
  if v.top == 0 && v.bot == v.rows - 1 then []
  else csiNum2 (v.top + 1) (v.bot + 1) 0x72

/-- **The tab ruler, emitted unconditionally**: `CSI 3 g` clears every stop, then
one `HTS` per stop the session holds.

This used to skip the whole thing when the session's ruler was the default, on the
theory that "the default is what a reset terminal has". That is the set-only
mistake `87f64b3` fixed in `modesAnsi`, one field later — a client is **not** a
reset terminal. Its previous occupant may have run `CSI 3 g` and set its own stops,
and nothing else in a restore stream clears a tab stop: the prologue has no `TBC`,
`ED 2` does not touch the ruler, and linger emits no `RIS` anywhere. So the
previous occupant's ruler survived verbatim and a `\t` from the session landed on
the wrong column. Reproduced against `Tests/Render.lean`'s own `replayEq` before
the fix (a receiver whose ruler was re-set every four columns made
`roundtripsFrom` false on `.tabs`) and pinned by the `dirtyTabs` fixture there; it
had passed only because no fixture moved the *receiver's* ruler.

Being unconditional costs one `CSI 3 g` plus a `CHA`+`HTS` pair per stop on every
attach — nine stops and ~70 bytes for an 80-column default ruler. The alternative
is a field that is only right when the client happens to be pristine, which is the
one thing `specs/restore-conformance.md` says a client never is. The `CHA`s move
the cursor, which is safe here because `savedAnsi` and `cursorAnsi` both address it
absolutely afterwards. -/
def tabsAnsi (v : Vt) : Bytes :=
  csiNum 3 0x67 ++ (((List.range v.cols).filter (fun i => v.tabs.getD i false)).flatMap
    (fun i => csiNum (i + 1) 0x47 ++ escSeq 0x48))

/-- Replay the DECSC slot (§Replay fix 3). -/
def savedAnsi (v : Vt) : Bytes :=
  penSgr v.saved.pen
    ++ csiNum2 (v.saved.cur.y + 1) (v.saved.cur.x + 1) 0x48 ++ escSeq 0x37

/-- Charset designations and the shift state (§Replay fix 2). -/
def charsetAnsi (v : Vt) : Bytes :=
  (if v.g0Line then escCharset 0x28 0x30 else escCharset 0x28 0x42)
    ++ (if v.g1Line then escCharset 0x29 0x30 else escCharset 0x29 0x42)
    ++ (if v.shiftOut then [0x0E] else [])

/-- Window title as an OSC 2, BEL-terminated. The payload is scrubbed
(`utf8s`), so it can contain neither ESC nor BEL and cannot terminate or
extend its own sequence.

Emitted **unconditionally**, including with an empty payload: skipping it for an empty
title was the same set-only bug as the modes had, leaving the client showing whatever
its previous occupant set. An empty OSC 2 clears it. -/
def titleAnsi (v : Vt) : Bytes :=
  escB ++ [0x5D, 0x32, 0x3B] ++ utf8s v.title.toList ++ [0x07]

/-- Final cursor placement — region-relative under DECOM (§Replay fix 5).
`restore` ends with this, which is also what makes the parser provably
quiesced: it is ESC-initiated, and ESC clears any pending UTF-8. -/
def cursorAnsi (v : Vt) : Bytes :=
  if v.modes.origin then csiNum2 (v.cursor.y - v.top + 1) (v.cursor.x + 1) 0x48
  else csiNum2 (v.cursor.y + 1) (v.cursor.x + 1) 0x48

/-- Everything a re-attaching client's terminal needs except the final
cursor placement. Emission order is load-bearing — each comment names
the §Replay constraint (specs/archive/bigger-theorems.md):

1. repaint before modes (IRM would shift cells; charset would
   re-translate ASCII glyphs);
2. in alt, park the stash cursor/pen *before* `?1049h` — the switch is
   what stashes them, so painting first and switching after would stash
   wherever the main repaint happened to end (fix 7);
3. the saved-cursor replay comes *after* the alt switch (which
   clobbers `saved`) and *before* DECOM is set (its address is
   absolute) (fix 3);
4. the final cursor address is region-relative iff DECOM is on (fix 5,
   in `cursorAnsi`).

Autowrap is deliberately **left on** across the repaint. Turning it off looks
attractive — it would delete the wrap-pending branches from the row-replay
induction — but it is wrong: `Vt.printMark` uses `cursor.pending` to tell
"parked on the margin cell just written" from "positioned before writing it",
and with wrap off both look identical, so a combining mark in the final column
attaches one cell to the left. Two fuzz seeds catch it (see SCRATCHPAD,
2026-08-15). The pending flag is load-bearing, and the replay proof has to
model it rather than legislate it away. -/
def restoreBody (v : Vt) : Bytes :=
  prologueAnsi v                          -- establish the receiver's state
    ++ csiNum 0 0x6D ++ csiNum 2 0x4A     -- clean slate
    ++ screensAnsi v
    ++ regionAnsi v
    ++ tabsAnsi v
    ++ savedAnsi v
    ++ titleAnsi v
    ++ modesAnsi v
    ++ charsetAnsi v
    ++ penSgr v.pen

/-- The reattach byte stream. -/
def restore (v : Vt) : Bytes := restoreBody v ++ cursorAnsi v

/-! ## Leave -/

/-- **Hand the terminal back.** The bytes a detaching client writes to the
user's terminal before it goes.

`prologueAnsi` exists because a *client* is whatever its previous occupant left
behind. The mirror image was unhandled: the user's **shell** is whatever the
*session* left behind. A client that only restores termios (which is the kernel's
line discipline, not the terminal's state) hands back a terminal still holding
whatever the session's last program set — and detaching out of a full-screen
application is the ordinary way to leave, not an edge case. Measured before this
existed (SCRATCHPAD 2026-08-15): after `printf` of a full-screen app's opening
sequences and `ctrl-\`, the shell was left on the alt screen, with mouse
reporting on, the cursor hidden, bracketed paste on, autowrap off, a six-line
scroll region, DEC line drawing selected (every ASCII character rendered as a box
glyph) and a bold red pen.

So this is the same discipline as the prologue, pointed the other way, and it is
a **constant**: what linger hands back does not depend on what the session was
doing. Each line is a hazard for the next program to use the terminal:

* `ESC \` (ST) — a program that died mid-OSC/DCS (a crashed sixel writer, a
  truncated title) leaves the parser in a string state that would swallow this
  entire stream, exactly as it swallowed `restore` before `cd7c17b`;
* `?1049l` — leave the alt screen, which also hands back the screen the terminal
  itself saved when the application switched;
* `4l` (IRM), `?6l` (DECOM), `?7h` (DECAWM), `CSI r` (DECSTBM) — a shell that
  inserts instead of overwriting, addresses relative to a stale region, does not
  wrap, or scrolls inside six lines;
* `?25h`, `?2004l`, the three mouse modes, `?1006l`, `?1004l` — a cursor you
  cannot see, pastes arriving wrapped in `ESC [ 200 ~`, and clicks or window
  focus changes arriving as garbage on the shell's command line;
* `?1l` (DECCKM), `ESC >` (DECKPNM) — arrow and keypad keys sending application
  forms the shell's line editor does not bind;
* `( B`, `) B`, `SI` — line-drawing ASCII;
* `SGR 0` — a coloured prompt.

Two positions are deliberate. `DECOM` reset and `DECSTBM` both home the cursor
(here and on real terminals), so the cursor **must** be placed afterwards rather
than preserved: `CSI 999 ; 1 H` parks it at the bottom-left — clamped by the
receiver, so it needs no size — which is where a program that painted the screen
and exited leaves the next prompt. And `SGR 0` comes last, since `DECSTBM` and
the mode resets do not touch the pen but a receiver's `DECRC`-like bundling
might.

What is **not** here, deliberately: the window title. `titleAnsi` set it on
attach, so linger is not fully invisible until it is put back, but we never read
the user's title and the emitter does not guess. xterm's title stack
(`CSI 22 ; 0 t` / `CSI 23 ; 0 t`) would do it and is not universal; recorded as a
known limit rather than a silent one.

Not `DECSTR` (`CSI ! p`), for the reason already recorded in
`specs/restore-conformance.md`: its reset list varies by terminal, and we would
be trusting bytes we do not parse. -/
def leaveAnsi : Bytes :=
  escSeq 0x5C
    ++ modeSet 1049 false
    ++ csiNum 4 0x6C
    ++ modeSet 25 true
    ++ modeSet 2004 false
    ++ modeSet 1000 false ++ modeSet 1002 false ++ modeSet 1003 false
    ++ modeSet 1006 false ++ modeSet 1004 false
    ++ modeSet 1 false ++ escSeq 0x3E
    ++ modeSet 6 false
    ++ modeSet 7 true
    ++ csiPlain 0x72
    ++ escCharset 0x28 0x42 ++ escCharset 0x29 0x42 ++ [0x0F]
    ++ csiNum2 999 1 0x48
    ++ csiNum 0 0x6D

/-! ## History (text) -/

/-- One row's characters, width-0 shadows skipped, every codepoint scrubbed. A named
stage so the trim and the encoding are separate steps a lemma can talk about. -/
def rowChars (row : Row) : List Char :=
  row.foldl
    (fun (acc : List Char) c =>
      if c.width == 0 then acc
      else acc ++ [safeChar c.base] ++ c.marks.map safeChar) []

/-- Drop trailing blanks. On the character list rather than on the bytes, though the
two agree: no byte of a multi-byte UTF-8 sequence is `0x20`. -/
def dropTrailingBlanks (cs : List Char) : List Char :=
  (cs.reverse.dropWhile (· == ' ')).reverse

/-- Row as plain text bytes (no SGR), trailing blanks trimmed.

This used to build a `String` — `(s.dropEndWhile (· == ' ')).toString` over a fold of
`String` appends — and it was the last thing in this module that did. That is the shape
the header above says makes output unprovable: a `String` does not reduce in the kernel,
so no theorem could see the bytes `linger history` writes to a terminal. Byte-level now,
so `history_framing` and `history_lines` can say that a cell cannot inject a line
break. -/
def rowText (row : Row) : Bytes := utf8s (dropTrailingBlanks (rowChars row))

/-- Scrollback + screen, oldest first; for `linger history`.

The plain branch emits one `LF`-terminated line per row. It was
`String.intercalate "\n" (rows.map rowText) ++ "\n"`, which agrees with this for every
reachable state and differs only when there are *no* rows at all: the old shape emitted a
lone newline, this emits nothing. A grid always has at least one row (`clampDim`), so the
difference is unreachable for a live session and is the more honest output for a decoded
one. -/
def history (v : Vt) (withAnsi : Bool) : Bytes :=
  let rows := v.sb.toList ++ v.grid.toList
  if withAnsi then
    let (body, _) := rows.foldl
      (fun (acc : Bytes × Pen) row =>
        let (line, pen') := rowAnsi row acc.2
        (acc.1 ++ line ++ [0x0A], pen'))
      ([], ({} : Pen))
    body
  else
    rows.flatMap (fun row => rowText row ++ [0x0A])

end Linger.Core.Render
