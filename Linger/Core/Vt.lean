module

public section

/-! # Linger.Core.Vt — restore-grade terminal emulation, pure

The daemon feeds every pty byte here (a passive observer, zmx-style:
clients get the raw bytes; this state exists so a *re*-attaching client
can be shown what it missed, and so `linger history` can dump it).

Design for the theorems (see THEOREMS.md):
* §Total — everything is one byte-at-a-time `step : Vt → UInt8 → Vt`
  built from total operations (`getD`/`setIfInBounds`/`min`/clamps);
  `feed = List.foldl step` — no `partial`, no panic path.
* §Chunk — `feed` over a `foldl` is chunking-invariant by
  `List.foldl_append`, definitionally.
* §Bound — every unbounded-looking thing has a structural cap: parser
  params (≤ 16, each ≤ 65535), OSC accumulator (≤ 2048 bytes), UTF-8
  pending (≤ 3), scrollback ring (≤ `sbCap`), grid (rows·cols from
  resize, clamped to 1000). Nothing grows with uptime.

Deliberate simplifications (restore-grade, not vt520-certified), each
chosen because zmx delegates live rendering to the real terminal:
* no reply channel: DA/DSR/CPR queries are ignored (when a client is
  attached the real terminal answers; detached, nobody should).
* resize truncates/pads rather than reflowing.
* OSC 8 hyperlinks, sixel, kitty graphics: skipped as strings, not
  stored.
* modes stored but not interpreted beyond the emulator's needs
  (bracketed paste, mouse, kitty keyboard flags) — the runtime replays
  them to a re-attaching client so applications keep working.
-/

namespace Linger.Core.Vt

/-! ## Pen, color, cell -/

inductive Color where
  | default
  | idx (i : UInt8)
  | rgb (r g b : UInt8)
  deriving Repr, DecidableEq, Inhabited

structure Pen where
  fg : Color := .default
  bg : Color := .default
  bold : Bool := false
  dim : Bool := false
  italic : Bool := false
  underline : Bool := false
  blink : Bool := false
  reverse : Bool := false
  strike : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- One grid cell. `width` is 1 (normal), 2 (leading cell of a wide
character), or 0 (continuation cell shadowed by a wide char to its
left). `marks` carries combining characters (usually empty). -/
structure Cell where
  base : Char := ' '
  marks : List Char := []
  width : Nat := 1
  pen : Pen := {}
  deriving Repr, DecidableEq, Inhabited

/-- An erased cell: blank, but keeps the erasing pen's background
(BCE), which is what makes full-screen apps restore correctly. -/
def Cell.erased (p : Pen) : Cell := { base := ' ', marks := [], width := 1, pen := { bg := p.bg } }

/-! ## Character width (minimal wcwidth)

Three classes: combining/zero-width (0), East-Asian wide + emoji (2),
everything else (1). Ranges cover what real TUI apps emit; a wrong
width here mis-aligns a restore but can never crash anything (§Total
does not depend on this table). -/

def isZeroWidth (c : Nat) : Bool :=
  (0x0300 ≤ c && c ≤ 0x036F) || -- combining diacritics
    (0x1AB0 ≤ c && c ≤ 0x1AFF) ||
    (0x20D0 ≤ c && c ≤ 0x20FF) ||
    (0xFE00 ≤ c && c ≤ 0xFE0F) || -- variation selectors
    (0xFE20 ≤ c && c ≤ 0xFE2F) ||
    c == 0x200B ||
    c == 0x200C ||
    c == 0x200D ||
    c == 0xFEFF

def isWide (c : Nat) : Bool :=
  (0x1100 ≤ c && c ≤ 0x115F) || -- Hangul Jamo leads
    (0x2E80 ≤ c && c ≤ 0x303E) || -- CJK radicals … punctuation
    (0x3041 ≤ c && c ≤ 0x33FF) || -- kana, CJK misc
    (0x3400 ≤ c && c ≤ 0x4DBF) ||
    (0x4E00 ≤ c && c ≤ 0x9FFF) || -- CJK unified
    (0xA000 ≤ c && c ≤ 0xA4CF) ||
    (0xAC00 ≤ c && c ≤ 0xD7A3) || -- Hangul syllables
    (0xF900 ≤ c && c ≤ 0xFAFF) ||
    (0xFE30 ≤ c && c ≤ 0xFE4F) ||
    (0xFF00 ≤ c && c ≤ 0xFF60) || -- fullwidth forms
    (0xFFE0 ≤ c && c ≤ 0xFFE6) ||
    (0x1F300 ≤ c && c ≤ 0x1F64F) || -- emoji
    (0x1F900 ≤ c && c ≤ 0x1F9FF) ||
    (0x20000 ≤ c && c ≤ 0x2FFFD) ||
    (0x30000 ≤ c && c ≤ 0x3FFFD)

def charWidth (c : Char) : Nat := if isZeroWidth c.toNat then 0 else if isWide c.toNat then 2 else 1

/-- The codepoint a cell is allowed to store: a C0 control or DEL becomes
U+FFFD.

A cell holding a control codepoint cannot be repainted — `Render.safeChar`
substitutes U+FFFD on emit, so the replayed screen would differ from the live
one — and such a codepoint is reachable: DEL arrives as itself, and an
overlong UTF-8 sequence decodes to a C0. Substituting **on store** is what
makes every stored cell repaintable, so `Renderable` is an invariant rather
than a hypothesis (the same move as fix 11). `Render.safeChar` stays as the
emit-side guard, which still has work to do for a decoded checkpoint. -/
def printableChar (c : Char) : Char := if c.toNat < 0x20 || c.toNat == 0x7F then '\uFFFD' else c

/-! ## Rows and the scrollback ring -/

abbrev Row := Array Cell

def blankRow (cols : Nat) (p : Pen) : Row := Array.replicate cols (Cell.erased p)

/-- The continuation cell a width-2 base owns: a blank carrying the base's
pen. Exactly what repainting the base re-creates, which is why a shadow may
hold nothing of its own — see `Row.mendAt`. -/
def Cell.shadow (c : Cell) : Cell := { base := ' ', marks := [], width := 0, pen := c.pen }

/-- Total cell read; out of range is a default (width-1) cell. -/
def Row.at (row : Row) (x : Nat) : Cell := row.getD x default

/-- Is the cell at `x` half of a wide pair whose other half is gone? A
width-2 base with no shadow on its right, or a shadow with no base on its
left. Out-of-range reads are width 1, so a base in the final column counts
as broken — fix 11's rule, stated once instead of per operation. -/
def Row.halfPair (row : Row) (x : Nat) : Bool :=
  let c := row.at x
  (c.width == 2 && (row.at (x + 1)).width != 0) ||
    (c.width == 0 && (x == 0 || (row.at (x - 1)).width != 2))

/-- Blank a half pair, keeping its background (BCE); otherwise canonicalize a
whole pair's shadow, so a shadow carries exactly what a repaint of its base
re-creates and nothing of its own. -/
def Row.mendAt (row : Row) (x : Nat) : Row :=
  if row.halfPair x then row.setIfInBounds x (Cell.erased (row.at x).pen)
  else if (row.at x).width == 0 then row.setIfInBounds x (Cell.shadow (row.at (x - 1))) else row

/-- Repair every wide pair in a row, left to right.

Half a wide glyph is not displayable and — the reason this exists — not
*expressible* by `Render.rowAnsi`: a lone width-2 base re-wraps on replay and
a lone width-0 shadow paints nothing while still occupying a column, so the
rest of the row lands one column off. A shadow carrying content of its own is
equally inexpressible, since the painter emits the base and nothing else.
Rather than adding side conditions to the replay theorem, the emulator does not
reach those shapes (fix 11's principle, generalized from printing to every row
mutation).

One pass is enough, in any order: a blank never creates a new half pair.
`mendAt` blanks a column only when its partner is *already* absent — a shadow
whose left neighbour is a width-2 base is left alone, and a base whose right
neighbour is a width-0 shadow is left alone — so the columns it rewrites are
exactly the ones no surviving pair depends on. (Order-independence is measured,
not assumed: sweeping right to left passes every fixture and the whole fuzz
corpus. Left to right is simply the order the proof is stated in.)

Every cell-writing operation ends here, printing included. That is a deliberate
trade: `putCell` reads its row out of the grid, so the row is shared and the
write copies it — printing is already O(cols) — and one more pass over the row
it just copied buys the pair invariant *uniformly*, with no per-operation index
reasoning (`mend_pairOk`). Restructuring for provability rather than weakening
the theorem, per AGENTS.md. -/
def Row.mend (row : Row) : Row := (List.range row.size).foldl (fun r x => r.mendAt x) row

/-- Scrollback: a ring over an array. `data.size ≤ cap` is §Bound's
structural invariant — `push` either grows toward the cap or overwrites
in place; nothing else writes. `start` indexes the oldest row. -/
structure Ring where
  data : Array Row := #[]
  start : Nat := 0
  deriving Repr, Inhabited

def sbCap : Nat := 10000

def Ring.push (r : Ring) (row : Row) : Ring :=
  if r.data.size < sbCap then { r with data := r.data.push row }
  else { data := r.data.setIfInBounds r.start row, start := (r.start + 1) % sbCap }

def Ring.size (r : Ring) : Nat := r.data.size

/-- Oldest-first. -/
def Ring.toList (r : Ring) : List Row :=
  (r.data.toList.drop r.start) ++ (r.data.toList.take r.start)

/-! ## Parser state -/

/-- CSI collection: params are clamped (≤ 16 of them, each ≤ 65535 —
tmux does the same). Each param carries whether it began with ':'
(sub-parameter, for SGR 38:2:… syntax) — one array by construction, so
the two facts cannot drift apart. -/
structure CsiState where
  priv : UInt8 := 0 -- leading '?' '<' '=' '>' byte, 0 = none
  params : Array (Nat × Bool) := #[] -- ≤ 16 of (value ≤ 65535, startedWithColon)
  cur : Nat := 0
  curSub : Bool := false
  haveCur : Bool := false
  inter : UInt8 := 0 -- one intermediate byte is all we honor
  ignore : Bool := false
  deriving Repr, DecidableEq, Inhabited

inductive PState where
  | ground
  | esc -- after ESC
  | escInter (b : UInt8) -- after ESC + intermediate (e.g. '(' )
  | csi (s : CsiState)
  | osc (acc : Array UInt8) (esc : Bool) -- collecting OSC, BEL/ST terminated
  | str (esc : Bool) -- DCS/SOS/PM/APC: skip to ST
  deriving Repr, DecidableEq, Inhabited

/-! ## The screen -/

structure Cursor where
  x : Nat := 0
  y : Nat := 0
  pending : Bool := false -- wrap-pending: at right margin, next print wraps
  deriving Repr, DecidableEq, Inhabited

structure Saved where
  cur : Cursor := {}
  pen : Pen := {}
  deriving Repr, DecidableEq, Inhabited

/-- Modes we track. Stored-but-uninterpreted ones exist so a restore
can replay them (`Render.modes`). -/
structure Modes where
  wrap : Bool := true -- DECAWM
  origin : Bool := false -- DECOM
  insert : Bool := false -- IRM
  cursorVisible : Bool := true
  appCursor : Bool := false -- DECCKM
  appKeypad : Bool := false
  bracketedPaste : Bool := false
  mouse : Nat := 0 -- 0 off; else the last-enabled mode number
  mouseSgr : Bool := false
  focusEvents : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- The emulator state. **The representation is sealed**: every field is
`private`, which also makes the constructor private, so an importer can neither
read a field nor write one nor forge a `Vt` — `Vt.init` is the one door in and
`resize`/`step`/`feed` the only ways on. Same move as `Buf`, one layer up, and
for the same reason: with a public constructor an importer could hold a `Vt` with
`cols := 0`, so `Good`/`Renderable`/`LiveReachableVt` would describe a subset of
what a client can actually have and would prove nothing about the rest. The seal
is what turns those predicates from decoration into guarantees.

The friend set is `import all Linger.Core.Vt`: `Render`/`Terminal` (the rest of
the toolkit), `Theorems/**`, `Tests/**`, and — **temporarily, until
`specs/vt-toolkit.md` Step 2** — `Checkpoint`. Exhaustiveness of that list is a
compile-time property, not a theorem: adding a reader outside it fails to build.
Break-verified from `Linger/Runtime/` (a read, a `{ v with … }`, and a forge each
refuse); see SCRATCHPAD.md. -/
structure Vt where
  private cols : Nat
  private rows : Nat
  private grid : Array Row
  private cursor : Cursor := {}
  private pen : Pen := {}
  private modes : Modes := {}
  private top : Nat := 0 -- scroll region [top, bot], 0-based inclusive
  private bot : Nat
  private tabs : Array Bool -- size cols
  private sb : Ring := {} -- scrollback (main screen only)
  private altGrid : Option (Array Row × Cursor × Pen) := none -- stashed MAIN state while in alt
  private saved : Saved := {}
  private title : String := ""
  private g0Line : Bool := false -- G0 is DEC line-drawing
  private g1Line : Bool := false
  private shiftOut : Bool := false -- SO selected G1
  private pstate : PState := .ground
  private u8need : Nat := 0 -- UTF-8 continuation bytes still expected (≤ 3)
  private u8acc : Nat := 0 -- accumulated codepoint bits
  private bell : Bool := false -- sticky until the runtime clears it (activity signal)
  deriving Repr, Inhabited

def clampDim (n : Nat) : Nat := min (max n 1) 1000

def defaultTabs (cols : Nat) : Array Bool := (Array.range cols).map (fun i => i % 8 == 0 && i != 0)

def Vt.init (cols rows : Nat) : Vt :=
  let c := clampDim cols
  let r := clampDim rows
  { cols := c, rows := r, grid := Array.replicate r (blankRow c {}), bot := r - 1,
    tabs := defaultTabs c }

/-! ## The read-only window

`Vt.init` is the door in; these are the window out, for consumers *outside* the
toolkit (`Render`/`Terminal` are friends and read the fields directly). They exist
because the seal blocks reads as well as writes, and `Linger/Core/Session.lean` —
the daemon's session model, a client of the emulator and not part of it — needs
geometry, cursor and the alt-screen flag to answer `linger info` and to decide
whether a resize is a no-op.

Read-only is the point: a friend import would have let the daemon *forge* a `Vt`,
which is exactly what the seal exists to prevent, so `Session` gets these instead.
Grow the window on demand and keep it total — every one of these is a projection,
so there is nothing here to get wrong, which is why the claims naming them
(`Theorems/Vt.lean`) are equations rather than bounds. -/

/-- Screen width. The public reading of the sealed `cols`. -/
def Vt.colCount (v : Vt) : Nat := v.cols

/-- Screen height. The public reading of the sealed `rows`. -/
def Vt.rowCount (v : Vt) : Nat := v.rows

/-- Cursor column and row, in that order. -/
def Vt.cursorPos (v : Vt) : Nat × Nat := (v.cursor.x, v.cursor.y)

/-- Is the alternate screen live? True exactly when MAIN state is stashed, which is
what "a full-screen app is running" means to `linger info`. -/
def Vt.inAlt (v : Vt) : Bool := v.altGrid.isSome

/-! ## The decoder's door

`Vt.init` is the door for a *fresh* session; this is the door for a *restored* one,
and it is the only other way a `Vt` comes into existence. It exists because
`Linger/Core/Checkpoint.lean` used to build one field-by-field out of decoded bytes
(`specs/vt-toolkit.md` Step 2): every length in that format is an arbitrary-precision
`Nat`, so a corrupt or hostile file could name `cols := 0`, a cursor outside the
screen, or a scroll region inverted — states no `init`/`resize`/`feed` path can
produce, and states `Good` is false of. The seal stopped an *importer* forging one;
it did nothing about the file on disk, which is the input an attacker actually
controls.

**Validate, not clamp**, and the reason is the grid. Clamping `cols` to `[1,1000]`
would satisfy `Good` while leaving `grid`'s rows at their decoded width, so the
restored screen would be `Good` and **not** `Renderable` — and `Renderable` is what
every `Render.restore` theorem needs. Establishing it by clamping means rebuilding
the grid, i.e. `Vt.resize`, which the resume path deliberately refuses (it resets the
scroll region and the tab ruler — see `Linger/Runtime/Daemon.lean`). Rejecting costs
nothing new: `load` is already `Option`-valued and a checkpoint that fails to parse
already means "start fresh". One rule, uniformly — *a record that does not describe a
`Good` state is not a checkpoint*.

`private`, which is the whole point: `Linger/Core/Checkpoint.lean` reaches it through
the friend import it already has, and no module outside the toolkit gains the power to
build a `Vt` out of parts. A public smart constructor would be a second public door
admitting every `Good` state — including unreachable ones — which is a wider hole than
the forge it replaces.

The check is `Good`'s decidable content, and it is a **named stage** rather than a
conjunction inside the `if` — the AGENTS.md "restructure for provability" rule, and it
was measured: with the guard inline, `split at h` in `ofDecoded_good` picks the `match
altGrid` nested in the *condition* instead of the `if`, and the proof falls apart with
`hg` bound to nothing useful. Naming it gives `split` one splittable term. -/

private def Vt.decodedOk (cols rows : Nat) (cursor : Cursor) (top bot : Nat) (sb : Ring)
    (altGrid : Option (Array Row × Cursor × Pen)) (saved : Saved) : Bool :=
  1 ≤ cols && cols ≤ 1000 && 1 ≤ rows && rows ≤ 1000 && cursor.x < cols && cursor.y < rows &&
    saved.cur.x < cols &&
    saved.cur.y < rows &&
    top ≤ bot &&
    bot < rows &&
    sb.size ≤ sbCap &&
    (match altGrid with
    | none => true
    | some (_, c, _) => c.x < cols && c.y < rows)

/-- The decoder's door itself: `Good`'s decidable content, then the record. Three of
`Good`'s fifteen clauses need no check because this constructor *fixes* the fields they
are about — `pstate := .ground` forces `csiLe`/`oscLe` and `u8need := 0` forces `u8Le`.
Parser state is deliberately not persisted (`Checkpoint.wVt`), so there is nothing on
disk to validate.

Claimed by `Vt.ofDecoded_good` (nothing bad comes out), `Vt.ofDecoded_of_good` (nothing
good is rejected) and `Vt.ofDecoded_none_of_cols_zero` (the canonical junk value is
refused) in `Theorems/Vt.lean`. -/
private def Vt.ofDecoded (cols rows : Nat) (grid : Array Row) (cursor : Cursor) (pen : Pen)
    (modes : Modes) (top bot : Nat) (tabs : Array Bool) (sb : Ring)
    (altGrid : Option (Array Row × Cursor × Pen)) (saved : Saved) (title : String)
    (g0Line g1Line shiftOut bell : Bool) : Option Vt :=
  if Vt.decodedOk cols rows cursor top bot sb altGrid saved then
    some
      { cols, rows, grid, cursor, pen, modes, top, bot, tabs, sb, altGrid, saved, title, g0Line,
        g1Line, shiftOut, bell, pstate := .ground, u8need := 0, u8acc := 0 }
  else none

/-! ## Grid primitives (all total) -/

def Vt.getRow (v : Vt) (y : Nat) : Row := v.grid.getD y (blankRow v.cols v.pen)

def Vt.putCell (v : Vt) (x y : Nat) (c : Cell) : Vt :=
  let row := (v.getRow y).setIfInBounds x c
  { v with grid := v.grid.setIfInBounds y row }

def Vt.getCell (v : Vt) (x y : Nat) : Cell := (v.getRow y).getD x default

/-- Repair a half wide pair at one column. Grid only. -/
def Vt.mendAt (v : Vt) (x y : Nat) : Vt :=
  { v with grid := v.grid.setIfInBounds y ((v.getRow y).mendAt x) }

/-- Repair every pair in one row. Every cell-writing operation ends here, so
the pair invariant holds by construction rather than per operation. -/
def Vt.mendRow (v : Vt) (y : Nat) : Vt :=
  { v with grid := v.grid.setIfInBounds y (v.getRow y).mend }

/-- Scroll rows [top, bot] up by one, no questions asked about the
current region. Grid + (optionally) scrollback only — never the
cursor. `allowSb`: evicted top line may go to scrollback (LF at screen
bottom yes, delete-lines no). -/
def Vt.scrollUpIn (v : Vt) (top bot : Nat) (allowSb : Bool) : Vt :=
  let evicted := v.getRow top
  let g :=
    (List.range (bot - top)).foldl (fun g i => g.setIfInBounds (top + i) (v.getRow (top + i + 1)))
      v.grid
  let g := g.setIfInBounds bot (blankRow v.cols v.pen)
  if allowSb && top == 0 && bot == v.rows - 1 && v.altGrid.isNone then
    { v with
      grid := g, sb := v.sb.push evicted }
  else { v with grid := g }

/-- Scroll rows [top, bot] down by one. Grid only. -/
def Vt.scrollDownIn (v : Vt) (top bot : Nat) : Vt :=
  let g :=
    (List.range (bot - top)).foldl (fun g i => g.setIfInBounds (bot - i) (v.getRow (bot - i - 1)))
      v.grid
  let g := g.setIfInBounds top (blankRow v.cols v.pen)
  { v with grid := g }

/-- Scroll the active region up; the evicted line goes to scrollback
iff the region is the full screen and we're not in alt. -/
def Vt.scrollUp (v : Vt) : Vt := v.scrollUpIn v.top v.bot true

def Vt.scrollDown (v : Vt) : Vt := v.scrollDownIn v.top v.bot

/-! ## Cursor motion -/

def Vt.clearPending (v : Vt) : Vt := { v with cursor := { v.cursor with pending := false } }

def Vt.moveTo (v : Vt) (x y : Nat) : Vt :=
  let lo := if v.modes.origin then v.top else 0
  let hi := if v.modes.origin then v.bot else v.rows - 1
  { v with cursor := { x := min x (v.cols - 1), y := min (lo + y) hi, pending := false } }

def Vt.moveRel (v : Vt) (dx dy : Int) : Vt :=
  let nx := (Int.ofNat v.cursor.x + dx).toNat -- Int.toNat clamps at 0
  let ny := (Int.ofNat v.cursor.y + dy).toNat
  -- vertical motion is confined to the scroll region when starting inside it
  let inRegion := v.cursor.y ≥ v.top && v.cursor.y ≤ v.bot
  let lo := if inRegion then v.top else 0
  let hi := if inRegion then v.bot else v.rows - 1
  { v with cursor := { x := min nx (v.cols - 1), y := min (max ny lo) hi, pending := false } }

/-- LF / IND: down one; scrolls when at the region bottom. -/
def Vt.lineFeed (v : Vt) : Vt :=
  let v := v.clearPending
  if v.cursor.y == v.bot then v.scrollUp
  else
    if v.cursor.y + 1 < v.rows then { v with cursor := { v.cursor with y := v.cursor.y + 1 } }
    else v

/-- RI: up one; scrolls down at the region top. -/
def Vt.reverseIndex (v : Vt) : Vt :=
  let v := v.clearPending
  if v.cursor.y == v.top then v.scrollDown
  else { v with cursor := { v.cursor with y := v.cursor.y - 1 } }

def Vt.carriageReturn (v : Vt) : Vt :=
  { v with
    cursor :=
      { v.cursor with
        x := 0, pending := false } }

/-- Set the column only (CHA/HPA): clamped, row untouched. -/
def Vt.setCol (v : Vt) (x : Nat) : Vt :=
  { v with
    cursor :=
      { v.cursor with
        x := min x (v.cols - 1), pending := false } }

def Vt.backspace (v : Vt) : Vt :=
  if v.cursor.pending then v.clearPending
  else { v with cursor := { v.cursor with x := v.cursor.x - 1 } }

def Vt.tab (v : Vt) : Vt :=
  let v := v.clearPending
  let next := (List.range v.cols).find? (fun i => i > v.cursor.x && v.tabs.getD i false)
  { v with cursor := { v.cursor with x := min (next.getD (v.cols - 1)) (v.cols - 1) } }

def Vt.backTab (v : Vt) : Vt :=
  let prev :=
    (List.range v.cursor.x).foldl (fun acc i => if v.tabs.getD i false then some i else acc) none
  -- the found stop is < cursor.x < cols already; the clamp makes the
  -- bound local so §Total doesn't need a foldl invariant
  { v with
    cursor :=
      { v.cursor with
        x := min (prev.getD 0) (v.cols - 1), pending := false } }

/-! ## Printing -/

/-- DEC special graphics for box drawing (ESC ( 0). -/
def decLine (c : Char) : Char :=
  match c with
  | 'j' => '┘'
  | 'k' => '┐'
  | 'l' => '┌'
  | 'm' => '└'
  | 'n' => '┼'
  | 'q' => '─'
  | 't' => '├'
  | 'u' => '┤'
  | 'v' => '┴'
  | 'w' => '┬'
  | 'x' => '│'
  | 'a' => '▒'
  | '`' => '◆'
  | '~' => '·'
  | 'f' => '°'
  | 'g' => '±'
  | 'o' => '⎺'
  | 's' => '⎽'
  | '0' => '█'
  | _ => c

/-- Wrap-pending resolution: if a previous print left us hanging at the
right margin, a new printable wraps to the next line first (DECAWM). -/
def Vt.printWrap (v : Vt) : Vt :=
  if v.cursor.pending && v.modes.wrap then (v.carriageReturn).lineFeed else v.clearPending

/-- A wide char that cannot fit in the last column wraps early. -/
def Vt.printWideWrap (v : Vt) (w : Nat) : Vt :=
  if w == 2 && v.cursor.x + 1 ≥ v.cols && v.modes.wrap then (v.carriageReturn).lineFeed else v

/-- IRM: shift the rest of the row right by `w`. Grid only. A pair pushed
off the row end loses its shadow, so the row is mended. -/
def Vt.printShift (v : Vt) (w : Nat) : Vt :=
  if v.modes.insert then
    let x := v.cursor.x
    let row := v.getRow v.cursor.y
    let shifted :=
      (List.range (v.cols - x - w)).foldl
        (fun (r : Row) iRev =>
          let i := v.cols - 1 - iRev
          r.setIfInBounds i (row.getD (i - w) default))
        row
    { v with grid := v.grid.setIfInBounds v.cursor.y shifted.mend }
  else v

/-- Write the glyph (and its shadow cell if wide). Grid only.

A wide glyph with no room for its shadow stores a **blank** instead (fix 11).
Reachable whenever autowrap is off — `printWideWrap` only pre-wraps when wrap
is on — and previously it left a width-2 cell in the final column with no
shadow, which `Render.rowAnsi` cannot express: on replay the glyph wraps to
the next row and the joining CRLF scrolls the whole grid. Half a glyph is not
displayable either, so a blank is what a terminal shows.

The write can equally orphan the *other* half of a pair it partly overwrote: a
narrow glyph over a wide base leaves that base's shadow behind, and any glyph
over a shadow leaves its base behind. Both are reachable by ordinary
redrawing over CJK text — no `ICH`/`DCH` needed, which is what the two pinned
deep fuzz seeds turned out to be — so the row is mended after every print.
Keeping the grid free of shapes the painter cannot express is what makes
`Renderable` an invariant rather than a hypothesis. -/
def Vt.printPut (v : Vt) (ch : Char) (w : Nat) : Vt :=
  let x := v.cursor.x
  let y := v.cursor.y
  if w == 2 && x + 1 ≥ v.cols then
    (v.putCell x y { base := ' ', marks := [], width := 1, pen := v.pen }).mendRow y
  else
    let v' := v.putCell x y { base := ch, marks := [], width := w, pen := v.pen }
    if w == 2 then
      (v'.putCell (x + 1) y { base := ' ', marks := [], width := 0, pen := v.pen }).mendRow y
    else v'.mendRow y

/-- Advance the cursor by `w`, arming wrap-pending at the margin. -/
def Vt.printAdvance (v : Vt) (w : Nat) : Vt :=
  let nx := v.cursor.x + w
  if nx ≥ v.cols then
    { v with
      cursor :=
        { v.cursor with
          x := v.cols - 1, pending := v.modes.wrap } }
  else
    { v with
      cursor :=
        { v.cursor with
          x := nx, pending := false } }

/-- The codepoint a print actually stores: charset translation, then control
neutralization. A named stage so a proof never has to peel these two `if`s out
of `print`'s width scrutinee — `split` picks the first splittable term it
finds, which would otherwise be the charset test rather than the width test. -/
def Vt.printChar (v : Vt) (ch : Char) : Char :=
  printableChar (if (v.shiftOut && v.g1Line) || (!v.shiftOut && v.g0Line) then decLine ch else ch)

/-- A combining mark attaches to the cell before the cursor — and to a wide
glyph's **base**, never to its shadow.

Capped at 8: an adversarial mark stream must not grow a cell (§Bound).

The shadow redirect is what lets a mark on the final column round-trip. A
shadow is a blank continuation cell that a repaint re-creates from its base, so
`Render.rowAnsi` cannot carry marks parked there, `Render.rowText` skips them
outright (they never appeared in `linger history`), and at the right margin the
cursor sits on the shadow with wrap pending — the one position no absolute
cursor move can address.

The `cx0 != 0` guard makes the step-left total rather than relying on the pair
invariant: a shadow in column 0 is a broken pair (`Row.halfPair`) that no
reachable state holds, but `cx0 - 1` on `Nat` would silently park the mark back
on column 0 and the repair would then blank it away. `renderable_step` does not
yet prove that state unreachable, so the guard carries it. -/
def Vt.printMark (v : Vt) (ch : Char) : Vt :=
  let cx0 := if v.cursor.pending then v.cursor.x else if v.cursor.x == 0 then 0 else v.cursor.x - 1
  let cx := if (v.getCell cx0 v.cursor.y).width == 0 && cx0 != 0 then cx0 - 1 else cx0
  let cell := v.getCell cx v.cursor.y
  if cell.marks.length ≥ 8 then v
  else (v.putCell cx v.cursor.y { cell with marks := cell.marks ++ [ch] }).mendRow v.cursor.y

/-- Place one printable character at the cursor, handling wrap-pending,
wide characters, insert mode, and combining marks. -/
def Vt.print (v : Vt) (ch : Char) : Vt :=
  let ch := v.printChar ch
  let w := charWidth ch
  if w == 0 then v.printMark ch
  else ((((v.printWrap).printWideWrap w).printShift w).printPut ch w).printAdvance w

/-! ## Erase / insert / delete -/

def Vt.eraseRowSpan (v : Vt) (y from_ to_ : Nat) : Vt := -- [from, to)
  let row := v.getRow y
  let row :=
    (List.range (to_ - from_)).foldl
      (fun (r : Row) i => r.setIfInBounds (from_ + i) (Cell.erased v.pen)) row
  { v with grid := v.grid.setIfInBounds y row.mend }

def Vt.eraseLine (v : Vt) (mode : Nat) : Vt :=
  match mode with
  | 0 => v.eraseRowSpan v.cursor.y v.cursor.x v.cols
  | 1 => v.eraseRowSpan v.cursor.y 0 (v.cursor.x + 1)
  | _ => v.eraseRowSpan v.cursor.y 0 v.cols

def Vt.eraseScreen (v : Vt) (mode : Nat) : Vt :=
  match mode with
  | 0 =>
    let v := v.eraseLine 0
    (List.range (v.rows - v.cursor.y - 1)).foldl
      (fun v' i => v'.eraseRowSpan (v.cursor.y + 1 + i) 0 v'.cols) v
  | 1 =>
    let v := v.eraseLine 1
    (List.range v.cursor.y).foldl (fun v' y => v'.eraseRowSpan y 0 v'.cols) v
  | 3 => -- clear including scrollback
    let v := (List.range v.rows).foldl (fun v' y => v'.eraseRowSpan y 0 v'.cols) v
    { v with sb := {} }
  | _ => (List.range v.rows).foldl (fun v' y => v'.eraseRowSpan y 0 v'.cols) v

def Vt.insertLines (v : Vt) (n : Nat) : Vt :=
  if v.cursor.y < v.top || v.cursor.y > v.bot then v
  else
    let n := min n (v.bot - v.cursor.y + 1)
    (List.range n).foldl (fun a _ => a.scrollDownIn v.cursor.y v.bot) v

def Vt.deleteLines (v : Vt) (n : Nat) : Vt :=
  if v.cursor.y < v.top || v.cursor.y > v.bot then v
  else
    let n := min n (v.bot - v.cursor.y + 1)
    (List.range n).foldl (fun a _ => a.scrollUpIn v.cursor.y v.bot false) v

def Vt.deleteChars (v : Vt) (n : Nat) : Vt :=
  let x := v.cursor.x
  let y := v.cursor.y
  let n := min n (v.cols - x)
  let row := v.getRow y
  let row :=
    (List.range (v.cols - x)).foldl
      (fun (r : Row) i =>
        let src := x + i + n
        r.setIfInBounds (x + i) (if src < v.cols then row.getD src default else Cell.erased v.pen))
      row
  { v with grid := v.grid.setIfInBounds y row.mend }

def Vt.insertChars (v : Vt) (n : Nat) : Vt :=
  let x := v.cursor.x
  let y := v.cursor.y
  let n := min n (v.cols - x)
  let row := v.getRow y
  let row :=
    (List.range (v.cols - x)).foldl
      (fun (r : Row) iRev =>
        let i := v.cols - 1 - iRev
        r.setIfInBounds i (if i ≥ x + n then row.getD (i - n) default else Cell.erased v.pen))
      row
  { v with grid := v.grid.setIfInBounds y row.mend }

def Vt.eraseChars (v : Vt) (n : Nat) : Vt :=
  v.eraseRowSpan v.cursor.y v.cursor.x (min (v.cursor.x + n) v.cols)

/-! ## SGR -/

def color256 (n : Nat) : Color := .idx (UInt8.ofNat (min n 255))

/-- Apply one SGR parameter chain. Handles 38/48 in both `38;5;n` /
`38;2;r;g;b` (semicolon) and `38:5:n` / `38:2::r:g:b` (colon) forms.

**Not `@[expose]` any more** (2026-09-13, the `Vt` seal). It was, because
`Theorems/Render/Pen.lean` inducts on the `let rec go` auxiliary by name
(`Vt.applySgr.go`) and a compiler-generated auxiliary stays module-private unless
the parent's body is exposed — 101 `Unknown constant` errors without it, from a
*legacy* (non-`module`) importer. Every importer that needs `go` is now a `module`
with `import all Linger.Core.Vt`, which grants the auxiliary directly, so the
attribute is redundant — and it is no longer *allowed*: an exposed body may not
mention a private constructor, and `{ v with pen := … }` below is one now that
every `Vt` field is `private`. If a legacy importer of `go` ever comes back, give
it `import all`; do not restore the attribute. -/
def Vt.applySgr (v : Vt) (params : List (Nat × Bool)) : Vt :=
  -- (value, isSubParam); a lone `m` means reset
  let rec go (p : Pen) (l : List (Nat × Bool)) (fuel : Nat) : Pen :=
    match fuel with
    | 0 => p
    | fuel + 1 =>
      match l with
      | [] => p
      | (n, _) :: rest =>
        -- extended color: consume its argument chain
        if n == 38 || n == 48 then
          let isFg := n == 38
          match rest with
          | (5, _) :: (idx, _) :: r =>
            let c := color256 idx
            go (if isFg then { p with fg := c } else { p with bg := c }) r fuel
          | (2, _) :: rest2 =>
            -- colon form may carry a color-space id: 38:2::r:g:b
            let (rgb, r) :=
              match rest2 with
              | (_, true) :: (r1, true) :: (g1, true) :: (b1, true) :: tl =>
                -- 4 sub-args: the first is a color-space id, skip it
                (some (r1, g1, b1), tl)
              | (r1, _) :: (g1, _) :: (b1, _) :: tl => (some (r1, g1, b1), tl)
              | tl => (none, tl)
            match rgb with
            | some (r1, g1, b1) =>
              let c :=
                Color.rgb (UInt8.ofNat (min r1 255)) (UInt8.ofNat (min g1 255))
                  (UInt8.ofNat (min b1 255))
              go (if isFg then { p with fg := c } else { p with bg := c }) r fuel
            | none => go p r fuel
          | _ => p
        else
          let p :=
            if n == 0 then {}
            else
              if n == 1 then { p with bold := true }
              else
                if n == 2 then { p with dim := true }
                else
                  if n == 3 then { p with italic := true }
                  else
                    if n == 4 then { p with underline := true }
                    else
                      if n == 5 || n == 6 then { p with blink := true }
                      else
                        if n == 7 then { p with reverse := true }
                        else
                          if n == 9 then { p with strike := true }
                          else
                            if n == 21 || n == 22 then
                              { p with
                                bold := false, dim := false }
                            else
                              if n == 23 then { p with italic := false }
                              else
                                if n == 24 then { p with underline := false }
                                else
                                  if n == 25 then { p with blink := false }
                                  else
                                    if n == 27 then { p with reverse := false }
                                    else
                                      if n == 29 then { p with strike := false }
                                      else
                                        if 30 ≤ n && n ≤ 37 then
                                          { p with fg := .idx (UInt8.ofNat (n - 30)) }
                                        else
                                          if n == 39 then { p with fg := .default }
                                          else
                                            if 40 ≤ n && n ≤ 47 then
                                              { p with bg := .idx (UInt8.ofNat (n - 40)) }
                                            else
                                              if n == 49 then { p with bg := .default }
                                              else
                                                if 90 ≤ n && n ≤ 97 then
                                                  { p with fg := .idx (UInt8.ofNat (n - 90 + 8)) }
                                                else
                                                  if 100 ≤ n && n ≤ 107 then
                                                    { p with
                                                      bg := .idx (UInt8.ofNat (n - 100 + 8)) }
                                                  else p
          go p rest fuel
  let ps := if params.isEmpty then [(0, false)] else params
  { v with pen := go v.pen ps (ps.length + 1) }

/-! ## Alt screen -/

def Vt.enterAlt (v : Vt) (saveCursor : Bool) : Vt :=
  if v.altGrid.isSome then v -- already there
  else
    let saved := if saveCursor then { cur := v.cursor, pen := v.pen } else v.saved
    { v with
      altGrid := some (v.grid, v.cursor, v.pen),
      grid := Array.replicate v.rows (blankRow v.cols {}), cursor := {}, saved, top := 0,
      bot := v.rows - 1 }

def Vt.leaveAlt (v : Vt) (restoreCursor : Bool) : Vt :=
  match v.altGrid with
  | none => v
  | some (g, cur, pen) =>
    { v with
      altGrid := none, grid := g, cursor := if restoreCursor then cur else v.cursor,
      pen := if restoreCursor then pen else v.pen, top := 0, bot := v.rows - 1 }

/-! ## Resize (truncate/pad; no reflow — see header) -/

/-- Truncate or pad one row, then repair it: truncation can cut a wide pair in
half. Built as a map over the target columns rather than `extract`/`++` so the
result's width and cell contents are one step from the definition — the proofs
(`rowOk_resizeRow`) would otherwise be index arithmetic over two array shapes.
Semantics are unchanged: column `i` keeps its cell when the old row had one, and
is a blank otherwise. -/
def resizeRow (row : Row) (cols : Nat) (p : Pen) : Row :=
  Row.mend
    ((Array.range cols).map (fun i => if i < row.size then row.getD i default else Cell.erased p))

def Vt.resize (v : Vt) (cols rows : Nat) : Vt :=
  let c := clampDim cols
  let r := clampDim rows
  -- keep the bottom `r` rows, padding at the end when growing. A map over the
  -- target rows for the same reason `resizeRow` is one: it makes the result's
  -- height and per-row contents immediate (`gridOk_fit`).
  let fit := fun (g : Array Row) =>
    (Array.range r).map
      (fun j =>
        let src := if g.size ≥ r then g.size - r + j else j
        if src < g.size then resizeRow (g.getD src #[]) c {} else blankRow c {})
  { v with
    cols := c, rows := r, grid := fit v.grid,
    altGrid :=
      v.altGrid.map
        (fun (g, cur, pen) =>
          (fit g,
            { cur with
              x := min cur.x (c - 1), y := min cur.y (r - 1) },
            pen)),
    cursor :=
      { v.cursor with
        x := min v.cursor.x (c - 1), y := min v.cursor.y (r - 1), pending := false },
    -- the saved cursor must shrink too, or DECRC after a
    -- shrink restores an out-of-bounds position (§Total)
    saved :=
      { cur := { x := min v.saved.cur.x (c - 1), y := min v.saved.cur.y (r - 1), pending := false },
        pen := v.saved.pen },
    top := 0, bot := r - 1, tabs := defaultTabs c }

/-! ## CSI dispatch -/

def CsiState.arg (s : CsiState) (i default_ : Nat) : Nat :=
  match (s.params.getD i (0, false)).1 with
  | 0 => default_
  | n => n

/-- Params paired with their sub-param flags, for SGR. -/
def CsiState.sgrParams (s : CsiState) : List (Nat × Bool) := s.params.toList

def Vt.setMode (v : Vt) (priv : Bool) (n : Nat) (on : Bool) : Vt :=
  if priv then
    match n with
    | 1 => { v with modes := { v.modes with appCursor := on } }
    | 6 => let v' := { v with modes := { v.modes with origin := on } }
           v'.moveTo 0 0
    | 7 => { v with modes := { v.modes with wrap := on } }
    | 25 => { v with modes := { v.modes with cursorVisible := on } }
    | 47 => if on then v.enterAlt false else v.leaveAlt false
    | 1000 | 1002 | 1003 =>
      { v with modes := { v.modes with mouse := if on then n else 0 } }
    | 1006 => { v with modes := { v.modes with mouseSgr := on } }
    | 1004 => { v with modes := { v.modes with focusEvents := on } }
    | 1047 => if on then v.enterAlt false else v.leaveAlt false
    | 1048 => if on then { v with saved := { cur := v.cursor, pen := v.pen } }
              else { v with cursor := v.saved.cur, pen := v.saved.pen }
    | 1049 => if on then v.enterAlt true else v.leaveAlt true
    | 2004 => { v with modes := { v.modes with bracketedPaste := on } }
    | _ => v
  else
    match n with
    | 4 => { v with modes := { v.modes with insert := on } }
    | _ => v

def Vt.csiDispatch (v : Vt) (s : CsiState) (final : UInt8) : Vt :=
  if s.ignore then v
  else
    let a1 := s.arg 0 1 -- first arg, default 1
    match final with
    | 0x40 => v.insertChars a1 -- @ ICH
    | 0x41 => v.moveRel 0 (-(Int.ofNat a1)) -- A CUU
    | 0x42 => v.moveRel 0 (Int.ofNat a1) -- B CUD
    | 0x43 => v.moveRel (Int.ofNat a1) 0 -- C CUF
    | 0x44 => v.moveRel (-(Int.ofNat a1)) 0 -- D CUB
    | 0x45 => (v.moveRel 0 (Int.ofNat a1)).carriageReturn -- E CNL
    | 0x46 => (v.moveRel 0 (-(Int.ofNat a1))).carriageReturn -- F CPL
    | 0x47 => v.setCol (a1 - 1) -- G CHA
    | 0x48 => v.moveTo (s.arg 1 1 - 1) (a1 - 1) -- H CUP
    | 0x49 => (List.range a1).foldl (fun a _ => a.tab) v -- I CHT
    | 0x4A => v.eraseScreen (s.arg 0 0) -- J ED
    | 0x4B => v.eraseLine (s.arg 0 0) -- K EL
    | 0x4C => v.insertLines a1 -- L IL
    | 0x4D => v.deleteLines a1 -- M DL
    | 0x50 => v.deleteChars a1 -- P DCH
    | 0x53 => (List.range a1).foldl (fun a _ => a.scrollUp) v -- S SU
    | 0x54 => (List.range a1).foldl (fun a _ => a.scrollDown) v -- T SD
    | 0x58 => v.eraseChars a1 -- X ECH
    | 0x5A => (List.range a1).foldl (fun a _ => a.backTab) v -- Z CBT
    | 0x60 => v.setCol (a1 - 1) -- ` HPA
    | 0x61 => v.moveRel (Int.ofNat a1) 0 -- a HPR
    | 0x64 => -- d VPA
      { v with
        cursor :=
          { v.cursor with
            y := min (a1 - 1) (v.rows - 1), pending := false } }
    | 0x65 => v.moveRel 0 (Int.ofNat a1) -- e VPR
    | 0x66 => v.moveTo (s.arg 1 1 - 1) (a1 - 1) -- f HVP
    | 0x67 => -- g TBC
      match s.arg 0 0 with
      | 0 => { v with tabs := v.tabs.setIfInBounds v.cursor.x false }
      | 3 => { v with tabs := Array.replicate v.cols false }
      | _ => v
    | 0x68 => v.setMode (s.priv == 0x3F) (s.arg 0 0) true -- h SM
    | 0x6C => v.setMode (s.priv == 0x3F) (s.arg 0 0) false -- l RM
    | 0x6D => if s.priv == 0 then v.applySgr s.sgrParams else v -- m SGR
    | 0x72 => -- r DECSTBM
      if s.priv != 0 then v
      else
        let t := s.arg 0 1 - 1
        let b := s.arg 1 v.rows - 1
        if t < b && b < v.rows then
          ({ v with
                top := t, bot := b }).moveTo
            0 0
        else v
    | 0x73 => { v with saved := { cur := v.cursor, pen := v.pen } } -- s DECSC (ANSI)
    | 0x75 => -- u DECRC (ANSI)
      if s.priv == 0 then
        { v with
          cursor := v.saved.cur, pen := v.saved.pen }
      else v
    | _ => v -- DA/DSR/CPR/DECSCUSR/… : queries and styling we don't act on

/-! ## Byte-at-a-time parser -/

def csiPush (s : CsiState) (sub : Bool) : CsiState :=
  if s.haveCur || s.params.size > 0 || sub then
    -- close the current parameter
    if s.params.size ≥ 16 then
      { s with
        ignore := true, cur := 0, haveCur := false }
    else
      { s with
        params := s.params.push (min s.cur 65535, s.curSub), cur := 0, curSub := sub,
        haveCur := false }
  else { s with curSub := sub }

def Vt.csiFinish (v : Vt) (s : CsiState) (final : UInt8) : Vt :=
  -- close any pending parameter, then dispatch
  let s :=
    if s.haveCur then
      (if s.params.size ≥ 16 then { s with ignore := true }
      else { s with params := s.params.push (min s.cur 65535, s.curSub) })
    else s
  let v := v.csiDispatch s final
  { v with pstate := .ground }

def Vt.oscFinish (v : Vt) (acc : Array UInt8) : Vt :=
  let txt := String.fromUTF8? (ByteArray.mk acc) |>.getD ""
  let v := { v with pstate := .ground }
  match txt.splitOn ";" with
  | code :: rest =>
    if code == "0" || code == "2" then { v with title := String.intercalate ";" rest } else v
  | _ => v

/-- Handle a C0 control byte (valid in most parser states). -/
def Vt.ctl (v : Vt) (b : UInt8) : Vt :=
  match b with
  | 0x07 => { v with bell := true }
  | 0x08 => v.backspace
  | 0x09 => v.tab
  | 0x0A | 0x0B | 0x0C => v.lineFeed
  | 0x0D => v.carriageReturn
  | 0x0E => { v with shiftOut := true }
  | 0x0F => { v with shiftOut := false }
  | _ => v

/-- One decoded codepoint reaches the screen. `Char.ofNat` is total;
invalid codepoints (surrogates, > U+10FFFF) print as U+FFFD. -/
def Vt.acceptChar (v : Vt) (n : Nat) : Vt :=
  if n.isValidChar then v.print (Char.ofNat n) else v.print '\uFFFD'

/-- Ground state: printables, C0, ESC, and UTF-8 assembly. -/
def Vt.stepGround (v : Vt) (b : UInt8) : Vt :=
  if b == 0x1B then { v with pstate := .esc }
  else
    if b < 0x20 then v.ctl b
    else
      if b < 0x80 then v.acceptChar b.toNat
      else
        if b < 0xC0 then
          -- continuation byte
          if v.u8need == 0 then v -- orphan: drop
          else
            -- clamp keeps §Bound trivial; valid sequences never reach it
            let acc := min (v.u8acc * 64 + (b.toNat - 0x80)) 2097151
            if v.u8need == 1 then
              ({ v with
                    u8need := 0, u8acc := 0 }).acceptChar
                acc
            else
              { v with
                u8need := v.u8need - 1, u8acc := acc }
        else
          if b < 0xE0 then
            { v with
              u8need := 1, u8acc := b.toNat - 0xC0 }
          else
            if b < 0xF0 then
              { v with
                u8need := 2, u8acc := b.toNat - 0xE0 }
            else
              if b < 0xF8 then
                { v with
                  u8need := 3, u8acc := b.toNat - 0xF0 }
              else v

/-- After ESC. -/
def Vt.stepEsc (v : Vt) (b : UInt8) : Vt :=
  match b with
  | 0x5B => { v with pstate := .csi {} } -- [
  | 0x5D => { v with pstate := .osc #[] false } -- ]
  | 0x50 | 0x58 | 0x5E | 0x5F => { v with pstate := .str false } -- P X ^ _
  | 0x37 =>
    { v with
      saved := { cur := v.cursor, pen := v.pen }, -- 7 DECSC
      pstate := .ground }
  | 0x38 =>
    { v with
      cursor := v.saved.cur, pen := v.saved.pen, -- 8 DECRC
      pstate := .ground }
  | 0x44 => { v.lineFeed with pstate := .ground } -- D IND
  | 0x45 => { (v.carriageReturn).lineFeed with pstate := .ground } -- E NEL
  | 0x48 =>
    { v with
      tabs := v.tabs.setIfInBounds v.cursor.x true, -- H HTS
      pstate := .ground }
  | 0x4D => { v.reverseIndex with pstate := .ground } -- M RI
  | 0x63 => -- c RIS
    let fresh := Vt.init v.cols v.rows
    { fresh with sb := if v.altGrid.isNone then v.sb else ({} : Ring) }
  | 0x3D =>
    { v with
      modes := { v.modes with appKeypad := true }, pstate := .ground }
  | 0x3E =>
    { v with
      modes := { v.modes with appKeypad := false }, pstate := .ground }
  | 0x1B => v -- ESC ESC: stay
  | _ =>
    if b == 0x28 || b == 0x29 || b == 0x2A || b == 0x2B then { v with pstate := .escInter b }
    else { v with pstate := .ground }

/-- After ESC + intermediate: charset designation. -/
def Vt.stepEscInter (v : Vt) (i b : UInt8) : Vt :=
  let v := { v with pstate := .ground }
  if i == 0x28 then { v with g0Line := b == 0x30 } -- ESC ( 0 / B
  else
    if i == 0x29 then { v with g1Line := b == 0x30 } -- ESC ) 0 / B
    else v

/-- Inside CSI. -/
def Vt.stepCsi (v : Vt) (s : CsiState) (b : UInt8) : Vt :=
  if b ≥ 0x30 && b ≤ 0x39 then
    { v with
      pstate :=
        .csi
          { s with
            cur := min (s.cur * 10 + (b.toNat - 0x30)) 65535, haveCur := true } }
  else
    if b == 0x3B then { v with pstate := .csi (csiPush s false) }
    else
      if b == 0x3A then { v with pstate := .csi (csiPush s true) }
      else
        if b ≥ 0x3C && b ≤ 0x3F then { v with pstate := .csi { s with priv := b } }
        else
          if b ≥ 0x20 && b ≤ 0x2F then { v with pstate := .csi { s with inter := b } }
          else
            if b ≥ 0x40 && b ≤ 0x7E then
              if s.inter != 0 then { v with pstate := .ground } -- e.g. DECSCUSR: ignore
              else v.csiFinish s b
            else
              if b == 0x1B then { v with pstate := .esc }
              else
                if b < 0x20 then (v.ctl b) -- C0 inside CSI executes, sequence continues
                else { v with pstate := .ground }

/-- Inside OSC: accumulate until BEL or ST, with a hard cap. -/
def Vt.stepOsc (v : Vt) (acc : Array UInt8) (esc : Bool) (b : UInt8) : Vt :=
  if esc && b == 0x5C then v.oscFinish acc -- ESC \\ = ST
  else
    if b == 0x07 then v.oscFinish acc -- BEL
    else
      if b == 0x1B then { v with pstate := .osc acc true }
      else
        if acc.size ≥ 2048 then { v with pstate := .osc acc false } -- §Bound: stop growing
        else { v with pstate := .osc (acc.push b) false }

/-- Inside DCS/SOS/PM/APC: skip to ST. -/
def Vt.stepStr (v : Vt) (esc : Bool) (b : UInt8) : Vt :=
  if esc && b == 0x5C then { v with pstate := .ground }
  else if b == 0x1B then { v with pstate := .str true } else { v with pstate := .str false }

/-- A stray byte aborts a pending UTF-8 sequence. Named (not inlined in
`step`) so proofs can rewrite `step`'s match scrutinee: it touches only
`u8need`/`u8acc`, never `pstate` (`ps_abortUtf8`). -/
def Vt.abortUtf8 (v : Vt) (b : UInt8) : Vt :=
  if v.u8need > 0 && (b < 0x80 || b ≥ 0xC0) then
    { v with
      u8need := 0, u8acc := 0 }
  else v

/-- The single-byte step — §Total's subject. -/
def Vt.step (v : Vt) (b : UInt8) : Vt :=
  let v := v.abortUtf8 b
  match v.pstate with
  | .ground => v.stepGround b
  | .esc => v.stepEsc b
  | .escInter i => v.stepEscInter i b
  | .csi s => v.stepCsi s b
  | .osc acc esc => v.stepOsc acc esc b
  | .str esc => v.stepStr esc b

/-- Feed a chunk. §Chunk holds definitionally: `List.foldl_append`. -/
def Vt.feed (v : Vt) (bytes : List UInt8) : Vt := bytes.foldl Vt.step v

/-- Forget partial parser state (what a checkpoint deliberately does
not persist — see `Linger.Core.Checkpoint`). -/
def Vt.quiesce (v : Vt) :
    Vt := { v with
    pstate := .ground, u8need := 0, u8acc := 0 }

/-- Feed a `ByteArray` by converting at the call site.

**Test-facing, and named as such** (pin-the-gaps item 5): the docstring here used
to read "the runtime hands us `ByteArray`s; convert at the boundary", which was
false — the daemon's pty path is `Terminal.feed s.vt s.scan chunk` on a
`List UInt8` (`Linger/Core/Session.lean`), and this definition has no caller
outside `Tests/`. It is kept because five fixtures use it and a convenience with
five callers is reachable code, not the unproved-and-unreachable state
`E2E/Coverage.lean` exists to prevent; what was wrong was the claim, not the
function. -/
def Vt.feedBytes (v : Vt) (bytes : ByteArray) : Vt := v.feed bytes.toList

end Linger.Core.Vt
