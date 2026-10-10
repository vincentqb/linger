module

public section

/-! # Linger.Core.Vt — restore-grade terminal emulation, pure

The daemon feeds every pty byte here (a passive observer: clients get
the raw bytes; this state exists so a *re*-attaching client can be shown
what it missed, and so `linger capture --history` can dump it).

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
chosen because linger delegates live rendering to the real terminal:
* no reply channel in this model: `Terminal` handles the owned query
  profile and supplies replies to the child.
* resize truncates/pads rather than reflowing.
* OSC 8 hyperlinks, sixel, kitty graphics: skipped as strings, not
  stored.
* modes stored but not interpreted beyond the emulator's needs
  (bracketed paste, mouse, focus events) — the runtime replays
  them to a re-attaching client so applications keep working.
-/

namespace Linger.Core.Vt

/-! ## Pen, color, cell -/

/-- A cell colour: the terminal default, a 256-colour palette index, or 24-bit RGB. -/
inductive Color where
  | default
  | idx (i : UInt8)
  | rgb (r g b : UInt8)
  deriving Repr, DecidableEq, Inhabited

/-- The SGR state written into new cells: colours and text attributes. -/
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

/-- Is the codepoint zero-width: a combining mark, variation selector, ZWSP, ZWNJ, ZWJ or BOM? -/
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

/-- Is the codepoint East Asian wide or an emoji, occupying two columns? -/
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

/-- Columns a glyph occupies: 0 if zero-width, 2 if wide, otherwise 1. -/
def charWidth (c : Char) : Nat := if isZeroWidth c.toNat then 0 else if isWide c.toNat then 2 else 1

/-- The codepoint a cell is allowed to store: a C0 control or DEL becomes
U+FFFD.

A cell holding a control codepoint cannot be repainted — `Render.safeChar`
substitutes U+FFFD on emit, so the replayed screen would differ from the live
one — and such a codepoint is reachable: an overlong UTF-8 sequence decodes to
a C0 or, as `0xC1 0xBF`, to DEL. Substituting **on store** is what
makes every stored cell repaintable, so `Renderable` is an invariant rather
than a hypothesis (the same move as fix 11). `Render.safeChar` stays as the
emit-side guard, which still has work to do for a decoded checkpoint. -/
def printableChar (c : Char) : Char := if c.toNat < 0x20 || c.toNat == 0x7F then '\uFFFD' else c

/-! ## Rows and the scrollback ring -/

/-- One screen row of cells. -/
abbrev Row := Array Cell

/-- A row of `cols` erased cells keeping pen `p`'s background. -/
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

/-- The same sweep without allocating the column list; compiled code uses it. -/
def Row.mendFast (row : Row) : Row := Nat.fold row.size (fun x _ r => r.mendAt x) row

/-- `Row.mend` and `Row.mendFast` are the same function, so compiled code runs the latter. -/
@[csimp]
theorem Row.mend_eq_mendFast : @Row.mend = @Row.mendFast := by
  funext row
  suffices h :
    ∀ len (r : Row),
      (List.range len).foldl (fun r x => r.mendAt x) r = Nat.fold len (fun x _ r => r.mendAt x) r
    from h row.size row
  intro len
  induction len with
  | zero =>
    intro r; simp
  | succ len ih =>
    intro r; simp [List.range_succ, List.foldl_append, ih]

/-- Scrollback: a ring over an array. `data.size ≤ cap` is §Bound's
structural invariant — `push` either grows toward the cap or overwrites
in place; nothing else writes. `start` indexes the oldest row. -/
structure Ring where
  data : Array Row := #[]
  start : Nat := 0
  deriving Repr, Inhabited

/-- Maximum number of rows the scrollback ring retains. -/
def sbCap : Nat := 10000

/-- Append a row, overwriting the oldest once the ring holds `sbCap` rows. -/
def Ring.push (r : Ring) (row : Row) : Ring :=
  if r.data.size < sbCap then { r with data := r.data.push row }
  else { data := r.data.setIfInBounds r.start row, start := (r.start + 1) % sbCap }

/-- Number of rows retained. -/
def Ring.size (r : Ring) : Nat := r.data.size

/-- Oldest-first. -/
def Ring.toList (r : Ring) : List Row :=
  (r.data.toList.drop r.start) ++ (r.data.toList.take r.start)

/-! ## Parser state -/

/-- CSI collection: params are clamped (≤ 16 of them, each ≤ 65535).
Each param carries whether it began with ':' (sub-parameter, for
SGR 38:2:… syntax) — one array by construction, so the two facts cannot
drift apart. -/
structure CsiState where
  priv : UInt8 := 0 -- leading '?' '<' '=' '>' byte, 0 = none
  params : Array (Nat × Bool) := #[] -- ≤ 16 of (value ≤ 65535, startedWithColon)
  cur : Nat := 0
  curSub : Bool := false
  haveCur : Bool := false
  inter : UInt8 := 0 -- one intermediate byte is all we honor
  ignore : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- Parser state between bytes: ground, ESC, an ESC intermediate, CSI, OSC or a skipped string. -/
inductive PState where
  | ground
  | esc -- after ESC
  | escInter (b : UInt8) -- first intermediate; 0 marks an unsupported compound sequence
  | csi (s : CsiState)
  | osc (acc : Array UInt8) (esc : Bool) -- collecting OSC, BEL/ST terminated
  | str (esc : Bool) -- DCS/SOS/PM/APC: skip to ST
  deriving Repr, DecidableEq, Inhabited

/-! ## The screen -/

/-- Cursor position and its wrap-pending flag. -/
structure Cursor where
  x : Nat := 0
  y : Nat := 0
  pending : Bool := false -- wrap-pending: at right margin, next print wraps
  deriving Repr, DecidableEq, Inhabited

/-- The cursor and pen DECSC saves and DECRC restores. -/
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
read a field nor write one nor forge a `Vt`. Internal mutators are private too:
`putCell` accepts arbitrary cells, `printPut` and `printMark` expect already
classified glyphs, and parser stages expect bounded parser states. Publishing
those operations would let an ordinary importer bypass the invariants without
ever naming a private field. `Vt.init` is the fresh door in; the complete
transformer list is below. Same move as `Buf`, one layer up, and
for the same reason: with a public constructor an importer could hold a `Vt` with
`cols := 0`, so `Good`/`Renderable`/`LiveReachableVt` would describe a subset of
what a client can actually have and would prove nothing about the rest. The seal
is what turns those predicates from decoration into guarantees.

The friend set is `import all Linger.Core.Vt`: `Render`/`Terminal`/`Replay` (the rest
of the toolkit), `Theorems/**`, `Tests/**`, and `Checkpoint` — the last **permanently**,
for `wVt`'s field reads and the one validating door below; its reason is written at
that file's import. The compiler accepts `import all` from any module, so
`scripts/gates.sh` enforces that list; a reader without the import fails to build.
Break-verified from `Linger/Runtime/` (a read, a `{ v with … }`, a `Vt.mk`, a bare `⟨…⟩`
and `(default : Vt)` each refuse, against a `v.colCount` control that compiles); see
SCRATCHPAD.md.

## Every door, and why the list is prose and not a theorem

`specs/archive/vt-toolkit.md` Step 3. The toolkit has two ways a `Vt` comes into
existence and one public family of ways it changes:

* `Vt.init` — the fresh session. `Good`, `Renderable` and `TabsOk` all hold of it
  (`Vt.good_init`, `Vt.renderable_init`, `Vt.tabsOk_init`).
* `Vt.ofDecoded` — the restored session, `private`, and it **validates**: a record that
  does not describe a `Good` **and** `Renderable` state, with a ruler the width of the
  screen, decodes to `none` (`Vt.ofDecoded_good`, `Vt.ofDecoded_renderable`,
  `Vt.ofDecoded_tabsOk`, and `Checkpoint.load_good`/`load_renderable`/`load_tabsOk` on
  the real path, for *arbitrary bytes*).
* `Vt.resize`, `Vt.step`, `Vt.feed`, `Vt.feedBytes`, `Vt.quiesce` — the session transformers,
  each of which preserves `Good`, `Renderable`, `U8Ok`, `TabsOk` and `CsiOk`.
  `LiveReachableVt` is that closure written as an inductive (`step` is a singleton
  feed and `feedBytes` converts to a list). The `*_of_liveReachable` lemmas are
  the payoff.
* `Vt.observe` — the attach client's history-free observer. It uses the same
  parser step and discards scrollback after each byte. `observe_good` and
  `observe_invariants` preserve those same five invariants, while `observe_dims`
  and `observe_no_history` bound its storage at the client's initial geometry.
  It is not a session restoration path.

`colCount`, `rowCount`, `cursorPos`, `inAlt`, `getRow`, `getCell`, `windowTitle`
and `atBoundary` form the public read-only surface.

There is deliberately **no `Inhabited Vt`**, and its absence is part of this list rather
than an oversight: `deriving Inhabited` produced `cols = 0, rows = 0, grid = #[]`, which
`(default : Vt)` handed to *any* importer with no `import all` and no forge — provably not
`Good` and provably not `LiveReachableVt`. It was a third public door, it admitted a state
the emulator cannot reach, and the Step 1 break-verify did not think to try it. `Repr` is
absent too, as explained below; nothing in the tree needed a canonical inhabitant (two
proof-scratch sites used `default` as an arbitrary carrier and now say `Vt.init 1 1`).

**Why this is prose.** `∀ v : Vt, Good v` is not provable and would not mean what it looks
like if it were: this module and its friends can `cases v` and name any twenty field values
they like, so the proposition is false *inside* the seal and the seal is not a statement
about propositions. It is a statement about which modules the compiler will accept — the
same species as `SHIM_CAP` and the `LingerVt` closure grep, and, per that spec's non-goals,
a theorem shaped like it would be decoration. What the theorems can and do say is the list
above: every door establishes the invariants and every transformer preserves them, so any
*program* holding a `Vt` holds one of those. Extending the friend set, or adding a door,
is what breaks the claim — and only a reader can see that, which is why the list is here
and not in a `Prop`.

**What the door establishes, after R2.** `Vt.decodedOk` decides `Good`'s content and
`Vt.decodedRenderable` decides `Renderable`'s two clauses plus the ruler's length, so a
decoded checkpoint is `Good`, `Renderable` and `TabsOk` — `Theorems/Resume.lean`'s
`resume_grid`/`resume_sb`/`resume_tabs` are now reachable from an arbitrary byte string
(`resume_grid_of_load` and its two siblings) and not only stated. Before that the check
was never passed the grid at all, and the consequence was observable rather than
theoretical: see the shape-half section below, and finding R2 in SCRATCHPAD.md.

The price is a mirror, paid deliberately: `ofDecoded_of_good` is the same predicate seen
from the other side, so `Checkpoint.rt_vt` → `load_save` → `load_save_exact` and the five
`resume_*` claims that never read the grid now carry `Renderable` and `TabsOk`
hypotheses. Every live session satisfies them (`renderable_of_liveReachable`,
`tabsOk_of_liveReachable`), each claim says so in its own docstring, and correctness beat
hypothesis-count: the old unconditional statements were *also* true of a screen the
emitter cannot reproduce.

**Still unreachable from disk:** `Render.restore_sb_exact`'s
`hrok : ∀ r ∈ v.sb.toList, RowOk v.cols r`, and it is unprovable from reachability rather
than merely unchecked — `Vt.resize` reinstalls the grid and the ruler at the new width and
leaves the scrollback rows at their old one, so a resized live session has ring rows wider
than `cols` and a decoder that demanded otherwise would refuse a legitimate checkpoint.
Measured, not argued. -/
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

-- No `Repr`: it would publicly read every private field (Tests/VtApi pins this).

/-- Clamp a requested dimension to [1, 1000]. -/
def clampDim (n : Nat) : Nat := min (max n 1) 1000

/-- The default tab ruler: a stop every eight columns after column 0. -/
def defaultTabs (cols : Nat) : Array Bool := (Array.range cols).map (fun i => i % 8 == 0 && i != 0)

/-- A fresh screen with each dimension clamped to [1, 1000]. -/
def Vt.init (cols rows : Nat) : Vt :=
  let c := clampDim cols
  let r := clampDim rows
  { cols := c, rows := r, grid := Array.replicate r (blankRow c {}), bot := r - 1,
    tabs := defaultTabs c }

/-! ## The read-only window

`Vt.init` is the door in; these are the window out, for consumers *outside* the
toolkit (`Render`/`Terminal`/`Replay` are friends and read the fields directly). They exist
because the seal blocks reads as well as writes, and `Linger/Core/Session.lean` —
the daemon's session model, a client of the emulator and not part of it — needs
geometry, cursor and the alt-screen flag to answer `linger info` and to decide
whether a resize is a no-op.

Read-only is the point: a friend import would have let the daemon *forge* a `Vt`,
which is exactly what the seal exists to prevent, so `Session` gets these instead.
Grow the window on demand and keep it total — every one of these is a projection,
so there is nothing here to get wrong, which is why the claims naming them
(`Theorems/Vt/State.lean`) are equations rather than bounds. -/

/-- Screen width. The public reading of the sealed `cols`. -/
def Vt.colCount (v : Vt) : Nat := v.cols

/-- Screen height. The public reading of the sealed `rows`. -/
def Vt.rowCount (v : Vt) : Nat := v.rows

/-- Cursor column and row, in that order. -/
def Vt.cursorPos (v : Vt) : Nat × Nat := (v.cursor.x, v.cursor.y)

/-- Is the alternate screen live? True exactly when MAIN state is stashed, which is
what "a full-screen app is running" means to `linger info`. -/
def Vt.inAlt (v : Vt) : Bool := v.altGrid.isSome

/-- The most recent application window title, as received through OSC 0 or 2. -/
def Vt.windowTitle (v : Vt) : String := v.title

/-- Injected terminal output is safe only between complete control sequences and
UTF-8 characters. Ground parser state alone does not imply the latter. -/
def Vt.atBoundary (v : Vt) : Bool := v.pstate == .ground && v.u8need == 0

/-! ## The decoder's door

`Vt.init` is the door for a *fresh* session; this is the door for a *restored* one,
and it is the only other way a `Vt` comes into existence. It exists because
`Linger/Core/Checkpoint.lean` used to build one field-by-field out of decoded bytes
(`specs/archive/vt-toolkit.md` Step 2): every length in that format is an arbitrary-precision
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
`Good` and `Renderable` state is not a checkpoint*.

`private`, which is the whole point: `Linger/Core/Checkpoint.lean` reaches it through
the friend import it already has, and no module outside the toolkit gains the power to
build a `Vt` out of parts. A public smart constructor would be a second public door
admitting every `Good` state — including unreachable ones — which is a wider hole than
the forge it replaces.

The check is in **named stages** rather than a conjunction inside the `if` — the
AGENTS.md "restructure for provability" rule, and it was measured: with the guard
inline, `split at h` in `ofDecoded_good` picks the `match altGrid` nested in the
*condition* instead of the `if`, and the proof falls apart with `hg` bound to nothing
useful. Naming it gives `split` one splittable term. Two stages now, `decodedOk` and
`decodedRenderable`, for the same reason one level down. -/

/-- Screen geometry, cursors and the scroll region — `Good`'s decidable content, and
nothing about the grid. `Vt.decodedRenderable` below is the other half; the door checks
both. -/
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

/-! ### The shape half of the door

`decodedOk` above is `Good`'s content, and `Good` says nothing whatever about the grid:
not its row count, not a row's width, not the shape of the stashed alt screen, not what
a cell holds. That was an **observable** defect and not merely a missing hypothesis
(SCRATCHPAD.md, "the adversarial audit of the seal", finding R2): one flipped byte of a
real 4×2 checkpoint — the `rows` byte, 2 → 3 — decoded to a state that is `Good`, is not
`Renderable`, and whose replay is not the screen it was made from, refuting the
conclusion of `Theorems/Resume.lean`'s `resume_grid` for a state that came off disk. The
grid's length is written as its own `rNat`, so nothing tied it to `rows`.

The deciders below are `Renderable`'s two clauses plus the tab ruler's length, in
`Bool`. Each is a **named stage** with its own `iff` claim in `Theorems/Vt/Renderable.lean`
(`decodedCharOk_iff` … `decodedRenderable_iff`) — for the reason `decodedOk` is one, and
for one more: an `iff` per rung is what keeps the `Bool` and the `Prop` from drifting,
and this is a ladder rather than one flat conjunction.

**What is deliberately NOT checked: the scrollback ring's rows.** `Vt.resize` reinstalls
the grid and the ruler at the new width and leaves the ring rows at their old one (no
reflow — measured in the Step 3 record), so a live session that has ever been resized
holds ring rows wider than `cols`. Checking them would refuse a checkpoint every
reachable state can produce. `Render.restore_sb_exact`'s `hrok` therefore stays
unreachable from disk, which is a named gap rather than an oversight.

**Cost: none worth naming, and that was measured rather than estimated.** The second stage
walks the grid and the stashed grid once — 1920 cell checks at 80×24, 2·10⁶ at the
1000×1000 cap — but `Checkpoint.rRow` already materialises every one of those cells through
`expand`, so the walk is a second pass over data the parser just built. Timed both ways on
the same interpreter (`load` of a filled checkpoint, before the change and after): 80×24
187 vs 189 ms per 20 loads, 200×50 601 vs 603 ms per 10, 1000×1000 30.5 vs 31.0 s per 1 —
i.e. inside the noise, and the 1000×1000 figure is the *parse* being slow, not the
validation. Loads happen once per resume. -/

/-- A codepoint a repaint reproduces as itself: not a C0 control, not DEL. The `Bool`
half of `Emittable` (`decodedCharOk_iff`).

Written as the comparison rather than as `printableChar c == c` on purpose: the two are
equivalent today, and spelling it out means an edit to `printableChar` cannot silently
move what the door accepts. Same reasoning as `Emittable`'s own docstring. -/
private def Vt.decodedCharOk (c : Char) : Bool := 0x20 ≤ c.toNat && c.toNat != 0x7F

/-- A cell a repaint reproduces: an emittable base of exactly the width it claims, and at
most eight zero-width emittable marks. The `Bool` half of `CellOk` (`decodedCellOk_iff`).

A `width = 0` cell is exempt from the width equation because a shadow carries a blank
base (`Cell.shadow`); what ties a shadow to its wide neighbour is `decodedPairOk`. This
clause is the one an attacker reaches most cheaply — `Checkpoint.rCell` reads `base` as
any valid `Char`, `marks` as any list and `width` as any `Nat`, so a cell holding
`'\x0A'` at width 7 was accepted. -/
private def Vt.decodedCellOk (c : Cell) : Bool :=
  Vt.decodedCharOk c.base && (c.width == 0 || charWidth c.base == c.width) && c.marks.length ≤ 8 &&
    c.marks.all (fun m => charWidth m == 0 && Vt.decodedCharOk m)

/-- The pair rule for one column: a width-2 base keeps exactly the shadow a repaint of it
re-creates, and a shadow keeps its base. The `Bool` half of `PairOk`
(`decodedPairOk_iff`).

Out-of-range reads are width-1 default cells (`Row.at`), so a wide base in the final
column is refused here with no special case — the same rule `Row.halfPair` states for the
live path. -/
private def Vt.decodedPairOk (row : Row) (x : Nat) : Bool :=
  ((row.at x).width != 2 || row.at (x + 1) == Cell.shadow (row.at x)) &&
    ((row.at x).width != 0 || (x != 0 && (row.at (x - 1)).width == 2))

/-- A row a repaint reproduces: `cols` wide, every cell and every column pair well
formed. The `Bool` half of `RowOk` (`decodedRowOk_iff`).

`RowOk` quantifies over **all** `x` rather than `x < cols`, and that is what makes this
finite rather than a partial approximation: past the width an out-of-range read is the
default cell, which is `CellOk` and trivially paired, so scanning `[0, cols)` decides the
whole quantifier. -/
private def Vt.decodedRowOk (cols : Nat) (row : Row) : Bool :=
  row.size == cols &&
    (List.range cols).all (fun x => Vt.decodedCellOk (row.at x) && Vt.decodedPairOk row x)

/-- A grid a repaint reproduces: `rows` rows of them. The `Bool` half of `GridOk`
(`decodedGridOk_iff`). Indexed through the same `getD … (blankRow cols {})` as `GridOk`
is, so past the last row both read a blank row of the right width and the two cannot
disagree at the edge. -/
private def Vt.decodedGridOk (cols rows : Nat) (g : Array Row) : Bool :=
  g.size == rows &&
    (List.range rows).all (fun y => Vt.decodedRowOk cols (g.getD y (blankRow cols {})))

/-- The whole shape half: the live screen, the tab ruler's length, and the stashed alt
screen — whose grid was checked *nowhere* before this, only its cursor. The `Bool` half
of `Renderable` ∧ `TabsOk` (`decodedRenderable_iff`). -/
private def Vt.decodedRenderable (cols rows : Nat) (grid : Array Row) (tabs : Array Bool)
    (altGrid : Option (Array Row × Cursor × Pen)) : Bool :=
  Vt.decodedGridOk cols rows grid && tabs.size == cols &&
    (match altGrid with
    | none => true
    | some (g, _, _) => Vt.decodedGridOk cols rows g)

/-- The decoder's door itself: `Good`'s decidable content **and** `Renderable`'s, then the
record. Three of `Good`'s fifteen clauses need no check because this constructor *fixes*
the fields they are about — `pstate := .ground` forces `csiLe`/`oscLe` and `u8need := 0`
forces `u8Le`. Parser state is deliberately not persisted (`Checkpoint.wVt`), so there is
nothing on disk to validate.

Claimed by `Vt.ofDecoded_good` and `Vt.ofDecoded_renderable`/`Vt.ofDecoded_tabsOk`
(nothing bad comes out), `Vt.ofDecoded_of_good` (nothing good is rejected) and
`Vt.ofDecoded_none_of_cols_zero` / `Vt.ofDecoded_none_of_rows_mismatch` (the two canonical
junk records are refused) in `Theorems/Vt/`. -/
private def Vt.ofDecoded (cols rows : Nat) (grid : Array Row) (cursor : Cursor) (pen : Pen)
    (modes : Modes) (top bot : Nat) (tabs : Array Bool) (sb : Ring)
    (altGrid : Option (Array Row × Cursor × Pen)) (saved : Saved) (title : String)
    (g0Line g1Line shiftOut bell : Bool) : Option Vt :=
  if
      Vt.decodedOk cols rows cursor top bot sb altGrid saved &&
        Vt.decodedRenderable cols rows grid tabs altGrid then
    some
      { cols, rows, grid, cursor, pen, modes, top, bot, tabs, sb, altGrid, saved, title, g0Line,
        g1Line, shiftOut, bell, pstate := .ground, u8need := 0, u8acc := 0 }
  else none

/-! ## Grid primitives (all total) -/

/-- Total row read; out of range is a blank row in the current pen. -/
def Vt.getRow (v : Vt) (y : Nat) : Row := v.grid.getD y (blankRow v.cols v.pen)

private def Vt.putCell (v : Vt) (x y : Nat) (c : Cell) : Vt :=
  let row := (v.getRow y).setIfInBounds x c
  { v with grid := v.grid.setIfInBounds y row }

/-- Total cell read; out of range is a default cell. -/
def Vt.getCell (v : Vt) (x y : Nat) : Cell := (v.getRow y).getD x default

/-- Repair every pair in one row. Every cell-writing operation ends here, so
the pair invariant holds by construction rather than per operation. -/
private def Vt.mendRow (v : Vt) (y : Nat) : Vt :=
  { v with grid := v.grid.setIfInBounds y (v.getRow y).mend }

/-- Scroll rows [top, bot] up by one, no questions asked about the
current region. Grid + (optionally) scrollback only — never the
cursor. `allowSb`: evicted top line may go to scrollback (LF at screen
bottom yes, delete-lines no). -/
private def Vt.scrollUpIn (v : Vt) (top bot : Nat) (allowSb : Bool) : Vt :=
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
private def Vt.scrollDownIn (v : Vt) (top bot : Nat) : Vt :=
  let g :=
    (List.range (bot - top)).foldl (fun g i => g.setIfInBounds (bot - i) (v.getRow (bot - i - 1)))
      v.grid
  let g := g.setIfInBounds top (blankRow v.cols v.pen)
  { v with grid := g }

/-- Scroll the active region up; the evicted line goes to scrollback
iff the region is the full screen and we're not in alt. -/
private def Vt.scrollUp (v : Vt) : Vt := v.scrollUpIn v.top v.bot true

private def Vt.scrollDown (v : Vt) : Vt := v.scrollDownIn v.top v.bot

/-! ## Input-controlled repeats -/

/-- Apply `f` `count` times, but at most `cap` times (`repeatAtMost_eq_repeat`). A CSI
count is input and reaches 65535, so every caller passes as `cap` the screen
measurement past which further repeats leave the screen as it is, and the screen's
dimensions are clamped to [1, 1000]. -/
private def Vt.repeatAtMost (v : Vt) (cap count : Nat) (f : Vt → Vt) : Vt :=
  (List.range (min count cap)).foldl (fun w _ => f w) v

/-! ## Cursor motion -/

private def Vt.clearPending (v : Vt) : Vt := { v with cursor := { v.cursor with pending := false } }

private def Vt.moveTo (v : Vt) (x y : Nat) : Vt :=
  let lo := if v.modes.origin then v.top else 0
  let hi := if v.modes.origin then v.bot else v.rows - 1
  { v with cursor := { x := min x (v.cols - 1), y := min (lo + y) hi, pending := false } }

private def Vt.moveRel (v : Vt) (dx dy : Int) : Vt :=
  let nx := (Int.ofNat v.cursor.x + dx).toNat -- Int.toNat clamps at 0
  let ny := (Int.ofNat v.cursor.y + dy).toNat
  -- vertical motion is confined to the scroll region when starting inside it
  let inRegion := v.cursor.y ≥ v.top && v.cursor.y ≤ v.bot
  let lo := if inRegion then v.top else 0
  let hi := if inRegion then v.bot else v.rows - 1
  { v with cursor := { x := min nx (v.cols - 1), y := min (max ny lo) hi, pending := false } }

/-- LF / IND: down one; scrolls when at the region bottom. -/
private def Vt.lineFeed (v : Vt) : Vt :=
  let v := v.clearPending
  if v.cursor.y == v.bot then v.scrollUp
  else
    if v.cursor.y + 1 < v.rows then { v with cursor := { v.cursor with y := v.cursor.y + 1 } }
    else v

/-- RI: up one; scrolls down at the region top. -/
private def Vt.reverseIndex (v : Vt) : Vt :=
  let v := v.clearPending
  if v.cursor.y == v.top then v.scrollDown
  else { v with cursor := { v.cursor with y := v.cursor.y - 1 } }

private def Vt.carriageReturn (v : Vt) : Vt :=
  { v with
    cursor :=
      { v.cursor with
        x := 0, pending := false } }

/-- Set the column only (CHA/HPA): clamped, row untouched. -/
private def Vt.setCol (v : Vt) (x : Nat) : Vt :=
  { v with
    cursor :=
      { v.cursor with
        x := min x (v.cols - 1), pending := false } }

private def Vt.backspace (v : Vt) : Vt :=
  if v.cursor.pending then v.clearPending
  else { v with cursor := { v.cursor with x := v.cursor.x - 1 } }

private def Vt.tab (v : Vt) : Vt :=
  let v := v.clearPending
  let next := (List.range v.cols).find? (fun i => i > v.cursor.x && v.tabs.getD i false)
  { v with cursor := { v.cursor with x := min (next.getD (v.cols - 1)) (v.cols - 1) } }

private def Vt.backTab (v : Vt) : Vt :=
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
private def Vt.printWrap (v : Vt) : Vt :=
  if v.cursor.pending && v.modes.wrap then (v.carriageReturn).lineFeed else v.clearPending

/-- A wide char that cannot fit in the last column wraps early. -/
private def Vt.printWideWrap (v : Vt) (w : Nat) : Vt :=
  if w == 2 && v.cursor.x + 1 ≥ v.cols && v.modes.wrap then (v.carriageReturn).lineFeed else v

/-- IRM: shift the rest of the row right by `w`. Grid only. A pair pushed
off the row end loses its shadow, so the row is mended. -/
private def Vt.printShift (v : Vt) (w : Nat) : Vt :=
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
private def Vt.printPut (v : Vt) (ch : Char) (w : Nat) : Vt :=
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
private def Vt.printAdvance (v : Vt) (w : Nat) : Vt :=
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
private def Vt.printChar (v : Vt) (ch : Char) : Char :=
  printableChar (if (v.shiftOut && v.g1Line) || (!v.shiftOut && v.g0Line) then decLine ch else ch)

/-- A combining mark attaches to the cell before the cursor — and to a wide
glyph's **base**, never to its shadow.

Capped at 8: an adversarial mark stream must not grow a cell (§Bound).

The shadow redirect is what lets a mark on the final column round-trip. A
shadow is a blank continuation cell that a repaint re-creates from its base, so
`Render.rowAnsi` cannot carry marks parked there, `Render.rowText` skips them
outright (they never appeared in `linger capture --history`), and at the right margin the
cursor sits on the shadow with wrap pending — the one position no absolute
cursor move can address.

Under `Renderable` (preserved by `renderable_step`) a column-0 shadow cannot occur; the
`cx0 != 0` guard keeps the step-left total without that hypothesis. -/
private def Vt.printMark (v : Vt) (ch : Char) : Vt :=
  let cx0 := if v.cursor.pending then v.cursor.x else v.cursor.x - 1
  let cx := if (v.getCell cx0 v.cursor.y).width == 0 && cx0 != 0 then cx0 - 1 else cx0
  let cell := v.getCell cx v.cursor.y
  if cell.marks.length ≥ 8 then v
  else (v.putCell cx v.cursor.y { cell with marks := cell.marks ++ [ch] }).mendRow v.cursor.y

/-- Place one printable character at the cursor, handling wrap-pending,
wide characters, insert mode, and combining marks. -/
private def Vt.print (v : Vt) (ch : Char) : Vt :=
  let ch := v.printChar ch
  let w := charWidth ch
  if w == 0 then v.printMark ch
  else ((((v.printWrap).printWideWrap w).printShift w).printPut ch w).printAdvance w

/-! ## Erase / insert / delete -/

private def Vt.eraseRowSpan (v : Vt) (y from_ to_ : Nat) : Vt := -- [from, to)
  let row := v.getRow y
  let row :=
    (List.range (to_ - from_)).foldl
      (fun (r : Row) i => r.setIfInBounds (from_ + i) (Cell.erased v.pen)) row
  { v with grid := v.grid.setIfInBounds y row.mend }

private def Vt.eraseLine (v : Vt) (mode : Nat) : Vt :=
  match mode with
  | 0 => v.eraseRowSpan v.cursor.y v.cursor.x v.cols
  | 1 => v.eraseRowSpan v.cursor.y 0 (v.cursor.x + 1)
  | _ => v.eraseRowSpan v.cursor.y 0 v.cols

private def Vt.eraseScreen (v : Vt) (mode : Nat) : Vt :=
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

private def Vt.insertLines (v : Vt) (n : Nat) : Vt :=
  if v.cursor.y < v.top || v.cursor.y > v.bot then v
  else v.repeatAtMost (v.bot - v.cursor.y + 1) n (·.scrollDownIn v.cursor.y v.bot)

private def Vt.deleteLines (v : Vt) (n : Nat) : Vt :=
  if v.cursor.y < v.top || v.cursor.y > v.bot then v
  else v.repeatAtMost (v.bot - v.cursor.y + 1) n (·.scrollUpIn v.cursor.y v.bot false)

private def Vt.deleteChars (v : Vt) (n : Nat) : Vt :=
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

private def Vt.insertChars (v : Vt) (n : Nat) : Vt :=
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

private def Vt.eraseChars (v : Vt) (n : Nat) : Vt :=
  v.eraseRowSpan v.cursor.y v.cursor.x (min (v.cursor.x + n) v.cols)

/-! ## SGR -/

/-- A 256-colour palette index, saturating at 255. -/
def color256 (n : Nat) : Color := .idx (UInt8.ofNat (min n 255))

/-- One single-number SGR code: a reset, an attribute or a 16-colour index; others are no-ops. -/
private def Vt.sgrAttr (p : Pen) (n : Nat) : Pen :=
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
                              if 30 ≤ n && n ≤ 37 then { p with fg := .idx (UInt8.ofNat (n - 30)) }
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
                                          { p with bg := .idx (UInt8.ofNat (n - 100 + 8)) }
                                        else p

/-- Apply an SGR parameter list; an empty one resets. `38`/`48` take `5;n` or `2;r;g;b`, either
separator, or `2:id:r:g:b` with the colour-space id ignored; other codes go to `sgrAttr`. -/
private def Vt.applySgr (v : Vt) (params : List (Nat × Bool)) : Vt :=
  -- (value, isSubParam)
  let rec go (p : Pen) : List (Nat × Bool) → Pen
    | [] => p
    | (n, _) :: rest =>
      -- extended color: consume its argument chain
      if n == 38 || n == 48 then
        let isFg := n == 38
        match rest with
        | (5, _) :: (idx, _) :: r =>
          let c := color256 idx
          go (if isFg then { p with fg := c } else { p with bg := c }) r
        -- truecolour; four colon sub-arguments lead with a colour-space id, which is skipped
        | (2, _) :: (_, true) :: (r1, true) :: (g1, true) :: (b1, true) :: r |
          (2, _) :: (r1, _) :: (g1, _) :: (b1, _) :: r =>
          let c :=
            Color.rgb (UInt8.ofNat (min r1 255)) (UInt8.ofNat (min g1 255))
              (UInt8.ofNat (min b1 255))
          go (if isFg then { p with fg := c } else { p with bg := c }) r
        | (2, _) :: r => go p r
        | _ => p
      else go (Vt.sgrAttr p n) rest
  let ps := if params.isEmpty then [(0, false)] else params
  { v with pen := go v.pen ps }

/-! ## Alt screen -/

private def Vt.enterAlt (v : Vt) (saveCursor : Bool) : Vt :=
  if v.altGrid.isSome then v -- already there
  else
    let saved := if saveCursor then { cur := v.cursor, pen := v.pen } else v.saved
    { v with
      altGrid := some (v.grid, v.cursor, v.pen),
      grid := Array.replicate v.rows (blankRow v.cols {}), cursor := {}, saved, top := 0,
      bot := v.rows - 1 }

private def Vt.leaveAlt (v : Vt) (restoreCursor : Bool) : Vt :=
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

/-- Resize to clamped dimensions without reflow: keep the bottom rows, truncate or pad
cells, and reset the scroll region and tab ruler. -/
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
              x := min cur.x (c - 1), y := min cur.y (r - 1), pending := false },
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

/-- CSI parameter `i`, reading an omitted or zero value as the given default. -/
def CsiState.arg (s : CsiState) (i default_ : Nat) : Nat :=
  match (s.params.getD i (0, false)).1 with
  | 0 => default_
  | n => n

private def Vt.setMode (v : Vt) (priv : Bool) (n : Nat) (on : Bool) : Vt :=
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

/-- SM/RM apply collected mode numbers in order, retaining each mode's existing
side effects. Unknown numbers (including omitted zero parameters) are no-ops. -/
private def Vt.setModes (v : Vt) (priv : Bool) (ps : List (Nat × Bool)) (on : Bool) : Vt :=
  ps.foldl (fun w p => w.setMode priv p.1 on) v

private def Vt.csiDispatch (v : Vt) (s : CsiState) (final : UInt8) : Vt :=
  if s.ignore then v
  else
    let a1 := s.arg 0 1 -- first arg, default 1
    -- Repeat counts stop where the screen stops changing (`repeatAtMost`): CHT/CBT reach
    -- a margin within `cols` moves and SU/SD blank the region within its height. Like
    -- tmux, SU therefore pushes at most one region of history.
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
    | 0x49 => v.repeatAtMost v.cols a1 Vt.tab -- I CHT
    | 0x4A => v.eraseScreen (s.arg 0 0) -- J ED
    | 0x4B => v.eraseLine (s.arg 0 0) -- K EL
    | 0x4C => v.insertLines a1 -- L IL
    | 0x4D => v.deleteLines a1 -- M DL
    | 0x50 => v.deleteChars a1 -- P DCH
    | 0x53 => v.repeatAtMost (v.bot - v.top + 1) a1 Vt.scrollUp -- S SU
    | 0x54 => v.repeatAtMost (v.bot - v.top + 1) a1 Vt.scrollDown -- T SD
    | 0x58 => v.eraseChars a1 -- X ECH
    | 0x5A => v.repeatAtMost v.cols a1 Vt.backTab -- Z CBT
    | 0x60 => v.setCol (a1 - 1) -- ` HPA
    | 0x61 => v.moveRel (Int.ofNat a1) 0 -- a HPR
    | 0x64 => v.moveTo v.cursor.x (a1 - 1) -- d VPA, relative to DECOM's origin
    | 0x65 => v.moveRel 0 (Int.ofNat a1) -- e VPR
    | 0x66 => v.moveTo (s.arg 1 1 - 1) (a1 - 1) -- f HVP
    | 0x67 => -- g TBC
      match s.arg 0 0 with
      | 0 => { v with tabs := v.tabs.setIfInBounds v.cursor.x false }
      | 3 => { v with tabs := Array.replicate v.cols false }
      | _ => v
    | 0x68 => v.setModes (s.priv == 0x3F) s.params.toList true -- h SM
    | 0x6C => v.setModes (s.priv == 0x3F) s.params.toList false -- l RM
    | 0x6D => if s.priv == 0 then v.applySgr s.params.toList else v -- m SGR
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

/-- A separator closes a parameter, including an omitted one. The empty-prefix
case still contributes a slot; otherwise `CSI ;5H` would be read as `CSI 5H`. -/
def csiPush (s : CsiState) (sub : Bool) : CsiState :=
  if s.params.size ≥ 16 then
    { s with
      ignore := true, cur := 0, haveCur := false }
  else
    { s with
      params := s.params.push (min s.cur 65535, s.curSub), cur := 0, curSub := sub,
      haveCur := false }

private def Vt.csiFinish (v : Vt) (s : CsiState) (final : UInt8) : Vt :=
  -- A final byte closes digits or a trailing omitted parameter. With no digits
  -- and no separator there is no explicit parameter to close.
  let s :=
    if s.haveCur then
      (if s.params.size ≥ 16 then { s with ignore := true }
      else { s with params := s.params.push (min s.cur 65535, s.curSub) })
    else
      match s.params.toList with
      | [] => s
      | _ :: _ => csiPush s false
  let v := v.csiDispatch s final
  { v with pstate := .ground }

private def Vt.oscFinish (v : Vt) (acc : Array UInt8) : Vt :=
  let txt := String.fromUTF8? (ByteArray.mk acc) |>.getD ""
  let v := { v with pstate := .ground }
  match txt.splitOn ";" with
  | code :: rest =>
    if code == "0" || code == "2" then { v with title := String.intercalate ";" rest } else v
  | _ => v

/-- Handle a C0 control byte (valid in most parser states). -/
private def Vt.ctl (v : Vt) (b : UInt8) : Vt :=
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
private def Vt.acceptChar (v : Vt) (n : Nat) : Vt :=
  if n.isValidChar then v.print (Char.ofNat n) else v.print '\uFFFD'

/-- Ground state: printables, C0, ESC, and UTF-8 assembly. DEL is ignored, as after
ESC, after an intermediate and inside CSI. -/
private def Vt.stepGround (v : Vt) (b : UInt8) : Vt :=
  if b == 0x1B then { v with pstate := .esc }
  else
    if b < 0x20 then v.ctl b
    else
      if b == 0x7F then v
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
private def Vt.stepEsc (v : Vt) (b : UInt8) : Vt :=
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
  | 0x1B | 0x7F => v -- ESC ESC and DEL: stay
  | _ =>
    if b ≥ 0x20 && b ≤ 0x2F then { v with pstate := .escInter b }
    else if b ≥ 0x30 && b ≤ 0x7E then { v with pstate := .ground } else v

/-- Consume ESC intermediates until a final byte. Only single '(' / ')'
designations are interpreted; a second intermediate marks the sequence unsupported
without accumulating bytes. DEL and other nonfinal bytes keep it pending. -/
private def Vt.stepEscInter (v : Vt) (i b : UInt8) : Vt :=
  if b ≥ 0x30 && b ≤ 0x7E then
    let v := { v with pstate := .ground }
    if i == 0x28 then { v with g0Line := b == 0x30 } -- ESC ( 0 / B
    else
      if i == 0x29 then { v with g1Line := b == 0x30 } -- ESC ) 0 / B
      else v
  else
    if b == 0x1B then { v with pstate := .esc }
    else
      if b ≥ 0x20 && b ≤ 0x2F then { v with pstate := .escInter 0 }
      else { v with pstate := .escInter i }

/-- Inside CSI. -/
private def Vt.stepCsi (v : Vt) (s : CsiState) (b : UInt8) : Vt :=
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
                if b == 0x7F then v -- DEL is ignored without dropping parameters
                else
                  if b < 0x20 then (v.ctl b) -- C0 inside CSI executes, sequence continues
                  else { v with pstate := .ground }

/-- Inside OSC: accumulate until BEL or ST, with a hard cap. -/
private def Vt.stepOsc (v : Vt) (acc : Array UInt8) (esc : Bool) (b : UInt8) : Vt :=
  if esc && b == 0x5C then v.oscFinish acc -- ESC \\ = ST
  else
    if b == 0x07 then v.oscFinish acc -- BEL
    else
      if b == 0x1B then { v with pstate := .osc acc true }
      else
        if acc.size ≥ 2048 then { v with pstate := .osc acc false } -- §Bound: stop growing
        else { v with pstate := .osc (acc.push b) false }

/-- Inside DCS/SOS/PM/APC: skip to ST. -/
private def Vt.stepStr (v : Vt) (esc : Bool) (b : UInt8) : Vt :=
  if esc && b == 0x5C then { v with pstate := .ground }
  else if b == 0x1B then { v with pstate := .str true } else { v with pstate := .str false }

/-- A stray byte aborts a pending UTF-8 sequence. Named (not inlined in
`step`) so proofs can rewrite `step`'s match scrutinee: it touches only
`u8need`/`u8acc`, never `pstate` (`ps_abortUtf8`). -/
private def Vt.abortUtf8 (v : Vt) (b : UInt8) : Vt :=
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

/-- Observe output with the same parser while discarding history after every byte.
The attach client's one-cell observer needs the title and parser boundary, not
scrollback. Keeping the existing parser also keeps OSC, DCS and UTF-8 chunking
semantics in one place. -/
def Vt.observe (v : Vt) (bytes : List UInt8) : Vt :=
  bytes.foldl (fun w b => { (w.step b) with sb := {} }) v

/-- Forget partial parser state (what a checkpoint deliberately does
not persist — see `Linger.Core.Checkpoint`). -/
def Vt.quiesce (v : Vt) :
    Vt := { v with
    pstate := .ground, u8need := 0, u8acc := 0 }

/-- Feed a `ByteArray` by converting at the call site.

**Test-facing, and named as such**: the daemon's pty path is
`Terminal.feed s.vt s.scan chunk` on a `List UInt8` (`Linger/Core/Session.lean`), and
this definition has no runtime caller. It is kept because `Tests/` and `E2E/` fixtures use
it, and a convenience with callers is reachable code, not the unproved-and-unreachable
state `Theorems/Coverage.lean` rejects. -/
def Vt.feedBytes (v : Vt) (bytes : ByteArray) : Vt := v.feed bytes.toList

end Linger.Core.Vt
