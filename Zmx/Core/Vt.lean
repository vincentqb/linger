/-! # Zmx.Core.Vt — restore-grade terminal emulation, pure

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

namespace Zmx.Core.Vt

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
def Cell.erased (p : Pen) : Cell :=
  { base := ' ', marks := [], width := 1, pen := { bg := p.bg } }

/-! ## Character width (minimal wcwidth)

Three classes: combining/zero-width (0), East-Asian wide + emoji (2),
everything else (1). Ranges cover what real TUI apps emit; a wrong
width here mis-aligns a restore but can never crash anything (§Total
does not depend on this table). -/

def isZeroWidth (c : Nat) : Bool :=
  (0x0300 ≤ c && c ≤ 0x036F) ||   -- combining diacritics
  (0x1AB0 ≤ c && c ≤ 0x1AFF) ||
  (0x20D0 ≤ c && c ≤ 0x20FF) ||
  (0xFE00 ≤ c && c ≤ 0xFE0F) ||   -- variation selectors
  (0xFE20 ≤ c && c ≤ 0xFE2F) ||
  c == 0x200B || c == 0x200C || c == 0x200D || c == 0xFEFF

def isWide (c : Nat) : Bool :=
  (0x1100 ≤ c && c ≤ 0x115F) ||   -- Hangul Jamo leads
  (0x2E80 ≤ c && c ≤ 0x303E) ||   -- CJK radicals … punctuation
  (0x3041 ≤ c && c ≤ 0x33FF) ||   -- kana, CJK misc
  (0x3400 ≤ c && c ≤ 0x4DBF) ||
  (0x4E00 ≤ c && c ≤ 0x9FFF) ||   -- CJK unified
  (0xA000 ≤ c && c ≤ 0xA4CF) ||
  (0xAC00 ≤ c && c ≤ 0xD7A3) ||   -- Hangul syllables
  (0xF900 ≤ c && c ≤ 0xFAFF) ||
  (0xFE30 ≤ c && c ≤ 0xFE4F) ||
  (0xFF00 ≤ c && c ≤ 0xFF60) ||   -- fullwidth forms
  (0xFFE0 ≤ c && c ≤ 0xFFE6) ||
  (0x1F300 ≤ c && c ≤ 0x1F64F) || -- emoji
  (0x1F900 ≤ c && c ≤ 0x1F9FF) ||
  (0x20000 ≤ c && c ≤ 0x2FFFD) ||
  (0x30000 ≤ c && c ≤ 0x3FFFD)

def charWidth (c : Char) : Nat :=
  if isZeroWidth c.toNat then 0 else if isWide c.toNat then 2 else 1

/-! ## Rows and the scrollback ring -/

abbrev Row := Array Cell

def blankRow (cols : Nat) (p : Pen) : Row :=
  Array.replicate cols (Cell.erased p)

/-- Scrollback: a ring over an array. `data.size ≤ cap` is §Bound's
structural invariant — `push` either grows toward the cap or overwrites
in place; nothing else writes. `start` indexes the oldest row. -/
structure Ring where
  data : Array Row := #[]
  start : Nat := 0
  deriving Repr, Inhabited

def sbCap : Nat := 10000

def Ring.push (r : Ring) (row : Row) : Ring :=
  if r.data.size < sbCap then
    { r with data := r.data.push row }
  else
    { data := r.data.setIfInBounds r.start row,
      start := (r.start + 1) % sbCap }

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
  priv : UInt8 := 0            -- leading '?' '<' '=' '>' byte, 0 = none
  params : Array (Nat × Bool) := #[]  -- ≤ 16 of (value ≤ 65535, startedWithColon)
  cur : Nat := 0
  curSub : Bool := false
  haveCur : Bool := false
  inter : UInt8 := 0           -- one intermediate byte is all we honor
  ignore : Bool := false
  deriving Repr, DecidableEq, Inhabited

inductive PState where
  | ground
  | esc                                  -- after ESC
  | escInter (b : UInt8)                 -- after ESC + intermediate (e.g. '(' )
  | csi (s : CsiState)
  | osc (acc : Array UInt8) (esc : Bool) -- collecting OSC, BEL/ST terminated
  | str (esc : Bool)                     -- DCS/SOS/PM/APC: skip to ST
  deriving Repr, DecidableEq, Inhabited

/-! ## The screen -/

structure Cursor where
  x : Nat := 0
  y : Nat := 0
  pending : Bool := false  -- wrap-pending: at right margin, next print wraps
  deriving Repr, DecidableEq, Inhabited

structure Saved where
  cur : Cursor := {}
  pen : Pen := {}
  deriving Repr, DecidableEq, Inhabited

/-- Modes we track. Stored-but-uninterpreted ones exist so a restore
can replay them (`Render.modes`). -/
structure Modes where
  wrap : Bool := true        -- DECAWM
  origin : Bool := false     -- DECOM
  insert : Bool := false     -- IRM
  cursorVisible : Bool := true
  appCursor : Bool := false  -- DECCKM
  appKeypad : Bool := false
  bracketedPaste : Bool := false
  mouse : Nat := 0           -- 0 off; else the last-enabled mode number
  mouseSgr : Bool := false
  focusEvents : Bool := false
  deriving Repr, DecidableEq, Inhabited

structure Vt where
  cols : Nat
  rows : Nat
  grid : Array Row
  cursor : Cursor := {}
  pen : Pen := {}
  modes : Modes := {}
  top : Nat := 0             -- scroll region [top, bot], 0-based inclusive
  bot : Nat
  tabs : Array Bool          -- size cols
  sb : Ring := {}            -- scrollback (main screen only)
  altGrid : Option (Array Row × Cursor × Pen) := none  -- stashed MAIN state while in alt
  saved : Saved := {}
  title : String := ""
  g0Line : Bool := false     -- G0 is DEC line-drawing
  g1Line : Bool := false
  shiftOut : Bool := false   -- SO selected G1
  pstate : PState := .ground
  u8need : Nat := 0          -- UTF-8 continuation bytes still expected (≤ 3)
  u8acc : Nat := 0           -- accumulated codepoint bits
  bell : Bool := false       -- sticky until the runtime clears it (activity signal)
  deriving Repr, Inhabited

def clampDim (n : Nat) : Nat := min (max n 1) 1000

def defaultTabs (cols : Nat) : Array Bool :=
  (Array.range cols).map (fun i => i % 8 == 0 && i != 0)

def Vt.init (cols rows : Nat) : Vt :=
  let c := clampDim cols
  let r := clampDim rows
  { cols := c, rows := r,
    grid := Array.replicate r (blankRow c {}),
    bot := r - 1,
    tabs := defaultTabs c }

/-! ## Grid primitives (all total) -/

def Vt.getRow (v : Vt) (y : Nat) : Row := v.grid.getD y (blankRow v.cols v.pen)

def Vt.putCell (v : Vt) (x y : Nat) (c : Cell) : Vt :=
  let row := (v.getRow y).setIfInBounds x c
  { v with grid := v.grid.setIfInBounds y row }

def Vt.getCell (v : Vt) (x y : Nat) : Cell := (v.getRow y).getD x default

/-- Scroll rows [top, bot] up by one, no questions asked about the
current region. Grid + (optionally) scrollback only — never the
cursor. `allowSb`: evicted top line may go to scrollback (LF at screen
bottom yes, delete-lines no). -/
def Vt.scrollUpIn (v : Vt) (top bot : Nat) (allowSb : Bool) : Vt :=
  let evicted := v.getRow top
  let g := (List.range (bot - top)).foldl
    (fun g i => g.setIfInBounds (top + i) (v.getRow (top + i + 1))) v.grid
  let g := g.setIfInBounds bot (blankRow v.cols v.pen)
  if allowSb && top == 0 && bot == v.rows - 1 && v.altGrid.isNone then
    { v with grid := g, sb := v.sb.push evicted }
  else
    { v with grid := g }

/-- Scroll rows [top, bot] down by one. Grid only. -/
def Vt.scrollDownIn (v : Vt) (top bot : Nat) : Vt :=
  let g := (List.range (bot - top)).foldl
    (fun g i => g.setIfInBounds (bot - i) (v.getRow (bot - i - 1))) v.grid
  let g := g.setIfInBounds top (blankRow v.cols v.pen)
  { v with grid := g }

/-- Scroll the active region up; the evicted line goes to scrollback
iff the region is the full screen and we're not in alt. -/
def Vt.scrollUp (v : Vt) : Vt := v.scrollUpIn v.top v.bot true

def Vt.scrollDown (v : Vt) : Vt := v.scrollDownIn v.top v.bot

/-! ## Cursor motion -/

def Vt.clearPending (v : Vt) : Vt :=
  { v with cursor := { v.cursor with pending := false } }

def Vt.moveTo (v : Vt) (x y : Nat) : Vt :=
  let lo := if v.modes.origin then v.top else 0
  let hi := if v.modes.origin then v.bot else v.rows - 1
  { v with cursor := { x := min x (v.cols - 1), y := min (lo + y) hi, pending := false } }

def Vt.moveRel (v : Vt) (dx dy : Int) : Vt :=
  let nx := (Int.ofNat v.cursor.x + dx).toNat  -- Int.toNat clamps at 0
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
  else if v.cursor.y + 1 < v.rows then
    { v with cursor := { v.cursor with y := v.cursor.y + 1 } }
  else v

/-- RI: up one; scrolls down at the region top. -/
def Vt.reverseIndex (v : Vt) : Vt :=
  let v := v.clearPending
  if v.cursor.y == v.top then v.scrollDown
  else { v with cursor := { v.cursor with y := v.cursor.y - 1 } }

def Vt.carriageReturn (v : Vt) : Vt :=
  { v with cursor := { v.cursor with x := 0, pending := false } }

/-- Set the column only (CHA/HPA): clamped, row untouched. -/
def Vt.setCol (v : Vt) (x : Nat) : Vt :=
  { v with cursor := { v.cursor with x := min x (v.cols - 1), pending := false } }

def Vt.backspace (v : Vt) : Vt :=
  if v.cursor.pending then v.clearPending
  else { v with cursor := { v.cursor with x := v.cursor.x - 1 } }

def Vt.tab (v : Vt) : Vt :=
  let v := v.clearPending
  let next := (List.range v.cols).find?
    (fun i => i > v.cursor.x && v.tabs.getD i false)
  { v with cursor := { v.cursor with x := min (next.getD (v.cols - 1)) (v.cols - 1) } }

def Vt.backTab (v : Vt) : Vt :=
  let prev := (List.range v.cursor.x).foldl
    (fun acc i => if v.tabs.getD i false then some i else acc) none
  -- the found stop is < cursor.x < cols already; the clamp makes the
  -- bound local so §Total doesn't need a foldl invariant
  { v with cursor :=
      { v.cursor with x := min (prev.getD 0) (v.cols - 1), pending := false } }

/-! ## Printing -/

/-- DEC special graphics for box drawing (ESC ( 0). -/
def decLine (c : Char) : Char :=
  match c with
  | 'j' => '┘' | 'k' => '┐' | 'l' => '┌' | 'm' => '└' | 'n' => '┼'
  | 'q' => '─' | 't' => '├' | 'u' => '┤' | 'v' => '┴' | 'w' => '┬'
  | 'x' => '│' | 'a' => '▒' | '`' => '◆' | '~' => '·' | 'f' => '°'
  | 'g' => '±' | 'o' => '⎺' | 's' => '⎽' | '0' => '█'
  | _ => c

/-- Wrap-pending resolution: if a previous print left us hanging at the
right margin, a new printable wraps to the next line first (DECAWM). -/
def Vt.printWrap (v : Vt) : Vt :=
  if v.cursor.pending && v.modes.wrap then (v.carriageReturn).lineFeed
  else v.clearPending

/-- A wide char that cannot fit in the last column wraps early. -/
def Vt.printWideWrap (v : Vt) (w : Nat) : Vt :=
  if w == 2 && v.cursor.x + 1 ≥ v.cols && v.modes.wrap then (v.carriageReturn).lineFeed
  else v

/-- IRM: shift the rest of the row right by `w`. Grid only. -/
def Vt.printShift (v : Vt) (w : Nat) : Vt :=
  if v.modes.insert then
    let x := v.cursor.x
    let row := v.getRow v.cursor.y
    let shifted := (List.range (v.cols - x - w)).foldl
      (fun (r : Row) iRev =>
        let i := v.cols - 1 - iRev
        r.setIfInBounds i (row.getD (i - w) default))
      row
    { v with grid := v.grid.setIfInBounds v.cursor.y shifted }
  else v

/-- Write the glyph (and its shadow cell if wide). Grid only. -/
def Vt.printPut (v : Vt) (ch : Char) (w : Nat) : Vt :=
  let x := v.cursor.x
  let y := v.cursor.y
  let v' := v.putCell x y { base := ch, marks := [], width := w, pen := v.pen }
  if w == 2 then
    v'.putCell (x + 1) y { base := ' ', marks := [], width := 0, pen := v.pen }
  else v'

/-- Advance the cursor by `w`, arming wrap-pending at the margin. -/
def Vt.printAdvance (v : Vt) (w : Nat) : Vt :=
  let nx := v.cursor.x + w
  if nx ≥ v.cols then
    { v with cursor := { v.cursor with x := v.cols - 1, pending := v.modes.wrap } }
  else
    { v with cursor := { v.cursor with x := nx, pending := false } }

/-- Place one printable character at the cursor, handling wrap-pending,
wide characters, insert mode, and combining marks. -/
def Vt.print (v : Vt) (ch : Char) : Vt :=
  let ch := if (v.shiftOut && v.g1Line) || (!v.shiftOut && v.g0Line)
            then decLine ch else ch
  let w := charWidth ch
  if w == 0 then
    -- combining mark: attach to the cell before the cursor (capped:
    -- adversarial mark-streams must not grow a cell — §Bound)
    let cx := if v.cursor.pending then v.cursor.x
              else if v.cursor.x == 0 then 0 else v.cursor.x - 1
    let cell := v.getCell cx v.cursor.y
    if cell.marks.length ≥ 8 then v
    else v.putCell cx v.cursor.y { cell with marks := cell.marks ++ [ch] }
  else
    ((((v.printWrap).printWideWrap w).printShift w).printPut ch w).printAdvance w

/-! ## Erase / insert / delete -/

def Vt.eraseRowSpan (v : Vt) (y from_ to_ : Nat) : Vt :=  -- [from, to)
  let row := v.getRow y
  let row := (List.range (to_ - from_)).foldl
    (fun (r : Row) i => r.setIfInBounds (from_ + i) (Cell.erased v.pen)) row
  { v with grid := v.grid.setIfInBounds y row }

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
  let row := (List.range (v.cols - x)).foldl
    (fun (r : Row) i =>
      let src := x + i + n
      r.setIfInBounds (x + i)
        (if src < v.cols then row.getD src default else Cell.erased v.pen))
    row
  { v with grid := v.grid.setIfInBounds y row }

def Vt.insertChars (v : Vt) (n : Nat) : Vt :=
  let x := v.cursor.x
  let y := v.cursor.y
  let n := min n (v.cols - x)
  let row := v.getRow y
  let row := (List.range (v.cols - x)).foldl
    (fun (r : Row) iRev =>
      let i := v.cols - 1 - iRev
      r.setIfInBounds i
        (if i ≥ x + n then row.getD (i - n) default else Cell.erased v.pen))
    row
  { v with grid := v.grid.setIfInBounds y row }

def Vt.eraseChars (v : Vt) (n : Nat) : Vt :=
  v.eraseRowSpan v.cursor.y v.cursor.x (min (v.cursor.x + n) v.cols)

/-! ## SGR -/

def color256 (n : Nat) : Color := .idx (UInt8.ofNat (min n 255))

/-- Apply one SGR parameter chain. Handles 38/48 in both `38;5;n` /
`38;2;r;g;b` (semicolon) and `38:5:n` / `38:2::r:g:b` (colon) forms. -/
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
              | (r1, _) :: (g1, _) :: (b1, _) :: tl =>
                (some (r1, g1, b1), tl)
              | tl => (none, tl)
            match rgb with
            | some (r1, g1, b1) =>
              let c := Color.rgb (UInt8.ofNat (min r1 255)) (UInt8.ofNat (min g1 255))
                        (UInt8.ofNat (min b1 255))
              go (if isFg then { p with fg := c } else { p with bg := c }) r fuel
            | none => go p r fuel
          | _ => p
        else
          let p :=
            if n == 0 then {}
            else if n == 1 then { p with bold := true }
            else if n == 2 then { p with dim := true }
            else if n == 3 then { p with italic := true }
            else if n == 4 then { p with underline := true }
            else if n == 5 || n == 6 then { p with blink := true }
            else if n == 7 then { p with reverse := true }
            else if n == 9 then { p with strike := true }
            else if n == 21 || n == 22 then { p with bold := false, dim := false }
            else if n == 23 then { p with italic := false }
            else if n == 24 then { p with underline := false }
            else if n == 25 then { p with blink := false }
            else if n == 27 then { p with reverse := false }
            else if n == 29 then { p with strike := false }
            else if 30 ≤ n && n ≤ 37 then { p with fg := .idx (UInt8.ofNat (n - 30)) }
            else if n == 39 then { p with fg := .default }
            else if 40 ≤ n && n ≤ 47 then { p with bg := .idx (UInt8.ofNat (n - 40)) }
            else if n == 49 then { p with bg := .default }
            else if 90 ≤ n && n ≤ 97 then { p with fg := .idx (UInt8.ofNat (n - 90 + 8)) }
            else if 100 ≤ n && n ≤ 107 then { p with bg := .idx (UInt8.ofNat (n - 100 + 8)) }
            else p
          go p rest fuel
  let ps := if params.isEmpty then [(0, false)] else params
  { v with pen := go v.pen ps (ps.length + 1) }

/-! ## Alt screen -/

def Vt.enterAlt (v : Vt) (saveCursor : Bool) : Vt :=
  if v.altGrid.isSome then v  -- already there
  else
    let saved := if saveCursor then { cur := v.cursor, pen := v.pen } else v.saved
    { v with altGrid := some (v.grid, v.cursor, v.pen),
             grid := Array.replicate v.rows (blankRow v.cols {}),
             cursor := {}, saved,
             top := 0, bot := v.rows - 1 }

def Vt.leaveAlt (v : Vt) (restoreCursor : Bool) : Vt :=
  match v.altGrid with
  | none => v
  | some (g, cur, pen) =>
    { v with altGrid := none, grid := g,
             cursor := if restoreCursor then cur else v.cursor,
             pen := if restoreCursor then pen else v.pen,
             top := 0, bot := v.rows - 1 }

/-! ## Resize (truncate/pad; no reflow — see header) -/

def resizeRow (row : Row) (cols : Nat) (p : Pen) : Row :=
  if row.size ≥ cols then row.extract 0 cols
  else row ++ Array.replicate (cols - row.size) (Cell.erased p)

def Vt.resize (v : Vt) (cols rows : Nat) : Vt :=
  let c := clampDim cols
  let r := clampDim rows
  let fit := fun (g : Array Row) =>
    let g := g.map (resizeRow · c {})
    if g.size ≥ r then g.extract (g.size - r) g.size  -- keep the bottom
    else g ++ Array.replicate (r - g.size) (blankRow c {})
  { v with cols := c, rows := r,
           grid := fit v.grid,
           altGrid := v.altGrid.map (fun (g, cur, pen) =>
             (fit g, { cur with x := min cur.x (c-1), y := min cur.y (r-1) }, pen)),
           cursor := { v.cursor with
             x := min v.cursor.x (c - 1),
             y := min v.cursor.y (r - 1),
             pending := false },
           -- the saved cursor must shrink too, or DECRC after a
           -- shrink restores an out-of-bounds position (§Total)
           saved := { cur := { x := min v.saved.cur.x (c - 1),
                               y := min v.saved.cur.y (r - 1),
                               pending := false },
                      pen := v.saved.pen },
           top := 0, bot := r - 1,
           tabs := defaultTabs c }

/-! ## CSI dispatch -/

def CsiState.arg (s : CsiState) (i default_ : Nat) : Nat :=
  match (s.params.getD i (0, false)).1 with
  | 0 => default_
  | n => n

/-- Params paired with their sub-param flags, for SGR. -/
def CsiState.sgrParams (s : CsiState) : List (Nat × Bool) :=
  s.params.toList

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
  let a1 := s.arg 0 1  -- first arg, default 1
  match final with
  | 0x40 => v.insertChars a1                                  -- @ ICH
  | 0x41 => v.moveRel 0 (-(Int.ofNat a1))                     -- A CUU
  | 0x42 => v.moveRel 0 (Int.ofNat a1)                        -- B CUD
  | 0x43 => v.moveRel (Int.ofNat a1) 0                        -- C CUF
  | 0x44 => v.moveRel (-(Int.ofNat a1)) 0                     -- D CUB
  | 0x45 => (v.moveRel 0 (Int.ofNat a1)).carriageReturn       -- E CNL
  | 0x46 => (v.moveRel 0 (-(Int.ofNat a1))).carriageReturn    -- F CPL
  | 0x47 => v.setCol (a1 - 1)                                 -- G CHA
  | 0x48 => v.moveTo (s.arg 1 1 - 1) (a1 - 1)                 -- H CUP
  | 0x49 => (List.range a1).foldl (fun a _ => a.tab) v        -- I CHT
  | 0x4A => v.eraseScreen (s.arg 0 0)                         -- J ED
  | 0x4B => v.eraseLine (s.arg 0 0)                           -- K EL
  | 0x4C => v.insertLines a1                                  -- L IL
  | 0x4D => v.deleteLines a1                                  -- M DL
  | 0x50 => v.deleteChars a1                                  -- P DCH
  | 0x53 => (List.range a1).foldl (fun a _ => a.scrollUp) v   -- S SU
  | 0x54 => (List.range a1).foldl (fun a _ => a.scrollDown) v -- T SD
  | 0x58 => v.eraseChars a1                                   -- X ECH
  | 0x5A => (List.range a1).foldl (fun a _ => a.backTab) v    -- Z CBT
  | 0x60 => v.setCol (a1 - 1)                                 -- ` HPA
  | 0x61 => v.moveRel (Int.ofNat a1) 0                        -- a HPR
  | 0x64 =>                                                    -- d VPA
      { v with cursor :=
          { v.cursor with y := min (a1 - 1) (v.rows - 1), pending := false } }
  | 0x65 => v.moveRel 0 (Int.ofNat a1)                        -- e VPR
  | 0x66 => v.moveTo (s.arg 1 1 - 1) (a1 - 1)                 -- f HVP
  | 0x67 =>                                                    -- g TBC
      match s.arg 0 0 with
      | 0 => { v with tabs := v.tabs.setIfInBounds v.cursor.x false }
      | 3 => { v with tabs := Array.replicate v.cols false }
      | _ => v
  | 0x68 => v.setMode (s.priv == 0x3F) (s.arg 0 0) true       -- h SM
  | 0x6C => v.setMode (s.priv == 0x3F) (s.arg 0 0) false      -- l RM
  | 0x6D => if s.priv == 0 then v.applySgr s.sgrParams else v -- m SGR
  | 0x72 =>                                                    -- r DECSTBM
      if s.priv != 0 then v else
      let t := s.arg 0 1 - 1
      let b := s.arg 1 v.rows - 1
      if t < b && b < v.rows then
        ({ v with top := t, bot := b }).moveTo 0 0
      else v
  | 0x73 => { v with saved := { cur := v.cursor, pen := v.pen } }  -- s DECSC (ANSI)
  | 0x75 => { v with cursor := v.saved.cur, pen := v.saved.pen }   -- u DECRC (ANSI)
  | _ => v  -- DA/DSR/CPR/DECSCUSR/… : queries and styling we don't act on

/-! ## Byte-at-a-time parser -/

def csiPush (s : CsiState) (sub : Bool) : CsiState :=
  if s.haveCur || s.params.size > 0 || sub then
    -- close the current parameter
    if s.params.size ≥ 16 then { s with ignore := true, cur := 0, haveCur := false }
    else { s with params := s.params.push (min s.cur 65535, s.curSub),
                  cur := 0, curSub := sub, haveCur := false }
  else { s with curSub := sub }

def Vt.csiFinish (v : Vt) (s : CsiState) (final : UInt8) : Vt :=
  -- close any pending parameter, then dispatch
  let s := if s.haveCur then
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
    if code == "0" || code == "2" then
      { v with title := String.intercalate ";" rest }
    else v
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
  if n.isValidChar then v.print (Char.ofNat n)
  else v.print '\uFFFD'

/-- Ground state: printables, C0, ESC, and UTF-8 assembly. -/
def Vt.stepGround (v : Vt) (b : UInt8) : Vt :=
  if b == 0x1B then { v with pstate := .esc }
  else if b < 0x20 then v.ctl b
  else if b < 0x80 then v.acceptChar b.toNat
  else if b < 0xC0 then
    -- continuation byte
    if v.u8need == 0 then v  -- orphan: drop
    else
      -- clamp keeps §Bound trivial; valid sequences never reach it
      let acc := min (v.u8acc * 64 + (b.toNat - 0x80)) 2097151
      if v.u8need == 1 then
        ({ v with u8need := 0, u8acc := 0 }).acceptChar acc
      else { v with u8need := v.u8need - 1, u8acc := acc }
  else if b < 0xE0 then { v with u8need := 1, u8acc := b.toNat - 0xC0 }
  else if b < 0xF0 then { v with u8need := 2, u8acc := b.toNat - 0xE0 }
  else if b < 0xF8 then { v with u8need := 3, u8acc := b.toNat - 0xF0 }
  else v

/-- After ESC. -/
def Vt.stepEsc (v : Vt) (b : UInt8) : Vt :=
  match b with
  | 0x5B => { v with pstate := .csi {} }                       -- [
  | 0x5D => { v with pstate := .osc #[] false }                -- ]
  | 0x50 | 0x58 | 0x5E | 0x5F => { v with pstate := .str false } -- P X ^ _
  | 0x37 => { v with saved := { cur := v.cursor, pen := v.pen },  -- 7 DECSC
                     pstate := .ground }
  | 0x38 => { v with cursor := v.saved.cur, pen := v.saved.pen,   -- 8 DECRC
                     pstate := .ground }
  | 0x44 => { v.lineFeed with pstate := .ground }                 -- D IND
  | 0x45 => { (v.carriageReturn).lineFeed with pstate := .ground } -- E NEL
  | 0x48 => { v with tabs := v.tabs.setIfInBounds v.cursor.x true, -- H HTS
                     pstate := .ground }
  | 0x4D => { v.reverseIndex with pstate := .ground }             -- M RI
  | 0x63 =>                                                      -- c RIS
    let fresh := Vt.init v.cols v.rows
    { fresh with sb := if v.altGrid.isNone then v.sb else ({} : Ring) }
  | 0x3D => { v with modes := { v.modes with appKeypad := true }, pstate := .ground }
  | 0x3E => { v with modes := { v.modes with appKeypad := false }, pstate := .ground }
  | 0x1B => v  -- ESC ESC: stay
  | _ =>
    if b == 0x28 || b == 0x29 || b == 0x2A || b == 0x2B then
      { v with pstate := .escInter b }
    else { v with pstate := .ground }

/-- After ESC + intermediate: charset designation. -/
def Vt.stepEscInter (v : Vt) (i b : UInt8) : Vt :=
  let v := { v with pstate := .ground }
  if i == 0x28 then { v with g0Line := b == 0x30 }        -- ESC ( 0 / B
  else if i == 0x29 then { v with g1Line := b == 0x30 }   -- ESC ) 0 / B
  else v

/-- Inside CSI. -/
def Vt.stepCsi (v : Vt) (s : CsiState) (b : UInt8) : Vt :=
  if b ≥ 0x30 && b ≤ 0x39 then
    { v with pstate := .csi { s with cur := min (s.cur * 10 + (b.toNat - 0x30)) 65535,
                                     haveCur := true } }
  else if b == 0x3B then { v with pstate := .csi (csiPush s false) }
  else if b == 0x3A then { v with pstate := .csi (csiPush s true) }
  else if b ≥ 0x3C && b ≤ 0x3F then
    { v with pstate := .csi { s with priv := b } }
  else if b ≥ 0x20 && b ≤ 0x2F then
    { v with pstate := .csi { s with inter := b } }
  else if b ≥ 0x40 && b ≤ 0x7E then
    if s.inter != 0 then { v with pstate := .ground }  -- e.g. DECSCUSR: ignore
    else v.csiFinish s b
  else if b == 0x1B then { v with pstate := .esc }
  else if b < 0x20 then (v.ctl b) -- C0 inside CSI executes, sequence continues
  else { v with pstate := .ground }

/-- Inside OSC: accumulate until BEL or ST, with a hard cap. -/
def Vt.stepOsc (v : Vt) (acc : Array UInt8) (esc : Bool) (b : UInt8) : Vt :=
  if esc && b == 0x5C then v.oscFinish acc            -- ESC \\ = ST
  else if b == 0x07 then v.oscFinish acc              -- BEL
  else if b == 0x1B then { v with pstate := .osc acc true }
  else if acc.size ≥ 2048 then { v with pstate := .osc acc false } -- §Bound: stop growing
  else { v with pstate := .osc (acc.push b) false }

/-- Inside DCS/SOS/PM/APC: skip to ST. -/
def Vt.stepStr (v : Vt) (esc : Bool) (b : UInt8) : Vt :=
  if esc && b == 0x5C then { v with pstate := .ground }
  else if b == 0x1B then { v with pstate := .str true }
  else { v with pstate := .str false }

/-- The single-byte step — §Total's subject. -/
def Vt.step (v : Vt) (b : UInt8) : Vt :=
  -- a stray byte aborts a pending UTF-8 sequence
  let v := if v.u8need > 0 && (b < 0x80 || b ≥ 0xC0) then
      { v with u8need := 0, u8acc := 0 }
    else v
  match v.pstate with
  | .ground => v.stepGround b
  | .esc => v.stepEsc b
  | .escInter i => v.stepEscInter i b
  | .csi s => v.stepCsi s b
  | .osc acc esc => v.stepOsc acc esc b
  | .str esc => v.stepStr esc b

/-- Feed a chunk. §Chunk holds definitionally: `List.foldl_append`. -/
def Vt.feed (v : Vt) (bytes : List UInt8) : Vt :=
  bytes.foldl Vt.step v

/-- Forget partial parser state (what a checkpoint deliberately does
not persist — see `Zmx.Core.Checkpoint`). -/
def Vt.quiesce (v : Vt) : Vt :=
  { v with pstate := .ground, u8need := 0, u8acc := 0 }

/-- The runtime hands us `ByteArray`s; convert at the boundary. -/
def Vt.feedBytes (v : Vt) (bytes : ByteArray) : Vt :=
  v.feed bytes.toList

end Zmx.Core.Vt
