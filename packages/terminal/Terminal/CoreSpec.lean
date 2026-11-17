module

public section

/-! # What terminal headlines are stated in

The values a terminal shows (colours, pens, cells, rows, modes and the screen settings a
repaint keeps), the bytes it is fed and the brackets of a synchronized update, the rows a history
keeps and the output that may ask to erase it, the marks a shell sends around its prompt and its
commands, and predicates over the emulator's operations, which they take as parameters.
Bodies are exposed: each definition here is its own specification.

`Live` is the least set of states containing a fresh emulator and closed under what a live
session does to one: feed pty bytes, resize on attach, forget partial parser state (what a
checkpoint save and load does) and come off disk through the decoder's door. Headline theorems
about repainting and checkpoints assume it of the terminals involved. Every state a program
can hold satisfies it: a fresh screen and the decoder are the only doors, and the session
transformers the only ways forward (`packages/terminal/Terminal/CoreCode/Vt.lean` lists them). It does not say a
scrollback row is the screen's width: a resize leaves the scrollback at its old width.

`Shows` and `Restores` say what a repaint leaves its receiver holding, through the emulator's
accessors and its feed, so no definition here names how the emulator stores a state. `Shows`
compares the screens two terminals show. `Restores` says what any receiver holds, what one as
tall as the terminal holds, and what a live receiver of a live terminal's size holds: the screen,
and, between control sequences, that no later output tells the two apart, which reaches what
the emulator reads and no accessor shows, such as a tab stop or the cursor DECSC saved.

`Replay.Emits` is the output of streaming a repaint plan one bounded step at a time. -/

namespace Terminal.Vt

/-- A cell colour: the terminal default, a 256-colour palette index, or 24-bit RGB. -/
inductive Color where
  /-- The receiving terminal's own default. -/
  | default
  /-- An entry of the 256-colour palette. -/
  | idx (i : UInt8)
  /-- A 24-bit colour, by red, green and blue. -/
  | rgb (r g b : UInt8)
  deriving Repr, DecidableEq, Inhabited

/-- The SGR state written into new cells: colours and text attributes. -/
structure Pen where
  /-- Foreground colour. -/
  fg : Color := .default
  /-- Background colour, which erased cells keep. -/
  bg : Color := .default
  /-- Bold (SGR 1). -/
  bold : Bool := false
  /-- Faint (SGR 2). -/
  dim : Bool := false
  /-- Italic (SGR 3). -/
  italic : Bool := false
  /-- Underlined (SGR 4). -/
  underline : Bool := false
  /-- Blinking (SGR 5 or 6). -/
  blink : Bool := false
  /-- Reverse video (SGR 7). -/
  reverse : Bool := false
  /-- Struck through (SGR 9). -/
  strike : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- One grid cell. The decoder does not check scrollback rows, so a cell loaded into
scrollback can hold values the emulator never writes. -/
structure Cell where
  /-- The character drawn; a blank in a shadow cell. -/
  base : Char := ' '
  /-- Combining characters drawn with `base`, usually none; printing attaches at most eight. -/
  marks : List Char := []
  /-- Display columns: 1, or 2 for the leading cell of a wide character and 0 for the shadow
  cell to its right. -/
  width : Nat := 1
  /-- The colours and attributes the cell is drawn with. -/
  pen : Pen := {}
  deriving Repr, DecidableEq, Inhabited

/-- One screen row of cells. -/
abbrev Row := Array Cell

/-- Modes we track: the settings a program makes on its terminal, the cursor's shape among
them. Stored-but-uninterpreted ones exist so a restore can replay them (`Render.modesAnsi`). -/
structure Modes where
  /-- Autowrap at the right margin (DECAWM, private mode 7). -/
  wrap : Bool := true
  /-- Origin mode (DECOM, private mode 6): cursor rows are relative to the scroll region. -/
  origin : Bool := false
  /-- Insert mode (IRM, mode 4): printing shifts the rest of the row right. -/
  insert : Bool := false
  /-- Cursor visibility (DECTCEM, private mode 25). -/
  cursorVisible : Bool := true
  /-- Application cursor keys (DECCKM, private mode 1). -/
  appCursor : Bool := false
  /-- Application keypad, set by `ESC =` and cleared by `ESC >`. -/
  appKeypad : Bool := false
  /-- Bracketed paste (private mode 2004). -/
  bracketedPaste : Bool := false
  /-- Mouse tracking: 0 when off, else the last enabled of private modes 1000, 1002 and
  1003. A loaded checkpoint can hold any number here. -/
  mouse : Nat := 0
  /-- SGR mouse encoding (private mode 1006). -/
  mouseSgr : Bool := false
  /-- Focus reporting (private mode 1004). -/
  focusEvents : Bool := false
  /-- The cursor's shape, as DECSCUSR (`CSI Ps SP q`) sets it: 0 for the terminal's own
  default, then a blinking or steady block (1, 2), underline (3, 4) or bar (5, 6). -/
  cursorShape : Fin 7 := 0
  deriving Repr, DecidableEq, Inhabited

/-- Clamp a requested dimension to [1, 1000]. -/
@[expose]
def clampDim (n : Nat) : Nat := min (max n 1) 1000

/-- The newest `n` entries of a list kept oldest first, as a history that keeps `n` rows holds
them. -/
@[expose]
def newest {α : Type} (n : Nat) (l : List α) : List α := l.drop (l.length - n)

/-- Where a scan of output for a request to erase history stands: outside one, or after a `[`
and bytes below `@` (0x40) or DEL, having seen a `3` among them or not. -/
inductive EraseScan where
  /-- No `[` begins a possible request. -/
  | outside
  /-- After a `[` and bytes below `@` or DEL, among which a `3` when `three` holds. -/
  | inside (three : Bool)
  deriving DecidableEq

/-- The scan after one more byte: a `[` begins a possible request, and any byte but one below `@`
or DEL ends it. -/
@[expose]
def EraseScan.next (scan : EraseScan) (b : UInt8) : EraseScan :=
  if b = 0x5B then .inside false
  else
    match scan with
    | .inside three => if b < 0x40 ∨ b = 0x7F then .inside (three || b == 0x33) else .outside
    | .outside => .outside

/-- Whether output, scanned from `scan`, may ask to erase history: a `J` comes after a `[` and
bytes below `@` or DEL among which a `3`. -/
@[expose]
def EraseScan.finds (scan : EraseScan) : List UInt8 → Bool
  | [] => false
  | b :: bs => decide (scan = .inside true ∧ b = 0x4A) || (scan.next b).finds bs

/-- Whether output may ask a terminal to erase its history: it holds a `[`, then bytes below `@`
(0x40) or DEL among which a `3`, then `J`, the shape of the erase request `CSI 3 J`. -/
@[expose]
def mayErase (bytes : List UInt8) : Bool := EraseScan.outside.finds bytes

/-- The receiver fields a repaint establishes and then must not disturb: the screen height,
the scroll region, the character sets, the shift state and the screen selection. -/
structure Sticky where
  /-- Screen height. -/
  rows : Nat
  /-- Top row of the scroll region, 0-based. -/
  top : Nat
  /-- Bottom row of the scroll region, 0-based and inclusive. -/
  bot : Nat
  /-- G0 is DEC line drawing. -/
  g0 : Bool
  /-- G1 is DEC line drawing. -/
  g1 : Bool
  /-- Shift Out selected G1. -/
  so : Bool
  /-- The alternate screen is current. -/
  alt : Bool

/-- The states a live session can hold, given the emulator's operations: a fresh screen of a
requested size, feeding bytes, resizing, forgetting partial parser state, and the states the
decoder's door admits. -/
inductive Live {S : Type} (init : Nat → Nat → S) (feed : S → List UInt8 → S)
    (resize : S → Nat → Nat → S) (quiesce : S → S) (decodable : S → Prop) : S → Prop where
  /-- A fresh screen. -/
  | init (cols rows : Nat) : Live init feed resize quiesce decodable (init cols rows)
  /-- Pty output fed to a state a session holds. -/
  |
  feed {v : S} (h : Live init feed resize quiesce decodable v) (bytes : List UInt8) :
    Live init feed resize quiesce decodable (feed v bytes)
  /-- A resize of a state a session holds. -/
  |
  resize {v : S} (h : Live init feed resize quiesce decodable v) (cols rows : Nat) :
    Live init feed resize quiesce decodable (resize v cols rows)
  /-- A state a session holds, with its partial parser state forgotten. -/
  |
  quiesce {v : S} (h : Live init feed resize quiesce decodable v) :
    Live init feed resize quiesce decodable (quiesce v)
  /-- **The resume rung.** A state the decoder's door accepts is one a live session can hold:
  not because the record on disk was trustworthy, but because the door refuses every record
  that does not describe such a state. The premise is the door's own acceptance, never a
  bound on the state's fields. -/
  | ofDecoded {v : S} (h : decodable v) : Live init feed resize quiesce decodable v

/-- `u` shows the screen `v` shows, as the emulator's accessors read it: the screen's size, each
of its rows, the cursor and the `Sticky` fields. -/
@[expose]
def Shows {S : Type} (colCount rowCount : S → Nat) (getRow : S → Nat → Row)
    (cursorPos : S → Nat × Nat) (stick : S → Sticky) (v u : S) : Prop :=
  colCount u = colCount v ∧
    rowCount u = rowCount v ∧
    (∀ y < rowCount v, getRow u y = getRow v y) ∧ cursorPos u = cursorPos v ∧ stick u = stick v

/-- `u`, what a receiver `w` holds once it has parsed a repaint of the terminal `v`, restores `v`
as far as `w` can show it. Whatever `w` is, `u` has `v`'s pen and every mode of `v`'s but the
mouse mode, the cursor's shape among them, has the mouse mode too when that is off or one a
program enables (1000, 1002 or 1003), and sits between control sequences and characters. When
`w` is as tall as `v` and `v`'s scroll region is one DECSTBM sets, two rows or more on a screen
under 65535 rows, `u` has `v`'s `Sticky` fields. When `v` and `w` are `live` and of one size, `u`
shows the screen `v` shows (`Shows`), and, when `v` sits between control sequences and characters
too, no output fed to both tells the two apart by the screens they show, their pens, their modes
but the mouse mode or whether they sit between them. A terminal inside a sequence or a character
holds a partial one its receiver does not. The history and the window title are not compared,
nor the mouse mode once output follows. -/
@[expose]
def Restores {S : Type} (live : S → Prop) (feed : S → List UInt8 → S) (colCount rowCount : S → Nat)
    (getRow : S → Nat → Row) (cursorPos : S → Nat × Nat) (getPen : S → Pen) (getModes : S → Modes)
    (stick : S → Sticky) (atBoundary : S → Bool) (v w u : S) : Prop :=
  getPen u = getPen v ∧
    ({ getModes u with mouse := 0 } : Modes) = { getModes v with mouse := 0 } ∧
    ((getModes v).mouse = 0 ∨
        (getModes v).mouse = 1000 ∨ (getModes v).mouse = 1002 ∨ (getModes v).mouse = 1003 →
      (getModes u).mouse = (getModes v).mouse) ∧
    atBoundary u = true ∧
    ((stick w).rows = (stick v).rows →
      (stick v).top < (stick v).bot →
      (stick v).bot < (stick v).rows → (stick v).rows < 65535 → stick u = stick v) ∧
    (live v →
      live w →
      colCount w = colCount v →
      rowCount w = rowCount v →
      Shows colCount rowCount getRow cursorPos stick v u ∧
        (atBoundary v = true →
          ∀ later : List UInt8,
            Shows colCount rowCount getRow cursorPos stick (feed v later) (feed u later) ∧
              getPen (feed u later) = getPen (feed v later) ∧
              ({ getModes (feed u later) with mouse := 0 } : Modes) =
                { getModes (feed v later) with mouse := 0 } ∧
              atBoundary (feed u later) = atBoundary (feed v later)))

/-! ## A reference model of the core sequences

What each sequence of a small standard set does to an abstract screen, written from the
standards rather than from the emulator: ECMA-48 (5th edition, 1991) for the controls and
control functions, xterm's `ctlseqs` (Thomas Dickey) for the private modes and OSC titles, and
the DEC VT510 manual for the margins and DECSC. A screen is its cells, as a function of column and
row, the cursor and its deferred wrap, the pen, the modes, the scroll region, the tab stops, what
DECSC saved, the main screen the alternate one stashes, the title and whether the bell rang.

The deferred wrap is DEC's: a print in the last column leaves the cursor there with a wrap
pending, which the next print resolves by wrapping first, under autowrap (DECAWM). Every cursor
movement drops it, as does a backspace, which then stays in the last column, and an erase or an
insertion or deletion of characters, which moves no cursor, keeps it, as tmux does.

Where linger departs from xterm it says so: entering the alternate screen (1049) homes the cursor
and makes the whole screen the scroll region, as leaving it does, where xterm keeps both, and
clears it with the default pen; synchronized output (2026) changes no state a screen holds. The
character sets, insert mode and wide characters are outside the model. -/

namespace Ref

/-- What DECSC (`ESC 7`) saves, as the VT510 says: the cursor's position and its deferred wrap,
the pen and origin mode. -/
structure Saved where
  /-- The saved column, from 0. -/
  x : Nat := 0
  /-- The saved row, from 0. -/
  y : Nat := 0
  /-- The saved deferred wrap. -/
  pending : Bool := false
  /-- The saved pen. -/
  pen : Pen := {}
  /-- The saved origin mode. -/
  origin : Bool := false
  deriving DecidableEq

/-- Cells by column and row, from 0. -/
abbrev Grid := Nat → Nat → Cell

/-- An abstract terminal screen. -/
structure Screen where
  /-- Width. -/
  cols : Nat
  /-- Height. -/
  rows : Nat
  /-- The cell at each column and row. -/
  cell : Grid
  /-- The cursor's column, from 0. -/
  x : Nat
  /-- The cursor's row, from 0. -/
  y : Nat
  /-- A print in the last column left a wrap pending. -/
  pending : Bool
  /-- The pen new text is drawn with. -/
  pen : Pen
  /-- The modes. -/
  modes : Modes
  /-- The scroll region's top row, from 0. -/
  top : Nat
  /-- The scroll region's bottom row, from 0, inclusive. -/
  bot : Nat
  /-- The tab stops, by column. -/
  tabs : Nat → Bool
  /-- What DECSC saved. -/
  saved : Saved
  /-- The main screen and the cursor 1049 stashed, while the alternate screen is shown. -/
  main : Option (Grid × Saved)
  /-- The window title. -/
  title : String
  /-- The bell rang. -/
  bell : Bool

/-- An erased cell: blank, in the background of the pen that erased it, as xterm erases with
its background colour erase. -/
@[expose]
def blank (p : Pen) : Cell := { pen := { bg := p.bg } }

/-- A count parameter: 0, which is also what an omitted one reads as, means 1 (ECMA-48 5.4.2). -/
@[expose]
def count (n : Nat) : Nat := if n = 0 then 1 else n

/-- The first tab stop at or after column `i`, or the last column when there is none (ECMA-48
8.3.60). -/
@[expose]
def nextStop (tabs : Nat → Bool) (cols i : Nat) : Nat :=
  ((List.range' i (cols - i)).find? tabs).getD (cols - 1)

namespace Screen

/-- The screen with `c` at column `x` and row `y`. -/
@[expose]
def put (s : Screen) (x y : Nat) (c : Cell) : Screen :=
  { s with cell := fun x' y' => if x' = x ∧ y' = y then c else s.cell x' y' }

/-- What DECSC saves of the screen. -/
@[expose]
def cursor (s : Screen) : Saved :=
  { x := s.x, y := s.y, pending := s.pending, pen := s.pen, origin := s.modes.origin }

/-- Scroll the region up a row: its top row leaves, and its bottom row comes in blank. -/
@[expose]
def scrollUp (s : Screen) : Screen :=
  { s with
    cell := fun x y =>
      if s.top ≤ y ∧ y < s.bot then s.cell x (y + 1)
      else if y = s.bot then blank s.pen else s.cell x y }

/-- Scroll the region down a row: its bottom row leaves, and its top row comes in blank. -/
@[expose]
def scrollDown (s : Screen) : Screen :=
  { s with
    cell := fun x y =>
      if s.top < y ∧ y ≤ s.bot then s.cell x (y - 1)
      else if y = s.top then blank s.pen else s.cell x y }

/-- CR: to the first column (ECMA-48 8.3.15). -/
@[expose]
def cr (s : Screen) :
    Screen := { s with
    x := 0, pending := false }

/-- LF and IND: down a row, scrolling the region up at its bottom margin, and staying put on the
last row below it (ECMA-48 8.3.74, the VT510's IND). -/
@[expose]
def lineFeed (s : Screen) : Screen :=
  if s.y = s.bot then { s.scrollUp with pending := false }
  else
    if s.y + 1 < s.rows then
      { s with
        y := s.y + 1, pending := false }
    else { s with pending := false }

/-- RI: up a row, scrolling the region down at its top margin (ECMA-48 8.3.104). -/
@[expose]
def reverseIndex (s : Screen) : Screen :=
  if s.y = s.top then { s.scrollDown with pending := false }
  else
    { s with
      y := s.y - 1, pending := false }

/-- A printable character: a pending wrap wraps first under autowrap, the character takes the
cursor's cell with the pen, and the cursor advances, holding at the last column with a wrap
pending under autowrap (DECAWM). -/
@[expose]
def print (s : Screen) (c : Char) : Screen :=
  let s := if s.pending ∧ s.modes.wrap then s.cr.lineFeed else { s with pending := false }
  let s := s.put s.x s.y { base := c, pen := s.pen }
  if s.cols ≤ s.x + 1 then
    { s with
      x := s.cols - 1, pending := s.modes.wrap }
  else { s with x := s.x + 1 }

/-- BS: back a column (ECMA-48 8.3.5); with a wrap pending, the wrap is dropped and the cursor
stays in the last column, as tmux does. -/
@[expose]
def backspace (s : Screen) : Screen :=
  if s.pending then { s with pending := false } else { s with x := s.x - 1 }

/-- HT: to the next tab stop, or the last column (ECMA-48 8.3.60). -/
@[expose]
def tab (s : Screen) : Screen :=
  { s with
    x := min (nextStop s.tabs s.cols (s.x + 1)) (s.cols - 1), pending := false }

/-- The row a CUP or VPA parameter names: from the region's top under origin mode, and confined
to it (DECOM), else from the screen's top. -/
@[expose]
def rowAt (s : Screen) (row : Nat) : Nat :=
  if s.modes.origin then min (s.top + (count row - 1)) s.bot else min (count row - 1) (s.rows - 1)

/-- Home: the top left, the region's under origin mode. -/
@[expose]
def home (s : Screen) :
    Screen := { s with
    x := 0, y := s.rowAt 1, pending := false }

/-- Erase the cells `erases` picks, in the pen's background. -/
@[expose]
def erase (s : Screen) (erases : Nat → Nat → Bool) : Screen :=
  { s with cell := fun x y => if erases x y then blank s.pen else s.cell x y }

/-- Switch to the alternate screen, unless it is shown: save the cursor as DECSC does, stash
the main screen with it, and show a cleared screen, homed, with the whole screen as the region. -/
@[expose]
def enterAlt (s : Screen) : Screen :=
  match s.main with
  | some _ => s
  | none =>
    { s with
      main := some (s.cell, s.cursor), saved := s.cursor, cell := fun _ _ => {}, x := 0, y := 0,
      pending := false, top := 0, bot := s.rows - 1 }

/-- Switch back to the main screen, if the alternate one is shown, restoring the cursor it stashed
as DECRC does, with the whole screen as the region. -/
@[expose]
def leaveAlt (s : Screen) : Screen :=
  match s.main with
  | none => s
  | some (g, c) =>
    { s with
      main := none, cell := g, x := c.x, y := c.y, pending := c.pending, pen := c.pen,
      modes := { s.modes with origin := c.origin }, top := 0, bot := s.rows - 1 }

end Screen

/-- An SGR attribute (ECMA-48 8.3.117, and xterm's 256-colour and direct-colour forms). -/
inductive Sgr where
  /-- 0: every attribute off, both colours the default. -/
  | reset
  /-- 1: bold. -/
  | bold
  /-- 2: faint. -/
  | faint
  /-- 3: italic. -/
  | italic
  /-- 4: underlined. -/
  | underline
  /-- 7: inverse. -/
  | inverse
  /-- 30 to 37: one of the eight colours as the foreground. -/
  | fg8 (i : Fin 8)
  /-- 40 to 47: one of the eight colours as the background. -/
  | bg8 (i : Fin 8)
  /-- 38;5;i: a palette colour as the foreground. -/
  | fg256 (i : UInt8)
  /-- 48;5;i: a palette colour as the background. -/
  | bg256 (i : UInt8)
  /-- 38;2;r;g;b: a direct colour as the foreground. -/
  | fgRgb (r g b : UInt8)
  /-- 48;2;r;g;b: a direct colour as the background. -/
  | bgRgb (r g b : UInt8)
  /-- 39: the default foreground. -/
  | fgDefault
  /-- 49: the default background. -/
  | bgDefault

/-- The parameters that write an attribute. -/
@[expose]
def Sgr.params : Sgr → List Nat
  | .reset => [0]
  | .bold => [1]
  | .faint => [2]
  | .italic => [3]
  | .underline => [4]
  | .inverse => [7]
  | .fg8 i => [30 + i.val]
  | .bg8 i => [40 + i.val]
  | .fg256 i => [38, 5, i.toNat]
  | .bg256 i => [48, 5, i.toNat]
  | .fgRgb r g b => [38, 2, r.toNat, g.toNat, b.toNat]
  | .bgRgb r g b => [48, 2, r.toNat, g.toNat, b.toNat]
  | .fgDefault => [39]
  | .bgDefault => [49]

/-- What an attribute does to the pen. -/
@[expose]
def Sgr.apply (p : Pen) : Sgr → Pen
  | .reset => {}
  | .bold => { p with bold := true }
  | .faint => { p with dim := true }
  | .italic => { p with italic := true }
  | .underline => { p with underline := true }
  | .inverse => { p with reverse := true }
  | .fg8 i => { p with fg := .idx (UInt8.ofNat i.val) }
  | .bg8 i => { p with bg := .idx (UInt8.ofNat i.val) }
  | .fg256 i => { p with fg := .idx i }
  | .bg256 i => { p with bg := .idx i }
  | .fgRgb r g b => { p with fg := .rgb r g b }
  | .bgRgb r g b => { p with bg := .rgb r g b }
  | .fgDefault => { p with fg := .default }
  | .bgDefault => { p with bg := .default }

/-- The private modes of the model (xterm's DECSET and DECRST numbers). -/
inductive Mode where
  /-- 25: the cursor is shown (DECTCEM). -/
  | cursor
  /-- 7: autowrap (DECAWM). -/
  | wrap
  /-- 1049: the alternate screen, with the cursor saved as DECSC does. -/
  | alt
  /-- 2004: bracketed paste. -/
  | paste
  /-- 2026: synchronized output. -/
  | sync

/-- A mode's number. -/
@[expose]
def Mode.number : Mode → Nat
  | .cursor => 25
  | .wrap => 7
  | .alt => 1049
  | .paste => 2004
  | .sync => 2026

/-- A number in decimal ASCII digits. -/
@[expose]
def dec (n : Nat) : List UInt8 :=
  if n < 10 then [UInt8.ofNat (0x30 + n)] else dec (n / 10) ++ [UInt8.ofNat (0x30 + n % 10)]
termination_by n
decreasing_by omega

/-- Parameters, `;`-separated. -/
@[expose]
def params : List Nat → List UInt8
  | [] => []
  | [n] => dec n
  | n :: ns => dec n ++ [0x3B] ++ params ns

/-- `CSI` with parameters and a final byte. -/
@[expose]
def csi (ps : List Nat) (final : UInt8) : List UInt8 := [0x1B, 0x5B] ++ params ps ++ [final]

/-- A sequence of the set. -/
inductive Seq where
  /-- A printable ASCII character. -/
  | print (c : Char)
  /-- CR. -/
  | cr
  /-- LF. -/
  | lf
  /-- BS. -/
  | bs
  /-- HT. -/
  | ht
  /-- BEL. -/
  | bel
  /-- CUU: up `n` rows. -/
  | cuu (n : Nat)
  /-- CUD: down `n` rows. -/
  | cud (n : Nat)
  /-- CUF: right `n` columns. -/
  | cuf (n : Nat)
  /-- CUB: left `n` columns. -/
  | cub (n : Nat)
  /-- CUP: to a row and a column, from 1. -/
  | cup (row col : Nat)
  /-- CHA: to a column, from 1. -/
  | cha (col : Nat)
  /-- VPA: to a row, from 1. -/
  | vpa (row : Nat)
  /-- ED: erase below (0), above (1) or all (2) of the screen. -/
  | ed (mode : Fin 3)
  /-- EL: erase right of (0), left of (1) or all (2) of the line. -/
  | el (mode : Fin 3)
  /-- IL: insert `n` lines. -/
  | il (n : Nat)
  /-- DL: delete `n` lines. -/
  | dl (n : Nat)
  /-- ICH: insert `n` blank characters. -/
  | ich (n : Nat)
  /-- DCH: delete `n` characters. -/
  | dch (n : Nat)
  /-- ECH: erase `n` characters. -/
  | ech (n : Nat)
  /-- SGR: set attributes, in order; none resets. -/
  | sgr (attrs : List Sgr)
  /-- DECSTBM: the scroll region, from 1, its bottom 0 for the last row. -/
  | decstbm (top bot : Nat)
  /-- IND (`ESC D`). -/
  | ind
  /-- RI (`ESC M`). -/
  | ri
  /-- DECSC (`ESC 7`). -/
  | decsc
  /-- DECRC (`ESC 8`). -/
  | decrc
  /-- DECSET (`CSI ? n h`) when `on`, else DECRST (`CSI ? n l`). -/
  | set (mode : Mode) (on : Bool)
  /-- OSC 0 when `both`, which also names the icon, else OSC 2: the window title, ended by BEL. -/
  | title (both : Bool) (text : String)

/-- The bytes of a sequence. -/
@[expose]
def Seq.bytes : Seq → List UInt8
  | .print c => [UInt8.ofNat c.toNat]
  | .cr => [0x0D]
  | .lf => [0x0A]
  | .bs => [0x08]
  | .ht => [0x09]
  | .bel => [0x07]
  | .cuu n => csi [n] 0x41
  | .cud n => csi [n] 0x42
  | .cuf n => csi [n] 0x43
  | .cub n => csi [n] 0x44
  | .cup row col => csi [row, col] 0x48
  | .cha col => csi [col] 0x47
  | .vpa row => csi [row] 0x64
  | .ed m => csi [m.val] 0x4A
  | .el m => csi [m.val] 0x4B
  | .il n => csi [n] 0x4C
  | .dl n => csi [n] 0x4D
  | .ich n => csi [n] 0x40
  | .dch n => csi [n] 0x50
  | .ech n => csi [n] 0x58
  | .sgr attrs => csi (attrs.flatMap Sgr.params) 0x6D
  | .decstbm t b => csi [t, b] 0x72
  | .ind => [0x1B, 0x44]
  | .ri => [0x1B, 0x4D]
  | .decsc => [0x1B, 0x37]
  | .decrc => [0x1B, 0x38]
  | .set m on => [0x1B, 0x5B, 0x3F] ++ dec m.number ++ [if on then 0x68 else 0x6C]
  | .title both text =>
    [0x1B, 0x5D, if both then 0x30 else 0x32, 0x3B] ++ text.toUTF8.data.toList ++ [0x07]

/-- A sequence of the set as a program writes it: a printable character is ASCII, a parameter is
at most 65535, the largest xterm reads, an SGR has at most 16 parameters, and a title holds no
BEL or ESC and fits the 2048 bytes an OSC payload keeps, `0;` or `2;` included. -/
@[expose]
def Seq.Ok : Seq → Prop
  | .print c => 0x20 ≤ c.toNat ∧ c.toNat < 0x7F
  | .cuu n | .cud n | .cuf n | .cub n | .cha n | .vpa n | .il n | .dl n | .ich n | .dch n |
    .ech n => n ≤ 65535
  | .cup a b | .decstbm a b => a ≤ 65535 ∧ b ≤ 65535
  | .sgr attrs => (attrs.flatMap Sgr.params).length ≤ 16
  | .title _ text =>
    (∀ b ∈ text.toUTF8.data.toList, b ≠ 0x07 ∧ b ≠ 0x1B) ∧ text.toUTF8.data.size + 2 ≤ 2048
  | _ => True

/-- What a sequence does to a screen. -/
@[expose]
def Seq.apply (s : Screen) : Seq → Screen
  | .print c => s.print c
  | .cr => s.cr
  | .lf | .ind => s.lineFeed
  | .bs => s.backspace
  | .ht => s.tab
  | .bel => { s with bell := true }
  | .cuu n =>
    { s with
      y := max (s.y - count n) (if s.top ≤ s.y then s.top else 0), pending := false }
  | .cud n =>
    { s with
      y := min (s.y + count n) (if s.y ≤ s.bot then s.bot else s.rows - 1), pending := false }
  | .cuf n =>
    { s with
      x := min (s.x + count n) (s.cols - 1), pending := false }
  | .cub n =>
    { s with
      x := s.x - count n, pending := false }
  | .cup row col =>
    { s with
      x := min (count col - 1) (s.cols - 1), y := s.rowAt row, pending := false }
  | .cha col =>
    { s with
      x := min (count col - 1) (s.cols - 1), pending := false }
  | .vpa row =>
    { s with
      y := s.rowAt row, pending := false }
  | .ed m =>
    s.erase fun x y =>
      (m.val = 0 && (y == s.y && decide (s.x ≤ x) || decide (s.y < y))) ||
        (m.val = 1 && (y == s.y && decide (x ≤ s.x) || decide (y < s.y))) ||
        m.val = 2
  | .el m =>
    s.erase fun x y =>
      y == s.y && ((m.val = 0 && decide (s.x ≤ x)) || (m.val = 1 && decide (x ≤ s.x)) || m.val = 2)
  | .il n =>
    if s.y < s.top ∨ s.bot < s.y then s
    else
      { s with
        cell := fun x y =>
          if s.y ≤ y ∧ y ≤ s.bot then
            if y < s.y + count n then blank s.pen else s.cell x (y - count n)
          else s.cell x y,
        x := 0, pending := false }
  | .dl n =>
    if s.y < s.top ∨ s.bot < s.y then s
    else
      { s with
        cell := fun x y =>
          if s.y ≤ y ∧ y ≤ s.bot then
            if y + count n ≤ s.bot then s.cell x (y + count n) else blank s.pen
          else s.cell x y,
        x := 0, pending := false }
  | .ich n =>
    { s with
      cell := fun x y =>
        if y = s.y ∧ s.x ≤ x then if s.x + count n ≤ x then s.cell (x - count n) y else blank s.pen
        else s.cell x y }
  | .dch n =>
    { s with
      cell := fun x y =>
        if y = s.y ∧ s.x ≤ x then
          if x + count n < s.cols then s.cell (x + count n) y else blank s.pen
        else s.cell x y }
  | .ech n => s.erase fun x y => y == s.y && decide (s.x ≤ x) && decide (x < s.x + count n)
  | .sgr attrs =>
    { s with pen := (if attrs.isEmpty then [Sgr.reset] else attrs).foldl Sgr.apply s.pen }
  | .decstbm t b =>
    if
        count t - 1 < (if b = 0 then s.rows else b) - 1 ∧
          (if b = 0 then s.rows else b) - 1 < s.rows then
      { s with
          top := count t - 1, bot := (if b = 0 then s.rows else b) - 1 }.home
    else s
  | .decsc => { s with saved := s.cursor }
  | .decrc =>
    { s with
      x := s.saved.x, y := if s.saved.origin then min (max s.saved.y s.top) s.bot else s.saved.y,
      pending := s.saved.pending, pen := s.saved.pen,
      modes := { s.modes with origin := s.saved.origin } }
  | .ri => s.reverseIndex
  | .set .cursor on => { s with modes := { s.modes with cursorVisible := on } }
  | .set .wrap on => { s with modes := { s.modes with wrap := on } }
  | .set .paste on => { s with modes := { s.modes with bracketedPaste := on } }
  | .set .sync _ => s
  | .set .alt on => if on then s.enterAlt else s.leaveAlt
  | .title _ text => { s with title := text }

/-- `s` is what a terminal shows through its accessors: its size, each cell on the screen, the
cursor, the pen, the modes, the scroll region, which screen is shown and the title. -/
@[expose]
def Reads {V : Type} (colCount rowCount : V → Nat) (getRow : V → Nat → Row)
    (cursorPos : V → Nat × Nat) (getPen : V → Pen) (getModes : V → Modes) (stick : V → Sticky)
    (windowTitle : V → String) (v : V) (s : Screen) : Prop :=
  s.cols = colCount v ∧
    s.rows = rowCount v ∧
    (∀ y < s.rows, ∀ x < s.cols, s.cell x y = (getRow v y).getD x default) ∧
    s.x = (cursorPos v).1 ∧
    s.y = (cursorPos v).2 ∧
    s.pen = getPen v ∧
    s.modes = getModes v ∧
    s.top = (stick v).top ∧
    s.bot = (stick v).bot ∧ s.main.isSome = (stick v).alt ∧ s.title = windowTitle v

/-- Two screens agree on everything a screen holds, each grid on the screen's cells. -/
@[expose]
def Same (a b : Screen) : Prop :=
  a.cols = b.cols ∧
    a.rows = b.rows ∧
    (∀ y < a.rows, ∀ x < a.cols, a.cell x y = b.cell x y) ∧
    a.x = b.x ∧
    a.y = b.y ∧
    a.pending = b.pending ∧
    a.pen = b.pen ∧
    a.modes = b.modes ∧
    a.top = b.top ∧
    a.bot = b.bot ∧
    (∀ x < a.cols, a.tabs x = b.tabs x) ∧
    a.saved = b.saved ∧
    (∀ g c,
      a.main = some (g, c) →
        ∃ g', b.main = some (g', c) ∧ ∀ y < a.rows, ∀ x < a.cols, g x y = g' x y) ∧
    (a.main = none → b.main = none) ∧ a.title = b.title ∧ a.bell = b.bell

/-- A terminal the model covers, through its accessors: every cell on its screen is one column
wide, insert mode is off and neither G0 nor G1 is DEC line drawing. -/
@[expose]
def Plain {V : Type} (colCount rowCount : V → Nat) (getRow : V → Nat → Row) (getModes : V → Modes)
    (stick : V → Sticky) (v : V) : Prop :=
  (∀ y < rowCount v, ∀ x < colCount v, ((getRow v y).getD x default).width = 1) ∧
    (getModes v).insert = false ∧ (stick v).g0 = false ∧ (stick v).g1 = false

/-! ### What linger keeps without drawing, and what it skips -/

/-- A sequence outside the model that linger keeps or skips: DECSCUSR (`CSI Ps SP q`) sets the
cursor's shape, which a repaint replays, and changes nothing a screen shows; a sixel image (`DCS
q … ST`), an APC string such as a kitty graphics command (`APC … ST`) and an OSC 8 hyperlink
(`OSC 8 ; params ; uri BEL`) are skipped as strings, so they change nothing a terminal shows. -/
inductive Kept where
  /-- DECSCUSR with shape `k`. -/
  | shape (k : Fin 7)
  /-- A sixel image's data. -/
  | sixel (data : List UInt8)
  /-- An APC string's data. -/
  | apc (data : List UInt8)
  /-- A hyperlink's parameters and URI. -/
  | hyperlink (params uri : List UInt8)

/-- The bytes of a kept or skipped sequence. -/
@[expose]
def Kept.bytes : Kept → List UInt8
  | .shape k => [0x1B, 0x5B] ++ dec k.val ++ [0x20, 0x71]
  | .sixel d => [0x1B, 0x50, 0x71] ++ d ++ [0x1B, 0x5C]
  | .apc d => [0x1B, 0x5F] ++ d ++ [0x1B, 0x5C]
  | .hyperlink p u => [0x1B, 0x5D, 0x38, 0x3B] ++ p ++ [0x3B] ++ u ++ [0x07]

/-- A string's data holds no ESC, and a hyperlink's no BEL either, so the string ends where its
terminator is. -/
@[expose]
def Kept.Ok : Kept → Prop
  | .shape _ => True
  | .sixel d | .apc d => ∀ b ∈ d, b ≠ 0x1B
  | .hyperlink p u => ∀ b ∈ p ++ u, b ≠ 0x07 ∧ b ≠ 0x1B

/-- The modes after a kept sequence: DECSCUSR sets the cursor's shape, and the others none. -/
@[expose]
def Kept.modes (m : Modes) : Kept → Modes
  | .shape k => { m with cursorShape := k }
  | _ => m

/-- A wrong emulator that does not skip strings: it drops every ESC, so a string's data prints. -/
@[expose]
def unescaped {V : Type} (feed : V → List UInt8 → V) (v : V) (bytes : List UInt8) : V :=
  feed v (bytes.filter (· != 0x1B))

/-! ### Wrong emulators the reference refutes -/

/-- An emulator whose EL 0 erases the whole line. -/
@[expose]
def elWhole {V : Type} (feed : V → List UInt8 → V) (v : V) (bytes : List UInt8) : V :=
  feed v (if bytes = Seq.bytes (.el 0) then Seq.bytes (.el 2) else bytes)

/-- An emulator that reads CUP's row and column from 0: `CSI 1 ; 1 H` goes to the second row
and column. -/
@[expose]
def cupFromZero {V : Type} (feed : V → List UInt8 → V) (v : V) (bytes : List UInt8) : V :=
  feed v (if bytes = Seq.bytes (.cup 1 1) then Seq.bytes (.cup 2 2) else bytes)

/-- An emulator without the deferred wrap: a print into the last column wraps at once. -/
@[expose]
def eagerWrap {V : Type} (feed : V → List UInt8 → V) (colCount : V → Nat)
    (cursorPos : V → Nat × Nat) (v : V) (bytes : List UInt8) : V :=
  if bytes.length = 1 ∧ (cursorPos v).1 + 1 = colCount v then feed (feed v bytes) [0x0D, 0x0A]
  else feed v bytes

/-- An emulator whose SGR 0 keeps bold. -/
@[expose]
def resetKeepsBold {V : Type} (feed : V → List UInt8 → V) (getPen : V → Pen) (v : V)
    (bytes : List UInt8) : V :=
  if bytes = Seq.bytes (.sgr [.reset]) ∧ (getPen v).bold = true then
    feed v (Seq.bytes (.sgr [.reset, .bold]))
  else feed v bytes

/-- An emulator whose IL keeps the cursor's column. -/
@[expose]
def ilKeepsColumn {V : Type} (feed : V → List UInt8 → V) (cursorPos : V → Nat × Nat) (v : V)
    (bytes : List UInt8) : V :=
  if bytes = Seq.bytes (.il 1) then feed (feed v bytes) (Seq.bytes (.cha ((cursorPos v).1 + 1)))
  else feed v bytes

end Ref

end Terminal.Vt

namespace Terminal.Render

/-- Bytes sent to or read from a terminal. -/
abbrev Bytes := List UInt8

/-- A wrong rendering: ESC, whatever the terminal holds. The headlines that the screen's and the
history's text are plain text are shown to reject it. -/
@[expose]
def escape {V : Type} (_ : V) : Bytes := [0x1B]

/-- `CSI ? 2026 h`, which opens a synchronized update: a terminal that knows DEC private mode 2026
holds what follows until the update closes, and shows it at once. -/
@[expose]
def syncBegin : Bytes := [0x1B, 0x5B, 0x3F, 0x32, 0x30, 0x32, 0x36, 0x68]

/-- `CSI ? 2026 l`, which closes a synchronized update: the terminal shows what it held. -/
@[expose]
def syncEnd : Bytes := [0x1B, 0x5B, 0x3F, 0x32, 0x30, 0x32, 0x36, 0x6C]

end Terminal.Render

namespace Terminal.Replay

/-- `out` is what streaming `plan` emits when each step of `next` may take `budget` bytes: the
chunks `next` returns until it reports the end, in order, each at most `budget` bytes long. -/
inductive Emits {P : Type} (next : Nat → P → Option (Render.Bytes × P)) (budget : Nat) :
    P → Render.Bytes → Prop where
  /-- The plan has nothing left to emit. -/
  | done {p : P} (h : next budget p = none) : Emits next budget p []
  /-- One step's chunk, then the rest of the stream. -/
  |
  step {p q : P} {chunk rest : Render.Bytes} (h : next budget p = some (chunk, q))
    (bounded : chunk.length ≤ budget) (more : Emits next budget q rest) :
    Emits next budget p (chunk ++ rest)

/-- A wrong step: a byte, whatever the budget, and the same plan again. The headline that each
step of a repaint fits its budget is shown to reject it. -/
@[expose]
def overrun {P : Type} (_ : Nat) (p : P) : Option (Render.Bytes × P) := some ([0], p)

/-- A wrong start: the plan `start` makes, past its first step of `Render.syncBegin`'s width, which
for a plan that sends the opening bracket first is the repaint without it. The headline that a
repaint is one synchronized update is shown to reject it. -/
@[expose]
def unbracketed {V P : Type} (start : V → P) (next : Nat → P → Option (Render.Bytes × P)) (v : V) :
    P := match next Render.syncBegin.length (start v) with
  | some (_, q) => q
  | none => start v

end Terminal.Replay

namespace Terminal.Mediation

open Terminal.Render

/-- The escape byte. -/
abbrev ESC : UInt8 := 0x1B

/-- Maximum retained bytes for one possible owned CSI request. -/
@[expose]
def csiCap : Nat := 128

/-- Maximum retained bytes for one possible owned OSC request. -/
@[expose]
def oscCap : Nat := 256

/-- Maximum retained bytes for one possible owned DCS request. -/
@[expose]
def dcsCap : Nat := 2048

/-- The state of the scanner between the pty and the presentation clients. Candidate buffers
are reversed, making byte-at-a-time accumulation O(1). Passthrough states retain no payload.
DCS only enters its buffered state after `+q` or `$q`; sixel (`DCS q`) therefore streams
immediately. -/
inductive Scan where
  /-- Outside any sequence: every byte but ESC is released at once. -/
  | ground
  /-- After ESC, which is held until the next byte. -/
  | esc
  /-- A CSI sequence that may be owned, held within `csiCap` bytes. -/
  | csi (rev : Bytes)
  /-- An unowned CSI sequence, released byte by byte until its final byte. -/
  | csiPass
  /-- An OSC sequence that may be owned, held within `oscCap` bytes; `escSeen` marks a
  trailing ESC. -/
  | osc (rev : Bytes) (escSeen : Bool)
  /-- An unowned OSC sequence, released byte by byte until BEL or ST. -/
  | oscPass (escSeen : Bool)
  /-- After `ESC P`, waiting for the `+` or `$` that may begin an owned request. -/
  | dcsIntro
  /-- After `ESC P` and `kind`, waiting for `q`. -/
  | dcsKind (kind : UInt8)
  /-- An XTGETTCAP or DECRQSS request held within `dcsCap` bytes; `escSeen` marks an ESC
  held outside the payload, which may begin ST. -/
  | dcs (kind : UInt8) (payloadRev : Bytes) (escSeen : Bool)
  /-- An unowned DCS, SOS, PM or APC string, released byte by byte until ST. -/
  | strPass (escSeen : Bool)
  deriving Repr, DecidableEq, Inhabited

/-- The scanner retains at most its caps: the memory bound a session state keeps. -/
@[expose]
def Scan.Bounded : Scan → Prop
  | .csi rev => rev.length ≤ csiCap
  | .osc rev _ => rev.length ≤ oscCap
  | .dcs kind payloadRev escSeen =>
    ([ESC, 0x50, kind, 0x71] ++ payloadRev.reverse ++ (if escSeen then [ESC] else [])).length ≤
      dcsCap
  | _ => True

/-- The command line a shell gives with a `C` mark, as the mediator read it: the bytes it
decoded, and whether they are all of it. A mark longer than `oscCap`, which the scanner releases
before it ends, or a value that stops decoding, gives the bytes read before that, not whole. -/
structure Cmdline where
  /-- The bytes of the command line, decoded, in order: empty when the mark gives none. -/
  bytes : Bytes := []
  /-- Whether `bytes` is the whole command line. -/
  whole : Bool := true
  deriving Repr, DecidableEq

/-- A semantic prompt mark, OSC 133, as a shell sends one around its prompt and each command it
runs, `ESC ] 133 ; <letter>`, possibly followed by `;` parameters, and ended by BEL or ST. -/
inductive Mark where
  /-- `A`: a prompt starts. -/
  | prompt
  /-- `B`: the prompt ends and the command's input starts. -/
  | input
  /-- `C`: the command runs and its output follows, with the command line its `cmdline_url=` or
  `cmdline=` parameter gives. -/
  | runs (cmdline : Cmdline)
  /-- `D`: the command finished, with the exit status its first parameter gives, when that is a
  decimal number. -/
  | finished (status : Option Nat)
  deriving Repr, DecidableEq

end Terminal.Mediation

namespace Terminal.Mediation

/-- Whether an OSC 9 text is a ConEmu sub-command instead of a notification: digits, then `;`, as
`4;1;50` reports progress. -/
@[expose]
def subcommand (text : List UInt8) : Bool :=
  !(text.takeWhile fun b => 0x30 ≤ b && b ≤ 0x39).isEmpty &&
    (text.dropWhile fun b => 0x30 ≤ b && b ≤ 0x39).head? == some 0x3B

/-- The text of the desktop notification an OSC payload posts, if it posts one: what follows
`9;`, as iTerm2 and Ghostty post it, unless that is a ConEmu sub-command, or what follows
`777;notify;`, its title and its body, joined by `: ` when it has both. -/
@[expose]
def noticeOf : List UInt8 → Option (List UInt8)
  | 0x39 :: 0x3B :: text => if subcommand text then none else some text
  | 0x37 :: 0x37 :: 0x37 :: 0x3B :: 0x6E :: 0x6F :: 0x74 :: 0x69 :: 0x66 :: 0x79 :: 0x3B :: rest =>
    let title := rest.takeWhile (· != 0x3B)
    let body := (rest.dropWhile (· != 0x3B)).drop 1
    some
      (if title.isEmpty then body
      else if body.isEmpty then title else title ++ [0x3A, 0x20] ++ body)
  | _ => none

/-- A state a program declares with ConEmu's progress report, OSC `9;4`, as Windows Terminal and
Ghostty read it too: the states of the Windows taskbar's progress indicator, which ConEmu's
report sets. -/
inductive Progress where
  /-- State 1: progress under way, with a percentage. -/
  | normal
  /-- State 2: an error stopped the progress; the indicator turns red. -/
  | error
  /-- State 3: under way, by an amount the program does not tell. -/
  | indeterminate
  /-- State 4: the progress is stopped, and may resume; the indicator turns yellow. -/
  | paused
  deriving Repr, DecidableEq, Inhabited

/-- Whether a progress state says the work goes on: normal and indeterminate progress do, as
the taskbar shows them moving; an error and a pause say the progress stopped, as the taskbar
shows them halted in red or yellow. -/
@[expose]
def Progress.underway : Progress → Bool
  | .normal | .indeterminate => true
  | .error | .paused => false

/-- The progress report an OSC payload is, if it is one: ConEmu's `9;4;`, then the state, one
digit from `0` to `4`, then nothing or `;` and the percentage. State 0 removes the progress
(`some none`); 1 to 4 set it; any other payload reports nothing. -/
@[expose]
def progressOf : List UInt8 → Option (Option Progress)
  | 0x39 :: 0x3B :: 0x34 :: 0x3B :: state :: rest =>
    if rest.head?.all (· == 0x3B) then
      if state == 0x30 then some none
      else
        if state == 0x31 then some (some .normal)
        else
          if state == 0x32 then some (some .error)
          else
            if state == 0x33 then some (some .indeterminate)
            else if state == 0x34 then some (some .paused) else none
    else none
  | _ => none

/-- After feeding a chunk to the mediator: the terminal, the scanner, the bytes released to
presentation clients, the replies to owned requests, and what the chunk told of its program. -/
structure Result (V : Type) where
  /-- The terminal after every byte of the chunk. -/
  vt : V
  /-- The scanner after the chunk, possibly holding an incomplete request. -/
  scan : Scan
  /-- Bytes released to presentation clients, in order. -/
  visible : Render.Bytes
  /-- Replies to owned requests, in order. -/
  replies : Render.Bytes
  /-- Whether the chunk rang the bell or posted a notification. -/
  asks : Bool := false
  /-- The text of the chunk's last notification, if it posted one. -/
  notice : Option Render.Bytes := none
  /-- The shell's marks the chunk completed, in order. -/
  marks : List Mark := []
  /-- The last progress report the chunk completed, if any: the state it sets, `none` when it
  removes the progress. -/
  progress : Option (Option Progress) := none
  /-- Whether the chunk added rows to the terminal's history. -/
  lines : Bool := false

end Terminal.Mediation

namespace Terminal.Stream

/-- A whole unit of terminal output, as ECMA-48 divides a stream and DEC's parser (vt100.net)
reads it: a printable ASCII character, a C0 control other than ESC, a control sequence (`CSI`,
with or without the private marker `?`), an operating system command (`OSC`) ended by BEL or by
ST, a DCS, SOS, PM or APC string ended by ST, or an escape sequence with a final byte. -/
inductive Token where
  /-- A printable ASCII character. -/
  | text (c : Char)
  /-- A C0 control other than ESC. -/
  | control (b : UInt8)
  /-- `CSI`, `?` when `priv`, parameters and a final byte. -/
  | csi (priv : Bool) (params : List Nat) (final : UInt8)
  /-- `OSC` and a payload, ended by ST when `st`, else by BEL. -/
  | osc (payload : List UInt8) (st : Bool)
  /-- `ESC` and `P`, `X`, `^` or `_`, the data, and ST. -/
  | str (intro : UInt8) (data : List UInt8)
  /-- `ESC` and a final byte. -/
  | esc (final : UInt8)

/-- The bytes of a token. -/
@[expose]
def Token.bytes : Token → List UInt8
  | .text c => [UInt8.ofNat c.toNat]
  | .control b => [b]
  | .csi priv ps f => [0x1B, 0x5B] ++ (if priv then [0x3F] else []) ++ Vt.Ref.params ps ++ [f]
  | .osc p st => [0x1B, 0x5D] ++ p ++ (if st then [0x1B, 0x5C] else [0x07])
  | .str i d => [0x1B, i] ++ d ++ [0x1B, 0x5C]
  | .esc f => [0x1B, f]

/-- A token as a program writes one: a character is printable ASCII, a control is no ESC, a
control sequence has at most 16 parameters of at most 65535 and a final byte from `@` to `~`, a
string's data holds no ESC and an OSC's payload neither BEL nor ESC, and fits the 256 bytes the
mediator holds of a possible request, `ESC ]` and an ending ESC included; an escape sequence's final
byte is from `0` to `~` and begins no control sequence or string. -/
@[expose]
def Token.Ok : Token → Prop
  | .text c => 0x20 ≤ c.toNat ∧ c.toNat < 0x7F
  | .control b => b < 0x20 ∧ b ≠ 0x1B
  | .csi _ ps f => ps.length ≤ 16 ∧ (∀ n ∈ ps, n ≤ 65535) ∧ 0x40 ≤ f ∧ f ≤ 0x7E
  | .osc p _ => (∀ b ∈ p, b ≠ 0x07 ∧ b ≠ 0x1B) ∧ p.length + 3 ≤ Mediation.oscCap
  | .str i d => (i = 0x50 ∨ i = 0x58 ∨ i = 0x5E ∨ i = 0x5F) ∧ ∀ b ∈ d, b ≠ 0x1B
  | .esc f => 0x30 ≤ f ∧ f ≤ 0x7E ∧ f ≠ 0x50 ∧ f ≠ 0x58 ∧ f ≠ 0x5B ∧ f ≠ 0x5D ∧ f ≠ 0x5E ∧ f ≠ 0x5F

/-- The window title after a token: OSC 0 and OSC 2 (xterm's `ctlseqs`) set it to their text when
it is UTF-8, and `0` or `2` alone to the empty one; RIS (`ESC c`) resets the terminal, its title
with it; nothing else sets it, OSC 1, the icon name, among them. -/
@[expose]
def Token.retitle (title : String) : Token → String
  | .osc [0x30] _ | .osc [0x32] _ => ""
  | .osc (0x30 :: 0x3B :: rest) _ | .osc (0x32 :: 0x3B :: rest) _ =>
    (String.fromUTF8? ⟨rest.toArray⟩).getD title
  | .esc 0x63 => ""
  | _ => title

/-- The text of the notification a token posts: an OSC whose payload posts one (`noticeOf`). -/
@[expose]
def Token.notice : Token → Option (List UInt8)
  | .osc p _ => Mediation.noticeOf p
  | _ => none

/-- Whether a token asks for someone: BEL as a control, which a terminal executes, never a BEL
that ends a string, or a notification. -/
@[expose]
def Token.asks : Token → Bool
  | .control b => b == 0x07
  | t => t.notice.isSome

/-- The progress report a token makes: an OSC whose payload is one (`progressOf`). -/
@[expose]
def Token.progress : Token → Option (Option Mediation.Progress)
  | .osc p _ => Mediation.progressOf p
  | _ => none

/-- The progress a program has declared after a token: the state a report sets, none after one
that removes it, and what it was before any other token. -/
@[expose]
def Token.reprogress (p : Option Mediation.Progress) (t : Token) : Option Mediation.Progress :=
  t.progress.getD p

/-- The last notification a stream posts. -/
@[expose]
def notice (ts : List Token) : Option (List UInt8) := ts.foldl (fun n t => t.notice.or n) none

/-- A wrong emulator that takes OSC 1, the icon name, for the title. -/
@[expose]
def iconAsTitle {V : Type} (feed : V → List UInt8 → V) (v : V) (bytes : List UInt8) : V :=
  feed v (if bytes.take 3 = [0x1B, 0x5D, 0x31] then [0x1B, 0x5D, 0x32] ++ bytes.drop 3 else bytes)

/-- A wrong mediator that hears a BEL ending a string as a bell. -/
@[expose]
def endingRings {V : Type} (feed : V → Mediation.Scan → Render.Bytes → Mediation.Result V) (v : V)
    (s : Mediation.Scan) (bytes : Render.Bytes) : Mediation.Result V :=
  { feed v s bytes with asks := (feed v s bytes).asks || bytes.contains 0x07 }

/-- A wrong mediator that hears ConEmu's progress report, OSC `9;4`, as a notification. -/
@[expose]
def progressAsks {V : Type} (feed : V → Mediation.Scan → Render.Bytes → Mediation.Result V) (v : V)
    (s : Mediation.Scan) (bytes : Render.Bytes) : Mediation.Result V :=
  { feed v s bytes with
    asks := (feed v s bytes).asks || bytes.take 5 == [0x1B, 0x5D, 0x39, 0x3B, 0x34] }

/-- A wrong mediator that hears a change of the window title as a declaration of work, as a
spinner a program draws in its title would be read. -/
@[expose]
def titleProgress {V : Type} (title : V → String)
    (feed : V → Mediation.Scan → Render.Bytes → Mediation.Result V) (v : V) (s : Mediation.Scan)
    (bytes : Render.Bytes) : Mediation.Result V :=
  { feed v s bytes with
    progress :=
      if title (feed v s bytes).vt = title v then (feed v s bytes).progress
      else some (some .indeterminate) }

end Terminal.Stream
