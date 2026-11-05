module

public section

/-! # What terminal headlines are stated in

The values a terminal shows (colours, pens, cells, rows, modes and the screen settings a
repaint keeps), the bytes it is fed, and two predicates over the emulator's operations, which
they take as parameters. Bodies are exposed: each definition here is its own specification.

`Live` is the least set of states containing a fresh emulator and closed under what a live
session does to one: feed pty bytes, resize on attach, forget partial parser state (what a
checkpoint save and load does) and come off disk through the decoder's door. Headline theorems
about repainting and checkpoints assume it of the terminals involved. Every state a program
can hold satisfies it: a fresh screen and the decoder are the only doors, and the session
transformers the only ways forward (`Linger/Terminal/Vt.lean` lists them). It does not say a
scrollback row is the screen's width: a resize leaves the scrollback at its old width.

`Replay.Emits` is the output of streaming a repaint plan one bounded step at a time. -/

namespace Linger.Terminal.Vt

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

/-- Modes we track. Stored-but-uninterpreted ones exist so a restore
can replay them (`Render.modesAnsi`). -/
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
  deriving Repr, DecidableEq, Inhabited

/-- Clamp a requested dimension to [1, 1000]. -/
@[expose]
def clampDim (n : Nat) : Nat := min (max n 1) 1000

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

end Linger.Terminal.Vt

namespace Linger.Terminal.Render

/-- Bytes sent to or read from a terminal. -/
abbrev Bytes := List UInt8

end Linger.Terminal.Render

namespace Linger.Terminal.Replay

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

end Linger.Terminal.Replay
