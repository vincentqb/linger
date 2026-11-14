module

public section

/-! # What terminal headlines are stated in

The values a terminal shows (colours, pens, cells, rows, modes and the screen settings a
repaint keeps), the bytes it is fed, the rows a history keeps and the output that may ask to
erase it, the marks a shell sends around its prompt and its commands, and predicates over the
emulator's operations, which they take as parameters.
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

end Terminal.Vt

namespace Terminal.Render

/-- Bytes sent to or read from a terminal. -/
abbrev Bytes := List UInt8

/-- A wrong rendering: ESC, whatever the terminal holds. The headlines that the screen's and the
history's text are plain text are shown to reject it. -/
@[expose]
def escape {V : Type} (_ : V) : Bytes := [0x1B]

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
