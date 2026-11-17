module

public section

/-! # What the input decoder's headlines are stated in

The physical input events a terminal application reads, and the decoder's state between bytes.
Which action an event requests is the application's own binding, which the decoder does not
know. -/

namespace Input

/-- Physical input events. C0 bytes without a dedicated key retain their byte
identity; consumers decide which of them have an application binding. -/
inductive Key where
  /-- A decoded Unicode scalar; `feed` delivers only printable ones. -/
  | text (char : Char)
  /-- A C0 byte other than BS, HT, LF, CR and ESC. -/
  | control (byte : UInt8)
  /-- BS (8) or DEL (127). -/
  | backspace
  /-- HT (9). -/
  | tab
  /-- CR (13) or LF (10). -/
  | enter
  /-- ESC with no sequence after it, reported by `flush` outside paste. -/
  | escape
  /-- CSI A or SS3 A. -/
  | up
  /-- CSI B or SS3 B. -/
  | down
  /-- CSI H, SS3 H, CSI 1 ~ or CSI 7 ~. -/
  | home
  /-- CSI F, SS3 F, CSI 4 ~ or CSI 8 ~. -/
  | end
  deriving BEq, Repr, DecidableEq

/-- CSI parameter prefixes with a recognized meaning; any other prefix is `other`. -/
inductive Parameter where
  /-- No parameter bytes yet. -/
  | empty
  /-- Exactly 1; with a final ~ it is Home. -/
  | one
  /-- Exactly 2, a prefix of both paste markers. -/
  | two
  /-- Exactly 4; with a final ~ it is End. -/
  | four
  /-- Exactly 7; with a final ~ it is Home. -/
  | seven
  /-- Exactly 8; with a final ~ it is End. -/
  | eight
  /-- Exactly 20, a prefix of both paste markers. -/
  | twenty
  /-- Exactly 200; with a final ~ it starts bracketed paste. -/
  | pasteStart
  /-- Exactly 201; with a final ~ it ends bracketed paste. -/
  | pasteEnd
  /-- Any other prefix. It absorbs later parameter bytes, and its final byte yields no key. -/
  | other
  deriving BEq, Repr, DecidableEq

/-- Progress through an escape, CSI, SS3 or UTF-8 sequence, retaining at most three bytes. -/
inductive Mode where
  /-- Between sequences. -/
  | idle
  /-- After ESC, awaiting [ or O. -/
  | escape
  /-- After ESC O, awaiting a final byte. -/
  | ss3
  /-- After ESC [, with the parameter recognized so far. -/
  | csi (parameter : Parameter)
  /-- After the lead byte of a two-byte scalar. -/
  | utf2 (first : UInt8)
  /-- After the lead byte of a three-byte scalar. -/
  | utf3 (first : UInt8)
  /-- After the lead byte of a four-byte scalar. -/
  | utf4 (first : UInt8)
  /-- Two bytes of a three-byte scalar, awaiting the last. -/
  | utf3Last (first second : UInt8)
  /-- Two bytes of a four-byte scalar, awaiting the third. -/
  | utf4Next (first second : UInt8)
  /-- Three bytes of a four-byte scalar, awaiting the last. -/
  | utf4Last (first second third : UInt8)
  deriving BEq, Repr, DecidableEq

/-- Decoder state between bytes. Paste suppression survives sequence resets. -/
structure State where
  /-- Inside bracketed paste. Only the paste end marker clears it. -/
  paste : Bool := false
  /-- Progress through the current sequence. -/
  mode : Mode := .idle
  deriving BEq, Repr, DecidableEq

/-! ## The keys linger reads, as their standards send them

A reference for the key sequences a terminal sends for the keys linger binds, and for the ones it
reads and leaves unbound: xterm's `ctlseqs` (PC-style function keys: the cursor keys as `CSI` or,
in application mode, `SS3`, Home and End as `CSI H`/`CSI F`, `SS3 H`/`SS3 F` or VT220's `CSI 1 ~`,
`CSI 7 ~`, `CSI 4 ~` and `CSI 8 ~`, Page Up and Page Down as `CSI 5 ~` and `CSI 6 ~`, and bracketed
paste's `CSI 200 ~` and `CSI 201 ~`), and ASCII for Enter (CR, or LF), Backspace (DEL, or BS), Tab
and the Ctrl-letters, Ctrl-H, Ctrl-I, Ctrl-J and Ctrl-M being BS, HT, LF and CR. ESC alone is the
Escape key once the wait for a sequence after it ends, which a caller reads as `flush`; an ESC
that a sequence follows begins that sequence. The keys linger binds none of, Left, Right, Page Up
and Page Down, decode to no key. -/

/-- A key sequence. -/
inductive Seq where
  /-- Up: `CSI A`, or `SS3 A` when `ss3`. -/
  | up (ss3 : Bool)
  /-- Down: `CSI B`, or `SS3 B`. -/
  | down (ss3 : Bool)
  /-- Right: `CSI C`, or `SS3 C`. -/
  | right (ss3 : Bool)
  /-- Left: `CSI D`, or `SS3 D`. -/
  | left (ss3 : Bool)
  /-- Home: `CSI H`, `SS3 H`, `CSI 1 ~` or `CSI 7 ~`. -/
  | home (form : Fin 4)
  /-- End: `CSI F`, `SS3 F`, `CSI 4 ~` or `CSI 8 ~`. -/
  | end_ (form : Fin 4)
  /-- Page Up: `CSI 5 ~`. -/
  | pageUp
  /-- Page Down: `CSI 6 ~`. -/
  | pageDown
  /-- Enter: CR, or LF when `lf`. -/
  | enter (lf : Bool)
  /-- Backspace: DEL, or BS when `bs`. -/
  | backspace (bs : Bool)
  /-- Tab: HT. -/
  | tab
  /-- Escape: ESC alone, then the end of the wait for a sequence. -/
  | escape
  /-- Ctrl and the letter, `A` for 0: its C0 byte. -/
  | ctrl (letter : Fin 26)
  /-- The printable ASCII character `i` after space. -/
  | text (i : Fin 95)
  /-- Bracketed paste starts: `CSI 200 ~`. -/
  | pasteStart
  /-- Bracketed paste ends: `CSI 201 ~`, read while a paste is in progress. -/
  | pasteEnd

/-- The bytes a terminal sends for a key sequence. -/
@[expose]
def Seq.bytes : Seq → List UInt8
  | .up ss3 => [0x1B, if ss3 then 0x4F else 0x5B, 0x41]
  | .down ss3 => [0x1B, if ss3 then 0x4F else 0x5B, 0x42]
  | .right ss3 => [0x1B, if ss3 then 0x4F else 0x5B, 0x43]
  | .left ss3 => [0x1B, if ss3 then 0x4F else 0x5B, 0x44]
  | .home f =>
    [[0x1B, 0x5B, 0x48], [0x1B, 0x4F, 0x48], [0x1B, 0x5B, 0x31, 0x7E],
          [0x1B, 0x5B, 0x37, 0x7E]].getD
      f.val []
  | .end_ f =>
    [[0x1B, 0x5B, 0x46], [0x1B, 0x4F, 0x46], [0x1B, 0x5B, 0x34, 0x7E],
          [0x1B, 0x5B, 0x38, 0x7E]].getD
      f.val []
  | .pageUp => [0x1B, 0x5B, 0x35, 0x7E]
  | .pageDown => [0x1B, 0x5B, 0x36, 0x7E]
  | .enter lf => [if lf then 0x0A else 0x0D]
  | .backspace bs => [if bs then 0x08 else 0x7F]
  | .tab => [0x09]
  | .escape => [0x1B]
  | .ctrl l => [UInt8.ofNat (l.val + 1)]
  | .text i => [UInt8.ofNat (0x20 + i.val)]
  | .pasteStart => [0x1B, 0x5B, 0x32, 0x30, 0x30, 0x7E]
  | .pasteEnd => [0x1B, 0x5B, 0x32, 0x30, 0x31, 0x7E]

/-- The keys a sequence is. -/
@[expose]
def Seq.keys : Seq → List Key
  | .up _ => [.up]
  | .down _ => [.down]
  | .home _ => [.home]
  | .end_ _ => [.end]
  | .enter _ => [.enter]
  | .backspace _ => [.backspace]
  | .tab => [.tab]
  | .escape => [.escape]
  | .ctrl l =>
    if l.val + 1 = 8 then [.backspace]
    else
      if l.val + 1 = 9 then [.tab]
      else
        if l.val + 1 = 10 ∨ l.val + 1 = 13 then [.enter] else [.control (UInt8.ofNat (l.val + 1))]
  | .text i => [.text (Char.ofNat (0x20 + i.val))]
  | _ => []

/-- Whether a paste is in progress before a sequence: only a paste's end is read inside one. -/
@[expose]
def Seq.pasting : Seq → Bool
  | .pasteEnd => true
  | _ => false

/-- Whether a paste is in progress after a sequence. -/
@[expose]
def Seq.pastes : Seq → Bool
  | .pasteStart => true
  | _ => false

/-- Whether a sequence ends with the wait for more: ESC alone. -/
@[expose]
def Seq.waits : Seq → Bool
  | .escape => true
  | _ => false

/-- The state and keys a decoder's steps reach from `state` over `bytes`. -/
@[expose]
def run (feed : State → UInt8 → State × List Key) (state : State) : List UInt8 → State × List Key
  | [] => (state, [])
  | b :: bs =>
    ((run feed (feed state b).1 bs).1, (feed state b).2 ++ (run feed (feed state b).1 bs).2)

/-- What a decoder makes of a sequence: its steps from the state before it, then, for ESC alone,
the end of the wait. -/
@[expose]
def reads (feed : State → UInt8 → State × List Key) (flush : State → State × List Key) (s : Seq) :
    State × List Key :=
  if s.waits then
    ((flush (run feed { paste := s.pasting } s.bytes).1).1,
      (run feed { paste := s.pasting } s.bytes).2 ++
        (flush (run feed { paste := s.pasting } s.bytes).1).2)
  else run feed { paste := s.pasting } s.bytes

/-- A wrong decoder that drops the `SS3` cursor keys. -/
@[expose]
def ss3Dropped (feed : State → UInt8 → State × List Key) (state : State) (byte : UInt8) :
    State × List Key :=
  if state.mode = .ss3 then ({ paste := state.paste }, []) else feed state byte

/-- A wrong decoder that reads DEL as the delete-char key, Ctrl-D, instead of Backspace. -/
@[expose]
def delDeletes (feed : State → UInt8 → State × List Key) (state : State) (byte : UInt8) :
    State × List Key :=
  if byte = 0x7F ∧ state.mode = .idle then (state, [.control 0x04]) else feed state byte

end Input
