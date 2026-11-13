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

end Input
