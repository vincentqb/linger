module

public import Tools.Key

public section

/-! Incremental input for the optional session selector.

There is no growing control-sequence buffer. CSI parameters have a finite
recognizer, and UTF-8 prefixes retain at most three bytes. Completed scalars use
Lean's UTF-8 validator on at most four bytes. Paste suppression belongs to the
outer state so a timeout or malformed sequence cannot turn it off. -/

namespace Tools.Input

inductive Parameter where
  | empty
  | one
  | two
  | four
  | seven
  | eight
  | twenty
  | pasteStart
  | pasteEnd
  | other
  deriving BEq, Repr, DecidableEq

inductive Mode where
  | idle
  | escape
  | ss3
  | csi (parameter : Parameter)
  | utf2 (first : UInt8)
  | utf3 (first : UInt8)
  | utf4 (first : UInt8)
  | utf3Last (first second : UInt8)
  | utf4Next (first second : UInt8)
  | utf4Last (first second third : UInt8)
  deriving BEq, Repr, DecidableEq

structure State where
  paste : Bool := false
  mode : Mode := .idle
  deriving BEq, Repr, DecidableEq

def init : State := {}

/-- Idle paste does not need a timeout: waiting never implies its end marker. -/
def pending (state : State) :
    Bool := match state.mode with
  | .idle => false
  | _ => true

private def stored (mode : Mode) : Array UInt8 :=
  match mode with
  | .utf2 a | .utf3 a | .utf4 a => #[a]
  | .utf3Last a b | .utf4Next a b => #[a, b]
  | .utf4Last a b c => #[a, b, c]
  | _ => #[]

private def advance (parameter : Parameter) (byte : UInt8) : Parameter :=
  match parameter, byte with
  | .empty, 0x31 => .one
  | .empty, 0x32 => .two
  | .empty, 0x34 => .four
  | .empty, 0x37 => .seven
  | .empty, 0x38 => .eight
  | .two, 0x30 => .twenty
  | .twenty, 0x30 => .pasteStart
  | .twenty, 0x31 => .pasteEnd
  | _, _ => .other

private def cursor (byte : UInt8) : Option Key :=
  match byte with
  | 0x41 => some .up
  | 0x42 => some .down
  | 0x48 => some .first
  | 0x46 => some .last
  | _ => none

private def decode (bytes : Array UInt8) : Option Char :=
  match String.fromUTF8? (ByteArray.mk bytes) with
  | some text =>
    match text.toList with
    | [char] => some char
    | _ => none
  | none => none

private def idle (paste : Bool) (byte : UInt8) : State × Option Key :=
  if byte == 0x1b then ({ paste, mode := .escape }, none)
  else
    if byte < 0x80 then
      ({ paste },
        match byte with
        | 8 | 127 => some .backspace
        | 21 => some .clear
        | 16 => some .up
        | 14 | 9 => some .down
        | 13 | 10 => some .accept
        | 3 | 4 => some .cancel
        | _ => if byte ≥ 32 then some (.text (Char.ofUInt8 byte)) else none)
    else
      if 0xc2 ≤ byte && byte ≤ 0xdf then ({ paste, mode := .utf2 byte }, none)
      else
        if 0xe0 ≤ byte && byte ≤ 0xef then ({ paste, mode := .utf3 byte }, none)
        else
          if 0xf0 ≤ byte && byte ≤ 0xf4 then ({ paste, mode := .utf4 byte }, none)
          else ({ paste }, none)

private def utf8Step (state : State) (byte : UInt8) : State × Option Key :=
  if 0x80 ≤ byte && byte ≤ 0xbf then
    match state.mode with
    | .utf3 a => ({ state with mode := .utf3Last a byte }, none)
    | .utf4 a => ({ state with mode := .utf4Next a byte }, none)
    | .utf4Next a b => ({ state with mode := .utf4Last a b byte }, none)
    | _ => ({ paste := state.paste }, (decode ((stored state.mode).push byte)).map .text)
  else idle state.paste byte

private def step (state : State) (byte : UInt8) : State × Option Key :=
  match state.mode with
  | .idle => idle state.paste byte
  | .escape =>
    match byte with
    | 0x1b => (state, none)
    | 0x5b => ({ state with mode := .csi .empty }, none)
    | 0x4f => ({ state with mode := .ss3 }, none)
    | _ => ({ paste := state.paste }, none)
  | .ss3 =>
    if byte == 0x1b then ({ state with mode := .escape }, none)
    else
      if 0x40 ≤ byte && byte ≤ 0x7e then ({ paste := state.paste }, cursor byte)
      else ({ state with mode := .csi .other }, none)
  | .csi parameter =>
    if byte == 0x1b then ({ state with mode := .escape }, none)
    else
      if 0x40 ≤ byte && byte ≤ 0x7e then
        match parameter, byte with
        | .pasteStart, 0x7e => ({ paste := true }, none)
        | .pasteEnd, 0x7e => (init, none)
        | .empty, _ => ({ paste := state.paste }, cursor byte)
        | .one, 0x7e | .seven, 0x7e => ({ paste := state.paste }, some .first)
        | .four, 0x7e | .eight, 0x7e => ({ paste := state.paste }, some .last)
        | _, _ => ({ paste := state.paste }, none)
      else ({ state with mode := .csi (advance parameter byte) }, none)
  | _ => utf8Step state byte

/-- Text excludes C0, DEL and C1 controls. Paste admits only text, even when a
decoder branch recognizes a navigation key or a command byte. -/
private def deliver (paste : Bool) (event : Option Key) : List Key :=
  (event.filter fun
      | .text char => 32 ≤ char.toNat && (char.toNat < 127 || 160 ≤ char.toNat)
      | _ => !paste).toList

def feed (state : State) (byte : UInt8) : State × List Key :=
  let (next, event) := step state byte
  (next, deliver state.paste event)

/-- A lone escape cancels outside paste. All other incomplete sequences are
discarded; in particular, a timeout cannot disable paste suppression. -/
def flush (state : State) : State × List Key :=
  ({ paste := state.paste }, if state.mode = .escape ∧ state.paste = false then [.cancel] else [])

end Tools.Input
