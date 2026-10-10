module

import Linger.Tools.Key
meta import Linger.Tools.Key

/-! Byte-level fixtures exercise incremental state, including paste boundaries.
The original selector expectations retain their concrete bindings, while raw
decoder checks distinguish physical events before binding. Unicode validation
is Lean's bounded UTF-8 conversion, not a second decoder. -/

namespace Linger.Tools.Input.Tests

def boundFeed (state : State) (byte : UInt8) : State × List Linger.Tools.Key :=
  let (next, events) := feed state byte
  (next, events.filterMap Linger.Tools.Key.ofInput)

def boundFlush (state : State) : State × List Linger.Tools.Key :=
  let (next, events) := flush state
  (next, events.filterMap Linger.Tools.Key.ofInput)

def walk (state : State) (bytes : List UInt8) : State × List Linger.Tools.Key :=
  bytes.foldl
    (fun (state, keys) byte =>
      let (next, emitted) := boundFeed state byte
      (next, keys ++ emitted))
    (state, [])

def input (text : String) : State × List Linger.Tools.Key := walk init text.toUTF8.toList

def decoded (state : State) (bytes : List UInt8) : State × List Key :=
  bytes.foldl
    (fun (state, keys) byte =>
      let (next, emitted) := feed state byte
      (next, keys ++ emitted))
    (state, [])

-- These six value checks also compile against the predecessor and fail there.
#guard (feed init 0).2.length == 1

#guard (feed init 18).2.length == 1

#guard (feed init 16).2 != (feed { mode := .ss3 } 0x41).2

#guard (feed init 14).2 != (feed init 9).2

#guard (feed init 3).2 != (feed init 4).2

#guard (feed init 3).2 != (flush { mode := .escape }).2

-- All idle byte events, including C0 bytes that have no selector binding.
#guard
  (List.range 256).all fun n =>
    let byte := UInt8.ofNat n
    let expected : List Key :=
      match n with
      | 8 | 127 => [.backspace]
      | 9 => [.tab]
      | 10 | 13 => [.enter]
      | 27 => []
      | _ => if n < 32 then [.control byte] else if n < 127 then [.text (Char.ofNat n)] else []
    (feed init byte).2 == expected

-- Independent concrete selector defaults for every byte, not adapter output
-- reused as an expected result.
#guard
  (List.range 256).all fun n =>
    let expected : List Linger.Tools.Key :=
      match n with
      | 8 | 127 => [.backspace]
      | 21 => [.clear]
      | 16 => [.up]
      | 14 | 9 => [.down]
      | 13 | 10 => [.accept]
      | 3 | 4 => [.cancel]
      | _ => if 32 ≤ n && n < 127 then [.text (Char.ofNat n)] else []
    (boundFeed init (UInt8.ofNat n)).2 == expected

-- The adapter also handles constructed control events outside the C0 range.
#guard
  (List.range 256).all fun n =>
    let expected : Option Linger.Tools.Key :=
      match n with
      | 21 => some .clear
      | 16 => some .up
      | 14 => some .down
      | 3 | 4 => some .cancel
      | _ => none
    Linger.Tools.Key.ofInput (.control (UInt8.ofNat n)) == expected

#guard
  [(.backspace, .backspace), (.tab, .down), (.enter, .accept), (.escape, .cancel), (.up, .up),
        (.down, .down), (.home, .first), (.end, .last), (.text 'a', .text 'a'),
        (.text '界', .text '界'), (.text '🙂', .text '🙂')].all
    fun (event, action) => Linger.Tools.Key.ofInput event == some action

#guard
  (decoded init [0, 18, 21, 16, 14, 3, 4, 9, 8, 127, 13, 10]).2 ==
    [.control 0, .control 18, .control 21, .control 16, .control 14, .control 3, .control 4, .tab,
      .backspace, .backspace, .enter, .enter]

#guard
  (decoded init "\x1b[A\x1b[B\x1b[H\x1b[F\x1bOA\x1bOB\x1bOH\x1bOF".toUTF8.toList).2 ==
    [.up, .down, .home, .end, .up, .down, .home, .end]

#guard (decoded init "\x1b[1~\x1b[7~\x1b[4~\x1b[8~".toUTF8.toList).2 == [.home, .home, .end, .end]

#guard
  (decoded init "é界🙂é".toUTF8.toList).2 == [.text 'é', .text '界', .text '🙂', .text 'e', .text '́']

#guard (decoded init [0xe2, 0x82, 0x61, 0xc3, 13, 0xc3, 18]).2 == [.text 'a', .enter, .control 18]

#guard
  let (state, events) := feed init 27
  events.isEmpty && pending state && flush state == (init, [.escape]) &&
    flush (flush state).1 == (init, [])

#guard
  let pasted := (decoded init "\x1b[200~".toUTF8.toList).1
  (List.range 32).all (fun n => (feed pasted (UInt8.ofNat n)).2.isEmpty) &&
    (decoded pasted "\x1b[A\x1bOB\x1b[7~\x1b[8~".toUTF8.toList).2.isEmpty &&
    (decoded pasted "é界🙂".toUTF8.toList).2 == [.text 'é', .text '界', .text '🙂']

#guard
  ["\x1b", "\x1b[", "\x1b[20", "\x1bO"].all fun suffix =>
    let state := (decoded { paste := true } suffix.toUTF8.toList).1
    let (flushed, events) := flush state
    events.isEmpty && flushed.paste && !pending flushed &&
      (List.range 32).all (fun n => (feed flushed (UInt8.ofNat n)).2.isEmpty)

#guard (input "a Z!").2 == [.text 'a', .text ' ', .text 'Z', .text '!']

#guard
  (walk init [8, 127, 21, 16, 14, 9, 13, 10, 3, 4]).2 ==
    [.backspace, .backspace, .clear, .up, .down, .down, .accept, .accept, .cancel, .cancel]

#guard (walk init [0, 1, 2, 7, 11, 12, 17, 18, 19, 20, 22, 26, 28, 31]).2.isEmpty

#guard boundFeed init 18 == (init, [])

#guard
  let (state, keys) := boundFeed init 27
  keys.isEmpty && pending state && boundFlush state == (init, [.cancel]) &&
    boundFlush (boundFlush state).1 == (init, [])

#guard
  (input "\x1b[A\x1b[B\x1b[H\x1b[F\x1bOA\x1bOB\x1bOH\x1bOF").2 ==
    [.up, .down, .first, .last, .up, .down, .first, .last]

#guard (input "\x1b[1~\x1b[7~\x1b[4~\x1b[8~").2 == [.first, .first, .last, .last]

-- Unsupported parameters and embedded controls are consumed until a final byte.
#guard (input "\x1b[12;3\r\n\x03~x\x1b[1;5Ay\x1b[99~z").2 == [.text 'x', .text 'y', .text 'z']

#guard (input "\x1bO12\r~x\x1b?y").2 == [.text 'x', .text 'y']

#guard
  let (state, keys) := input "\x1b[123"
  keys.isEmpty && pending state && boundFlush state == (init, []) &&
    (boundFeed (boundFlush state).1 13).2 == [.accept]

#guard
  let (state, keys) := input "\x1bO"
  keys.isEmpty && pending state && boundFlush state == (init, [])

-- Valid two-, three- and four-byte scalars, including combining characters.
#guard (input "é界🙂é").2 == [.text 'é', .text '界', .text '🙂', .text 'e', .text '́']

#guard
  let (part, keys) := walk init [0xf0, 0x9f, 0x99]
  keys.isEmpty && pending part && boundFeed part 0x82 == (init, [.text '🙂'])

#guard
  let (part, keys) := walk init [0xe7, 0x95]
  keys.isEmpty && pending part && boundFeed part 0x8c == (init, [.text '界'])

#guard
  let (part, keys) := boundFeed init 0xc3
  keys.isEmpty && pending part && boundFeed part 0xa9 == (init, [.text 'é'])

-- Reject overlong encodings, surrogate scalars, out-of-range scalars and stray
-- continuation bytes; do not turn each byte into a Latin-1 character.
#guard
  [[0xc0, 0xaf], [0xc1, 0xbf], [0xe0, 0x80, 0xaf], [0xed, 0xa0, 0x80], [0xf0, 0x80, 0x80, 0xaf],
        [0xf4, 0x90, 0x80, 0x80], [0xf5, 0x80, 0x80, 0x80], [0x80, 0xbf, 0xff]].all
    fun bytes => (walk init bytes).2.isEmpty

#guard (walk init [0xc2, 0x80, 0xc2, 0x9f, 0xc2, 0xa0]).2 == [.text ' ']

#guard (walk init [0xe2, 0x82, 0x61, 0xc3, 13]).2 == [.text 'a', .accept]

#guard
  [[0xc3], [0xe7, 0x95], [0xf0, 0x9f, 0x99]].all fun bytes =>
    let state := (walk init bytes).1
    pending state && boundFlush state == (init, [])

-- Paste changes query text only; no pasted byte can act as a control key.
#guard
  let (state, keys) := input "\x1b[200~a\r\n\x03\x04\t\x12\x15\x08\x7fé界🙂\x1b[201~"
  keys == [.text 'a', .text 'é', .text '界', .text '🙂'] && !state.paste && !pending state &&
    boundFeed state 13 == (init, [.accept])

#guard
  let (state, keys) := input "\x1b[200~a\x1b[A\x1bOB\x1b[7~\x1b[8~b\x1b[201~"
  keys == [.text 'a', .text 'b'] && state == init

#guard
  let (state, keys) := input "\x1b[200~"
  keys.isEmpty && state.paste && !pending state && boundFlush state == (state, []) &&
    (walk (boundFlush state).1 [13, 3, 4, 18, 21]).2.isEmpty

-- Timeouts discard an incomplete sequence but never disable paste suppression.
#guard
  ["\x1b", "\x1b[", "\x1b[20", "\x1bO", "é\x1b["].all fun suffix =>
    let state := (input ("\x1b[200~" ++ suffix)).1
    let (flushed, keys) := boundFlush state
    keys.isEmpty && flushed.paste && !pending flushed && (walk flushed [13, 3, 4, 16, 14]).2.isEmpty

#guard
  let part := (input "\x1b[200~").1
  let state := (walk part [0xf0, 0x9f]).1
  let (flushed, keys) := boundFlush state
  keys.isEmpty && flushed.paste && !pending flushed &&
    (walk flushed [13, 3, 4, 0x99, 0x82]).2.isEmpty

-- Every split of the end marker is retained across byte reads. The Enter after
-- its final byte is ordinary input again.
#guard
  (List.range 7).all fun split =>
    let pasted := (input "\x1b[200~x").1
    let marker := "\x1b[201~".toUTF8.toList
    let (part, before) := walk pasted (marker.take split)
    let (state, after) := walk part (marker.drop split ++ [13])
    before.isEmpty && after == [.accept] && state == init

-- A long unsupported CSI is bounded state, even while paste remains active.
#guard
  let start := (input "\x1b[200~\x1b[").1
  let state := (walk start (List.replicate 4096 0x39 ++ [13, 3, 0x7e])).1
  state.paste && !pending state && (boundFeed state 13).2.isEmpty

#guard
  let (state, keys) := input "\x1b[200~\x1b[999\r\x03~x\x1b?\x04\x1b[201~\r"
  keys == [.text 'x', .accept] && state == init

#guard
  let (state, keys) := input "\x1b[201~x\x1b[200~y\x1b[200~z\x1b[201~"
  keys == [.text 'x', .text 'y', .text 'z'] && state == init

#guard !pending init && boundFlush init == (init, [])

end Linger.Tools.Input.Tests
