module

import Tools.Input
public meta import Tools.Input

/-! Byte-level fixtures exercise incremental state, including paste boundaries.
Unicode validation is Lean's bounded UTF-8 conversion, not a second decoder. -/

namespace Tools.Input.Tests

open Tools.Input

private def walk (state : State) (bytes : List UInt8) : State × List Key :=
  bytes.foldl
    (fun (state, keys) byte =>
      let (next, emitted) := feed state byte
      (next, keys ++ emitted))
    (state, [])

private def input (text : String) : State × List Key := walk init text.toUTF8.toList

#guard (input "a Z!").2 == [.text 'a', .text ' ', .text 'Z', .text '!']

#guard
  (walk init [8, 127, 21, 16, 14, 9, 13, 10, 3, 4, 18]).2 ==
    [.backspace, .backspace, .clear, .up, .down, .down, .accept, .accept, .cancel, .cancel,
      .refresh]

#guard (walk init [0, 1, 2, 7, 11, 12, 17, 19, 20, 22, 26, 28, 31]).2.isEmpty

#guard
  let (state, keys) := feed init 27
  keys.isEmpty && pending state && flush state == (init, [.cancel]) &&
    flush (flush state).1 == (init, [])

#guard
  (input "\x1b[A\x1b[B\x1b[H\x1b[F\x1bOA\x1bOB\x1bOH\x1bOF").2 ==
    [.up, .down, .first, .last, .up, .down, .first, .last]

#guard (input "\x1b[1~\x1b[7~\x1b[4~\x1b[8~").2 == [.first, .first, .last, .last]

-- Unsupported parameters and embedded controls are consumed until a final byte.
#guard (input "\x1b[12;3\r\n\x03~x\x1b[1;5Ay\x1b[99~z").2 == [.text 'x', .text 'y', .text 'z']

#guard (input "\x1bO12\r~x\x1b?y").2 == [.text 'x', .text 'y']

#guard
  let (state, keys) := input "\x1b[123"
  keys.isEmpty && pending state && flush state == (init, []) &&
    (feed (flush state).1 13).2 == [.accept]

#guard
  let (state, keys) := input "\x1bO"
  keys.isEmpty && pending state && flush state == (init, [])

-- Valid two-, three- and four-byte scalars, including combining characters.
#guard (input "é界🙂é").2 == [.text 'é', .text '界', .text '🙂', .text 'e', .text '́']

#guard
  let (part, keys) := walk init [0xf0, 0x9f, 0x99]
  keys.isEmpty && pending part && feed part 0x82 == (init, [.text '🙂'])

#guard
  let (part, keys) := walk init [0xe7, 0x95]
  keys.isEmpty && pending part && feed part 0x8c == (init, [.text '界'])

#guard
  let (part, keys) := feed init 0xc3
  keys.isEmpty && pending part && feed part 0xa9 == (init, [.text 'é'])

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
    pending state && flush state == (init, [])

-- Paste changes query text only; no pasted byte can act as a control key.
#guard
  let (state, keys) := input "\x1b[200~a\r\n\x03\x04\t\x12\x15\x08\x7fé界🙂\x1b[201~"
  keys == [.text 'a', .text 'é', .text '界', .text '🙂'] && !state.paste && !pending state &&
    feed state 13 == (init, [.accept])

#guard
  let (state, keys) := input "\x1b[200~a\x1b[A\x1bOB\x1b[7~\x1b[8~b\x1b[201~"
  keys == [.text 'a', .text 'b'] && state == init

#guard
  let (state, keys) := input "\x1b[200~"
  keys.isEmpty && state.paste && !pending state && flush state == (state, []) &&
    (walk (flush state).1 [13, 3, 4, 18, 21]).2.isEmpty

-- Timeouts discard an incomplete sequence but never disable paste suppression.
#guard
  ["\x1b", "\x1b[", "\x1b[20", "\x1bO", "é\x1b["].all fun suffix =>
    let state := (input ("\x1b[200~" ++ suffix)).1
    let (flushed, keys) := flush state
    keys.isEmpty && flushed.paste && !pending flushed && (walk flushed [13, 3, 4, 16, 14]).2.isEmpty

#guard
  let part := (input "\x1b[200~").1
  let state := (walk part [0xf0, 0x9f]).1
  let (flushed, keys) := flush state
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
  state.paste && !pending state && (feed state 13).2.isEmpty

#guard
  let (state, keys) := input "\x1b[200~\x1b[999\r\x03~x\x1b?\x04\x1b[201~\r"
  keys == [.text 'x', .accept] && state == init

#guard
  let (state, keys) := input "\x1b[201~x\x1b[200~y\x1b[200~z\x1b[201~"
  keys == [.text 'x', .text 'y', .text 'z'] && state == init

#guard !pending init && flush init == (init, [])

end Tools.Input.Tests
