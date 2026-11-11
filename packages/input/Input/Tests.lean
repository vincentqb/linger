module

import Input
meta import Input

/-! Byte-level fixtures exercise incremental state, including paste boundaries, as physical
events before any application binds them. Unicode validation is Lean's bounded UTF-8
conversion, not a second decoder. -/

namespace Input.Tests

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

-- All idle byte events, including C0 bytes that have no application binding.
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

end Input.Tests
