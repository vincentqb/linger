module

import all Linger.Session.CoreCode.Wire
meta import Linger.Session.CoreCode.Wire

/-! # Wire unit tests — concrete bytes the theorems quantify over

The theorems say the codec is correct for all inputs; these pin the
actual byte layout (a peer in another language must see these exact
bytes) and exercise the decoder the way a socket would: worst-case
chunking, garbage, oversize frames, evaluated at build time.
-/

namespace Linger.Session.Wire.Tests

/-- Golden frame: `input "hi"` is tag 0, LE length 2, payload. A
different byte layout would break every deployed peer — this test is
the freeze. -/
example : encode (.input [0x68, 0x69]) = [0, 2, 0, 0, 0, 0x68, 0x69] := by decide

/-- Golden frames: a writable and a read-only `attach 80×24` are tag 18, the mode byte, then
cols and rows as LE u32s. -/
example : encode (.attach .writable 80 24) = [18, 9, 0, 0, 0, 0, 80, 0, 0, 0, 24, 0, 0, 0] := by
  decide

example : encode (.attach .readOnly 80 24) = [18, 9, 0, 0, 0, 1, 80, 0, 0, 0, 24, 0, 0, 0] := by
  decide

/-- The attach of levels 1 and 2, tag 3 with only a size, is a message this version does not
know, as is an attach whose mode byte it does not know: both are refused, never read as an
attach. -/
example :
    ((decode [3, 8, 0, 0, 0, 80, 0, 0, 0, 24, 0, 0, 0]).2 ==
        [.unknown 3 [80, 0, 0, 0, 24, 0, 0, 0]]) =
      true := by
  native_decide

/-- The label requests of versions before the session record had fields of its own, tags 11 to
13, are messages this version does not know, so an older client's `set` is refused, never read
as a description; tag 21 describes the session. -/
example :
    ((decode ([11, 3, 0, 0, 0, 107, 61, 118] ++ [12, 1, 0, 0, 0, 107] ++ [13, 0, 0, 0, 0])).2 ==
        [.unknown 11 [107, 61, 118], .unknown 12 [107], .unknown 13 []]) =
      true := by
  native_decide

example : encode (.describe [100]) = [21, 1, 0, 0, 0, 100] := by decide

example :
    ((decode [18, 9, 0, 0, 0, 2, 80, 0, 0, 0, 24, 0, 0, 0]).2 ==
        [.unknown 18 [2, 80, 0, 0, 0, 24, 0, 0, 0]]) =
      true := by
  native_decide

/-- A tag-18 frame with no mode byte at all names no mode either. -/
example : ((decode [18, 0, 0, 0, 0]).2 == [.unknown 18 []]) = true := by native_decide

/-- Both modes, and a 0×0 size, survive the trip. -/
example : (decode (encode (.attach .writable 0 0))).2 == [.attach .writable 0 0] := by native_decide

example : (decode (encode (.attach .readOnly 213 58))).2 == [.attach .readOnly 213 58] := by
  native_decide

/-- Nullary verb: header only. -/
example : encode .kill = [5, 0, 0, 0, 0] := by decide

/-- Byte-by-byte feeding (the worst chunking a socket can produce)
delivers exactly the same messages as one-shot decoding. -/
example :
    (let bytes := encode (.attach .writable 80 24) ++ encode (.input [1, 2, 3]) ++ encode .kill
     let oneShot := (decode bytes).2
      let byteWise :=
        bytes.foldl
          (fun (acc : Decoder × List Msg) b =>
            let (d, ms) := acc.1.feed [b]
            (d, acc.2 ++ ms))
          ({}, [])
      byteWise.2 == oneShot && byteWise.1.buf.isEmpty && !byteWise.1.errored) =
      true := by
  native_decide

/-- Fixed-size chunker for the re-chunking test: every 7 bytes, which cuts each frame but the last
of the stream below. -/
def chop7 (l : List UInt8) : List (List UInt8) :=
  if l.length ≤ 7 then [l] else l.take 7 :: chop7 (l.drop 7)
termination_by l.length
decreasing_by simp only [List.length_drop]; omega

/-- `feedAll` (the subject of `decode_encode_chunked`) over a chunking that splits every
frame across boundaries delivers exactly the one-shot decode: same
messages, same order, clean final state. -/
example :
    (let bytes := encode (.attach .readOnly 80 24) ++ encode (.input [1, 2, 3])
                    ++ encode (.describe [107, 61, 118]) ++ encode .kill
     let (d, ms) := Decoder.feedAll {} (chop7 bytes)
     ms == (decode bytes).2 && d.buf.isEmpty && !d.errored) = true := by native_decide

/-- A frame claiming a payload larger than `maxPayload` poisons the
decoder (which the runtime treats as connection-fatal) — it does not
buffer. 0x00040001 = maxPayload + 1. -/
example :
    (let (d, ms) := Decoder.feed {} [0, 1, 0, 4, 0]
     d.errored && d.buf.isEmpty && ms.isEmpty) = true := by native_decide

/-- The errored state is sticky: even a subsequently valid frame is
ignored. -/
example :
    (let (d, _) := Decoder.feed {} [0, 1, 0, 4, 0]
     let (d2, ms) := d.feed (encode .kill)
     d2.errored && ms.isEmpty) = true := by native_decide

/-- An unassigned tag (99) is delivered as `.unknown`, payload intact,
and the frame after it still parses — a newer peer cannot desync us. -/
example :
    ((decode ([99, 3, 0, 0, 0, 7, 8, 9] ++ encode .kill)).2 == [.unknown 99 [7, 8, 9], .kill]) =
      true := by
  native_decide

/-- A partial frame is retained, not delivered: 5-byte header claiming
4 payload bytes, only 2 present. -/
example :
    (let (d, ms) := decode [0, 4, 0, 0, 0, 1, 2]
     ms.isEmpty && !d.errored && d.buf.length == 7) = true := by native_decide

/-- Structured fields survive the trip. -/
example : (decode (encode (.resize 213 58))).2 == [.resize 213 58] := by native_decide

example : (decode (encode (.exited 127))).2 == [.exited 127] := by native_decide

/-- Golden frame: `screen` (capture) is tag 16, nullary — frozen-append, so
16 is `.screen` forever. And it round-trips as itself,
not as `.unknown 16`. -/
example : encode .screen = [16, 0, 0, 0, 0] := by decide

example : (decode (encode .screen)).2 == [.screen] := by native_decide

end Linger.Session.Wire.Tests
