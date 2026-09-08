import Linger.Core.Wire

/-! # Wire unit tests — concrete bytes the theorems quantify over

The theorems say the codec is correct for all inputs; these pin the
actual byte layout (a peer in another language must see these exact
bytes) and exercise the decoder the way a socket would: worst-case
chunking, garbage, oversize frames. `example : … := by decide` runs at
build time.
-/

namespace Linger.Core.Wire.Tests

open Linger.Core.Wire

/-- Golden frame: `input "hi"` is tag 0, LE length 2, payload. A
different byte layout would break every deployed peer — this test is
the freeze. -/
example : encode (.input [0x68, 0x69]) = [0, 2, 0, 0, 0, 0x68, 0x69] := by decide

/-- Golden frame: `attach 80×24`. cols/rows are LE u32s in the payload. -/
example : encode (.attach 80 24) = [3, 8, 0, 0, 0, 80, 0, 0, 0, 24, 0, 0, 0] := by decide

/-- Nullary verb: header only. -/
example : encode .kill = [5, 0, 0, 0, 0] := by decide

/-- Byte-by-byte feeding (the worst chunking a socket can produce)
delivers exactly the same messages as one-shot decoding. -/
example :
    (let bytes := encode (.attach 80 24) ++ encode (.input [1, 2, 3]) ++ encode .kill
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

/-- Fixed-size chunker for the §Stream test (7 never divides a frame
boundary in the stream below). -/
private def chop7 (l : List UInt8) (fuel : Nat) : List (List UInt8) :=
  match fuel with
  | 0 => [l]
  | fuel + 1 => if l.length ≤ 7 then [l] else l.take 7 :: chop7 (l.drop 7) fuel

/-- `feedAll` (§Stream's subject) over a chunking that splits every
frame across boundaries delivers exactly the one-shot decode: same
messages, same order, clean final state. -/
example :
    (let bytes := encode (.attach 80 24) ++ encode (.input [1, 2, 3])
                    ++ encode (.labelSet [107, 61, 118]) ++ encode .kill
     let (d, ms) := Decoder.feedAll {} (chop7 bytes bytes.length)
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
16 is `.screen` forever (specs/agent-cli.md). And it round-trips as itself,
not as `.unknown 16`. -/
example : encode .screen = [16, 0, 0, 0, 0] := by decide

example : (decode (encode .screen)).2 == [.screen] := by native_decide

end Linger.Core.Wire.Tests
