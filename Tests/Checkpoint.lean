import Linger.Core.Checkpoint

/-! # Checkpoint codec tests

§Restore is proved in `Theorems/Checkpoint.lean`; these pin the two
things a proof does not show — that RLE actually *compresses* (the
whole point of the change), and that a fed-then-saved-then-loaded
session comes back exactly (an end-to-end sanity check over the real
`Vt.feed` path).
-/

namespace Linger.Core.Checkpoint.Tests

open Linger.Core.Checkpoint Linger.Core.Vt

/-- runs/expand invert (the load-bearing RLE fact, on concrete data). -/
example : (expand (runs [1, 1, 1, 2, 2, 3, 1, 1]) == [1, 1, 1, 2, 2, 3, 1, 1]) = true := by
  native_decide

/-- A run of N identical cells serializes to a small constant, not O(N):
a blank 80-cell row is one run. This is why an empty screen dropped
from 22.7 KiB to under 2. -/
example :
    (let blank : Row := blankRow 80 {}
     (wRow blank).length < 20) =
      true := by
  native_decide

/-- …and it still round-trips (RLE is exact, not lossy). -/
example :
    (let blank : Row := blankRow 80 {}
     match rRow (wRow blank) with
      | some (r, rest) => r == blank && rest.isEmpty
      | none => false) =
      true := by
  native_decide

/-- A mixed row round-trips through the run boundaries. -/
example :
    (let row : Row :=
        #[{ base := 'a' }, { base := 'a' }, { base := 'b', pen := { bold := true } },
          { base := ' ' }, { base := ' ' }]
     match rRow (wRow row) with
      | some (r, _) => r == row
      | none => false) =
      true := by
  native_decide

/-- End-to-end: feed a real byte stream, checkpoint it, load it back,
and the visible screen (and scrollback, cwd, labels) matches modulo the
parser-state quiesce the format deliberately drops. -/
example :
    (let v := (Vt.init 40 6).feedBytes "hello\r\n\x1b[33mworld\x1b[0m\r\nline3\r\nline4".toUTF8
     let ck : Ckpt := { vt := v, cwd := "/tmp/x", labels := [("k", "v")] }
      match load (save ck) with
      | some ck' =>
        ck'.vt.grid == v.grid && ck'.vt.sb.toList == v.sb.toList && ck'.vt.cursor == v.cursor &&
          ck'.cwd == "/tmp/x" &&
          ck'.labels == [("k", "v")]
      | none => false) =
      true := by
  native_decide

/-- A checkpoint with scrollback round-trips the history too. -/
example :
    (let v := (Vt.init 10 2).feedBytes "1\r\n2\r\n3\r\n4\r\n5".toUTF8
     match load (save { vt := v, cwd := "", labels := [] }) with
      | some ck' => ck'.vt.sb.toList.map (·.size) == v.sb.toList.map (·.size)
      | none => false) =
      true := by
  native_decide

/-! ### The format tag

`save` writes `"LNGR"` v1 and `load` accepts nothing else. The theorems are about the
*constant*, so these pin the bytes — which is what catches someone editing four hex
literals to the wrong value, a change no round-trip theorem can see. -/

/-- The bytes themselves, spelled out. -/
example : (magic == [0x4C, 0x4E, 0x47, 0x52, 1]) = true := by native_decide

/-- What `save` emits starts with exactly that. -/
example :
    (let c : Ckpt := { vt := Vt.init 4 2, cwd := "", labels := [] }
     (save c).take 5 == magic) =
      true := by
  native_decide

/-- Any other tag is refused — including the pre-rename `"LZMX"` (whose reader was
removed in `e1ac562`'s successor; check that commit out if you ever need it), a future
version byte, and rubbish. A checkpoint is a cache, not a contract. -/
example :
    (let c : Ckpt := { vt := Vt.init 4 2, cwd := "", labels := [] }
     let body := (save c).drop 5
     (load ([0x4C, 0x5A, 0x4D, 0x58, 1] ++ body)).isNone      -- "LZMX" v1
       && (load ([0x4C, 0x4E, 0x47, 0x52, 2] ++ body)).isNone  -- "LNGR" v2
       && (load ([0x00, 0x00, 0x00, 0x00, 0] ++ body)).isNone) = true := by
  native_decide

end Linger.Core.Checkpoint.Tests
