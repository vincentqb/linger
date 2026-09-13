module

public import Linger.Core.Checkpoint
-- Converted from legacy by the `Vt` seal (`specs/vt-toolkit.md` Step 1): the codec
-- fixtures compare the decoded screen field-by-field, so they are a friend of the
-- emulator.
import all Linger.Core.Vt
import all Linger.Core.Checkpoint
-- `native_decide` compiles its goals, and a module's compiled code only sees
-- meta-imported modules — names alone arrive via the public import above.
public meta import Linger.Core.Vt
public meta import Linger.Core.Checkpoint

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

/-! ### The corrupt record

`specs/vt-toolkit.md` Step 2. `rVt` hands its seventeen decoded values to
`Vt.ofDecoded`, which returns `none` unless they describe a `Good` screen, so a hostile
file cannot put `cols := 0` — or a cursor off the screen, or an inverted scroll region —
into the emulator. `Theorems/Checkpoint.lean`'s `load_good` states it for *any* byte
string and `load_save_none_of_cols_zero` for the canonical junk value; these pin the two
things the theorems do not show.

The first two are the honest shape of the attack: a **real** checkpoint with **one byte
flipped**, not a forged `Vt` serialised. The payload starts at index 5 (after the
`"LNGR"` v1 tag) with LEB128 `cols` then `rows`, both single-byte at these dimensions —
which the fixtures assert rather than assume, so a format change fails here loudly
instead of silently patching some other field. -/

/-- The control. Without it, every refusal below is equally consistent with `load`
having become unconditionally `none`. -/
example :
    (let c : Ckpt := { vt := Vt.init 4 2, cwd := "/tmp", labels := [("k", "v")] }
     (load (save c)).isSome) =
      true := by
  native_decide

/-- One byte flipped so the record claims **zero columns** — a screen no
`init`/`resize`/`feed` path can produce, and the state the pre-Step-2 decoder built
without complaint. Refused. -/
example :
    (let c : Ckpt := { vt := Vt.init 4 2, cwd := "/tmp", labels := [("k", "v")] }
     let bytes := save c
     bytes[5]? == some 4                       -- the byte being patched IS `cols`
       && (load (bytes.set 5 0)).isNone) =
      true := by
  native_decide

/-- The same at **zero rows**. -/
example :
    (let c : Ckpt := { vt := Vt.init 4 2, cwd := "/tmp", labels := [("k", "v")] }
     let bytes := save c
     bytes[6]? == some 2                       -- and this one IS `rows`
       && (load (bytes.set 6 0)).isNone) =
      true := by
  native_decide

/-- Past the **ceiling**, not the floor: `clampDim` bounds a live session to 1000
columns, so 1001 is a state the emulator cannot reach and the shim's `(unsigned short)`
cast is the reason it matters. Forged here rather than byte-patched because 1001 is two
LEB128 bytes. -/
example :
    (let v := { Vt.init 4 2 with cols := 1001 }
     (load (save { vt := v, cwd := "", labels := [] })).isNone) =
      true := by
  native_decide

/-- Not only the dimensions: a cursor **outside** the screen is refused too, which is
`Good.curX`/`curY` and the clause a naive "clamp the dimensions" fix would have missed
entirely. -/
example :
    (let v := { Vt.init 4 2 with cursor := { x := 9, y := 0 } }
     (load (save { vt := v, cwd := "", labels := [] })).isNone) =
      true := by
  native_decide

/-- And an **inverted scroll region** (`Good.topLe`), the third independent clause. -/
example :
    (let v :=
        { Vt.init 4 2 with
          top := 1, bot := 0 }
     (load (save { vt := v, cwd := "", labels := [] })).isNone) =
      true := by
  native_decide

end Linger.Core.Checkpoint.Tests
