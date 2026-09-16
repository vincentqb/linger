module

public import Linger.Core.Checkpoint
-- Converted from legacy by the `Vt` seal (`specs/archive/vt-toolkit.md` Step 1): the codec
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

`specs/archive/vt-toolkit.md` Step 2. `rVt` hands its seventeen decoded values to
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
`init`/`resize`/`feed` path can produce, and the state the decoder built without
complaint before it validated `Good`. Refused. -/
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

/-! ### The corrupt record, part two: the shape of the screen (finding R2)

`Vt.decodedOk` decided `Good`'s content and was **never passed the grid**, so none of the
clauses below were checked and a `Good ∧ ¬Renderable` state was one byte away. The audit
recorded in SCRATCHPAD.md exhibited that from disk and refuted `resume_grid`'s conclusion at
it. `Vt.decodedRenderable` is the second stage of the door;
`Theorems/Checkpoint.lean`'s `load_renderable`/`load_tabsOk` state its guarantee for *any*
byte string, `Theorems/Vt.lean`'s `ofDecoded_none_of_rows_mismatch` states the refusal, and
these pin what the theorems do not: the byte offsets, and that the four sub-clauses are
independently reachable.

The control above still applies to all of them — a real checkpoint loads, so `isNone`
passing is not `load` having become unconditionally `none`. -/

/-- **The exhibited attack, at the byte level.** The `rows` byte of a real 4×2 checkpoint,
2 → 3. Every clause `decodedOk` checks still holds (`bot = 1 < 3`, cursor at the origin), the
grid's own length is a separate `rNat` further along the record, and the result was a screen
whose replay is not the screen it came from. Refused.

This is the fixture the audit's `#eval` produced `false` for on the pre-change decoder, so it
is the one to run first against any weakening of the guard. -/
example :
    (let c : Ckpt := { vt := Vt.init 4 2, cwd := "/tmp", labels := [("k", "v")] }
     let bytes := save c
     bytes[6]? == some 2                       -- the byte being patched IS `rows`
       && (load (bytes.set 6 3)).isNone) =
      true := by
  native_decide

/-- …and the same in the other direction, where the row count is *lower* than the grid's
length. `grid.size = rows` is an equation, not a bound: a record with rows to spare would
replay a screen with the surplus rows silently dropped. -/
example :
    (let v :=
        { Vt.init 4 3 with
          rows := 2, bot := 1 }
     (load (save { vt := v, cwd := "", labels := [] })).isNone) =
      true := by
  native_decide

/-- A row of the **wrong width** — the second sub-clause, and the one `rows` and `cols`
cannot catch between them, since `wRow` writes each row's length itself. -/
example :
    (let short : Row := blankRow 3 {}
     let v := { Vt.init 4 2 with grid := #[short, blankRow 4 {}] }
     (load (save { vt := v, cwd := "", labels := [] })).isNone) =
      true := by
  native_decide

/-- A **cell** the emitter cannot reproduce: base `'\x0A'` at width 7. `rCell` reads `base`
as any valid `Char`, `marks` as any list and `width` as any `Nat`, so this was accepted —
`Render.safeChar` would substitute U+FFFD on emit and the replayed screen would differ from
the one on disk. Both halves of `CellOk` are wrong here at once, which is the point: a
control codepoint *and* a width no `charWidth` returns. -/
example :
    (let bad : Row := (blankRow 4 {}).set! 0 { base := '\x0A', marks := [], width := 7, pen := {} }
     let v := { Vt.init 4 2 with grid := #[bad, blankRow 4 {}] }
     (load (save { vt := v, cwd := "", labels := [] })).isNone) =
      true := by
  native_decide

/-- A **half wide pair**: a width-2 base whose right neighbour is an ordinary blank. Half a
glyph is not expressible by `Render.rowAnsi` — the base re-wraps on replay and everything
after it lands a column off — which is why the live emulator ends every write in `Row.mend`
and why the door has to refuse what a file can still name. -/
example :
    (let bad : Row := (blankRow 4 {}).set! 1 { base := '中', marks := [], width := 2, pen := {} }
     let v := { Vt.init 4 2 with grid := #[bad, blankRow 4 {}] }
     (load (save { vt := v, cwd := "", labels := [] })).isNone) =
      true := by
  native_decide

/-- The **stashed alt screen**, whose grid was checked *nowhere* before this — `decodedOk`
looks at the stashed cursor and stops there. A session in the alt screen carries the main
screen in `altGrid`, and `Render.restore_grid_any_alt` paints it, so a bad one is the same
defect one indirection away. -/
example :
    (let v := { Vt.init 4 2 with altGrid := some (#[blankRow 4 {}], { x := 0, y := 0 }, {}) }
     (load (save { vt := v, cwd := "", labels := [] })).isNone) =
      true := by
  native_decide

/-- The **tab ruler**, the fourth sub-clause: `wVt` writes `tabs` as its own list, so a file
can name a ruler of any length. `Render.restore_tabs_any` needs it to be the width of the
screen (`Resume.resume_tabs_of_load` is what that buys), and `Renderable` does not carry it. -/
example :
    (let v := { Vt.init 4 2 with tabs := #[false, false] }
     (load (save { vt := v, cwd := "", labels := [] })).isNone) =
      true := by
  native_decide

/-- **The ring's rows are deliberately NOT checked**, and this fixture is that decision made
visible rather than a hole left implied. `Vt.resize` reinstalls the grid and the ruler at the
new width and leaves the scrollback rows at their old one, so a live session that has been
resized holds ring rows wider than `cols` — a legitimate checkpoint the door must accept.
The consequence is that `Render.restore_sb_exact`'s `hrok` stays unreachable from disk.

Fed 5 lines into a 10×2 screen and then resized to 6 wide: the ring rows are 10 wide, the
screen is 6, and the checkpoint loads. -/
example :
    (let v := ((Vt.init 10 2).feedBytes "1\r\n2\r\n3\r\n4\r\n5".toUTF8).resize 6 2
     match load (save { vt := v, cwd := "", labels := [] }) with
      | some ck' => ck'.vt.sb.toList.any (fun r => r.size != 6) && ck'.vt.colCount == 6
      | none => false) =
      true := by
  native_decide

end Linger.Core.Checkpoint.Tests
