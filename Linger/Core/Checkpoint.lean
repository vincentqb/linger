module

public import Linger.Core.Vt
-- A **permanent** friend import, and the one in the tree that needs its reason
-- written down. `specs/archive/vt-toolkit.md` Step 2 held it open for one step to remove
-- `rVt`'s forge; the forge is gone (`rVt` goes through `Vt.ofDecoded`, which validates)
-- and this line stayed. Two things it buys, and the difference between them is the
-- whole design decision:
--
-- * **`wVt`'s 17 field reads.** The seal blocks reads as well as writes. The
--   alternative was 15 new public accessors on `Vt` (13 fields have none; `cursorPos`
--   drops `pending` and `inAlt` drops the stashed screen, so neither serves the
--   codec) — 15 permanent public defs, 15 new claims for the zero-headroom coverage
--   ratchet, and read-hiding surrendered on 15 of 20 fields to buy nothing the
--   no-forge property needs. A `Vt` written *out* cannot create a bad one.
-- * **`Vt.ofDecoded`, which is `private`.** That is what makes this line the cheaper
--   trade rather than the lazier one: dropping the import would force the smart
--   constructor to be *public*, i.e. a second public door admitting any `Good` state,
--   unreachable ones included, for every module forever. The friend import confines
--   that power to this file, which is reviewed and grep-gated.
--
-- So: reads and one checked constructor, permanently. What must never come back is a
-- `Vt` structure literal here — `scripts/gates.sh` asserts `rVt` calls `Vt.ofDecoded`
-- and that no `Vt` field is assigned anywhere in this file. Do not copy the pattern
-- to a third module: `Render`/`Terminal` are friends because they *are* the emulator,
-- and this one is a friend because it is the emulator's only serialiser.
import all Linger.Core.Vt

public section

/-! # Linger.Core.Checkpoint — the reboot-resume codec

Serializes the resumable part of a session — screen, scrollback,
cursor, pen, modes, title, labels, and working directory — to bytes
and back. The parser state is reset on load.

§Restore (THEOREMS.md):
* The default `read* ∘ write*` round-trips **unconditionally** — every length is
  encoded as an arbitrary-precision little-endian `Nat`, so there is
  no "fits in u32" side condition anywhere.
* Readers are total by type: `R α = List UInt8 → Option (α × rest)`.
  Invalid encodings and shapes yield `none`; accepted records satisfy
  the decoder's invariants. Totality does not bound allocation or
  decoding time for arbitrary length and run-count fields. `rVt` bounds screen
  expansion using validated dimensions. History row widths remain unrestricted:
  a resize legitimately preserves rows wider than the current screen.

Format: `magic "LNGR" ++ version 1 ++ payload`. Bump the version on
any layout change; old daemons refuse newer files (load = none) and
start fresh — a checkpoint is a cache, not a contract.
-/

namespace Linger.Core.Checkpoint

open Linger.Core.Vt

/-- Readers: consume a prefix, return the value and the rest.

`abbrev`, not `def`: a type-level definition has to be visible across a `module`
boundary or the compiler cannot agree on the compiled representation of anything
typed by it ("locally inferred compilation type differs…"). This was a `def` with
`@[expose]`, which says the same thing in two more lines — an alias has no
implementation to hide, so reducible-and-exposed is simply what it is. -/
abbrev R (α : Type) : Type := List UInt8 → Option (α × List UInt8)

/-! ## Primitive writers/readers -/

/-- Arbitrary-precision Nat, LEB128: 7 bits per byte, high bit =
"more follows". Total in both directions and round-trips with no
side conditions — no "fits in u32" caveat anywhere in the format. -/
def wNat (n : Nat) : List UInt8 :=
  if h : n < 128 then [UInt8.ofNat n] else UInt8.ofNat (128 + n % 128) :: wNat (n / 128)
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/-- Inverse of `wNat` (`rt_nat`): reads bytes up to the first one below 128, and fails
if the input ends before it. -/
def rNat : R Nat := fun l =>
  match l with
  | [] => none
  | b :: rest =>
    if b < 128 then some (b.toNat, rest)
    else
      match rNat rest with
      | none => none
      | some (hi, rest') => some ((b.toNat - 128) + 128 * hi, rest')

/-- One byte: 1 for true, 0 for false. -/
def wBool (b : Bool) : List UInt8 := [if b then 1 else 0]

/-- Inverse of `wBool` (`rt_bool`): one byte, where any nonzero value reads as true. -/
def rBool : R Bool := fun l =>
  match l with
  | [] => none
  | b :: rest => some (b != 0, rest)

/-- A character as its codepoint, through `wNat`. -/
def wChar (c : Char) : List UInt8 := wNat c.toNat

/-- Inverse of `wChar` (`rt_char`); a number that is not a Unicode scalar value fails. -/
def rChar : R Char := fun l => do
  let (n, rest) ← rNat l
  if h : n.isValidChar then
    some (Char.ofNatAux n h, rest)
  else
    none

/-- A list as its length, then each element through `w`. -/
def wList {α : Type} (w : α → List UInt8) (l : List α) : List UInt8 := wNat l.length ++ l.flatMap w

/-- Read exactly the given number of elements with `r`, in order (`rt_listAux`). -/
def rListAux {α : Type} (r : R α) : Nat → R (List α)
  | 0 => fun l => some ([], l)
  | k + 1 => fun l => do
    let (x, rest) ← r l
    let (xs, rest') ← rListAux r k rest
    some (x :: xs, rest')

/-- Check an optional element-count limit before invoking the element reader.
The unbounded default keeps the format's general list roundtrip. -/
def rList {α : Type} (r : R α) (l : List UInt8) (maxCount : Option Nat := none) :
    Option (List α × List UInt8) := do
  let (n, rest) ← rNat l
  if maxCount.all (fun limit => n ≤ limit) then
    rListAux r n rest
  else
    none

/-- A string as its character count, then each character through `wChar`. -/
def wStr (s : String) : List UInt8 := wList wChar s.toList

/-- Inverse of `wStr` (`rt_str`). The character count is not bounded. -/
def rStr : R String := fun l => do
  let (cs, rest) ← rList rChar l
  some (String.ofList cs, rest)

/-- The first component's bytes, then the second's. -/
def wPair {α β : Type} (wa : α → List UInt8) (wb : β → List UInt8) (p : α × β) :
    List UInt8 := wa p.1 ++ wb p.2

/-- Inverse of `wPair` when each component reader inverts its writer (`rt_pair`). -/
def rPair {α β : Type} (ra : R α) (rb : R β) : R (α × β) := fun l => do
  let (a, rest) ← ra l
  let (b, rest') ← rb rest
  some ((a, b), rest')

/-- Tag 0 for `none`; tag 1, then the value. -/
def wOpt {α : Type} (w : α → List UInt8) : Option α → List UInt8
  | none => [0]
  | some a => 1 :: w a

/-- Inverse of `wOpt` (`rt_opt`); any other tag byte fails. -/
def rOpt {α : Type} (r : R α) : R (Option α) := fun l =>
  match l with
  | [] => none
  | 0 :: rest => some (none, rest)
  | 1 :: rest => do
    let (a, rest') ← r rest
    some (some a, rest')
  | _ => none

/-! ## Domain writers/readers -/

/-- Tag 0 for the default colour, tag 1 and the palette index, or tag 2 and the red,
green and blue bytes. -/
def wColor : Color → List UInt8
  | .default => [0]
  | .idx i => [1, i]
  | .rgb r g b => [2, r, g, b]

/-- Inverse of `wColor` (`rt_color`); an unknown tag or a missing byte fails. -/
def rColor : R Color := fun l =>
  match l with
  | 0 :: rest => some (.default, rest)
  | 1 :: i :: rest => some (.idx i, rest)
  | 2 :: r :: g :: b :: rest => some (.rgb r g b, rest)
  | _ => none

/-- Foreground, background, then the seven attribute flags in field order. -/
def wPen (p : Pen) : List UInt8 :=
  wColor p.fg ++ wColor p.bg ++ wBool p.bold ++ wBool p.dim ++ wBool p.italic ++
    wBool p.underline ++
    wBool p.blink ++
    wBool p.reverse ++
    wBool p.strike

/-- Inverse of `wPen` (`rt_pen`). -/
def rPen : R Pen := fun l => do
  let (fg, l) ← rColor l
  let (bg, l) ← rColor l
  let (bold, l) ← rBool l
  let (dim, l) ← rBool l
  let (italic, l) ← rBool l
  let (underline, l) ← rBool l
  let (blink, l) ← rBool l
  let (reverse, l) ← rBool l
  let (strike, l) ← rBool l
  some ({ fg, bg, bold, dim, italic, underline, blink, reverse, strike }, l)

/-- Base character, combining marks, width, then pen. -/
def wCell (c : Cell) : List UInt8 :=
  wChar c.base ++ wList wChar c.marks ++ wNat c.width ++ wPen c.pen

/-- Inverse of `wCell` (`rt_cell`). Any base, mark list and width are accepted here;
`Vt.ofDecoded` checks the cells of both screens. -/
def rCell : R Cell := fun l => do
  let (base, l) ← rChar l
  let (marks, l) ← rList rChar l
  let (width, l) ← rNat l
  let (pen, l) ← rPen l
  some ({ base, marks, width, pen }, l)

/-! ## Run-length encoding

A terminal row is mostly runs of identical cells — trailing blanks, or
stretches of same-styled text — so storing it cell-by-cell is ~30×
larger than it needs to be. `wRLE` collapses maximal equal runs to
`(count, cell)` pairs. Exact fidelity (no re-render approximation), and
the round-trip proof composes like any other combinator: see §Restore
`rt_rle`, which rests on `expand_runs`. -/

/-- Maximal runs of `DecidableEq`-equal elements, in order. -/
def runs {α : Type} [DecidableEq α] : List α → List (Nat × α)
  | [] => []
  | a :: t =>
    match runs t with
    | (n, b) :: rest => if a = b then (n + 1, b) :: rest else (1, a) :: (n, b) :: rest
    | [] => [(1, a)]

/-- Inverse of `runs`: expand each `(count, elem)` back to a flat list. -/
def expand {α : Type} : List (Nat × α) → List α
  | [] => []
  | (n, a) :: rest => List.replicate n a ++ expand rest

/-- A list as the number of its maximal runs (`runs`), then each run as a count and one
element. -/
def wRLE {α : Type} [DecidableEq α] (w : α → List UInt8) (l : List α) : List UInt8 :=
  wList (wPair wNat w) (runs l)

/-- Sum the encoded counts before expanding any run. Bounding each run separately
would still allow several small runs to exceed the row's width. Zero-length and
non-maximal runs remain accepted when their total fits. -/
def rRLE {α : Type} (r : R α) (bytes : List UInt8) (maxLength : Option Nat := none) :
    Option (List α × List UInt8) := do
  let (groups, rest) ← rList (rPair rNat r) bytes
  if maxLength.all (fun limit => (groups.map Prod.fst).sum ≤ limit) then
    some (expand groups, rest)
  else
    none

/-- A row's cells, run-length encoded. -/
def wRow (r : Row) : List UInt8 := wRLE wCell r.toList

/-- Inverse of `wRow` (`rt_row`). With `maxLength`, a row of more cells fails before any run
is expanded. -/
def rRow (l : List UInt8) (maxLength : Option Nat := none) : Option (Row × List UInt8) := do
  let (cs, l) ← rRLE rCell l maxLength
  some (cs.toArray, l)

/-- Column, row, then the wrap-pending flag. -/
def wCursor (c : Cursor) : List UInt8 := wNat c.x ++ wNat c.y ++ wBool c.pending

/-- Inverse of `wCursor` (`rt_cursor`). The position is not checked here; `Vt.ofDecoded`
bounds it by the screen. -/
def rCursor : R Cursor := fun l => do
  let (x, l) ← rNat l
  let (y, l) ← rNat l
  let (pending, l) ← rBool l
  some ({ x, y, pending }, l)

/-- Every mode in field order: a flag each, and the mouse mode number through `wNat`. -/
def wModes (m : Modes) : List UInt8 :=
  wBool m.wrap ++ wBool m.origin ++ wBool m.insert ++ wBool m.cursorVisible ++ wBool m.appCursor ++
    wBool m.appKeypad ++
    wBool m.bracketedPaste ++
    wNat m.mouse ++
    wBool m.mouseSgr ++
    wBool m.focusEvents

/-- Inverse of `wModes` (`rt_modes`). -/
def rModes : R Modes := fun l => do
  let (wrap, l) ← rBool l
  let (origin, l) ← rBool l
  let (insert, l) ← rBool l
  let (cursorVisible, l) ← rBool l
  let (appCursor, l) ← rBool l
  let (appKeypad, l) ← rBool l
  let (bracketedPaste, l) ← rBool l
  let (mouse, l) ← rNat l
  let (mouseSgr, l) ← rBool l
  let (focusEvents, l) ← rBool l
  some
      ({ wrap, origin, insert, cursorVisible, appCursor, appKeypad,
          bracketedPaste, mouse, mouseSgr, focusEvents },
        l)

/-- The saved cursor, then the saved pen. -/
def wSaved (s : Saved) : List UInt8 := wCursor s.cur ++ wPen s.pen

/-- Inverse of `wSaved` (`rt_saved`). -/
def rSaved : R Saved := fun l => do
  let (cur, l) ← rCursor l
  let (pen, l) ← rPen l
  some ({ cur, pen }, l)

/-- The ring's start index, then its rows in storage order rather than oldest first. -/
def wRing (r : Ring) : List UInt8 :=
  -- verbatim geometry (data + start) so the round-trip is exact
  wNat r.start ++ wList wRow r.data.toList

/-- Inverse of `wRing` (`rt_ring`). With `maxRows`, a larger row count fails before any row
is read; row widths are not bounded. -/
def rRing (l : List UInt8) (maxRows : Option Nat := none) : Option (Ring × List UInt8) := do
  let (start, l) ← rNat l
  let (rows, l) ← rList rRow l maxRows
  some ({ data := rows.toArray, start }, l)

/-- The stashed main screen, if any, behind a `wOpt` tag: its rows, cursor and pen. -/
def wAlt : Option (Array Row × Cursor × Pen) → List UInt8 :=
  wOpt (fun (g, c, p) => wList wRow g.toList ++ wCursor c ++ wPen p)

/-- Inverse of `wAlt` (`rt_alt`). `maxRows` bounds the stash's row count before any row is
read, and `maxCols` each row's cells before that row is expanded. -/
def rAlt (l : List UInt8) (maxCols : Option Nat := none) (maxRows : Option Nat := none) :
    Option (Option (Array Row × Cursor × Pen) × List UInt8) :=
  rOpt
    (fun l => do
      let (rows, l) ← rList (fun bytes => rRow bytes maxCols) l maxRows
      let (c, l) ← rCursor l
      let (p, l) ← rPen l
      some ((rows.toArray, c, p), l))
    l

/-- The parser state is deliberately not persisted. A poll boundary can bisect
an escape sequence or a UTF-8 character; loading discards that partial parser
state while retaining the screen and modes. This is a format choice, separate
from the runtime's atomic file replacement. -/
def wVt (v : Vt) : List UInt8 :=
  wNat v.cols ++ wNat v.rows ++ wList wRow v.grid.toList ++ wCursor v.cursor ++ wPen v.pen ++
    wModes v.modes ++
    wNat v.top ++
    wNat v.bot ++
    wList wBool v.tabs.toList ++
    wRing v.sb ++
    wAlt v.altGrid ++
    wSaved v.saved ++
    wStr v.title ++
    wBool v.g0Line ++
    wBool v.g1Line ++
    wBool v.shiftOut ++
    wBool v.bell

/-- **The decoder, and no longer a forge.** It used to build a `Vt` field-by-field
out of decoded bytes, which is exactly how a corrupt or hostile on-disk record would
hand the emulator `cols := 0` — a state no `Vt.init`/`resize`/`feed` path can produce.
Nothing validated: `rNat` accepts whatever the file says.

Dimensions must already be in the live range before reading any rows. Both screen
grids use those dimensions to bound row counts and the sum of encoded cell runs
before expansion; the tab ruler and history row count are bounded too. The final
`Vt.ofDecoded` (`Linger/Core/Vt.lean`) check still owns exact shapes and cell validity.
History row widths are not bounded by the current columns: resize keeps their old
widths, and the existing decoder contract accepts unrestricted history rows.

`Vt.ofDecoded` is `private`, reached through this module's friend import — which is
therefore **permanent, and for reads plus that one checked door**. What must not come
back is the structure literal; `scripts/gates.sh` greps for it in both directions (the
positive check that this function calls `ofDecoded`, and the negative one that no
`Vt` field is assigned anywhere in this file). Same species of oracle as `SHIM_CAP`:
evadeable by deliberately writing something new, not by reverting a fix. -/
def rVt : R Vt := fun l => do
  let (cols, l) ← rNat l
  let (rows, l) ← rNat l
  if cols != clampDim cols || rows != clampDim rows then
    none
  else
    do
      let (grid, l) ← rList (fun bytes => rRow bytes (some cols)) l (some rows)
      let (cursor, l) ← rCursor l
      let (pen, l) ← rPen l
      let (modes, l) ← rModes l
      let (top, l) ← rNat l
      let (bot, l) ← rNat l
      let (tabs, l) ← rList rBool l (some cols)
      let (sb, l) ← rRing l (some sbCap)
      let (altGrid, l) ← rAlt l (some cols) (some rows)
      let (saved, l) ← rSaved l
      let (title, l) ← rStr l
      let (g0Line, l) ← rBool l
      let (g1Line, l) ← rBool l
      let (shiftOut, l) ← rBool l
      let (bell, l) ← rBool l
      let v ←
        Vt.ofDecoded cols rows grid.toArray cursor pen modes top bot tabs.toArray sb altGrid saved
            title g0Line g1Line shiftOut bell
      some (v, l)

/-! ## The checkpoint record -/

/-- **No `deriving Inhabited`**, and that is deliberate (`specs/archive/vt-toolkit.md` Step 3):
it would need `Inhabited Vt`, which is the third public door out of the `Vt` seal — a
`cols = 0` screen any importer could name as `default` with no friend import. Nothing in
the tree used either instance. If a canonical checkpoint is ever wanted, write it out
(`⟨Vt.init 80 24, "", []⟩`) rather than deriving one: a default that is a *choice* cannot
silently become a state the emulator can't reach. -/
structure Ckpt where
  /-- The terminal state; its parser state is not saved. -/
  vt : Vt
  /-- The directory the restored session's child starts in. -/
  cwd : String
  /-- The session's labels, as key/value pairs. -/
  labels : List (String × String)

/-- On-disk magic: `"LNGR"` and the format version. What `save` writes. -/
def magic : List UInt8 := [0x4C, 0x4E, 0x47, 0x52, 1] -- "LNGR" v1

/-- The checkpoint record: `magic`, then the terminal, the working directory and the labels.
Loading the record of a live state returns it with its parser quiesced (`load_save_live`). -/
def save (c : Ckpt) : List UInt8 :=
  magic ++ wVt c.vt ++ wStr c.cwd ++ wList (wPair wStr wStr) c.labels

/-- Strip the format tag. A **named stage** rather than the check inlined in `load`,
and it stays one even though there is now only a single tag to check: with the decision
inline, `load_save`'s round-trip proof carries it through the whole parser chain and
times out at two million heartbeats, where naming it gives the round trip one rewrite
(`stripMagic_magic`) and needs no raise at all. Measured both ways — the AGENTS.md
"restructure for provability" rule, on the smallest possible thing. -/
def stripMagic (l : List UInt8) : Option (List UInt8) := magic.isPrefixOf? l

/-- Total: any byte list either parses fully or is `none`. Trailing
garbage is rejected (a torn write is not a checkpoint). -/
def load (l : List UInt8) : Option Ckpt := do
  let rest ← stripMagic l
  let (vt, rest) ← rVt rest
  let (cwd, rest) ← rStr rest
  let (labels, rest) ← rList (rPair rStr rStr) rest
  if rest.isEmpty then
    some { vt, cwd, labels }
  else
    none

/-! ## Writing into a byte array

`save` is the specification: the round-trip proofs read its list one byte at a time.
Evaluated, that list costs a heap cell per byte, and a full 200-column history peaks near a
gigabyte. `saveBytes` writes the same record into one `ByteArray`. Each accumulator writer
mirrors the list writer of the same shape (`natB` is `wNat`; `rowB` is `wRow` over the same
`runs`), so no screen row becomes a list of bytes; the short fields between the screens keep
their list writers. `saveBytes_eq` proves the bytes equal `save`'s, so the format and its
theorems are unchanged. -/

/-- `wNat` into an accumulator (`natB_appends`). -/
def natB (acc : ByteArray) (n : Nat) : ByteArray :=
  if h : n < 128 then acc.push (UInt8.ofNat n)
  else natB (acc.push (UInt8.ofNat (128 + n % 128))) (n / 128)
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/-- `wBool` into an accumulator (`boolB_appends`). -/
def boolB (acc : ByteArray) (b : Bool) : ByteArray := acc.push (if b then 1 else 0)

/-- `wChar` into an accumulator (`charB_appends`). -/
def charB (acc : ByteArray) (c : Char) : ByteArray := natB acc c.toNat

/-- `wList` into an accumulator. `listB` and `rleB` are specialized at each element writer:
on a full 200-column history that took `saveBytes` from 282 to 237 ms. -/
@[specialize]
def listB {α : Type} (f : ByteArray → α → ByteArray) (acc : ByteArray) (l : List α) :
    ByteArray := l.foldl f (natB acc l.length)

/-- `wColor` into an accumulator (`colorB_appends`). -/
def colorB (acc : ByteArray) : Color → ByteArray
  | .default => acc.push 0
  | .idx i => (acc.push 1).push i
  | .rgb r g b => (((acc.push 2).push r).push g).push b

/-- `wPen` into an accumulator (`penB_appends`). -/
def penB (acc : ByteArray) (p : Pen) : ByteArray :=
  let acc := colorB (colorB acc p.fg) p.bg
  let acc := boolB (boolB (boolB (boolB acc p.bold) p.dim) p.italic) p.underline
  boolB (boolB (boolB acc p.blink) p.reverse) p.strike

/-- `wCell` into an accumulator (`cellB_appends`). -/
def cellB (acc : ByteArray) (c : Cell) : ByteArray :=
  penB (natB (listB charB (charB acc c.base) c.marks) c.width) c.pen

/-- `wRLE` into an accumulator (`rleB_appends`). -/
@[specialize]
def rleB {α : Type} [DecidableEq α] (f : ByteArray → α → ByteArray) (acc : ByteArray) (l : List α) :
    ByteArray := listB (fun acc (n, a) => f (natB acc n) a) acc (runs l)

/-- `wRow` into an accumulator (`rowB_appends`). -/
def rowB (acc : ByteArray) (r : Row) : ByteArray := rleB cellB acc r.toList

/-- `save`, written into a byte array (`saveBytes_eq`). Every screen row, including the
stashed alternate screen's, goes through `rowB`. -/
def saveBytes (c : Ckpt) : ByteArray :=
  let v := c.vt
  let acc := (magic ++ wNat v.cols ++ wNat v.rows).toByteArray
  let acc := listB rowB acc v.grid.toList
  let acc :=
    acc ++
      (wCursor v.cursor ++ wPen v.pen ++ wModes v.modes ++ wNat v.top ++ wNat v.bot ++
          wList wBool v.tabs.toList ++
          wNat v.sb.start).toByteArray
  let acc := listB rowB acc v.sb.data.toList
  let acc :=
    match v.altGrid with
    | none => acc.push 0
    | some (screen, cursor, pen) =>
      listB rowB (acc.push 1) screen.toList ++ (wCursor cursor ++ wPen pen).toByteArray
  acc ++
    (wSaved v.saved ++ wStr v.title ++ wBool v.g0Line ++ wBool v.g1Line ++ wBool v.shiftOut ++
        wBool v.bell ++
        wStr c.cwd ++
        wList (wPair wStr wStr) c.labels).toByteArray

/-! ## Reading from a byte array

`load` is the specification and reads a list. Evaluated, converting a file's bytes to that
list costs a heap cell per byte, about 18 million for a full 200-column history. `loadBytes`
reads the same record in place: each reader below mirrors the list reader of the same shape,
consuming bytes from a position and returning the value with the next position. The count,
run and dimension limits are checked at the same points as the list readers check them,
before any element is decoded or any run expanded. `loadBytes_eq` proves that `loadBytes`
returns what `load` returns on the array's bytes, so every theorem about `load` holds of it. -/

/-- Readers over a byte array: decode from a position, returning the value and the position
after it. -/
abbrev RB (α : Type) : Type := ByteArray → Nat → Option (α × Nat)

/-- `rNat` at a position, for an encoding of any length. -/
def rNatLongB (b : ByteArray) (i : Nat) : Option (Nat × Nat) :=
  if h : i < b.size then
    if b[i] < 128 then some (b[i].toNat, i + 1)
    else
      match rNatLongB b (i + 1) with
      | none => none
      | some (hi, j) => some ((b[i].toNat - 128) + 128 * hi, j)
  else none
termination_by b.size - i

/-- `rNatLongB` unrolled once and inlined at every call. Most counts, codepoints and widths
are one byte, so they decode at the call site; only a longer encoding calls `rNatLongB`. -/
@[inline]
def rNatB (b : ByteArray) (i : Nat) : Option (Nat × Nat) :=
  if h : i < b.size then
    if b[i] < 128 then some (b[i].toNat, i + 1)
    else
      match rNatLongB b (i + 1) with
      | none => none
      | some (hi, j) => some ((b[i].toNat - 128) + 128 * hi, j)
  else none

/-- `rBool` at a position. -/
@[inline]
def rBoolB : RB Bool := fun b i => if h : i < b.size then some (b[i] != 0, i + 1) else none

/-- `rChar` at a position. -/
@[inline]
def rCharB : RB Char := fun b i => do
  let (n, i) ← rNatB b i
  if h : n.isValidChar then
    some (Char.ofNatAux n h, i)
  else
    none

/-- `rListAux` at a position. -/
@[specialize]
def rListAuxB {α : Type} (r : RB α) : Nat → RB (List α)
  | 0 => fun _ i => some ([], i)
  | k + 1 => fun b i => do
    let (x, i) ← r b i
    let (xs, i) ← rListAuxB r k b i
    some (x :: xs, i)

/-- `rList` at a position, checking the same optional count limit before reading any element. -/
@[specialize]
def rListB {α : Type} (r : RB α) (b : ByteArray) (i : Nat) (maxCount : Option Nat := none) :
    Option (List α × Nat) := do
  let (n, j) ← rNatB b i
  if maxCount.all (fun limit => n ≤ limit) then
    rListAuxB r n b j
  else
    none

/-- `rStr` at a position. -/
def rStrB : RB String := fun b i => do
  let (cs, i) ← rListB rCharB b i
  some (String.ofList cs, i)

/-- `rPair` at a position. -/
@[specialize]
def rPairB {α β : Type} (ra : RB α) (rb : RB β) : RB (α × β) := fun b i => do
  let (a, i) ← ra b i
  let (c, i) ← rb b i
  some ((a, c), i)

/-- `rOpt` at a position. -/
@[specialize]
def rOptB {α : Type} (r : RB α) : RB (Option α) := fun b i =>
  if h : i < b.size then
    if b[i] = 0 then some (none, i + 1)
    else
      if b[i] = 1 then do
        let (a, j) ← r b (i + 1)
        some (some a, j)
      else none
  else none

/-- `rColor` at a position. -/
@[inline]
def rColorB : RB Color := fun b i =>
  if h : i < b.size then
    if b[i] = 0 then some (.default, i + 1)
    else
      if b[i] = 1 then if h1 : i + 1 < b.size then some (.idx b[i + 1], i + 2) else none
      else
        if b[i] = 2 then
          if h3 : i + 3 < b.size then some (.rgb b[i + 1] b[i + 2] b[i + 3], i + 4) else none
        else none
  else none

/-- `rPen` at a position. -/
def rPenB : RB Pen := fun b i => do
  let (fg, i) ← rColorB b i
  let (bg, i) ← rColorB b i
  let (bold, i) ← rBoolB b i
  let (dim, i) ← rBoolB b i
  let (italic, i) ← rBoolB b i
  let (underline, i) ← rBoolB b i
  let (blink, i) ← rBoolB b i
  let (reverse, i) ← rBoolB b i
  let (strike, i) ← rBoolB b i
  some ({ fg, bg, bold, dim, italic, underline, blink, reverse, strike }, i)

/-- `rCell` at a position. -/
def rCellB : RB Cell := fun b i => do
  let (base, i) ← rCharB b i
  let (marks, i) ← rListB rCharB b i
  let (width, i) ← rNatB b i
  let (pen, i) ← rPenB b i
  some ({ base, marks, width, pen }, i)

/-- `acc` with the given number of copies of `a` pushed onto it. -/
def pushRun {α : Type} (acc : Array α) (a : α) : Nat → Array α
  | 0 => acc
  | n + 1 => pushRun (acc.push a) a n

/-- `expand`, pushed onto an array. -/
def expandB {α : Type} (acc : Array α) : List (Nat × α) → Array α
  | [] => acc
  | (n, a) :: rest => expandB (pushRun acc a n) rest

/-- `rRLE` at a position, summing the run counts before expanding any run. The runs expand
straight into an array sized to their total: the row `rRow` builds from `rRLE`'s list, without
building the list. -/
@[specialize]
def rRLEB {α : Type} (r : RB α) (b : ByteArray) (i : Nat) (maxLength : Option Nat := none) :
    Option (Array α × Nat) := do
  let (groups, j) ← rListB (rPairB rNatB r) b i
  let total := groups.foldl (fun n g => n + g.1) 0
  if maxLength.all (fun limit => total ≤ limit) then
    some (expandB (Array.emptyWithCapacity total) groups, j)
  else
    none

/-- `rRow` at a position. -/
def rRowB (b : ByteArray) (i : Nat) (maxLength : Option Nat := none) : Option (Row × Nat) :=
  rRLEB rCellB b i maxLength

/-- `rCursor` at a position. -/
def rCursorB : RB Cursor := fun b i => do
  let (x, i) ← rNatB b i
  let (y, i) ← rNatB b i
  let (pending, i) ← rBoolB b i
  some ({ x, y, pending }, i)

/-- `rModes` at a position. -/
def rModesB : RB Modes := fun b i => do
  let (wrap, i) ← rBoolB b i
  let (origin, i) ← rBoolB b i
  let (insert, i) ← rBoolB b i
  let (cursorVisible, i) ← rBoolB b i
  let (appCursor, i) ← rBoolB b i
  let (appKeypad, i) ← rBoolB b i
  let (bracketedPaste, i) ← rBoolB b i
  let (mouse, i) ← rNatB b i
  let (mouseSgr, i) ← rBoolB b i
  let (focusEvents, i) ← rBoolB b i
  some
      ({ wrap, origin, insert, cursorVisible, appCursor, appKeypad,
          bracketedPaste, mouse, mouseSgr, focusEvents },
        i)

/-- `rSaved` at a position. -/
def rSavedB : RB Saved := fun b i => do
  let (cur, i) ← rCursorB b i
  let (pen, i) ← rPenB b i
  some ({ cur, pen }, i)

/-- `rRing` at a position. -/
def rRingB (b : ByteArray) (i : Nat) (maxRows : Option Nat := none) : Option (Ring × Nat) := do
  let (start, j) ← rNatB b i
  let (rows, j) ← rListB rRowB b j maxRows
  some ({ data := rows.toArray, start }, j)

/-- `rAlt` at a position. -/
def rAltB (b : ByteArray) (i : Nat) (maxCols : Option Nat := none) (maxRows : Option Nat := none) :
    Option (Option (Array Row × Cursor × Pen) × Nat) :=
  rOptB
    (fun bytes j => do
      let (rows, j) ← rListB (fun bytes j => rRowB bytes j maxCols) bytes j maxRows
      let (c, j) ← rCursorB bytes j
      let (p, j) ← rPenB bytes j
      some ((rows.toArray, c, p), j))
    b i

/-- `rVt` at a position: the same dimension check before reading any row, the same bounds on
both screens, the tab ruler and the history, and the same checked constructor. -/
def rVtB : RB Vt := fun b i => do
  let (cols, i) ← rNatB b i
  let (rows, i) ← rNatB b i
  if cols != clampDim cols || rows != clampDim rows then
    none
  else
    do
      let (grid, i) ← rListB (fun bytes j => rRowB bytes j (some cols)) b i (some rows)
      let (cursor, i) ← rCursorB b i
      let (pen, i) ← rPenB b i
      let (modes, i) ← rModesB b i
      let (top, i) ← rNatB b i
      let (bot, i) ← rNatB b i
      let (tabs, i) ← rListB rBoolB b i (some cols)
      let (sb, i) ← rRingB b i (some sbCap)
      let (altGrid, i) ← rAltB b i (some cols) (some rows)
      let (saved, i) ← rSavedB b i
      let (title, i) ← rStrB b i
      let (g0Line, i) ← rBoolB b i
      let (g1Line, i) ← rBoolB b i
      let (shiftOut, i) ← rBoolB b i
      let (bell, i) ← rBoolB b i
      let v ←
        Vt.ofDecoded cols rows grid.toArray cursor pen modes top bot tabs.toArray sb altGrid saved
            title g0Line g1Line shiftOut bell
      some (v, i)

/-- `List.isPrefixOf?` at a position: when the array's bytes from the given position start
with the given list, the position just past it. -/
def prefixB : List UInt8 → ByteArray → Nat → Option Nat
  | [], _, i => some i
  | x :: p, b, i => if h : i < b.size then if x == b[i] then prefixB p b (i + 1) else none else none

/-- `load` on a byte array (`loadBytes_eq`): the same tag check, the same reader chain, and
the same refusal of unread trailing bytes. -/
def loadBytes (b : ByteArray) : Option Ckpt := do
  let i ← prefixB magic b 0
  let (vt, i) ← rVtB b i
  let (cwd, i) ← rStrB b i
  let (labels, i) ← rListB (rPairB rStrB rStrB) b i
  if b.size ≤ i then
    some { vt, cwd, labels }
  else
    none

end Linger.Core.Checkpoint
