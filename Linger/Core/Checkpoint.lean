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

def rNat : R Nat := fun l =>
  match l with
  | [] => none
  | b :: rest =>
    if b < 128 then some (b.toNat, rest)
    else
      match rNat rest with
      | none => none
      | some (hi, rest') => some ((b.toNat - 128) + 128 * hi, rest')

def wBool (b : Bool) : List UInt8 := [if b then 1 else 0]

def rBool : R Bool := fun l =>
  match l with
  | [] => none
  | b :: rest => some (b != 0, rest)

def wChar (c : Char) : List UInt8 := wNat c.toNat

def rChar : R Char := fun l => do
  let (n, rest) ← rNat l
  if h : n.isValidChar then
    some (Char.ofNatAux n h, rest)
  else
    none

def wList {α : Type} (w : α → List UInt8) (l : List α) : List UInt8 := wNat l.length ++ l.flatMap w

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

def wStr (s : String) : List UInt8 := wList wChar s.toList

def rStr : R String := fun l => do
  let (cs, rest) ← rList rChar l
  some (String.ofList cs, rest)

def wPair {α β : Type} (wa : α → List UInt8) (wb : β → List UInt8) (p : α × β) :
    List UInt8 := wa p.1 ++ wb p.2

def rPair {α β : Type} (ra : R α) (rb : R β) : R (α × β) := fun l => do
  let (a, rest) ← ra l
  let (b, rest') ← rb rest
  some ((a, b), rest')

def wOpt {α : Type} (w : α → List UInt8) : Option α → List UInt8
  | none => [0]
  | some a => 1 :: w a

def rOpt {α : Type} (r : R α) : R (Option α) := fun l =>
  match l with
  | [] => none
  | 0 :: rest => some (none, rest)
  | 1 :: rest => do
    let (a, rest') ← r rest
    some (some a, rest')
  | _ => none

/-! ## Domain writers/readers -/

def wColor : Color → List UInt8
  | .default => [0]
  | .idx i => [1, i]
  | .rgb r g b => [2, r, g, b]

def rColor : R Color := fun l =>
  match l with
  | 0 :: rest => some (.default, rest)
  | 1 :: i :: rest => some (.idx i, rest)
  | 2 :: r :: g :: b :: rest => some (.rgb r g b, rest)
  | _ => none

def wPen (p : Pen) : List UInt8 :=
  wColor p.fg ++ wColor p.bg ++ wBool p.bold ++ wBool p.dim ++ wBool p.italic ++
    wBool p.underline ++
    wBool p.blink ++
    wBool p.reverse ++
    wBool p.strike

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

def wCell (c : Cell) : List UInt8 :=
  wChar c.base ++ wList wChar c.marks ++ wNat c.width ++ wPen c.pen

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

def wRow (r : Row) : List UInt8 := wRLE wCell r.toList

def rRow (l : List UInt8) (maxLength : Option Nat := none) : Option (Row × List UInt8) := do
  let (cs, l) ← rRLE rCell l maxLength
  some (cs.toArray, l)

def wCursor (c : Cursor) : List UInt8 := wNat c.x ++ wNat c.y ++ wBool c.pending

def rCursor : R Cursor := fun l => do
  let (x, l) ← rNat l
  let (y, l) ← rNat l
  let (pending, l) ← rBool l
  some ({ x, y, pending }, l)

def wModes (m : Modes) : List UInt8 :=
  wBool m.wrap ++ wBool m.origin ++ wBool m.insert ++ wBool m.cursorVisible ++ wBool m.appCursor ++
    wBool m.appKeypad ++
    wBool m.bracketedPaste ++
    wNat m.mouse ++
    wBool m.mouseSgr ++
    wBool m.focusEvents

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

def wSaved (s : Saved) : List UInt8 := wCursor s.cur ++ wPen s.pen

def rSaved : R Saved := fun l => do
  let (cur, l) ← rCursor l
  let (pen, l) ← rPen l
  some ({ cur, pen }, l)

def wRing (r : Ring) : List UInt8 :=
  -- verbatim geometry (data + start) so the round-trip is exact
  wNat r.start ++ wList wRow r.data.toList

def rRing (l : List UInt8) (maxRows : Option Nat := none) : Option (Ring × List UInt8) := do
  let (start, l) ← rNat l
  let (rows, l) ← rList rRow l maxRows
  some ({ data := rows.toArray, start }, l)

def wAlt : Option (Array Row × Cursor × Pen) → List UInt8 :=
  wOpt (fun (g, c, p) => wList wRow g.toList ++ wCursor c ++ wPen p)

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
  vt : Vt
  cwd : String
  labels : List (String × String)

/-- On-disk magic: `"LNGR"` and the format version. What `save` writes. -/
def magic : List UInt8 := [0x4C, 0x4E, 0x47, 0x52, 1] -- "LNGR" v1

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

def natB (acc : ByteArray) (n : Nat) : ByteArray :=
  if h : n < 128 then acc.push (UInt8.ofNat n)
  else natB (acc.push (UInt8.ofNat (128 + n % 128))) (n / 128)
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

def boolB (acc : ByteArray) (b : Bool) : ByteArray := acc.push (if b then 1 else 0)

def charB (acc : ByteArray) (c : Char) : ByteArray := natB acc c.toNat

/-- `wList` into an accumulator. `listB` and `rleB` are specialized at each element writer:
on a full 200-column history that took `saveBytes` from 282 to 237 ms. -/
@[specialize]
def listB {α : Type} (f : ByteArray → α → ByteArray) (acc : ByteArray) (l : List α) :
    ByteArray := l.foldl f (natB acc l.length)

def colorB (acc : ByteArray) : Color → ByteArray
  | .default => acc.push 0
  | .idx i => (acc.push 1).push i
  | .rgb r g b => (((acc.push 2).push r).push g).push b

def penB (acc : ByteArray) (p : Pen) : ByteArray :=
  let acc := colorB (colorB acc p.fg) p.bg
  let acc := boolB (boolB (boolB (boolB acc p.bold) p.dim) p.italic) p.underline
  boolB (boolB (boolB acc p.blink) p.reverse) p.strike

def cellB (acc : ByteArray) (c : Cell) : ByteArray :=
  penB (natB (listB charB (charB acc c.base) c.marks) c.width) c.pen

@[specialize]
def rleB {α : Type} [DecidableEq α] (f : ByteArray → α → ByteArray) (acc : ByteArray) (l : List α) :
    ByteArray := listB (fun acc (n, a) => f (natB acc n) a) acc (runs l)

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

end Linger.Core.Checkpoint
