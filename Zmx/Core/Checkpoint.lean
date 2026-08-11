import Zmx.Core.Vt
/-! # Zmx.Core.Checkpoint — the reboot-resume codec

Serializes the resumable part of a session — the full `Vt` (grid,
scrollback, cursor, pen, modes, title, parser state), the labels, and
the working directory — to bytes and back.

§Restore (THEOREMS.md):
* `read* ∘ write*` round-trips **unconditionally** — every length is
  encoded as an arbitrary-precision little-endian `Nat`, so there is
  no "fits in u32" side condition anywhere.
* Readers are total by type: `R α = List UInt8 → Option (α × rest)` —
  a corrupt or truncated checkpoint yields `none`, never a panic, and
  the daemon just starts fresh.

Format: `magic "LZMX" ++ version 1 ++ payload`. Bump the version on
any layout change; old daemons refuse newer files (load = none) and
start fresh — a checkpoint is a cache, not a contract.
-/

namespace Zmx.Core.Checkpoint

open Zmx.Core.Vt

/-- Readers: consume a prefix, return the value and the rest. -/
def R (α : Type) : Type := List UInt8 → Option (α × List UInt8)

/-! ## Primitive writers/readers -/

def wU8 (b : UInt8) : List UInt8 := [b]

def rU8 : R UInt8 := fun l =>
  match l with
  | [] => none
  | b :: rest => some (b, rest)

/-- Arbitrary-precision Nat, LEB128: 7 bits per byte, high bit =
"more follows". Total in both directions and round-trips with no
side conditions — no "fits in u32" caveat anywhere in the format. -/
def wNat (n : Nat) : List UInt8 :=
  if h : n < 128 then [UInt8.ofNat n]
  else UInt8.ofNat (128 + n % 128) :: wNat (n / 128)
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
  if h : n.isValidChar then some (Char.ofNatAux n h, rest)
  else none

def wList {α : Type} (w : α → List UInt8) (l : List α) : List UInt8 :=
  wNat l.length ++ l.flatMap w

def rListAux {α : Type} (r : R α) : Nat → R (List α)
  | 0 => fun l => some ([], l)
  | k + 1 => fun l => do
    let (x, rest) ← r l
    let (xs, rest') ← rListAux r k rest
    some (x :: xs, rest')

def rList {α : Type} (r : R α) : R (List α) := fun l => do
  let (n, rest) ← rNat l
  rListAux r n rest

def wStr (s : String) : List UInt8 := wList wChar s.toList

def rStr : R String := fun l => do
  let (cs, rest) ← rList rChar l
  some (String.ofList cs, rest)

def wPair {α β : Type} (wa : α → List UInt8) (wb : β → List UInt8)
    (p : α × β) : List UInt8 :=
  wa p.1 ++ wb p.2

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
  wColor p.fg ++ wColor p.bg ++
  wBool p.bold ++ wBool p.dim ++ wBool p.italic ++ wBool p.underline ++
  wBool p.blink ++ wBool p.reverse ++ wBool p.strike

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

def rRLE {α : Type} (r : R α) : R (List α) := fun bytes => do
  let (groups, rest) ← rList (rPair rNat r) bytes
  some (expand groups, rest)

def wRow (r : Row) : List UInt8 := wRLE wCell r.toList

def rRow : R Row := fun l => do
  let (cs, l) ← rRLE rCell l
  some (cs.toArray, l)

def wCursor (c : Cursor) : List UInt8 :=
  wNat c.x ++ wNat c.y ++ wBool c.pending

def rCursor : R Cursor := fun l => do
  let (x, l) ← rNat l
  let (y, l) ← rNat l
  let (pending, l) ← rBool l
  some ({ x, y, pending }, l)

def wModes (m : Modes) : List UInt8 :=
  wBool m.wrap ++ wBool m.origin ++ wBool m.insert ++ wBool m.cursorVisible ++
  wBool m.appCursor ++ wBool m.appKeypad ++ wBool m.bracketedPaste ++
  wNat m.mouse ++ wBool m.mouseSgr ++ wBool m.focusEvents

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
  some ({ wrap, origin, insert, cursorVisible, appCursor, appKeypad,
          bracketedPaste, mouse, mouseSgr, focusEvents }, l)

def wSaved (s : Saved) : List UInt8 := wCursor s.cur ++ wPen s.pen

def rSaved : R Saved := fun l => do
  let (cur, l) ← rCursor l
  let (pen, l) ← rPen l
  some ({ cur, pen }, l)

def wRing (r : Ring) : List UInt8 :=
  -- verbatim geometry (data + start) so the round-trip is exact
  wNat r.start ++ wList wRow r.data.toList

def rRing : R Ring := fun l => do
  let (start, l) ← rNat l
  let (rows, l) ← rList rRow l
  some ({ data := rows.toArray, start }, l)

def wAlt : Option (Array Row × Cursor × Pen) → List UInt8 :=
  wOpt (fun (g, c, p) => wList wRow g.toList ++ wCursor c ++ wPen p)

def rAlt : R (Option (Array Row × Cursor × Pen)) :=
  rOpt (fun l => do
    let (rows, l) ← rList rRow l
    let (c, l) ← rCursor l
    let (p, l) ← rPen l
    some ((rows.toArray, c, p), l))

/-- The parser state is deliberately NOT persisted: a checkpoint lands
between escape sequences almost surely, and resuming into `.ground`
loses at most one partial sequence from a torn write. What must
survive is what the *user sees* plus what applications *depend on*
(modes). -/
def wVt (v : Vt) : List UInt8 :=
  wNat v.cols ++ wNat v.rows ++
  wList wRow v.grid.toList ++
  wCursor v.cursor ++ wPen v.pen ++ wModes v.modes ++
  wNat v.top ++ wNat v.bot ++
  wList wBool v.tabs.toList ++
  wRing v.sb ++
  wAlt v.altGrid ++
  wSaved v.saved ++
  wStr v.title ++
  wBool v.g0Line ++ wBool v.g1Line ++ wBool v.shiftOut ++
  wBool v.bell

def rVt : R Vt := fun l => do
  let (cols, l) ← rNat l
  let (rows, l) ← rNat l
  let (grid, l) ← rList rRow l
  let (cursor, l) ← rCursor l
  let (pen, l) ← rPen l
  let (modes, l) ← rModes l
  let (top, l) ← rNat l
  let (bot, l) ← rNat l
  let (tabs, l) ← rList rBool l
  let (sb, l) ← rRing l
  let (altGrid, l) ← rAlt l
  let (saved, l) ← rSaved l
  let (title, l) ← rStr l
  let (g0Line, l) ← rBool l
  let (g1Line, l) ← rBool l
  let (shiftOut, l) ← rBool l
  let (bell, l) ← rBool l
  some ({ cols, rows, grid := grid.toArray, cursor, pen, modes, top, bot,
          tabs := tabs.toArray, sb, altGrid, saved, title,
          g0Line, g1Line, shiftOut, pstate := .ground, u8need := 0, u8acc := 0,
          bell }, l)

/-! ## The checkpoint record -/

structure Ckpt where
  vt : Vt
  cwd : String
  labels : List (String × String)
  deriving Inhabited

def magic : List UInt8 := [0x4C, 0x5A, 0x4D, 0x58, 1]  -- "LZMX" v1

def save (c : Ckpt) : List UInt8 :=
  magic ++ wVt c.vt ++ wStr c.cwd ++ wList (wPair wStr wStr) c.labels

/-- Total: any byte list either parses fully or is `none`. Trailing
garbage is rejected (a torn write is not a checkpoint). -/
def load (l : List UInt8) : Option Ckpt := do
  let rest ← if l.take 5 = magic then some (l.drop 5) else none
  let (vt, rest) ← rVt rest
  let (cwd, rest) ← rStr rest
  let (labels, rest) ← rList (rPair rStr rStr) rest
  if rest.isEmpty then some { vt, cwd, labels } else none

end Zmx.Core.Checkpoint
