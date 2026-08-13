import Tests.Render
/-! # §Replay fuzzing — the net for assumptions nobody wrote down

Every fidelity bug found by *proving* rather than by testing had the same
shape: an emitter stage that is correct only under a precondition on the
emulator state it is fed into, which some caller violated. Fixtures do not
find those, because a fixture only explores the state a person thought to
write down — and worse, a fixture can pass for the wrong reason (the
pre-existing alt fixture masked fix 9 for exactly that reason).

So: splice random escape-sequence fragments, feed them, and check
`roundtrips`. A failing seed is a bug with a reproducer attached. The
generator is a pure LCG so a seed is all you need to replay a case.

This is deliberately cheap and dumb. It found nothing on the corpus below
only because the corpus excludes the two shapes that are *known* broken —
see `knownGap` — and every previously-found bug in the corpus's range is
fixed.
-/

namespace Zmx.Core.Render.Fuzz

open Zmx.Core.Vt Zmx.Core.Render Zmx.Core.Render.Tests

/-- A pure LCG. Reproducible: a failing seed replays exactly. -/
def nextRand (s : Nat) : Nat := (s * 1103515245 + 12345) % 2147483648

/-- Fragments spliced to build a case. Each is one thing a program does that
`restore` has to be able to reproduce: pens (16/256/true colour), wide
glyphs, combining marks, the alt screen and its older variants, scroll
regions, DECOM, DECSC/DECRC, cursor addressing, wrap, tabs, charsets,
titles, erases. -/
def frags : Array String := #[
  "A", "b", "\u6f22", "e\u0301", " ", "\r\n", "\u6f22\u0301",
  "\x1b[31m", "\x1b[41m", "\x1b[1;4m", "\x1b[7m", "\x1b[0m",
  "\x1b[38;5;123m", "\x1b[48;5;200m", "\x1b[38;2;10;20;30m",
  "\x1b[1;2;3;4;5;7;9m",
  "\x1b[1;1H", "\x1b[2;3H", "\x1b[3;5H", "\x1b[2G", "\x1b[1d",
  "\x1b[?1049h", "\x1b[?1049l", "\x1b[?47h", "\x1b[?47l", "\x1b[?1047h",
  "\x1b[?1048h", "\x1b[?1048l",
  "\x1b7", "\x1b8", "\x1b[s", "\x1b[u",
  "\x1b[2;5r", "\x1b[?6h", "\x1b[?6l",
  "\x1b[?7l", "\x1b[?7h", "\x1b[4h", "\x1b[4l",
  "\x1b[?25l", "\x1b[?2004h", "\x1b[?1000h", "\x1b[?1006h", "\x1b[?1004h",
  "\x1b(0", "\x1b(B", "\x1b)0", "\x0e", "\x0f",
  "\x1b[3g", "\x1bH", "\x1b[0g",
  "\x1b[2J", "\x1b[K", "\x1b[1J", "\x1b[2X",
  "\x1b]2;t\x07", "\x1b[T", "\x1b[S", "\x1b[L", "\x1b[M"
]

/-- **The known-gap exclusion list, stated rather than quietly omitted.**
`ICH`/`DCH` can split a wide glyph, leaving a grid the row painter cannot
express: a width-2 cell in the final column (its shadow pushed off the row)
or an orphaned width-0 cell (its base deleted). Both are recorded in
specs/grid-fidelity.md with candidate fixes; the right one normalises the
*grid* at the mutation, since no terminal can produce these by printing.
Until then the fuzzer would rediscover them on every run, so they are held
out here — and this list existing is what makes the hold-out honest. Delete
an entry when its fix lands. -/
def knownGap : Array String := #["\x1b[3@", "\x1b[1P", "\x1b[2@", "\x1b[1@"]

/-- Splice `n` fragments chosen by the seed. -/
def genCase (seed n : Nat) : String :=
  let rec go (s : Nat) (k : Nat) (acc : String) : String :=
    match k with
    | 0 => acc
    | k + 1 =>
      let s := nextRand s
      go s k (acc ++ frags[s % frags.size]!)
  go seed n ""

/-- Sizes worth exercising: 1-column and 1-row edge cases, a narrow screen
where the right margin is easy to hit, and a normal one. -/
def dims : Array (Nat × Nat) := #[(1, 1), (2, 2), (4, 2), (6, 3), (10, 4)]

/-- The seeds whose case does not round-trip. Empty is the claim. -/
def failing (count : Nat) : List Nat :=
  (List.range count).filter (fun i =>
    let seed := nextRand (i * 7919 + 1)
    let (c, r) := dims[seed % dims.size]!
    !roundtrips (screen c r (genCase seed 6)))

/-- **The fuzz claim.** No seed in range produces a state whose replay
differs from it. A failure prints the seed; reproduce with
`#eval genCase <seed> 6`. -/
example : failing 400 = [] := by native_decide

/-- Longer cases, fewer of them: depth finds interactions that breadth does
not (fix 9 needed a pen *and* an alt switch *and* a default-pen first cell).

**Two seeds fail today**, pinned rather than hidden so that any *new* failure
breaks the build and this list only ever shrinks — the `SHIM_CAP` idiom.
Reproduce a case with `#eval genCase (nextRand (i * 104729 + 17)) 14`.

Seed 3 used to be here and is **fixed** (fix 11): it reached the
width-2-cell-in-the-final-column state with `\x1b[?7l` and a wide glyph, no
`ICH` involved, which refuted the `knownGap` reasoning above — with wrap off
`printWideWrap` does not pre-wrap, so any program that disables autowrap and
prints CJK at the margin produced it. `Vt.printPut` now stores a blank when a
wide glyph has no room for its shadow, so the grid never holds that shape.
Seeds 24 and 139 are also wide-glyph cases (charset and mark interactions)
and are not yet narrowed.

Delete a seed from this list when its fix lands. -/
def failingDeep (count : Nat) : List Nat :=
  (List.range count).filter (fun i =>
    let seed := nextRand (i * 104729 + 17)
    let (c, r) := dims[seed % dims.size]!
    !roundtrips (screen c r (genCase seed 14)))

example : failingDeep 150 = [24, 139] := by native_decide

end Zmx.Core.Render.Fuzz
