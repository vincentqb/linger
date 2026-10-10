module

-- `roundtrips` and `roundtripsFrom` are private to `Tests.Render` and run under `native_decide`.
import all Tests.Render
meta import Tests.Render

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

This is deliberately cheap and dumb, and it has earned its keep: it found
three real replay bugs, two of which no fixture would have reached (see
`failingDeep`). Nothing is held out of the corpus any more — `knownGap` is
empty and the `ICH`/`DCH` mutations that used to be excluded are in `frags`,
because the shapes they produced are now repaired in the emulator rather than
avoided in the test.
-/

namespace Linger.Core.Render.Fuzz

open Linger.Core.Render.Tests

/-- A pure LCG. Reproducible: a failing seed replays exactly. -/
def nextRand (s : Nat) : Nat := (s * 1103515245 + 12345) % 2147483648

/-- Fragments spliced to build a case. Each is one thing a program does that
`restore` has to be able to reproduce: pens (16/256/true colour), wide
glyphs, combining marks, the alt screen and its older variants, scroll
regions, DECOM, DECSC/DECRC, cursor addressing, wrap, tabs, charsets,
titles, erases. -/
def frags : Array String :=
  #["A", "b", "\u6f22", "e\u0301", " ", "\r\n", "\u6f22\u0301", "\x1b[31m", "\x1b[41m", "\x1b[1;4m",
    "\x1b[7m", "\x1b[0m", "\x1b[38;5;123m", "\x1b[48;5;200m", "\x1b[38;2;10;20;30m",
    "\x1b[1;2;3;4;5;7;9m", "\x1b[1;1H", "\x1b[2;3H", "\x1b[3;5H", "\x1b[2G", "\x1b[1d",
    "\x1b[?1049h", "\x1b[?1049l", "\x1b[?47h", "\x1b[?47l", "\x1b[?1047h", "\x1b[?1048h",
    "\x1b[?1048l", "\x1b7", "\x1b8", "\x1b[s", "\x1b[u", "\x1b[2;5r", "\x1b[?6h", "\x1b[?6l",
    "\x1b[?7l", "\x1b[?7h", "\x1b[4h", "\x1b[4l", "\x1b[?25l", "\x1b[?2004h", "\x1b[?1000h",
    "\x1b[?1006h", "\x1b[?1004h", "\x1b(0", "\x1b(B", "\x1b)0", "\x0e", "\x0f", "\x1b[3g", "\x1bH",
    "\x1b[0g", "\x1b[2J", "\x1b[K", "\x1b[1J", "\x1b[2X", "\x1b]2;t\x07", "\x1b[T", "\x1b[S",
    "\x1b[L", "\x1b[M",
    -- the four former `knownGap` mutations: `ICH`/`DCH` split a wide pair, which
    -- `Vt.printPut`/`Row.mend` now repair at the mutation instead of leaving a
    -- shape the row painter cannot express
    "\x1b[3@", "\x1b[1P", "\x1b[2@", "\x1b[1@"]

/-- **The exclusion list, now empty.** `ICH`/`DCH` used to be held out here:
they can split a wide glyph, leaving a width-2 cell whose shadow was pushed off
the row or an orphaned width-0 cell whose base was deleted, and the row painter
cannot express either. Both are repaired in the emulator now — the mutations are
in `frags` above, and this list existing is what keeps such a hold-out honest.

Kept as the empty array rather than deleted: a future gap gets recorded here
instead of quietly narrowing the corpus. -/
def knownGap : Array String := #[]

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
  (List.range count).filter
    (fun i =>
      let seed := nextRand (i * 7919 + 1)
      let (c, r) := dims[seed % dims.size]!
      !roundtrips (screen c r (genCase seed 6)))

/-- **The fuzz claim.** No seed in range produces a state whose replay
differs from it. A failure prints the seed; reproduce with
`#eval genCase <seed> 6`. -/
example : failing 400 = [] := by native_decide

/-- Longer cases, fewer of them: depth finds interactions that breadth does
not (fix 9 needed a pen *and* an alt switch *and* a default-pen first cell).

**The list is empty**, and pinned as empty so that any new failure breaks the
build — the `SHIM_CAP` idiom. Reproduce a case with
`#eval genCase (nextRand (i * 104729 + 17)) 14`.

Three seeds have been here and are fixed. Seed 3 (fix 11) reached a width-2
cell in the final column with `\x1b[?7l` and a wide glyph, no `ICH` involved,
refuting the reasoning that had held `ICH`/`DCH` out of the corpus. Seeds 24
and 139 turned out to be the same bug as each other and equally free of
`ICH`/`DCH`: printing a **narrow** glyph over a wide base orphans that base's
shadow, which the row painter then paints as a plain blank (seed 24) or whose
marks it re-attaches to the wrong cell (seed 139). Ordinary redrawing over CJK
text reaches it, so the repair is in the emulator (`Vt.printPut` mends the two
columns a write can half-orphan, and the row mutations mend the row). -/
def failingDeep (count : Nat) : List Nat :=
  (List.range count).filter
    (fun i =>
      let seed := nextRand (i * 104729 + 17)
      let (c, r) := dims[seed % dims.size]!
      !roundtrips (screen c r (genCase seed 14)))

example : failingDeep 150 = [] := by native_decide

end Linger.Core.Render.Fuzz
