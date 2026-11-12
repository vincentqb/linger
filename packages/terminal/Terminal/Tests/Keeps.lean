module

-- The `Test`s evaluate each instance in the kernel, which needs the bodies of the emulator, its
-- value types and the repaint; the `example`s run larger ones compiled under `native_decide`.
import all Terminal.Spec
import all Terminal.Vt
import all Terminal.Render
import all Terminal.Proofs.Replay
import Terminal.Spec.Claims
import SoftwareChallenge.Commands
meta import Terminal.Vt
meta import Terminal.Proofs.Replay

/-! # `Replay.KeepsShowing`, instance by instance

`KeepsShowing` (`Terminal/Spec/Claims.lean`) says a receiver that parsed the repaint of a live
terminal, taken between control sequences and characters, keeps showing what the terminal shows
as the same output reaches both. No theorem proves it. Each `Test` proves one instance in the
kernel: a session screen, a fresh receiver of its size, the repaint streamed one byte at a time,
and output fed to both, after which every row agrees. The repaint is `Render.restore` at every
budget (`Replay.start_faithful`), so the budget of one byte stands for all.

The instances are the saved cursors a repaint once lost or could lose: DECRC under origin mode
restoring the default slot, the instance that refuted the claim while the slot did not save origin
mode; a slot saved under origin mode in a region smaller than the screen; a slot clamped into a
region set after it was saved; a slot saved with its wrap pending; mode 1048; and the main screen
stashed by mode 1049 under origin mode. The `example`s run the first at 80 by 24 and at several
budgets, compiled. -/

namespace Terminal.Replay.Tests

open Terminal.Vt

/-- `KeepsShowing` at a session screen `v`, a receiver `w`, output `later` and a budget of one
byte: the claim's hypotheses, then its conclusion. -/
abbrev Instance (v w : Vt) (later : List UInt8) : Prop :=
  0 < 1 →
    Live Vt.init Vt.feed Vt.resize Vt.quiesce Vt.Decodable v →
    Live Vt.init Vt.feed Vt.resize Vt.quiesce Vt.Decodable w →
    w.colCount = v.colCount →
    w.rowCount = v.rowCount →
    v.atBoundary = true →
    ∃ bytes,
      Emits next 1 (start v) bytes ∧
        ∀ y < (v.feed later).rowCount,
          ((w.feed bytes).feed later).getRow y = (v.feed later).getRow y

/-- The repaint, streamed one byte at a time. -/
theorem emits (v : Vt) : Emits next 1 (start v) (Render.restore v) := by
  rw [← start_faithful]
  exact emits_remaining 1 Nat.one_pos _

/-- An instance holds when the rows agree after the repaint and `later`. -/
theorem kept {v w : Vt} {later : List UInt8}
    (rows :
      ∀ y < (v.feed later).rowCount,
        ((w.feed (Render.restore v)).feed later).getRow y = (v.feed later).getRow y) :
    Instance v w later := fun _ _ _ _ _ _ => ⟨_, emits v, rows⟩

/-- `CSI 2;4 r`, `CSI ?6 h`, `ESC 8` on 10 by 4: DECRC under origin mode restores the default
slot, saved with origin mode off, so the next character lands on row 0, above the region. -/
def refuted : Vt := (Vt.init 10 4).feed [27, 91, 50, 59, 52, 114, 27, 91, 63, 54, 104, 27, 56]

-- `Z`.
Test
  KeepsShowing (Live Vt.init Vt.feed Vt.resize Vt.quiesce Vt.Decodable) Vt.feed Vt.colCount
    Vt.rowCount Vt.getRow Vt.atBoundary start next :
  Instance refuted (Vt.init 10 4) [90] := kept (by decide +kernel)

/-- `CSI 2;4 r`, `CSI ?6 h`, `CSI 2;3 H`, `ESC 7`, `CSI ?6 l`, `CSI 5;1 H`, `x` on 10 by 5: the slot
is saved under origin mode at row 2 inside rows 1 to 3, then origin mode is left. -/
def partialRegion : Vt :=
  (Vt.init 10 5).feed
    [27, 91, 50, 59, 52, 114, 27, 91, 63, 54, 104, 27, 91, 50, 59, 51, 72, 27, 55, 27, 91, 63, 54,
      108, 27, 91, 53, 59, 49, 72, 120]

-- `ESC 8`, `Z`, `CSI H`, `Y`: DECRC restores origin mode, so home is the region's top row.
Test
  KeepsShowing (Live Vt.init Vt.feed Vt.resize Vt.quiesce Vt.Decodable) Vt.feed Vt.colCount
    Vt.rowCount Vt.getRow Vt.atBoundary start next :
  Instance partialRegion (Vt.init 10 5) [27, 56, 90, 27, 91, 72, 89] := kept (by decide +kernel)

/-- `CSI 1;5 r`, `CSI ?6 h`, `CSI 4;2 H`, `ESC 7`, `CSI ?6 l`, `CSI 1;2 r` on 10 by 5: the slot is
saved under origin mode at row 3, then the region shrinks to rows 0 and 1. -/
def clamped : Vt :=
  (Vt.init 10 5).feed
    [27, 91, 49, 59, 53, 114, 27, 91, 63, 54, 104, 27, 91, 52, 59, 50, 72, 27, 55, 27, 91, 63, 54,
      108, 27, 91, 49, 59, 50, 114]

-- `ESC 8`, `C`: DECRC clamps the restored row into the region, to row 1.
Test
  KeepsShowing (Live Vt.init Vt.feed Vt.resize Vt.quiesce Vt.Decodable) Vt.feed Vt.colCount
    Vt.rowCount Vt.getRow Vt.atBoundary start next :
  Instance clamped (Vt.init 10 5) [27, 56, 67] := kept (by decide +kernel)

/-- `CSI 1;10 H`, `a`, `ESC 7`, `CSI 3;1 H` on 10 by 3: the slot is saved with its wrap pending at
the last column. -/
def pendingSlot : Vt :=
  (Vt.init 10 3).feed [27, 91, 49, 59, 49, 48, 72, 97, 27, 55, 27, 91, 51, 59, 49, 72]

-- `ESC 8`, `P`: the restored wrap moves `P` to the start of row 1.
Test
  KeepsShowing (Live Vt.init Vt.feed Vt.resize Vt.quiesce Vt.Decodable) Vt.feed Vt.colCount
    Vt.rowCount Vt.getRow Vt.atBoundary start next :
  Instance pendingSlot (Vt.init 10 3) [27, 56, 80] := kept (by decide +kernel)

/-- `CSI 2;4 r`, `CSI ?6 h`, `CSI ?1048 h`, `CSI ?6 l`, `CSI 5;1 H`, `x` on 10 by 5: mode 1048 saves
the slot under origin mode. -/
def saved1048 : Vt :=
  (Vt.init 10 5).feed
    [27, 91, 50, 59, 52, 114, 27, 91, 63, 54, 104, 27, 91, 63, 49, 48, 52, 56, 104, 27, 91, 63, 54,
      108, 27, 91, 53, 59, 49, 72, 120]

-- `CSI ?1048 l`, `CSI H`, `W`: restoring the slot restores origin mode.
Test
  KeepsShowing (Live Vt.init Vt.feed Vt.resize Vt.quiesce Vt.Decodable) Vt.feed Vt.colCount
    Vt.rowCount Vt.getRow Vt.atBoundary start next :
  Instance saved1048 (Vt.init 10 5) [27, 91, 63, 49, 48, 52, 56, 108, 27, 91, 72, 87] :=
  kept (by decide +kernel)

/-- `CSI 2;4 r`, `CSI ?6 h`, `CSI ?1049 h`, `CSI ?6 l`, `A` on 10 by 5: mode 1049 stashes the main
screen with its cursor saved under origin mode, and the alternate screen leaves origin mode. -/
def stashed : Vt :=
  (Vt.init 10 5).feed
    [27, 91, 50, 59, 52, 114, 27, 91, 63, 54, 104, 27, 91, 63, 49, 48, 52, 57, 104, 27, 91, 63, 54,
      108, 65]

-- `CSI ?1049 l`, `CSI 2;3 r`, `Q`: leaving restores origin mode, so the new region's top is home.
Test
  KeepsShowing (Live Vt.init Vt.feed Vt.resize Vt.quiesce Vt.Decodable) Vt.feed Vt.colCount
    Vt.rowCount Vt.getRow Vt.atBoundary start next :
  Instance stashed (Vt.init 10 5) [27, 91, 63, 49, 48, 52, 57, 108, 27, 91, 50, 59, 51, 114, 81] :=
  kept (by decide +kernel)

/-- A string's UTF-8 bytes. -/
def bytesOf (s : String) : List UInt8 := s.toUTF8.toList

/-- One instance of `KeepsShowing`, compiled: the rows agree after the repaint of `v`, streamed at
`budget` into `w`, and `later` fed to both. -/
def keepsShowing (budget : Nat) (positive : 0 < budget) (v w : Vt) (later : List UInt8) : Bool :=
  let bytes := drain budget positive (start v)
  let shown := v.feed later
  let kept := (w.feed bytes).feed later
  (List.range shown.rowCount).all fun y => kept.getRow y == shown.getRow y

/-- The refuted instance at 80 by 24, at budgets from one byte to the whole repaint. -/
example :
    ([1, 7, 64, 65536].attach.all fun b =>
        keepsShowing b.1
          (by
            have := b.2; simp at this; omega)
          ((Vt.init 80 24).feed (bytesOf "\x1b[2;24r\x1b[?6h\x1b8")) (Vt.init 80 24)
          (bytesOf "Z")) =
      true := by
  native_decide

end Terminal.Replay.Tests
