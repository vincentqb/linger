module

public import Terminal.Spec
import SoftwareChallenge.Commands

public section

/-! # The VT toolkit's named claims

The claims the toolkit's headlines take as hypotheses while no theorem proves them. This is the only
module of the package that imports the claim commands. -/

namespace Terminal.Replay

/-- A receiver that has parsed the repaint of a live terminal, taken between
control sequences and characters, keeps showing what the terminal shows as the same output
then reaches both: after any output, every row agrees. A repaint taken inside a control
sequence or a character is outside it: the receiver would read the sequence's rest as text. -/
Conjecture KeepsShowing {V P : Type} (live : V → Prop) (feed : V → List UInt8 → V)
  (colCount rowCount : V → Nat) (getRow : V → Nat → Vt.Row) (atBoundary : V → Bool) (start : V → P)
  (next : Nat → P → Option (Render.Bytes × P)) :=
  ∀ (budget : Nat) (v w : V) (later : List UInt8),
    0 < budget →
      live v →
      live w →
      colCount w = colCount v →
      rowCount w = rowCount v →
      atBoundary v = true →
      ∃ bytes,
        Emits next budget (start v) bytes ∧
          ∀ y < rowCount (feed v later),
            getRow (feed (feed w bytes) later) y = getRow (feed v later) y

end Terminal.Replay
