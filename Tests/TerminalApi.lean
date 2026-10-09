module

import Theorems.TerminalTitle
import Theorems.Replay

/-! Ordinary imports expose reusable operations and their public contracts
without granting access to sealed VT or replay representation. -/

open Linger.Core Linger.Core.Vt

example : Vt → Replay.Plan := Replay.start

example : Nat → Replay.Plan → Option (Render.Bytes × Replay.Plan) := Replay.next

example (budget : Nat) (p q : Replay.Plan) (bytes : Render.Bytes)
    (step : Replay.next budget p = some (bytes, q)) : bytes.length ≤ budget :=
  Replay.next_bounded step

example (budget : Nat) (positive : 0 < budget) (v : Vt) :
    Replay.drain budget positive (Replay.start v) = Render.restore v :=
  Replay.drain_start budget positive v

example (v : Vt) (title : String) : Terminal.Title.update v title ≠ [] ↔ v.atBoundary = true :=
  Terminal.Title.update_nonempty_iff v title

example (title : String) (c : Char) (h : c ∈ Terminal.Title.payload title) :
    0x20 ≤ c.toNat ∧ c.toNat ≠ 0x7F ∧ ¬(0x80 ≤ c.toNat ∧ c.toNat < 0xA0) :=
  Terminal.Title.payload_safe title c h

example (v : Vt) (a b : List UInt8) :
    v.observe (a ++ b) = (v.observe a).observe b := Linger.Core.Vt.observe_append v a b

/-- Unknown constant `Linger.Core.Replay.Plan.mk` -/
#guard_msgs (error, substring := true) in
#check Replay.Plan.mk

/-- Unknown constant `_private.Linger.Core.Vt.0.Linger.Core.Vt.Vt.pstate` -/
#guard_msgs (error, substring := true) in
#check (Vt.init 2 1).pstate
