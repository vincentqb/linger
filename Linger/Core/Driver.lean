module

public import Linger.Core.Session

public section

namespace Linger.Core.Driver

open Linger.Core.Session (State Event Effect step)

/-- A transport operation reports whether its target disconnected; a checkpoint
reports whether saving failed. Other effects cannot enqueue feedback. -/
abbrev Reply : Effect → Type
  | .send .. | .replay .. | .close .. | .checkpoint => Bool
  | _ => Unit

/-- The events an effect's reply feeds back to the session. -/
def feedback : (eff : Effect) → Reply eff → List Event
  | .send id _, gone => if gone then [.closed id] else []
  | .replay id _, gone => if gone then [.closed id] else []
  | .close id, gone => if gone then [.closed id] else []
  | .checkpoint, failed => if failed then [.checkpointFailed] else []
  | .writePty _, _ | .resizePty .., _ | .killChild, _ | .dropCheckpoint, _ | .exit, _ => []

/-- Feedback strictly descends: external input, disconnect, checkpoint failure. -/
def eventDepth : Event → Nat
  | .checkpointFailed => 0
  | .closed _ => 1
  | _ => 2

/-- A strict upper bound on the depth of the events an effect's reply feeds back. -/
def effectDepth : Effect → Nat
  | .send .. | .replay .. | .close .. => 2
  | .checkpoint => 1
  | _ => 0

theorem feedback_depth (eff : Effect) (reply : Reply eff) :
    ∀ ev ∈ feedback eff reply, eventDepth ev < effectDepth eff := by
  cases eff <;> simp [feedback, eventDepth, effectDepth]

theorem step_depth (s : State) (ev : Event) :
    ∀ eff ∈ (step s ev).2, effectDepth eff ≤ eventDepth ev := by
  cases ev with
  | closed id =>
    intro eff h
    rw [Session.closed_effects s id eff h]
    simp [effectDepth, eventDepth]
  | checkpointFailed => simp [Session.checkpointFailed_effects]
  | _ =>
    intro eff _
    cases eff <;> simp [effectDepth, eventDepth]

/-- The driver's state between events. -/
structure Result (World : Type) where
  /-- The session state. -/
  st : State
  /-- The interpreter's world. -/
  world : World
  /-- An event's effects requested exit, so no later event is consumed. -/
  exiting : Bool := false

/-- Execute a finite effect list in order, retaining the proof that each
feedback event has lower depth than the event that produced this batch. -/
def effects {m : Type → Type} [Monad m] {World : Type}
    (execute : State → World → (eff : Effect) → m (World × Reply eff)) (st : State) (world : World)
    (depth : Nat) (effs : List Effect) (h : ∀ eff ∈ effs, effectDepth eff ≤ depth) :
    m (World × List { ev : Event // eventDepth ev < depth }) := do
  let (world, reversed) ←
    effs.attach.foldlM
        (fun (acc : World × List { ev : Event // eventDepth ev < depth }) eff => do
          let (world, reply) ← execute st acc.1 eff.val
          let more :=
            (feedback eff.val reply).attach.map fun ev =>
              (⟨ev.val,
                  Nat.lt_of_lt_of_le (feedback_depth eff.val reply ev.val ev.property)
                    (h eff.val eff.property)⟩ :
                { ev : Event // eventDepth ev < depth })
          return (world, more.reverse ++ acc.2))
        (world, [])
  return (world, reversed.reverse)

/-- Settle one event and its feedback before consuming another external event.
Recursion is justified by feedback depth, never by a retry count or fuel. -/
def handle {m : Type → Type} [Monad m] {World : Type}
    (execute : State → World → (eff : Effect) → m (World × Reply eff)) (r : Result World)
    (ev : Event) : m (Result World) := do
  if r.exiting then
    return r
  let stepped := step r.st ev
  let (world, more) ←
    effects execute stepped.1 r.world (eventDepth ev) stepped.2 (step_depth r.st ev)
  let next : Result World := { st := stepped.1, world, exiting := stepped.2.contains .exit }
  if next.exiting then
    return next
  more.foldlM (fun r follow => handle execute r follow.val) next
termination_by eventDepth ev
decreasing_by exact follow.property

/-- The daemon's finite-batch driver, parameterized by its effect interpreter.
The interpreter owns world state; only `Session.step` owns session state. -/
def run {m : Type → Type} [Monad m] {World : Type}
    (execute : State → World → (eff : Effect) → m (World × Reply eff)) (r : Result World) :
    List Event → m (Result World)
  | [] => pure r
  | ev :: rest => do
    if r.exiting then
      return r
    let next ← handle execute r ev
    run execute next rest

end Linger.Core.Driver
