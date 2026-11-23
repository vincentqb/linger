module

public import Linger.App.CoreCode.Kill
public import Linger.App.CoreCode.Recovery
public import Linger.App.CoreCode.Wait
public import Linger.Os.CoreCode.Answer
public import Linger.Session.CoreCode
public import Linger.Session.CoreCode.Checkpoint
public import Linger.Session.CoreCode.Driver
public import Linger.Session.CoreSpec
public import Linger.Session.WorldSpec
public import Terminal.CoreCode.Replay
public import Terminal.CoreSpec
import all Linger.App.Proofs.Api
import all Linger.App.Proofs.Capture
import all Linger.App.Proofs.Commands
import all Linger.App.Proofs.Entry
import all Linger.App.Proofs.Kill
import all Linger.App.Proofs.Recovery
import all Linger.App.Proofs.Serve
import all Linger.App.Proofs.Screen
import all Linger.App.Proofs.Wait
import Linger.Display.Proofs.Clean
import all Linger.App.Proofs.Fields
import all Linger.App.Proofs.Owned
import all Linger.Display.Proofs.Alert
import all Linger.Display.Proofs.Listing
import all Linger.Display.Proofs.Status
import all Linger.Display.Proofs.View
import all Linger.Import.Proofs.Resurrect
import all Linger.Selector.Proofs.Picker
import all Linger.Selector.Proofs.Fetch
import all Linger.Display.Proofs.Title
import all Linger.Os.Proofs.Answer
import all Linger.Os.Proofs.Env
import all Os.Proofs.Wait
import Linger.Target.Proofs.Name
import Linger.Target.Proofs.Remote
import all Linger.Session.Proofs.Buf
import all Linger.Session.Proofs.Offloop
import all Linger.Session.Proofs.Present
import all Linger.Session.Proofs.Checkpoint
import all Linger.Session.Proofs.Handoff
import all Linger.Session.Proofs.Claim
import all Linger.Session.Proofs.Names
import all Linger.Session.Proofs.Driver
import all Linger.Session.Proofs.Record
import all Linger.Session.Proofs.Session
import all Linger.Session.Proofs.Start
import all Linger.Session.Proofs.Wire
public import Linger.Session.CoreCode.Record
public import Linger.Session.CoreCode.Wire
import all Terminal.CoreCode.Vt
import all Terminal.Proofs.Vt
import all Terminal.Proofs.Vt.History
import all Terminal.Proofs.Vt.Renderable
import all Terminal.Proofs.Render.Grid
import all Terminal.Proofs.Render.History
import all Terminal.Proofs.Render.PendingWrap
import all Terminal.Proofs.Render.Scrollback
import all Terminal.Proofs.Render.Sticky
import all Terminal.Proofs.Replay
import all Terminal.Proofs.Vt.State

/-! # Part 5 of `Challenge.lean`, accountability: the proofs of its headline theorems and their kills

`Challenge.lean` states them; each proof cites the component theorems it restates, and
`Theorems.Solution` gathers every part for `./lake comparator`. -/

public section

namespace Linger

open Linger.Display Linger.Session Linger.Target Terminal

theorem step_kill_stops (s : State) (id : Nat) (chunk : List UInt8) {c : Client}
    {dec : Wire.Decoder} {rest : List Wire.Msg} (hc : s.client? id = some c)
    (writable : c.mode = .writable) (read : c.decoder.feed chunk = (dec, .kill :: rest))
    (healthy : dec.errored = false) :
    (Session.step s (.bytes id chunk)).2 = [.stopProgram, .close id] ∧
      (Session.step s (.bytes id chunk)).1.terminal = s.terminal ∧
      (Session.step s (.bytes id chunk)).1.fieldList = s.fieldList :=
  Session.step_kill_stops s id chunk hc writable read healthy

theorem step_kill_stops_rejects_exit :
    ¬∀ (s : State) (id : Nat) (chunk : List UInt8) {c : Client} {dec : Wire.Decoder}
        {rest : List Wire.Msg},
        s.client? id = some c →
          c.mode = .writable →
          c.decoder.feed chunk = (dec, .kill :: rest) →
          dec.errored = false →
          ((fun (s : State) (_ : Event) => (s, ([.exit] : List (Effect Replay.Plan)))) s
                  (.bytes id chunk)).2 =
              [.stopProgram, .close id] ∧
            ((fun (s : State) (_ : Event) => (s, ([.exit] : List (Effect Replay.Plan)))) s
                  (.bytes id chunk)).1.terminal =
              s.terminal ∧
            ((fun (s : State) (_ : Event) => (s, ([.exit] : List (Effect Replay.Plan)))) s
                  (.bytes id chunk)).1.fieldList =
              s.fieldList := by
  intro h
  obtain ⟨joined, -⟩ := Session.connected_client_witness
  have stopped :=
    (@h (Session.trace Session.step (State.boot (Vt.Vt.init 1 1) [] []) [.connected 1]).1 1
        (Wire.encode .kill) { id := 1 } {} [] joined rfl
        (Session.feed_encode_fresh .kill (by simp [Wire.Msg.Fits])) rfl).1
  simp at stopped

theorem step_ended_reports (s : State) (ev : Event) :
    (Effect.exit ∈ (Session.step s ev).2 ↔ (ev.ends (seenBy s.roster)).isSome) ∧
      ∀ e keep,
        ev.ends (seenBy s.roster) = some (e, keep) →
          ∃ front,
            (Session.step s ev).2 =
                front ++
                  [.record e.record, if keep then Effect.checkpoint else Effect.dropCheckpoint,
                    .exit] ∧
              Effect.checkpoint ∉ front ∧
              Effect.dropCheckpoint ∉ front ∧
              (∀ c ∈ s.roster,
                c.attached = true ∨ c.waiting = true → e.told.map (Effect.send c.id) <:+: front) ∧
              (Session.step s ev).1.terminal = s.terminal := Session.step_ended_reports s ev

theorem step_ended_reports_rejects_status :
    ¬∀ (s : State) (ev : Event),
        (Effect.exit ∈
              ((fun s _ =>
                    (s,
                      ([.send 0 (.exited 1), .record (.ended .unknown), .dropCheckpoint, .exit] :
                        List (Effect Replay.Plan))))
                  s ev).2 ↔
            (ev.ends
                (seenBy
                  ((fun (_ : State) => [({ id := 0, attached := true } : Client)]) s))).isSome) ∧
          ∀ e keep,
            ev.ends (seenBy ((fun (_ : State) => [({ id := 0, attached := true } : Client)]) s)) =
                some (e, keep) →
              ∃ front,
                ((fun s _ =>
                          (s,
                            ([.send 0 (.exited 1), .record (.ended .unknown), .dropCheckpoint,
                                .exit] :
                              List (Effect Replay.Plan))))
                        s ev).2 =
                    front ++
                      [.record e.record, if keep then Effect.checkpoint else Effect.dropCheckpoint,
                        .exit] ∧
                  Effect.checkpoint ∉ front ∧
                  Effect.dropCheckpoint ∉ front ∧
                  (∀ c ∈ (fun (_ : State) => [({ id := 0, attached := true } : Client)]) s,
                    c.attached = true ∨ c.waiting = true →
                      e.told.map (Effect.send c.id) <:+: front) ∧
                  ((fun s _ =>
                          (s,
                            ([.send 0 (.exited 1), .record (.ended .unknown), .dropCheckpoint,
                                .exit] :
                              List (Effect Replay.Plan))))
                        s ev).1.terminal =
                    s.terminal := by
  intro h
  obtain ⟨front, effects, -, -, heard, -⟩ :=
    (h (State.boot (Vt.Vt.init 1 1) [] []) (.childExited .unknown)).2 (.program .unknown) false rfl
  have only :
    [Effect.send 0 (.exited 1)] ++ [.record (.ended .unknown), .dropCheckpoint, .exit] =
      front ++ [.record (.ended .unknown), .dropCheckpoint, .exit] :=
    effects
  rw [← List.append_cancel_right only] at heard
  -- the ending's two messages cannot fit in the one the wrong daemon sends
  have short := (heard { id := 0, attached := true } (by simp) (.inl rfl)).length_le
  simp [Ending.told] at short

theorem step_signal_saves (s : State) (n : UInt8) :
    ∃ front,
      (Session.step s (.signal n)).2 =
          .stopProgram :: front ++ [.record (.saved n), .checkpoint, .exit] ∧
        Effect.dropCheckpoint ∉ front ∧
        (∀ c ∈ s.roster,
          c.attached = true ∨ c.waiting = true → Effect.send c.id (.saved n) ∈ front) ∧
        (Session.step s (.signal n)).1.terminal = s.terminal := Session.step_signal_saves s n

theorem step_signal_saves_rejects_drop :
    ¬∀ (s : State) (n : UInt8),
        ∃ front,
          ((fun (s : State) (_ : Event) =>
                    (s,
                      ([.stopProgram, .record (.saved 15), .dropCheckpoint, .exit] :
                        List (Effect Replay.Plan))))
                  s (.signal n)).2 =
              .stopProgram :: front ++ [.record (.saved n), .checkpoint, .exit] ∧
            Effect.dropCheckpoint ∉ front ∧
            (∀ c ∈ s.roster,
              c.attached = true ∨ c.waiting = true → Effect.send c.id (.saved n) ∈ front) ∧
            ((fun (s : State) (_ : Event) =>
                    (s,
                      ([.stopProgram, .record (.saved 15), .dropCheckpoint, .exit] :
                        List (Effect Replay.Plan))))
                  s (.signal n)).1.terminal =
              s.terminal := by
  intro h
  obtain ⟨front, effects, -⟩ := h (State.boot (Vt.Vt.init 1 1) [] []) 15
  have short := congrArg List.length effects
  simp only [List.length_cons, List.length_append, List.length_nil] at short
  have empty : front = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst empty
  simp at effects

theorem step_signal_saves_rejects_silent :
    ¬∀ (s : State) (n : UInt8),
        ∃ front,
          ((fun (s : State) (_ : Event) =>
                    (s,
                      ([.stopProgram, .record (.saved 15), .checkpoint, .exit] :
                        List (Effect Replay.Plan))))
                  s (.signal n)).2 =
              .stopProgram :: front ++ [.record (.saved n), .checkpoint, .exit] ∧
            Effect.dropCheckpoint ∉ front ∧
            (∀ c ∈ (fun (_ : State) => [({ id := 0, attached := true } : Client)]) s,
              c.attached = true ∨ c.waiting = true → Effect.send c.id (.saved n) ∈ front) ∧
            ((fun (s : State) (_ : Event) =>
                    (s,
                      ([.stopProgram, .record (.saved 15), .checkpoint, .exit] :
                        List (Effect Replay.Plan))))
                  s (.signal n)).1.terminal =
              s.terminal := by
  intro h
  obtain ⟨front, effects, -, heard, -⟩ := h (State.boot (Vt.Vt.init 1 1) [] []) 15
  have short := congrArg List.length effects
  simp only [List.length_cons, List.length_append, List.length_nil] at short
  have empty : front = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst empty
  simpa using heard { id := 0, attached := true } (by simp) (.inl rfl)

theorem visit_result (afterSave : List UInt8 → Option (List UInt8)) (kept : Record.Kept afterSave)
    (readOnly : Bool) (o : Outcome) (n : UInt8) (seen : Option Seen) :
    App.Recovery.visit readOnly (afterSave (Record.encode (.ended o))) =
        [.show, .tell o, .discard] ∧
      App.Recovery.visit readOnly (afterSave (Record.encode (.saved n))) =
        (if readOnly then [.show] else [.resume]) ∧
      App.Recovery.visit readOnly (afterSave (Record.encode (.running seen))) =
        (if readOnly then [.show] else [.resume]) ∧
      App.Recovery.visit readOnly none = (if readOnly then [.show] else [.resume]) := by
  rw [kept, kept, kept]
  exact
    ⟨App.Recovery.visit_ended readOnly o, App.Recovery.visit_saved readOnly n,
      App.Recovery.visit_running readOnly seen, App.Recovery.visit_none readOnly⟩

theorem visit_result_rejects_resume :
    ¬∀ (afterSave : List UInt8 → Option (List UInt8)),
        Record.Kept afterSave →
          ∀ (readOnly : Bool) (o : Outcome) (n : UInt8) (seen : Option Seen),
            (fun (readOnly : Bool) (_ : Option (List UInt8)) =>
                    if readOnly then [App.Visit.Step.show] else [App.Visit.Step.resume])
                  readOnly (afterSave (Record.encode (.ended o))) =
                [.show, .tell o, .discard] ∧
              (fun (readOnly : Bool) (_ : Option (List UInt8)) =>
                    if readOnly then [App.Visit.Step.show] else [App.Visit.Step.resume])
                  readOnly (afterSave (Record.encode (.saved n))) =
                (if readOnly then [.show] else [.resume]) ∧
              (fun (readOnly : Bool) (_ : Option (List UInt8)) =>
                    if readOnly then [App.Visit.Step.show] else [App.Visit.Step.resume])
                  readOnly (afterSave (Record.encode (.running seen))) =
                (if readOnly then [.show] else [.resume]) ∧
              (fun (readOnly : Bool) (_ : Option (List UInt8)) =>
                    if readOnly then [App.Visit.Step.show] else [App.Visit.Step.resume])
                  readOnly none =
                (if readOnly then [.show] else [.resume]) := by
  intro h
  have shown := (h some (fun _ => rfl) false .unknown 0 none).1
  simp at shown

theorem record_answer (afterSave : List UInt8 → Option (List UInt8)) (kept : Record.Kept afterSave)
    (o : Outcome) (n : UInt8) (seen : Option Seen) (file : Option (List UInt8)) :
    Record.answer (afterSave (Record.encode (.ended o))) = some (.program o) ∧
      Record.answer (afterSave (Record.encode (.saved n))) = some (.saved n) ∧
      Record.answer (afterSave (Record.encode (.running seen))) = some (.program .unknown) ∧
      (Record.answer file).isSome = file.isSome := by
  rw [kept, kept, kept]
  exact
    ⟨Record.answer_ended o, Record.answer_saved n, Record.answer_running seen,
      Record.answer_isSome file⟩

theorem record_answer_rejects_unknown :
    ¬∀ (afterSave : List UInt8 → Option (List UInt8)),
        Record.Kept afterSave →
          ∀ (o : Outcome) (n : UInt8) (seen : Option Seen) (file : Option (List UInt8)),
            (fun (_ : Option (List UInt8)) => some (Ending.program .unknown))
                  (afterSave (Record.encode (.ended o))) =
                some (.program o) ∧
              (fun (_ : Option (List UInt8)) => some (Ending.program .unknown))
                  (afterSave (Record.encode (.saved n))) =
                some (.saved n) ∧
              (fun (_ : Option (List UInt8)) => some (Ending.program .unknown))
                  (afterSave (Record.encode (.running seen))) =
                some (.program .unknown) ∧
              ((fun (_ : Option (List UInt8)) => some (Ending.program .unknown)) file).isSome =
                file.isSome := by
  intro h
  -- a file system that keeps every record whole, as the claim says
  exact absurd (h some (fun _ => rfl) (.exited 0) 15 none none).1 (by simp)

theorem record_answer_rejects_running :
    ¬∀ (afterSave : List UInt8 → Option (List UInt8)),
        Record.Kept afterSave →
          ∀ (o : Outcome) (n : UInt8) (seen : Option Seen) (file : Option (List UInt8)),
            Record.answer
                  (afterSave ((fun (_ : Record) => Record.encode (.running none)) (.ended o))) =
                some (.program o) ∧
              Record.answer
                  (afterSave ((fun (_ : Record) => Record.encode (.running none)) (.saved n))) =
                some (.saved n) ∧
              Record.answer
                  (afterSave
                    ((fun (_ : Record) => Record.encode (.running none)) (.running seen))) =
                some (.program .unknown) ∧
              (Record.answer file).isSome = file.isSome := by
  intro h
  -- a daemon whose end records all say its program still runs, as one that a signal killed left
  have ended := (h some (fun _ => rfl) (.exited 0) 15 none none).1
  simp [Record.answer_running] at ended

theorem wait_ending (deadline heldSince : Option Nat) (now : Nat) (e : Ending) :
    App.Wait.decide deadline heldSince now (.ended e) = .answer (.ended e) ∧
      App.Wait.decide deadline heldSince now (.recorded (some e)) = .answer (.ended e) :=
  App.Wait.wait_ending deadline heldSince now e

theorem wait_ending_rejects_failed :
    ¬∀ (deadline heldSince : Option Nat) (now : Nat) (e : Ending),
        (fun (_ _ : Option Nat) (_ : Nat) (_ : App.Wait.Heard) => App.Wait.Next.answer .unknown)
              deadline heldSince now (.ended e) =
            .answer (.ended e) ∧
          (fun (_ _ : Option Nat) (_ : Nat) (_ : App.Wait.Heard) => App.Wait.Next.answer .unknown)
              deadline heldSince now (.recorded (some e)) =
            .answer (.ended e) := by
  intro h
  have told := (h none none 0 (.program (.exited 0))).1
  simp at told

theorem wait_held (deadline heldSince : Option Nat) (now : Nat) (heard : App.Wait.Heard) :
    (App.Wait.Next.told (App.Wait.decide deadline heldSince now heard) = some .failed ↔
        heard = .ended (.program .unknown) ∨
          heard = .recorded (some (.program .unknown)) ∨
          heard = .held ∧ ∃ since, heldSince = some since ∧ since + App.Wait.heldNameMs ≤ now) ∧
      (heard = .held →
        (∀ due, deadline = some due → now < due) →
        (∀ since, heldSince = some since → now < since + App.Wait.heldNameMs) →
        App.Wait.decide deadline heldSince now heard = .again (some (heldSince.getD now))) ∧
      (heard = .held →
        ∀ since,
          heldSince = some since →
            now < since + (Session.drainTimeoutMs + (Session.ending.map (·.wait)).sum) →
            App.Wait.Next.told (App.Wait.decide deadline heldSince now heard) ≠ some .failed) := by
  refine
    ⟨(App.Wait.wait_held deadline heldSince now heard).1,
      (App.Wait.wait_held deadline heldSince now heard).2, ?_⟩
  intro held since named ending failed
  have := (App.Wait.wait_held deadline heldSince now heard).1.mp failed
  subst held
  rcases this with h | h | ⟨-, since', named', late⟩
  · cases h
  · cases h
  · rw [named] at named'
    cases named'
    have := App.Wait.held_covers_ending
    omega

theorem wait_held_rejects_eager :
    ¬∀ (deadline heldSince : Option Nat) (now : Nat) (heard : App.Wait.Heard),
        (App.Wait.Next.told
                ((fun (_ _ : Option Nat) (_ : Nat) (_ : App.Wait.Heard) =>
                    App.Wait.Next.answer .unknown)
                  deadline heldSince now heard) =
              some .failed ↔
            heard = .ended (.program .unknown) ∨
              heard = .recorded (some (.program .unknown)) ∨
              heard = .held ∧ ∃ since, heldSince = some since ∧ since + App.Wait.heldNameMs ≤ now) ∧
          (heard = .held →
            (∀ due, deadline = some due → now < due) →
            (∀ since, heldSince = some since → now < since + App.Wait.heldNameMs) →
            (fun (_ _ : Option Nat) (_ : Nat) (_ : App.Wait.Heard) => App.Wait.Next.answer .unknown)
                deadline heldSince now heard =
              .again (some (heldSince.getD now))) ∧
          (heard = .held →
            ∀ since,
              heldSince = some since →
                now < since + (Session.drainTimeoutMs + (Session.ending.map (·.wait)).sum) →
                App.Wait.Next.told
                    ((fun (_ _ : Option Nat) (_ : Nat) (_ : App.Wait.Heard) =>
                        App.Wait.Next.answer .unknown)
                      deadline heldSince now heard) ≠
                  some .failed) := by
  intro h
  have failed := ((h none none 0 .held).1).mp rfl
  simp at failed

theorem wait_held_rejects_drain :
    ¬∀ (deadline heldSince : Option Nat) (now : Nat) (heard : App.Wait.Heard),
        (App.Wait.Next.told (App.Wait.decide deadline heldSince now heard) = some .failed ↔
            heard = .ended (.program .unknown) ∨
              heard = .recorded (some (.program .unknown)) ∨
              heard = .held ∧
                ∃ since, heldSince = some since ∧ since + Session.drainTimeoutMs ≤ now) ∧
          (heard = .held →
            (∀ due, deadline = some due → now < due) →
            (∀ since, heldSince = some since → now < since + Session.drainTimeoutMs) →
            App.Wait.decide deadline heldSince now heard = .again (some (heldSince.getD now))) ∧
          (heard = .held →
            ∀ since,
              heldSince = some since →
                now < since + (Session.drainTimeoutMs + (Session.ending.map (·.wait)).sum) →
                App.Wait.Next.told (App.Wait.decide deadline heldSince now heard) ≠
                  some .failed) := by
  intro h
  -- a wait that fails once a drain has passed, while the ending's signals still wait
  have k := h none (some 0) Session.drainTimeoutMs .held
  exact k.2.2 rfl 0 rfl (by decide) (k.1.mpr (.inr (.inr ⟨rfl, 0, rfl, by simp⟩)))

theorem kill_answers (taken now : Nat) (heard : App.Kill.Heard) :
    (App.Kill.Next.told (App.Kill.decide taken now heard) = some .done ↔
        heard = .free ∨ heard = .newer) ∧
      (App.Kill.Next.told (App.Kill.decide taken now heard) = some .notDone ↔
        heard = .asked ∧ taken + App.Wait.heldNameMs ≤ now) ∧
      (App.Kill.Next.told (App.Kill.decide taken now heard) = some .failed ↔
        heard = .held ∧ taken + App.Wait.heldNameMs ≤ now) ∧
      (App.Kill.Next.told (App.Kill.decide taken now heard) = none ↔
        (heard = .asked ∨ heard = .held) ∧ now < taken + App.Wait.heldNameMs) ∧
      (now < taken + (Session.drainTimeoutMs + (Session.ending.map (·.wait)).sum) →
        App.Kill.Next.told (App.Kill.decide taken now heard) = some .done ∨
          App.Kill.Next.told (App.Kill.decide taken now heard) = none) :=
  ⟨(App.Kill.kill_answers taken now heard).1, (App.Kill.kill_answers taken now heard).2.1,
    (App.Kill.kill_answers taken now heard).2.2.1, (App.Kill.kill_answers taken now heard).2.2.2,
    App.Kill.kill_patient taken now heard⟩

theorem kill_answers_rejects_lock :
    ¬∀ (taken now : Nat) (heard : App.Kill.Heard),
        (App.Kill.Next.told (App.Kill.byLock App.Wait.heldNameMs taken now heard) = some .done ↔
            heard = .free ∨ heard = .newer) ∧
          (App.Kill.Next.told (App.Kill.byLock App.Wait.heldNameMs taken now heard) =
              some .notDone ↔
            heard = .asked ∧ taken + App.Wait.heldNameMs ≤ now) ∧
          (App.Kill.Next.told (App.Kill.byLock App.Wait.heldNameMs taken now heard) = some .failed ↔
            heard = .held ∧ taken + App.Wait.heldNameMs ≤ now) ∧
          (App.Kill.Next.told (App.Kill.byLock App.Wait.heldNameMs taken now heard) = none ↔
            (heard = .asked ∨ heard = .held) ∧ now < taken + App.Wait.heldNameMs) ∧
          (now < taken + (Session.drainTimeoutMs + (Session.ending.map (·.wait)).sum) →
            App.Kill.Next.told (App.Kill.byLock App.Wait.heldNameMs taken now heard) = some .done ∨
              App.Kill.Next.told (App.Kill.byLock App.Wait.heldNameMs taken now heard) = none) := by
  intro h
  -- a name a newer session took, which the rule before this one never reads as an ending
  exact App.Kill.byLock_newer 0 0 (((h 0 0 .newer).1).mpr (.inr rfl))

theorem code_documented (status : UInt32) (signal : UInt8) :
    Os.Answer.code .done = 0 ∧
      Os.Answer.code .notDone = 1 ∧
      Os.Answer.code .usage = 2 ∧
      Os.Answer.code .timedOut = 124 ∧
      Os.Answer.code .failed = 125 ∧
      Os.Answer.code .cannotRun = 126 ∧
      Os.Answer.code .notFound = 127 ∧
      Os.Answer.code .cancelled = 130 ∧
      Os.Answer.code (.stopped signal) = 128 + signal.toUInt32 ∧
      Os.Answer.code (.saved signal) = 128 + signal.toUInt32 ∧
      Os.Answer.code (.program status) = status := Os.Answer.code_documented status signal

theorem code_documented_rejects_zero :
    ¬∀ (status : UInt32) (signal : UInt8),
        (fun (_ : Os.Answer) => (0 : UInt32)) .done = 0 ∧
          (fun (_ : Os.Answer) => (0 : UInt32)) .notDone = 1 ∧
          (fun (_ : Os.Answer) => (0 : UInt32)) .usage = 2 ∧
          (fun (_ : Os.Answer) => (0 : UInt32)) .timedOut = 124 ∧
          (fun (_ : Os.Answer) => (0 : UInt32)) .failed = 125 ∧
          (fun (_ : Os.Answer) => (0 : UInt32)) .cannotRun = 126 ∧
          (fun (_ : Os.Answer) => (0 : UInt32)) .notFound = 127 ∧
          (fun (_ : Os.Answer) => (0 : UInt32)) .cancelled = 130 ∧
          (fun (_ : Os.Answer) => (0 : UInt32)) (.stopped signal) = 128 + signal.toUInt32 ∧
          (fun (_ : Os.Answer) => (0 : UInt32)) (.saved signal) = 128 + signal.toUInt32 ∧
          (fun (_ : Os.Answer) => (0 : UInt32)) (.program status) = status := by
  intro h
  exact absurd (h 0 0).2.1 (by decide)

theorem code_documented_rejects_lumped :
    ¬∀ (status : UInt32) (signal : UInt8),
        Os.Answer.lumped .done = 0 ∧
          Os.Answer.lumped .notDone = 1 ∧
          Os.Answer.lumped .usage = 2 ∧
          Os.Answer.lumped .timedOut = 124 ∧
          Os.Answer.lumped .failed = 125 ∧
          Os.Answer.lumped .cannotRun = 126 ∧
          Os.Answer.lumped .notFound = 127 ∧
          Os.Answer.lumped .cancelled = 130 ∧
          Os.Answer.lumped (.stopped signal) = 128 + signal.toUInt32 ∧
          Os.Answer.lumped (.saved signal) = 128 + signal.toUInt32 ∧
          Os.Answer.lumped (.program status) = status := by
  intro h
  -- SIGTERM's status is 143, which the rule that answered 130 for every signal does not give
  exact absurd (h 0 15).2.2.2.2.2.2.2.2.1 (by decide)

theorem endingFields_injective :
    (∀ o, Session.endingFields (.program o) = Session.outcomeFields o) ∧
      ∀ e₁ e₂, Session.endingFields e₁ = Session.endingFields e₂ → e₁ = e₂ :=
  ⟨Session.endingFields_program, fun _ _ h => Session.endingFields_injective h⟩

theorem endingFields_injective_rejects_unknown :
    ¬((∀ o,
          (fun (e : Ending) =>
                Session.endingFields (if e = .saved 15 then .program .unknown else e))
              (.program o) =
            Session.outcomeFields o) ∧
        ∀ e₁ e₂,
          (fun (e : Ending) =>
                  Session.endingFields (if e = .saved 15 then .program .unknown else e))
                e₁ =
              (fun (e : Ending) =>
                  Session.endingFields (if e = .saved 15 then .program .unknown else e))
                e₂ →
            e₁ = e₂) := by
  intro h
  -- a reader that hears a saved session as one whose program's ending is unknown
  have same := h.2 (.saved 15) (.program .unknown) (by simp)
  cases same

theorem endingFields_injective_rejects_silence :
    ¬((∀ o,
          Session.endingFields (.program o) =
            (fun (_ : Outcome) => ([] : List (String × String))) o) ∧
        ∀ e₁ e₂, Session.endingFields e₁ = Session.endingFields e₂ → e₁ = e₂) := by
  intro h
  -- a listing of end records that reports no ending at all
  exact
    Session.outcomeFields_ne_nil (.exited 0) ((Session.endingFields_program _).symm.trans (h.1 _))

theorem infoFields_protocol (s : State) :
    ("protocol", toString Wire.protocol) ∈ Session.infoFields s := (Session.infoFields_protocol s).1

theorem infoFields_protocol_rejects_empty :
    ¬∀ (s : State),
        ("protocol", toString Wire.protocol) ∈
          (fun (_ : State) => ([] : List (String × String))) s := by
  intro h
  exact absurd (h (State.boot (Vt.Vt.init 1 1) [] [])) (by simp)

theorem admits_level (level : Option Nat) :
    Wire.admits level = true ↔ level = some Wire.protocol := Wire.admits_iff level

theorem admits_level_rejects_any :
    ¬∀ (level : Option Nat),
        (fun (_ : Option Nat) => true) level = true ↔ level = some Wire.protocol := by
  intro h
  cases (h none).1 rfl

theorem step_unknown_refused (s : State) (id : Nat) (chunk : List UInt8) {c : Client}
    {dec : Wire.Decoder} {tag : UInt8} {payload : List UInt8} (hc : s.client? id = some c)
    (read : c.decoder.feed chunk = (dec, [.unknown tag payload])) (healthy : dec.errored = false) :
    (Session.step s (.bytes id chunk)).2 = [.send id (.err "unknown message".toUTF8.toList)] ∧
      (Session.step s (.bytes id chunk)).1.terminal = s.terminal ∧
      (Session.step s (.bytes id chunk)).1.fieldList = s.fieldList :=
  Session.step_unknown_refused s id chunk hc read healthy

theorem step_unknown_refused_rejects_silence :
    ¬∀ (s : State) (id : Nat) (chunk : List UInt8) {c : Client} {dec : Wire.Decoder} {tag : UInt8}
        {payload : List UInt8},
        s.client? id = some c →
          c.decoder.feed chunk = (dec, [.unknown tag payload]) →
          dec.errored = false →
          ((fun (s : State) (_ : Event) => (s, ([] : List (Effect Replay.Plan)))) s
                  (.bytes id chunk)).2 =
              [.send id (.err "unknown message".toUTF8.toList)] ∧
            ((fun (s : State) (_ : Event) => (s, ([] : List (Effect Replay.Plan)))) s
                  (.bytes id chunk)).1.terminal =
              s.terminal ∧
            ((fun (s : State) (_ : Event) => (s, ([] : List (Effect Replay.Plan)))) s
                  (.bytes id chunk)).1.fieldList =
              s.fieldList := by
  intro h
  obtain ⟨joined, -⟩ := Session.connected_client_witness
  have refused :=
    (@h (Session.trace Session.step (State.boot (Vt.Vt.init 1 1) [] []) [.connected 1]).1 1
        (Wire.encode (.unknown 200 [])) { id := 1 } {} 200 [] joined
        (Session.feed_encode_fresh (.unknown 200 []) ⟨by simp, by decide⟩) rfl).1
  simp at refused

theorem run_refines {World : Type}
    (execute : State → World → (eff : Effect Replay.Plan) → Id (World × Driver.Reply eff))
    (ending : Outcome)
    (succeeds : ∀ st world eff, (execute st world eff).2 = Driver.success ending eff)
    (r : Driver.Result State World) (events : List Event) (running : r.exiting = false) :
    ∃ handled exits,
      Driver.Handles Session.step ending r.st events handled exits ∧
        (Driver.run execute r events).st = (Session.trace Session.step r.st handled).1 ∧
        (Driver.run execute r events).world =
          (Session.trace (Driver.withState Session.step) r.st handled).2.foldl
            (fun world (asked : State × Effect Replay.Plan) => (execute asked.1 world asked.2).1)
            r.world ∧
        (Driver.run execute r events).exiting = exits :=
  Driver.run_refines execute ending succeeds r events running

theorem run_refines_rejects_inert :
    ¬∀ {World : Type}
        (execute : State → World → (eff : Effect Replay.Plan) → Id (World × Driver.Reply eff))
        (ending : Outcome),
        (∀ st world eff, (execute st world eff).2 = Driver.success ending eff) →
          ∀ (r : Driver.Result State World) (events : List Event),
            r.exiting = false →
              ∃ handled exits,
                Driver.Handles Session.step ending r.st events handled exits ∧
                  (Driver.inert execute r events).st = (Session.trace Session.step r.st handled).1 ∧
                  (Driver.inert execute r events).world =
                    (Session.trace (Driver.withState Session.step) r.st handled).2.foldl
                      (fun world (asked : State × Effect Replay.Plan) =>
                        (execute asked.1 world asked.2).1)
                      r.world ∧
                  (Driver.inert execute r events).exiting = exits := by
  intro h
  obtain ⟨handled, exits, handles, -, -, stayed⟩ :=
    @h Unit (fun _ world eff => (world, Driver.success .unknown eff)) .unknown (fun _ _ _ => rfl)
      { st := State.boot (Vt.Vt.init 1 1) [] [], world := () } [.childExited .unknown] rfl
  have ends :=
    (Session.step_exit_iff (State.boot (Vt.Vt.init 1 1) [] []) (.childExited .unknown) false).mpr
      rfl
  cases handles with
  | exit => simp [Driver.inert] at stayed
  | next _ _ _ _ _ stays => exact stays ends

theorem run_total_safe {World ε : Type}
    (execute : State → World → (eff : Effect Replay.Plan) → Except ε (World × Driver.Reply eff))
    (hw : Driver.Responds execute) (r : Driver.Result State World) (events : List Event)
    (hb : Bounds State.roster State.fieldList State.scanner r.st)
    (hlive :
      Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
        (Checkpoint.Decoded Checkpoint.loadBytes) r.st.terminal) :
    ∃ out,
      Driver.run execute r events = .ok out ∧
        Bounds State.roster State.fieldList State.scanner out.st ∧
        Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
          (Checkpoint.Decoded Checkpoint.loadBytes) out.st.terminal := by
  have live : LiveVt r.st := (Session.liveVt_iff _).mpr (Checkpoint.live_decoded_iff.mp hlive)
  obtain ⟨out, ok, ⟨bounded, _⟩, kept⟩ :=
    Driver.run_total_safe execute hw r events
      ⟨(Session.bounded_iff_bounds _).mpr hb, Vt.good_of_liveReachable live⟩ live
  exact
    ⟨out, ok, (Session.bounded_iff_bounds _).mp bounded,
      Checkpoint.live_decoded_iff.mpr ((Session.liveVt_iff _).mp kept)⟩

theorem run_total_safe_rejects_jump :
    ¬∀ {World ε : Type}
        (execute :
          State → World → (eff : Effect Replay.Plan) → Except ε (World × Driver.Reply eff)),
        Driver.Responds execute →
          ∀ (r : Driver.Result State World) (events : List Event),
            Bounds State.roster
                (fun st =>
                  if st.terminal.colCount = 80 then [] else List.replicate (maxFields + 1) ("", ""))
                State.scanner r.st →
              Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
                (Checkpoint.Decoded Checkpoint.loadBytes) r.st.terminal →
              ∃ out,
                Driver.jump (State.boot (Vt.Vt.init 1 1) [] []) execute r events = .ok out ∧
                  Bounds State.roster
                    (fun st =>
                      if st.terminal.colCount = 80 then []
                      else List.replicate (maxFields + 1) ("", ""))
                    State.scanner out.st ∧
                  Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
                    (Checkpoint.Decoded Checkpoint.loadBytes) out.st.terminal := by
  intro h
  obtain ⟨-, -, wide, roster, -, scanner⟩ := Session.boot_observed (Vt.Vt.init 80 24) [] []
  obtain ⟨-, -, narrow, -, -, -⟩ := Session.boot_observed (Vt.Vt.init 1 1) [] []
  let execute : State → Unit → (eff : Effect Replay.Plan) → Except Unit (Unit × Driver.Reply eff) :=
    fun _ world eff => .ok (world, Driver.success .unknown eff)
  obtain ⟨out, jumped, bounds, -⟩ :=
    @h Unit Unit execute (fun _ _ _ => ⟨_, rfl⟩)
      { st := State.boot (Vt.Vt.init 80 24) [] [], world := () } []
      ⟨by
        rw [roster]; decide, by
        rw [wide]; decide +kernel, fun c member =>
        absurd member
          (by
            rw [roster]; exact List.not_mem_nil),
        by
        rw [scanner]; trivial⟩
      (by
        rw [wide]; exact .init 80 24)
  cases jumped
  have overflow := bounds.fieldsLe
  rw [narrow] at overflow
  exact absurd overflow (by decide +kernel)

theorem run_feedback_alive {World : Type}
    (execute : State → World → (eff : Effect Replay.Plan) → Id (World × Driver.Reply eff))
    (r : Driver.Result State World) (events : List Event) (running : r.exiting = false)
    (failures : ∀ ev ∈ events, ev = .checkpointFailed ∨ ∃ id, ev = .closed id) :
    (Driver.run execute r events).exiting = false :=
  Driver.run_feedback_alive execute r events running failures

theorem run_feedback_alive_rejects_halt :
    ¬∀ {World : Type}
        (execute : State → World → (eff : Effect Replay.Plan) → Id (World × Driver.Reply eff))
        (r : Driver.Result State World) (events : List Event),
        r.exiting = false →
          (∀ ev ∈ events, ev = .checkpointFailed ∨ ∃ id, ev = .closed id) →
          (Driver.halt execute r events).exiting = false := by
  intro h
  have stopped :=
    @h Unit (fun _ world eff => (world, Driver.success .unknown eff))
      { st := State.boot (Vt.Vt.init 1 1) [] [], world := () } [] rfl (by simp)
  exact absurd stopped (by decide)

theorem run_stop_exits {World : Type}
    (execute : State → World → (eff : Effect Replay.Plan) → Id (World × Driver.Reply eff))
    (r : Driver.Result State World) (ev : Event) (running : r.exiting = false)
    (stops : Effect.stopProgram ∈ (Session.step r.st ev).2) :
    (Driver.run execute r [ev]).exiting = true := Driver.run_stop_exits execute r ev running stops

theorem run_stop_exits_rejects_jump :
    ¬∀ {World : Type}
        (execute : State → World → (eff : Effect Replay.Plan) → Id (World × Driver.Reply eff))
        (r : Driver.Result State World) (ev : Event),
        r.exiting = false →
          Effect.stopProgram ∈ (Session.step r.st ev).2 →
          (Driver.jump (State.boot (Vt.Vt.init 1 1) [] []) execute r [ev]).exiting = true := by
  intro h
  obtain ⟨joined, -⟩ := Session.connected_client_witness
  have stops :=
    (Session.step_kill_stops _ 1 (Wire.encode .kill) joined rfl
        (Session.feed_encode_fresh .kill (by simp [Wire.Msg.Fits])) rfl).1
  have jumped :=
    @h Unit (fun _ world eff => (world, Driver.success .unknown eff))
      { st := (Session.trace Session.step (State.boot (Vt.Vt.init 1 1) [] []) [.connected 1]).1,
        world := () }
      (.bytes 1 (Wire.encode .kill)) rfl
      (by
        rw [stops]; simp)
  simp [Driver.jump] at jumped

end Linger
