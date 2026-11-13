module

import all Linger.Session.CoreCode.Driver
import all Linger.Session.Proofs.Session
import Linger.Session.CoreSpec
import Linger.Session.WorldSpec

/-! The effect interpreter is an arbitrary total function on an abstract world.
Its replies are constrained by the same dependent type the daemon implements.
The execution relation below describes the feedback queue independently of the
driver's recursive traversal: finishing means an empty queue or explicit exit.

The model assumes each primitive returns and has the meaning of its typed reply.
It does not assume that writes or checkpoint saves succeed. -/

namespace Linger.Session.Driver

open Linger.Session (State Event Effect step WF LiveVt)
open Terminal.Replay (Plan)
variable {World : Type}

/-- A total effect interpreter over an abstract world, with typed replies. -/
abbrev Interpreter (World : Type) := State → World → (eff : Effect Plan) → World × Reply eff

/-- Erasing the termination witnesses gives ordinary left-to-right effect
execution and FIFO feedback. Reversing either order changes this equation. -/
theorem effects_in_order (execute : Interpreter World) (st : State) (world : World) (depth : Nat)
    (effs : List (Effect Plan)) (h : ∀ eff ∈ effs, effectDepth eff ≤ depth) :
    let answered := effects (m := Id) execute st world depth effs h
    (answered.1, answered.2.map Subtype.val) =
      effs.foldl
        (fun (acc : World × List Event) eff =>
          let answer := execute st acc.1 eff
          (answer.1, acc.2 ++ feedback eff answer.2))
        (world, []) := by
  let project := fun (acc : World × List { ev : Event // eventDepth ev < depth }) =>
    (acc.1, acc.2.reverse.map Subtype.val)
  change
    (fun answered => (answered.1, answered.2.map Subtype.val))
        (effects (m := Id) execute st world depth effs h).run =
      _
  rw [effects]
  simp only [Id.run_bind, Id.run_pure, List.idRun_foldlM]
  change project (effs.attach.foldl _ (world, [])) = _
  rw [←
    List.foldl_hom project (g₂ := fun acc eff =>
      let answer := execute st acc.1 eff.val
      (answer.1, acc.2 ++ feedback eff.val answer.2))]
  · dsimp [project]
    simpa only [List.map_nil] using
      (List.foldl_attach (l := effs) (f := fun (acc : World × List Event) eff =>
        let answer := execute st acc.1 eff
        (answer.1, acc.2 ++ feedback eff answer.2))
        (b := (world, [])))
  · intro acc eff
    simp only [List.map_reverse, Id.run, List.map_append, List.map_map, Function.comp_def,
      List.reverse_append, List.reverse_reverse, Prod.mk.injEq, List.append_cancel_left_eq,
      true_and, project]
    exact (List.attach_map_subtype_val _).symm

/-- One event's complete effect batch, with feedback in execution order. -/
def batch (execute : Interpreter World) (r : Result State World) (ev : Event) :
    Result State World × List Event :=
  let stepped := step r.st ev
  let answered :=
    effects (m := Id) execute stepped.1 r.world (eventDepth ev) stepped.2 (step_depth r.st ev)
  ({ st := stepped.1, world := answered.1, exiting := stepped.2.contains .exit },
    answered.2.map Subtype.val)

theorem feedback_strictly_decreases (eff : Effect Plan) (reply : Reply eff)
    (ev : Event) (h : ev ∈ feedback eff reply) : eventDepth ev < effectDepth eff :=
  feedback_depth eff reply ev h

theorem batch_feedback_decreases (execute : Interpreter World) (r : Result State World) (ev : Event) :
    ∀ follow ∈ (batch execute r ev).2, eventDepth follow < eventDepth ev := by
  intro follow h
  obtain ⟨value, _, rfl⟩ := List.mem_map.mp h
  exact value.property

theorem handle_eq (execute : Interpreter World) (r : Result State World) (ev : Event) :
    handle (m := Id) execute r ev =
      if r.exiting then r
      else
        let next := batch execute r ev
        if next.1.exiting then next.1
        else next.2.foldl (handle (m := Id) execute) next.1 := by
  change (handle (m := Id) execute r ev).run = _
  rw [handle]
  split <;>
    simp_all only [Id.run_pure, Bool.not_eq_true, List.contains_eq_mem, decide_eq_true_eq,
      decide_true, decide_false, List.foldlM_subtype, Id.run_bind, batch, List.map_subtype,
      List.map_id_fun', id_eq]
  split <;>
    simp_all only [Id.run_pure, Result.mk.injEq, and_true, true_and, List.idRun_foldlM] <;> rfl

/-- Feedback-queue semantics: a batch stops at exit or an empty queue, and each event's feedback
runs before the remaining input. -/
inductive Execution (execute : Interpreter World) :
    Result State World → List Event → Result State World → Prop where
  | idle (r) : Execution execute r [] r
  | stopped (r) (events) : r.exiting = true → Execution execute r events r
  | next {r ev rest out} :
      r.exiting = false →
      Execution execute (batch execute r ev).1 ((batch execute r ev).2 ++ rest) out →
      Execution execute r (ev :: rest) out

theorem Execution.exited_eq {execute : Interpreter World} {r out : Result State World}
    {events : List Event} (h : Execution execute r events out) (hexit : r.exiting = true) :
    out = r := by
  cases h with
  | idle => rfl
  | stopped => rfl
  | next hfalse _ => simp_all

theorem Execution.append {execute : Interpreter World} {r mid out : Result State World}
    {first rest : List Event} (hfirst : Execution execute r first mid)
    (hrest : Execution execute mid rest out) : Execution execute r (first ++ rest) out := by
  induction hfirst with
  | idle => exact hrest
  | stopped r events hexit =>
    rw [hrest.exited_eq hexit]
    exact .stopped r _ hexit
  | next hactive _ ih =>
    apply Execution.next hactive
    simpa [List.append_assoc] using ih hrest

theorem foldl_execution (execute : Interpreter World) (events : List Event)
    (heach : ∀ ev ∈ events, ∀ r,
      Execution execute r [ev] (handle (m := Id) execute r ev)) (r : Result State World) :
    Execution execute r events (events.foldl (handle (m := Id) execute) r) := by
  induction events generalizing r with
  | nil => exact .idle r
  | cons ev rest ih =>
    have tail := ih (fun e he => heach e (by simp [he])) (handle (m := Id) execute r ev)
    simpa only [List.foldl_cons, List.singleton_append] using
      (heach ev (by simp) r).append tail

theorem handle_execution (execute : Interpreter World) (r : Result State World) (ev : Event) :
    Execution execute r [ev] (handle (m := Id) execute r ev) := by
  induction ev using (measure eventDepth).wf.induction generalizing r with
  | h ev ih =>
    rw [handle_eq]
    split
    · rename_i hexit
      exact .stopped r _ hexit
    · rename_i hactive
      have hfalse : r.exiting = false := by simpa using hactive
      apply Execution.next hfalse
      simp only [List.append_nil]
      split
      · rename_i hexit
        exact .stopped _ _ hexit
      · apply foldl_execution
        intro follow hf r'
        exact ih follow (batch_feedback_decreases execute r ev follow hf) r'

/-- Every finite input batch finishes the actual feedback-queue semantics.
This quantifies over every permitted pattern of operation failures. -/
theorem run_execution (execute : Interpreter World) (r : Result State World) (events : List Event) :
    Execution execute r events (run (m := Id) execute r events) := by
  induction events generalizing r with
  | nil => exact .idle r
  | cons ev rest ih =>
    change Execution execute r (ev :: rest) (run (m := Id) execute r (ev :: rest)).run
    simp only [run]
    split
    · rename_i hexit
      exact .stopped r _ hexit
    · have tail := ih (handle (m := Id) execute r ev)
      simpa only [bind, Id.run, List.singleton_append] using
        (handle_execution execute r ev).append tail

/-- Any invariant preserved by a session transition survives all automatically
generated feedback, for every permitted interpreter. -/
theorem Execution.preserves {execute : Interpreter World} {r out : Result State World}
    {events : List Event} (h : Execution execute r events out) (P : State → Prop)
    (hstep : ∀ st ev, P st → P (step st ev).1) (hstart : P r.st) : P out.st := by
  induction h with
  | idle => exact hstart
  | stopped => exact hstart
  | next _ _ ih => exact ih (hstep _ _ hstart)

/-- Client/parser bounds and live terminal structure survive complete batches,
including transport failures and failed checkpoint saves. -/
theorem run_safe (execute : Interpreter World) (r : Result State World) (events : List Event)
    (hwf : WF r.st) (hlive : LiveVt r.st) :
    WF (run (m := Id) execute r events).st ∧ LiveVt (run (m := Id) execute r events).st :=
  (run_execution execute r events).preserves (fun st => WF st ∧ LiveVt st)
    (fun st ev h => ⟨Session.step_wf st ev h.1, Session.step_vt_live st ev h.2⟩)
    ⟨hwf, hlive⟩

theorem feedback_step_no_exit (st : State) (ev : Event) (h : eventDepth ev < 2) :
    .exit ∉ (step st ev).2 := by
  cases ev with
  | closed id =>
    intro hexit
    rcases Session.closed_effects st id .exit hexit with h | h <;> cases h
  | checkpointFailed => simp [Session.checkpointFailed_effects]
  | _ => simp [eventDepth] at h

/-- Transport and persistence failure feedback cannot request daemon exit,
even when its own effects fail as well. -/
theorem handle_feedback_keeps_alive (execute : Interpreter World) (r : Result State World)
    (ev : Event) (hactive : r.exiting = false) (hdepth : eventDepth ev < 2) :
    (handle (m := Id) execute r ev).exiting = false := by
  induction ev using (measure eventDepth).wf.induction generalizing r with
  | h ev ih =>
    have hnext : (batch execute r ev).1.exiting = false := by
      simpa [batch] using feedback_step_no_exit r.st ev hdepth
    rw [handle_eq]
    simp only [hactive, Bool.false_eq_true, ↓reduceIte, hnext]
    apply List.foldlRecOn (motive := fun out : Result State World => out.exiting = false) _ _ hnext
    intro acc hacc follow hf
    have hlt := batch_feedback_decreases execute r ev follow hf
    exact ih follow hlt acc hacc (Nat.lt_trans hlt hdepth)

/-- Executing effects in order only adds feedback after what came before. -/
theorem foldl_feedback_prefix (execute : Interpreter World) (st : State)
    (effs : List (Effect Plan)) (acc : World × List Event) :
    acc.2 <+:
      (effs.foldl
          (fun (acc : World × List Event) eff =>
            let answer := execute st acc.1 eff
            (answer.1, acc.2 ++ feedback eff answer.2))
          acc).2 := by
  induction effs generalizing acc with
  | nil => exact List.prefix_refl _
  | cons eff rest ih =>
    rw [List.foldl_cons]
    exact
      (List.prefix_append acc.2 (feedback eff (execute st acc.1 eff).2)).trans
        (ih ((execute st acc.1 eff).1, acc.2 ++ feedback eff (execute st acc.1 eff).2))

/-- A stop of the program in a batch of effects feeds back how the program ended. -/
theorem foldl_feedback_stopped (execute : Interpreter World) (st : State)
    (effs : List (Effect Plan)) (stops : Effect.stopProgram ∈ effs) (acc : World × List Event) :
    ∃ o,
      Event.stopped o ∈
        (effs.foldl
            (fun (acc : World × List Event) eff =>
              let answer := execute st acc.1 eff
              (answer.1, acc.2 ++ feedback eff answer.2))
            acc).2 := by
  induction effs generalizing acc with
  | nil => simp at stops
  | cons eff rest ih =>
    rcases List.mem_cons.mp stops with rfl | later
    · refine ⟨(execute st acc.1 .stopProgram).2, ?_⟩
      apply (foldl_feedback_prefix execute st rest _).subset
      simp [feedback]
    · exact ih later _

/-- An event whose effects stop the program has the program's end among its feedback. -/
theorem batch_stopped (execute : Interpreter World) (r : Result State World) (ev : Event)
    (stops : Effect.stopProgram ∈ (step r.st ev).2) :
    ∃ o, Event.stopped o ∈ (batch execute r ev).2 := by
  have horder :=
    effects_in_order execute (step r.st ev).1 r.world (eventDepth ev) (step r.st ev).2
      (step_depth r.st ev)
  have hsnd := congrArg Prod.snd horder
  simp only at hsnd
  unfold batch
  simp only
  rw [hsnd]
  exact foldl_feedback_stopped execute _ _ stops _

/-- An exited driver handles nothing more. -/
theorem foldl_handle_exited (execute : Interpreter World) (events : List Event)
    (r : Result State World) (exited : r.exiting = true) :
    events.foldl (handle (m := Id) execute) r = r := by
  induction events with
  | nil => rfl
  | cons ev rest ih =>
    rw [List.foldl_cons, handle_eq]
    simpa [exited] using ih

/-- Once the program's end comes back from a stop, the session ends: the driver exits. -/
theorem handle_stopped_exits (execute : Interpreter World) (r : Result State World)
    (o : Session.Outcome) : (handle (m := Id) execute r (.stopped o)).exiting = true := by
  rw [handle_eq]
  split
  · assumption
  · have hexit : (batch execute r (.stopped o)).1.exiting = true := by
      simpa [batch] using (Session.step_exit_iff r.st (.stopped o)).mpr rfl
    simp [hexit]

/-- Handling events among which a stopped program's end is ends with the driver exited. -/
theorem foldl_handle_stopped (execute : Interpreter World) (events : List Event)
    (o : Session.Outcome) (told : Event.stopped o ∈ events) (r : Result State World) :
    (events.foldl (handle (m := Id) execute) r).exiting = true := by
  induction events generalizing r with
  | nil => simp at told
  | cons ev rest ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.mp told with rfl | later
    · rw [foldl_handle_exited execute rest _ (handle_stopped_exits execute r o)]
      exact handle_stopped_exits execute r o
    · exact ih later _

/-- **A stop ends the session**: once an event's effects stop the program, the driver hands the
program's end back to the session, which then ends, so the daemon never runs on past a kill. -/
theorem run_stop_exits (execute : Interpreter World) (r : Result State World) (ev : Event)
    (running : r.exiting = false) (stops : Effect.stopProgram ∈ (step r.st ev).2) :
    (run (m := Id) execute r [ev]).exiting = true := by
  have handled : (handle (m := Id) execute r ev).exiting = true := by
    rw [handle_eq]
    simp only [running, Bool.false_eq_true, ↓reduceIte]
    split
    · assumption
    · obtain ⟨o, told⟩ := batch_stopped execute r ev stops
      exact foldl_handle_stopped execute _ o told _
  simpa [run, running] using handled

theorem bind_total {α β ε : Type} (x : Except ε α) (f : α → Except ε β)
    (hx : ∃ a, x = .ok a) (hf : ∀ a, ∃ b, f a = .ok b) :
    ∃ b, x >>= f = .ok b := by
  obtain ⟨a, rfl⟩ := hx
  exact hf a

theorem foldlM_total {α β ε : Type} (xs : List α) (f : β → α → Except ε β)
    (htotal : ∀ acc x, x ∈ xs → ∃ out, f acc x = .ok out) (acc : β) :
    ∃ out, xs.foldlM f acc = .ok out := by
  induction xs generalizing acc with
  | nil => exact ⟨acc, rfl⟩
  | cons x xs ih =>
    obtain ⟨next, hn⟩ := htotal acc x (by simp)
    obtain ⟨out, ho⟩ := ih (fun acc y hy => htotal acc y (by simp [hy])) next
    exact ⟨out, by simpa only [List.foldlM_cons, hn, bind, Except.bind] using ho⟩

theorem foldlM_preserves {α β ε : Type} (xs : List α) (f : β → α → Except ε β)
    (P : β → Prop)
    (htotal : ∀ acc x, P acc → x ∈ xs → ∃ out, f acc x = .ok out ∧ P out)
    (acc : β) (hstart : P acc) : ∃ out, xs.foldlM f acc = .ok out ∧ P out := by
  induction xs generalizing acc with
  | nil => exact ⟨acc, rfl, hstart⟩
  | cons x xs ih =>
    obtain ⟨next, hn, hp⟩ := htotal acc x hstart (by simp)
    obtain ⟨out, ho, hout⟩ := ih (fun acc y hp hy => htotal acc y hp (by simp [hy])) next hp
    exact ⟨out, by simpa only [List.foldlM_cons, hn, bind, Except.bind] using ho, hout⟩

/-- The external contract (`Responds`, in `Linger/Session/WorldSpec.lean`) gives every primitive a
result, so the effects of one event complete. -/
theorem effects_no_error {ε : Type}
    (execute : State → World → (eff : Effect Plan) → Except ε (World × Reply eff))
    (hw : Responds execute) (st : State) (world : World) (depth : Nat) (effs : List (Effect Plan))
    (h : ∀ eff ∈ effs, effectDepth eff ≤ depth) :
    ∃ answer, effects execute st world depth effs h = .ok answer := by
  unfold effects
  apply bind_total
  · apply foldlM_total
    intro acc eff _
    apply bind_total
    · exact hw _ _ _
    · intro answer
      exact ⟨_, rfl⟩
  · intro answer
    exact ⟨_, rfl⟩

theorem handle_total {ε : Type}
    (execute : State → World → (eff : Effect Plan) → Except ε (World × Reply eff))
    (hw : Responds execute) (P : State → Prop)
    (hstep : ∀ st ev, P st → P (step st ev).1)
    (r : Result State World) (ev : Event) (hstart : P r.st) :
    ∃ out, handle execute r ev = .ok out ∧ P out.st := by
  induction ev using (measure eventDepth).wf.induction generalizing r with
  | h ev ih =>
    rw [handle]
    split
    · exact ⟨r, rfl, hstart⟩
    · obtain ⟨⟨world, more⟩, heffects⟩ :=
        effects_no_error execute hw (step r.st ev).1 r.world
          (eventDepth ev) (step r.st ev).2 (step_depth r.st ev)
      dsimp only
      rw [heffects]
      simp only [bind, Except.bind]
      split
      · exact ⟨_, rfl, hstep r.st ev hstart⟩
      · apply foldlM_preserves _ _ (fun out : Result State World => P out.st)
        · intro acc follow hacc _
          exact ih follow.val follow.property acc hacc
        · exact hstep r.st ev hstart

/-- Total correctness of the shared driver under the external response
contract: it returns successfully and preserves every transition invariant. -/
theorem run_total {ε : Type}
    (execute : State → World → (eff : Effect Plan) → Except ε (World × Reply eff))
    (hw : Responds execute) (P : State → Prop)
    (hstep : ∀ st ev, P st → P (step st ev).1)
    (r : Result State World) (events : List Event) (hstart : P r.st) :
    ∃ out, run execute r events = .ok out ∧ P out.st := by
  induction events generalizing r with
  | nil => exact ⟨r, rfl, hstart⟩
  | cons ev rest ih =>
    rw [run]
    split
    · exact ⟨r, rfl, hstart⟩
    · obtain ⟨next, hn, hp⟩ := handle_total execute hw P hstep r ev hstart
      obtain ⟨out, ho, hout⟩ := ih next hp
      exact ⟨out, by simpa only [hn, bind, Except.bind] using ho, hout⟩

/-- Under the primitive-response contract, every finite batch completes
without an uncaught modeled exception. No assumption on failure frequency,
client traffic, terminal bytes or event ordering is needed. -/
theorem run_no_error {ε : Type}
    (execute : State → World → (eff : Effect Plan) → Except ε (World × Reply eff))
    (hw : Responds execute) (r : Result State World) (events : List Event) :
    ∃ out, run execute r events = .ok out := by
  obtain ⟨out, ho, _⟩ := run_total execute hw (fun _ => True) (by simp) r events True.intro
  exact ⟨out, ho⟩

/-- Finite batches return without modeled exceptions and retain the session
bounds and renderable terminal, including all permitted failure feedback. -/
theorem run_total_safe {ε : Type}
    (execute : State → World → (eff : Effect Plan) → Except ε (World × Reply eff))
    (hw : Responds execute) (r : Result State World) (events : List Event)
    (hwf : WF r.st) (hlive : LiveVt r.st) :
    ∃ out, run execute r events = .ok out ∧ WF out.st ∧ LiveVt out.st :=
  run_total execute hw (fun st => WF st ∧ LiveVt st)
    (fun st ev h => ⟨Session.step_wf st ev h.1, Session.step_vt_live st ev h.2⟩)
    r events ⟨hwf, hlive⟩

/-- No queued event or external effect is consumed after exit. This identity
holds for the shared driver in every monad, including the daemon's interpreter. -/
theorem run_exited {m : Type → Type} [Monad m]
    (execute : State → World → (eff : Effect Plan) → m (World × Reply eff))
    (r : Result State World) (events : List Event) (h : r.exiting = true) :
    run execute r events = pure r := by
  cases events <;> simp [run, h]

/-- **Disconnects and failed saves never stop the daemon**: handling a batch of them keeps it
running, whatever the interpreter reports about their own effects. -/
theorem run_feedback_alive (execute : Interpreter World) (r : Result State World)
    (events : List Event) (running : r.exiting = false)
    (failures : ∀ ev ∈ events, ev = .checkpointFailed ∨ ∃ id, ev = .closed id) :
    (run (m := Id) execute r events).exiting = false := by
  induction events generalizing r with
  | nil => exact running
  | cons ev rest ih =>
    have hdepth : eventDepth ev < 2 := by
      rcases failures ev (by simp) with rfl | ⟨id, rfl⟩ <;> simp [eventDepth]
    have hnext := handle_feedback_keeps_alive execute r ev running hdepth
    have hrest :=
      ih (handle (m := Id) execute r ev) hnext (fun e he => failures e (List.mem_cons_of_mem ev he))
    simp only [run, running, Bool.false_eq_true, ↓reduceIte]
    exact hrest

/-! ## Succeeding effects

When every effect succeeds, the only feedback is a stop's reply, how the program ended: the driver
hands the session exactly the events `Handles` describes and executes exactly the effects of their
trace, in order, each with the state its event left. This pins `run` to `Session.trace step` for
`Challenge.lean`. -/

/-- `Handles` leaves no choice: from a state, the events given decide the events handled and the
exit flag. -/
theorem handles_unique {S : Type} {step : S → Event → S × List (Effect Plan)}
    {ending : Session.Outcome} {s : S} {events handled handled' : List Event} {exits exits' : Bool}
    (h : Handles step ending s events handled exits)
    (h' : Handles step ending s events handled' exits') : handled = handled' ∧ exits = exits' := by
  induction h generalizing handled' exits' with
  | done =>
    cases h'
    exact ⟨rfl, rfl⟩
  | exit _ _ _ asks =>
    cases h' with
    | exit => exact ⟨rfl, rfl⟩
    | next _ _ _ _ _ stays => exact absurd asks stays
  | next _ _ _ _ _ stays _ ih =>
    cases h' with
    | exit _ _ _ asks => exact absurd asks stays
    | next _ _ _ _ _ _ later =>
      obtain ⟨rfl, rfl⟩ := ih later
      exact ⟨rfl, rfl⟩

/-- A succeeding effect feeds back what `fedBack` says: a stop's reply as the program's end, and
nothing else. -/
theorem feedback_success (ending : Session.Outcome) (eff : Effect Plan) :
    feedback eff (success ending eff) = fedBack ending eff := by
  cases eff <;> rfl

/-- Executing effects that succeed threads the world through each in order and collects what each
feeds back, in order. -/
theorem foldl_success (execute : Interpreter World) (ending : Session.Outcome)
    (succeeds : ∀ st w eff, (execute st w eff).2 = success ending eff) (st : State)
    (effs : List (Effect Plan)) (acc : World × List Event) :
    effs.foldl
        (fun (acc : World × List Event) eff =>
          ((execute st acc.1 eff).1, acc.2 ++ feedback eff (execute st acc.1 eff).2))
        acc =
      (effs.foldl (fun world eff => (execute st world eff).1) acc.1,
        acc.2 ++ effs.flatMap (fedBack ending)) := by
  induction effs generalizing acc with
  | nil => simp
  | cons eff rest ih =>
    rw [List.foldl_cons, ih]
    simp [succeeds, feedback_success, List.append_assoc]

/-- With succeeding effects, one event's batch is the session's step: its state and exit flag are
the step's, its world is the world after executing the step's effects in order with the state the
step left, and its feedback is what those effects feed back. -/
theorem batch_success (execute : Interpreter World) (ending : Session.Outcome)
    (succeeds : ∀ st w eff, (execute st w eff).2 = success ending eff) (r : Result State World)
    (ev : Event) :
    (batch execute r ev).1.st = (step r.st ev).1 ∧
      (batch execute r ev).1.world =
        (withState step r.st ev).2.foldl
          (fun world (asked : State × Effect Plan) => (execute asked.1 world asked.2).1) r.world ∧
      (batch execute r ev).1.exiting = (step r.st ev).2.contains .exit ∧
      (batch execute r ev).2 = (step r.st ev).2.flatMap (fedBack ending) := by
  have horder :=
    effects_in_order execute (step r.st ev).1 r.world (eventDepth ev) (step r.st ev).2
      (step_depth r.st ev)
  simp only at horder
  rw [foldl_success execute ending succeeds] at horder
  have hworld := congrArg Prod.fst horder
  have hfeed := congrArg Prod.snd horder
  simp only at hworld hfeed
  refine ⟨rfl, ?_, rfl, ?_⟩
  · unfold batch
    simp only [withState, List.foldl_map]
    exact hworld
  · unfold batch
    simpa using hfeed

/-- With succeeding effects, an execution from an active driver ends where the trace of the events
`Handles` describes ends, with the world its effects leave and the exit flag `Handles` gives. -/
theorem execution_refines {execute : Interpreter World} {ending : Session.Outcome}
    (succeeds : ∀ st w eff, (execute st w eff).2 = success ending eff) {r out : Result State World}
    {events : List Event} (h : Execution execute r events out) (running : r.exiting = false) :
    ∃ handled exits,
      Handles step ending r.st events handled exits ∧
        out.st = (Session.trace step r.st handled).1 ∧
        out.world =
          (Session.trace (withState step) r.st handled).2.foldl
            (fun world (asked : State × Effect Plan) => (execute asked.1 world asked.2).1)
            r.world ∧
        out.exiting = exits := by
  induction h with
  | idle r => exact ⟨[], false, .done _, rfl, rfl, running⟩
  | stopped r events hexit => simp_all
  | @next r ev rest out hactive hrest ih =>
    obtain ⟨hst, hworld, hexits, hfeed⟩ := batch_success execute ending succeeds r ev
    by_cases asks : Effect.exit ∈ (step r.st ev).2
    · have hexit : (batch execute r ev).1.exiting = true := by
        rw [hexits]
        exact List.contains_iff_mem.mpr asks
      rw [hrest.exited_eq hexit]
      refine ⟨[ev], true, .exit _ _ _ asks, ?_, ?_, hexit⟩
      · simp [Session.trace, hst]
      · simp [Session.trace, hworld]
    · have hexit : (batch execute r ev).1.exiting = false := by
        rw [hexits]
        simpa using asks
      obtain ⟨handled, exits, hh, hout, hw, hx⟩ := ih hexit
      rw [hfeed, hst] at hh
      refine ⟨ev :: handled, exits, .next _ _ _ _ _ asks hh, ?_, ?_, hx⟩
      · rw [hout, hst]
        rfl
      · rw [hw, hst, hworld]
        simp only [Session.trace, List.foldl_append]
        rfl

/-- **With every effect succeeding, the driver runs the session's trace**: from an active driver,
it hands the session the events `Handles` describes, the events and what their effects feed back,
ends in the state of their trace through `step` and in the world the trace's effects give when
executed in order, each with the state its event left, and exits exactly when one of them asked it
to. -/
theorem run_refines (execute : State → World → (eff : Effect Plan) → Id (World × Reply eff))
    (ending : Session.Outcome) (succeeds : ∀ st w eff, (execute st w eff).2 = success ending eff)
    (r : Result State World) (events : List Event) (running : r.exiting = false) :
    ∃ handled exits,
      Handles step ending r.st events handled exits ∧
        (run execute r events).st = (Session.trace step r.st handled).1 ∧
        (run execute r events).world =
          (Session.trace (withState step) r.st handled).2.foldl
            (fun world (asked : State × Effect Plan) => (execute asked.1 world asked.2).1)
            r.world ∧
        (run execute r events).exiting = exits :=
  execution_refines (execute := execute) succeeds (run_execution execute r events) running

end Linger.Session.Driver
