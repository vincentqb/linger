module

import all Linger.Core.Driver
import all Theorems.Session

/-! The effect interpreter is an arbitrary total function on an abstract world.
Its replies are constrained by the same dependent type the daemon implements.
The execution relation below describes the feedback queue independently of the
driver's recursive traversal: finishing means an empty queue or explicit exit.

The model assumes each primitive returns and has the meaning of its typed reply.
It does not assume that writes or checkpoint saves succeed. -/

namespace Linger.Core.Driver

open Linger.Core.Session (State Event Effect step WF LiveVt)
variable {World : Type}

/-- A total effect interpreter over an abstract world, with typed replies. -/
abbrev Interpreter (World : Type) := State → World → (eff : Effect) → World × Reply eff

/-- Erasing the termination witnesses gives ordinary left-to-right effect
execution and FIFO feedback. Reversing either order changes this equation. -/
theorem effects_in_order (execute : Interpreter World) (st : State) (world : World) (depth : Nat)
    (effs : List Effect) (h : ∀ eff ∈ effs, effectDepth eff ≤ depth) :
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
def batch (execute : Interpreter World) (r : Result World) (ev : Event) :
    Result World × List Event :=
  let stepped := step r.st ev
  let answered :=
    effects (m := Id) execute stepped.1 r.world (eventDepth ev) stepped.2 (step_depth r.st ev)
  ({ st := stepped.1, world := answered.1, exiting := stepped.2.contains .exit },
    answered.2.map Subtype.val)

theorem feedback_strictly_decreases (eff : Effect) (reply : Reply eff)
    (ev : Event) (h : ev ∈ feedback eff reply) : eventDepth ev < effectDepth eff :=
  feedback_depth eff reply ev h

theorem batch_feedback_decreases (execute : Interpreter World) (r : Result World) (ev : Event) :
    ∀ follow ∈ (batch execute r ev).2, eventDepth follow < eventDepth ev := by
  intro follow h
  obtain ⟨value, _, rfl⟩ := List.mem_map.mp h
  exact value.property

theorem handle_eq (execute : Interpreter World) (r : Result World) (ev : Event) :
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
    Result World → List Event → Result World → Prop where
  | idle (r) : Execution execute r [] r
  | stopped (r) (events) : r.exiting = true → Execution execute r events r
  | next {r ev rest out} :
      r.exiting = false →
      Execution execute (batch execute r ev).1 ((batch execute r ev).2 ++ rest) out →
      Execution execute r (ev :: rest) out

theorem Execution.exited_eq {execute : Interpreter World} {r out : Result World}
    {events : List Event} (h : Execution execute r events out) (hexit : r.exiting = true) :
    out = r := by
  cases h with
  | idle => rfl
  | stopped => rfl
  | next hfalse _ => simp_all

theorem Execution.append {execute : Interpreter World} {r mid out : Result World}
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
      Execution execute r [ev] (handle (m := Id) execute r ev)) (r : Result World) :
    Execution execute r events (events.foldl (handle (m := Id) execute) r) := by
  induction events generalizing r with
  | nil => exact .idle r
  | cons ev rest ih =>
    have tail := ih (fun e he => heach e (by simp [he])) (handle (m := Id) execute r ev)
    simpa only [List.foldl_cons, List.singleton_append] using
      (heach ev (by simp) r).append tail

theorem handle_execution (execute : Interpreter World) (r : Result World) (ev : Event) :
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
theorem run_execution (execute : Interpreter World) (r : Result World) (events : List Event) :
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
theorem Execution.preserves {execute : Interpreter World} {r out : Result World}
    {events : List Event} (h : Execution execute r events out) (P : State → Prop)
    (hstep : ∀ st ev, P st → P (step st ev).1) (hstart : P r.st) : P out.st := by
  induction h with
  | idle => exact hstart
  | stopped => exact hstart
  | next _ _ ih => exact ih (hstep _ _ hstart)

/-- Client/parser bounds and live terminal structure survive complete batches,
including transport failures and failed checkpoint saves. -/
theorem run_safe (execute : Interpreter World) (r : Result World) (events : List Event)
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
    have impossible := Session.closed_effects st id .exit hexit
    cases impossible
  | checkpointFailed => simp [Session.checkpointFailed_effects]
  | _ => simp [eventDepth] at h

/-- Transport and persistence failure feedback cannot request daemon exit,
even when its own effects fail as well. -/
theorem handle_feedback_keeps_alive (execute : Interpreter World) (r : Result World)
    (ev : Event) (hactive : r.exiting = false) (hdepth : eventDepth ev < 2) :
    (handle (m := Id) execute r ev).exiting = false := by
  induction ev using (measure eventDepth).wf.induction generalizing r with
  | h ev ih =>
    have hnext : (batch execute r ev).1.exiting = false := by
      simpa [batch] using feedback_step_no_exit r.st ev hdepth
    rw [handle_eq]
    simp only [hactive, Bool.false_eq_true, ↓reduceIte, hnext]
    apply List.foldlRecOn (motive := fun out : Result World => out.exiting = false) _ _ hnext
    intro acc hacc follow hf
    have hlt := batch_feedback_decreases execute r ev follow hf
    exact ih follow hlt acc hacc (Nat.lt_trans hlt hdepth)

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

/-- The external contract excludes unreported exceptions; it permits every
disconnect/checkpoint-failure result. This is a premise about primitive
execution, not an assumption that the event driver succeeds. -/
def Responds {ε : Type}
    (execute : State → World → (eff : Effect) → Except ε (World × Reply eff)) : Prop :=
  ∀ st world eff, ∃ answer, execute st world eff = .ok answer

theorem effects_no_error {ε : Type}
    (execute : State → World → (eff : Effect) → Except ε (World × Reply eff))
    (hw : Responds execute) (st : State) (world : World) (depth : Nat) (effs : List Effect)
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
    (execute : State → World → (eff : Effect) → Except ε (World × Reply eff))
    (hw : Responds execute) (P : State → Prop)
    (hstep : ∀ st ev, P st → P (step st ev).1)
    (r : Result World) (ev : Event) (hstart : P r.st) :
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
      · apply foldlM_preserves _ _ (fun out : Result World => P out.st)
        · intro acc follow hacc _
          exact ih follow.val follow.property acc hacc
        · exact hstep r.st ev hstart

/-- Total correctness of the shared driver under the external response
contract: it returns successfully and preserves every transition invariant. -/
theorem run_total {ε : Type}
    (execute : State → World → (eff : Effect) → Except ε (World × Reply eff))
    (hw : Responds execute) (P : State → Prop)
    (hstep : ∀ st ev, P st → P (step st ev).1)
    (r : Result World) (events : List Event) (hstart : P r.st) :
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
    (execute : State → World → (eff : Effect) → Except ε (World × Reply eff))
    (hw : Responds execute) (r : Result World) (events : List Event) :
    ∃ out, run execute r events = .ok out := by
  obtain ⟨out, ho, _⟩ := run_total execute hw (fun _ => True) (by simp) r events True.intro
  exact ⟨out, ho⟩

/-- Finite batches return without modeled exceptions and retain the session
bounds and renderable terminal, including all permitted failure feedback. -/
theorem run_total_safe {ε : Type}
    (execute : State → World → (eff : Effect) → Except ε (World × Reply eff))
    (hw : Responds execute) (r : Result World) (events : List Event)
    (hwf : WF r.st) (hlive : LiveVt r.st) :
    ∃ out, run execute r events = .ok out ∧ WF out.st ∧ LiveVt out.st :=
  run_total execute hw (fun st => WF st ∧ LiveVt st)
    (fun st ev h => ⟨Session.step_wf st ev h.1, Session.step_vt_live st ev h.2⟩)
    r events ⟨hwf, hlive⟩

/-- No queued event or external effect is consumed after exit. This identity
holds for the shared driver in every monad, including the daemon's interpreter. -/
theorem run_exited {m : Type → Type} [Monad m]
    (execute : State → World → (eff : Effect) → m (World × Reply eff))
    (r : Result World) (events : List Event) (h : r.exiting = true) :
    run execute r events = pure r := by
  cases events <;> simp [run, h]

end Linger.Core.Driver
