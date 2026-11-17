module

public import Linger.Session.CoreSpec
import all Linger.Session.CoreCode

/-! # A daemon's off-loop writes coalesce, and the latest one reaches the disk

Writes of one kind run one at a time (`Offloop.ask`, `Offloop.done`): a write starts only when
none runs, so the writes started outnumber the writes that ended by at most the one running, and
the latest write asked for is the last to start, at once or as soon as the running one ends. -/

namespace Linger.Session

/-- One if a write runs, else none. -/
def runs {W : Type} (o : Offloop W W) : Nat := if o.running.isSome then 1 else 0

theorem cycle_started {W : Type} (o : Offloop W W × List W) (op : Offloop.Op W) (k : Nat)
    (h : o.2.length ≤ k + runs o.1) :
    (Offloop.cycle Offloop.ask Offloop.done o op).2.length ≤
      k + (if op.isDone then 1 else 0) + runs (Offloop.cycle Offloop.ask Offloop.done o op).1 := by
  obtain ⟨s, started⟩ := o
  cases op with
  | ask w =>
    by_cases r : s.running.isSome
    · simp_all [Offloop.cycle, Offloop.ask, Offloop.Op.isDone, runs]
    · simp_all [Offloop.cycle, Offloop.ask, Offloop.Op.isDone, runs]
  | done =>
    cases hw : s.waiting <;>
      simp [Offloop.cycle, Offloop.done, hw, Offloop.Op.isDone, runs] at h ⊢ <;>
      split at h <;>
      omega

theorem foldl_started {W : Type} (ops : List (Offloop.Op W)) (o : Offloop W W × List W) (k : Nat)
    (h : o.2.length ≤ k + runs o.1) :
    (ops.foldl (Offloop.cycle Offloop.ask Offloop.done) o).2.length ≤
      k + (ops.filter Offloop.Op.isDone).length +
        runs (ops.foldl (Offloop.cycle Offloop.ask Offloop.done) o).1 := by
  induction ops generalizing o k with
  | nil => simpa using h
  | cons op rest ih =>
    have := ih _ _ (cycle_started o op k h)
    cases hd : op.isDone <;> simp [hd] at this ⊢ <;> omega

/-- **Writes never queue**: each write started but the first follows the end of one that ran. -/
theorem Offloop.started_bound {W : Type} (ops : List (Offloop.Op W)) :
    (ops.foldl (Offloop.cycle Offloop.ask Offloop.done) ({}, [])).2.length ≤
      (ops.filter Offloop.Op.isDone).length + 1 := by
  have := foldl_started ops ({}, []) 0 (by simp [runs])
  have : runs (ops.foldl (Offloop.cycle Offloop.ask Offloop.done) ({}, [])).1 ≤ 1 := by
    unfold runs; split <;> omega
  omega

/-- A write waits only while another runs. -/
theorem foldl_steady {W : Type} (ops : List (Offloop.Op W)) (o : Offloop W W × List W)
    (h : o.1.waiting.isSome → o.1.running.isSome) :
    (ops.foldl (Offloop.cycle Offloop.ask Offloop.done) o).1.waiting.isSome →
      (ops.foldl (Offloop.cycle Offloop.ask Offloop.done) o).1.running.isSome := by
  induction ops generalizing o with
  | nil => exact h
  | cons op rest ih =>
    apply ih
    obtain ⟨s, started⟩ := o
    cases op with
    | ask w => by_cases r : s.running.isSome <;> simp_all [Offloop.cycle, Offloop.ask]
    | done => cases hw : s.waiting <;> simp [Offloop.cycle, Offloop.done, hw]

/-- Ends heard while no write waits start nothing. -/
theorem foldl_ends {W : Type} (n : Nat) (o : Offloop W W × List W) (h : o.1.waiting = none) :
    ((List.replicate n (Offloop.Op.done : Offloop.Op W)).foldl
          (Offloop.cycle Offloop.ask Offloop.done) o).2 =
      o.2 := by
  induction n generalizing o with
  | zero => rfl
  | succ n ih =>
    obtain ⟨s, started⟩ := o
    rw [List.replicate_succ, List.foldl_cons]
    have : Offloop.cycle Offloop.ask Offloop.done (s, started) .done = ({}, started) := by
      simp only at h
      simp [Offloop.cycle, Offloop.done, h]
    rw [this, ih _ rfl]

/-- **The latest write reaches the disk**: the last write asked for is the last to start, or, while
the one before it still runs, the one that waits to start. -/
theorem Offloop.latest_started {W : Type} (earlier : List (Offloop.Op W)) (w : W) (ends : Nat) :
    ((earlier ++ (.ask w : Offloop.Op W) :: List.replicate ends .done).foldl
            (Offloop.cycle Offloop.ask Offloop.done) ({}, [])).2.getLast? =
        some w ∨
      ends = 0 ∧
        ((earlier ++ (.ask w : Offloop.Op W) :: List.replicate ends .done).foldl
              (Offloop.cycle Offloop.ask Offloop.done) ({}, [])).1.waiting =
          some w := by
  rw [List.foldl_append, List.foldl_cons]
  have steady := foldl_steady earlier ({}, []) (by simp)
  generalize earlier.foldl (Offloop.cycle Offloop.ask Offloop.done) ({}, []) = o at steady
  obtain ⟨s, started⟩ := o
  by_cases r : s.running.isSome
  · have asked :
      Offloop.cycle Offloop.ask Offloop.done (s, started) (.ask w) =
        ({ s with waiting := some w }, started) := by
      simp [Offloop.cycle, Offloop.ask, r]
    rw [asked]
    cases ends with
    | zero => exact .inr ⟨rfl, rfl⟩
    | succ n =>
      left
      rw [List.replicate_succ, List.foldl_cons]
      have ended :
        Offloop.cycle Offloop.ask Offloop.done ({ s with waiting := some w }, started) .done =
          ({ running := some w }, started ++ [w]) := by
        simp [Offloop.cycle, Offloop.done]
      rw [ended, foldl_ends n _ rfl]
      simp
  · have idle : s.waiting = none := by
      cases hw : s.waiting
      · rfl
      · simp_all
    have asked :
      Offloop.cycle Offloop.ask Offloop.done (s, started) (.ask w) =
        ({ s with running := some w }, started ++ [w]) := by
      simp [Offloop.cycle, Offloop.ask, r]
    rw [asked, foldl_ends ends _ idle]
    simp

end Linger.Session
