module

public import Linger.App.CoreSpec
import all Linger.App.CoreCode.Capture

/-! # What `capture` of a saved session waits on while it holds the name

The shell runs each step holding the name's locks exactly when `work` says it does, whatever the
plan; and the plan loads, renders and writes, in that order, loads holding the locks, and takes
no step holding them that waits on a party outside linger. -/

namespace Linger.App.Capture

/-- The phases run what `work` reads, from any steps gathered since an unmatched `acquire`. -/
theorem phasesFrom_work (held : Option (List Step)) (steps : List Step) :
    (phasesFrom held steps).flatMap Phase.work =
      ((held.map fun inside => inside.map (·, true)).getD []) ++ work steps held.isSome := by
  induction steps generalizing held with
  | nil => cases held <;> simp [phasesFrom, work, Phase.work]
  | cons step rest ih => cases step <;> cases held <;> simp [phasesFrom, work, Phase.work, ih]

/-- **The shell holds the locks exactly where `work` says.** -/
theorem phases_work (steps : List Step) : (phases steps).flatMap Phase.work = work steps false := by
  simpa [phases] using phasesFrom_work none steps

/-- **The locks are let go before the write.** -/
theorem waits_unlocked :
    (work plan false).map Prod.fst = [.load, .render, .write] ∧
      (.load, true) ∈ work plan false ∧
      ∀ step, (step, true) ∈ work plan false → step.waitsOutside = false := by
  refine ⟨by decide, by decide, fun step held => ?_⟩
  simp only [plan, work, List.mem_cons, Prod.mk.injEq, List.not_mem_nil] at held
  rcases held with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨-, h⟩ | h
  · rfl
  · rfl
  · cases h
  · exact h.elim

end Linger.App.Capture
