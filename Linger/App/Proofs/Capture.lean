module

public import Linger.App.CoreSpec
import all Linger.App.CoreCode.Capture

/-! # What `capture` of a saved session waits on while it holds the name

It loads, renders and writes, in that order; it loads holding the name's locks; and no step it
takes holding them waits on a party outside linger. -/

namespace Linger.App.Capture

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
