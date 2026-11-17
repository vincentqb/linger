module

import all Linger.App.CoreCode.Fields
public import Linger.Display.CoreSpec

/-! # Every field has one owner and each owner's fields one role -/

namespace Linger.App.Fields

/-- Each field is listed once. -/
theorem keys_nodup : (table.map (·.key)).Nodup := by decide

/-- Every field a human row reads has its kind and owner. -/
theorem sources_listed : ∀ key ∈ Linger.Display.Listing.sources, key ∈ table.map (·.key) := by
  decide

/-- A field is human exactly when a human row prints it. -/
theorem kind_shown : ∀ f ∈ table, (f.kind = .human ↔ f.key ∈ Linger.Display.Listing.shown) := by
  decide

/-- A field the user owns has one command that writes it, which writes no other field. -/
theorem user_one_writer :
    ∀ f ∈ table,
      ∀ op,
        f.owner = .user op → op ∈ Commands.Op.all ∧ ∀ g ∈ table, g.owner = .user op → g = f := by
  intro f hf op hop
  simp only [table, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Owner.user.injEq, reduceCtorEq] at hop
  subst hop
  refine ⟨by decide, fun g hg hown => ?_⟩
  simp only [table, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all

/-- Distinct images make a map injective on its list. -/
theorem inj_of_nodup {α β : Type} (f : α → β) :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {a b : α}, a ∈ l → b ∈ l → f a = f b → a = b
  | [], _, _, _, ha, _, _ => absurd ha List.not_mem_nil
  | x :: xs, h, a, b, ha, hb, hab => by
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · rfl
    · exact
        absurd
          (by
            rw [hab]; exact List.mem_map_of_mem hb')
          h.1
    · exact
        absurd
          (by
            rw [← hab]; exact List.mem_map_of_mem ha')
          h.1
    · exact inj_of_nodup f h.2 ha' hb' hab

/-- No two fields tell the same thing. -/
theorem roles_nodup : (table.map (·.role)).Nodup := by decide

/-- No two fields of one owner tell the same thing. -/
theorem roles_distinct : ∀ f ∈ table, ∀ g ∈ table, f.owner = g.owner → f.role = g.role → f = g :=
  fun _ hf _ hg _ hr => inj_of_nodup (·.role) roles_nodup hf hg hr

end Linger.App.Fields
