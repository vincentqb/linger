module

public import Fuzzy
import all Fuzzy.Proofs

/-! The fuzzy matcher's headline theorems, proved of the matcher: `lake comparator` checks that
these are exactly the statements of `FuzzyChallenge.lean`. -/

public section

namespace Fuzzy

theorem align_exact (query target : String) :
    ((Fuzzy.align query target).isSome = true ↔
        (query.toList.map Char.toLower).Sublist (target.toList.map Char.toLower)) ∧
      ∀ a,
        Fuzzy.align query target = some a →
          a.marks.length = target.length ∧
            ((target.toList.zip a.marks).filterMap fun (c, marked) =>
                if marked then some c.toLower else none) =
              query.toList.map Char.toLower :=
  ⟨Fuzzy.align_isSome_iff_sublist query target, fun a found =>
    ⟨Fuzzy.align_marks_length query target a found, Fuzzy.align_spells query target a found⟩⟩

theorem align_exact_rejects_none :
    ¬∀ (query target : String),
        (((fun (_ _ : String) => (none : Option Fuzzy.Alignment)) query target).isSome = true ↔
            (query.toList.map Char.toLower).Sublist (target.toList.map Char.toLower)) ∧
          ∀ a,
            (fun (_ _ : String) => (none : Option Fuzzy.Alignment)) query target = some a →
              a.marks.length = target.length ∧
                ((target.toList.zip a.marks).filterMap fun (c, marked) =>
                    if marked then some c.toLower else none) =
                  query.toList.map Char.toLower := by
  intro h
  exact absurd ((h "" "").1.mpr (by simp)) (by simp)

end Fuzzy
