module

public import Fuzzy.CoreSpec
meta import SoftwareChallenge

/-! # Headline theorems of the fuzzy matcher

What interactive selection's matcher must do: match a target exactly when the query's
characters, case folded, appear in it in order, and highlight characters that spell the query.
The theorem is stated over the matcher, declared below as a hole: `sorry` here, which the
package's code supplies, and `Fuzzy.Solution` proves the same statement
of it. -/

public section

def Fuzzy.align : String → String → Option Fuzzy.Alignment := sorry

namespace Fuzzy

theorem align_exact (query target : String) :
    ((Fuzzy.align query target).isSome = true ↔
        (query.toList.map Char.toLower).Sublist (target.toList.map Char.toLower)) ∧
      ∀ a,
        Fuzzy.align query target = some a →
          a.marks.length = target.length ∧
            ((target.toList.zip a.marks).filterMap fun p =>
                if p.2 then some p.1.toLower else none) =
              query.toList.map Char.toLower := by
  sorry

@[kills align_exact]
theorem align_exact_rejects_none :
    ¬∀ (query target : String),
        (((fun (_ _ : String) => (none : Option Fuzzy.Alignment)) query target).isSome = true ↔
            (query.toList.map Char.toLower).Sublist (target.toList.map Char.toLower)) ∧
          ∀ a,
            (fun (_ _ : String) => (none : Option Fuzzy.Alignment)) query target = some a →
              a.marks.length = target.length ∧
                ((target.toList.zip a.marks).filterMap fun p =>
                    if p.2 then some p.1.toLower else none) =
                  query.toList.map Char.toLower := by
  sorry

end Fuzzy
