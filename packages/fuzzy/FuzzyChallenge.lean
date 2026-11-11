module

public import Fuzzy.Spec

/-! # Headline theorems of the fuzzy matcher

What interactive selection's matcher must do: match a target exactly when the query's
characters, case folded, appear in it in order, and highlight characters that spell the query.
The theorem is stated over the matcher, declared below as a hole: `sorry` here, which the
package's code supplies, and `Fuzzy.Solution` proves the same statement
of it. -/

public section

/-- The selector's fuzzy match of a query against a target, if there is one. -/
@[expose]
def Fuzzy.align : String → String → Option Fuzzy.Alignment := sorry

namespace Fuzzy

/-- A target matches the selector's query exactly when the query's characters, case folded, appear
in it in order, and the characters the selector highlights spell the query, one mark per target
character. -/
theorem align_exact (query target : String) :
    ((Fuzzy.align query target).isSome = true ↔
        (query.toList.map Char.toLower).Sublist (target.toList.map Char.toLower)) ∧
      ∀ a,
        Fuzzy.align query target = some a →
          a.marks.length = target.length ∧
            ((target.toList.zip a.marks).filterMap fun (c, marked) =>
                if marked then some c.toLower else none) =
              query.toList.map Char.toLower := by
  sorry

/-- `align_exact` rejects a matcher that matches nothing. -/
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
  sorry

end Fuzzy
