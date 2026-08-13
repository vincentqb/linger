import Zmx.Core.Status
/-! # §Status — the seven states partition the observation space

A legend is a claim, and it can be wrong in three ways: two rows that differ
could show the same glyph (not exclusive), a row could match no glyph (not
covering), or a glyph could be unreachable (a lie in the legend). This file
rules out all three.

The predicates below are the states as *described in the legend*, written
independently of `classify`'s cascade — that independence is the point. If
they were the cascade's guards with the earlier branches negated, cover and
disjointness would be tautologies and the theorems would say nothing. As
written, `classify_sound` is a real claim: the cascade computes the
description.
-/

namespace Zmx.Core.Status

/-- The legend, as predicates on an observation. -/
def Is : Status → Obs → Prop
  | .unknown, o => o.known = false
  | .exitedOk, o => o.known = true ∧ o.exit = some 0
  | .exitedBad, o => o.known = true ∧ ∃ n, o.exit = some n ∧ n ≠ 0
  | .resumable, o => o.known = true ∧ o.exit = none ∧ o.daemonUp = false
  | .working, o => o.known = true ∧ o.exit = none ∧ o.daemonUp = true
      ∧ o.fresh = true
  | .wantsYou, o => o.known = true ∧ o.exit = none ∧ o.daemonUp = true
      ∧ o.fresh = false ∧ o.unseen = true
  | .idle, o => o.known = true ∧ o.exit = none ∧ o.daemonUp = true
      ∧ o.fresh = false ∧ o.unseen = false

/-- All seven states, for the quantifiers below. -/
def all : List Status :=
  [.unknown, .exitedBad, .exitedOk, .resumable, .wantsYou, .working, .idle]

theorem mem_all (s : Status) : s ∈ all := by cases s <;> simp [all]

/-- **Cover.** Every observation is in some state — no row can fail to be
described. -/
theorem cover (o : Obs) : ∃ s, Is s o := by
  by_cases hk : o.known = true
  · match hex : o.exit with
    | some 0 => exact ⟨.exitedOk, hk, hex⟩
    | some (n + 1) => exact ⟨.exitedBad, hk, ⟨n + 1, hex, by omega⟩⟩
    | none =>
      by_cases hd : o.daemonUp = true
      · by_cases hf : o.fresh = true
        · exact ⟨.working, hk, hex, hd, hf⟩
        · by_cases hu : o.unseen = true
          · exact ⟨.wantsYou, hk, hex, hd, by simpa using hf, hu⟩
          · exact ⟨.idle, hk, hex, hd, by simpa using hf, by simpa using hu⟩
      · exact ⟨.resumable, hk, hex, by simpa using hd⟩
  · exact ⟨.unknown, show o.known = false from by simpa using hk⟩

/-- **Disjoint.** No observation is in two states — two rows showing the
same glyph really are in the same state. -/
theorem disjoint (o : Obs) (s t : Status) (hs : Is s o) (ht : Is t o) : s = t := by
  cases s <;> cases t <;> simp only [Is] at hs ht <;>
    first
      | rfl
      | (exfalso
         obtain _ := hs
         obtain _ := ht
         simp_all)

/-- **Sound.** The cascade computes the legend: what `classify` returns is
the state the row is actually in. This is the claim that would break if a
guard were mis-ordered. -/
theorem classify_sound (o : Obs) : Is (classify o) o := by
  unfold classify
  by_cases hk : o.known = true
  · rw [if_neg (by simp [hk])]
    match hex : o.exit with
    | some 0 => exact ⟨hk, hex⟩
    | some (n + 1) => exact ⟨hk, ⟨n + 1, hex, by omega⟩⟩
    | none =>
      by_cases hd : o.daemonUp = true
      · rw [if_neg (by simp [hd])]
        by_cases hf : o.fresh = true
        · rw [if_pos hf]; exact ⟨hk, hex, hd, hf⟩
        · rw [if_neg (by simpa using hf)]
          by_cases hu : o.unseen = true
          · rw [if_pos hu]; exact ⟨hk, hex, hd, by simpa using hf, hu⟩
          · rw [if_neg (by simpa using hu)]
            exact ⟨hk, hex, hd, by simpa using hf, by simpa using hu⟩
      · rw [if_pos (by simpa using hd)]
        exact ⟨hk, hex, by simpa using hd⟩
  · rw [if_pos (by simpa using hk)]
    show o.known = false
    simpa using hk

/-- **Complete.** `classify` is the *only* function agreeing with the
legend, so the cascade is not one choice among several. Cover + disjoint +
sound, combined. -/
theorem classify_unique (o : Obs) (s : Status) (h : Is s o) : classify o = s :=
  disjoint o _ _ (classify_sound o) h

/-! ## Every glyph is reachable, and no two states share one -/

/-- **No dead legend entry.** Each state is produced by some observation, so
no glyph in the legend is a state the program can never report. -/
theorem reachable : ∀ s : Status, ∃ o : Obs, classify o = s := by
  intro s
  cases s
  · exact ⟨{ known := false }, rfl⟩
  · exact ⟨{ exit := some 1 }, rfl⟩
  · exact ⟨{ exit := some 0 }, rfl⟩
  · exact ⟨{ daemonUp := false }, rfl⟩
  · exact ⟨{ unseen := true }, rfl⟩
  · exact ⟨{ fresh := true }, rfl⟩
  · exact ⟨{}, rfl⟩

/-- **No glyph collision.** Distinct states get distinct glyphs — the design
rule "share a glyph only when the action is the same" made concrete, so a
future merge has to delete a state rather than quietly overload a symbol.
(An earlier draft reused `!` for both a bell and a failed exit; this is the
theorem that rejects it.) -/
theorem icon_injective (s t : Status) (h : icon s = icon t) : s = t := by
  cases s <;> cases t <;> simp_all [icon]

/-- The same for the porcelain names, which recipes parse. -/
theorem name_injective (s t : Status) (h : name s = name t) : s = t := by
  cases s <;> cases t <;> simp_all [name]

/-- Porcelain names carry no separator or newline, so a row stays one
unambiguous record — the invariant that makes tab-separated output safe
without an escaping pass. -/
theorem name_clean (s : Status) : ∀ c ∈ (name s).toList, c ≠ '\t' ∧ c ≠ '\n' := by
  cases s <;> simp [name] <;> decide

end Zmx.Core.Status
