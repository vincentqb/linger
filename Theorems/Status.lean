module

public import Linger.Core.Status
import all Linger.Core.Status
import Init.Data.Nat.ToString
import Init.Data.String.Lemmas.Intercalate
import Init.Data.Char.Lemmas

-- Converted from legacy by the `Vt` seal (`specs/archive/vt-toolkit.md` Step 1) — not for
-- anything in this file, which never mentions a `Vt`, but because a `module` cannot
-- import a non-`module`, and `Theorems/Listing.lean` had to become one to reach
-- `Render.utf8s_no_ctl` through `import all`. The conversion is transitive
-- upstream; nothing here changes but the visibility posture.

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

namespace Linger.Core.Status

/-- The legend, as predicates on an observation. -/
def Is : Status → Obs → Prop
  | .unknown, o => o.known = false
  | .exitedOk, o => o.known = true ∧ o.exit = some 0
  | .exitedBad, o => o.known = true ∧ ∃ n, o.exit = some n ∧ n ≠ 0
  | .resumable, o => o.known = true ∧ o.exit = none ∧ o.daemonUp = false
  | .working, o => o.known = true ∧ o.exit = none ∧ o.daemonUp = true ∧ o.fresh = true
  | .wantsYou, o =>
    o.known = true ∧ o.exit = none ∧ o.daemonUp = true ∧ o.fresh = false ∧ o.unseen = true
  | .idle, o =>
    o.known = true ∧ o.exit = none ∧ o.daemonUp = true ∧ o.fresh = false ∧ o.unseen = false

/-- All seven states, for the quantifiers below. -/
def all : List Status := [.unknown, .exitedBad, .exitedOk, .resumable, .wantsYou, .working, .idle]

theorem mem_all (s : Status) : s ∈ all := by cases s <;> simp [all]

/-- The cascade agrees exactly with the independent legend predicates. -/
theorem classify_iff (o : Obs) (s : Status) : classify o = s ↔ Is s o := by
  cases o with
  | mk known daemonUp exit fresh unseen =>
    cases known <;> cases daemonUp <;> cases fresh <;> cases unseen <;>
      cases exit with
      | none => cases s <;> simp [classify, Is]
      | some n => cases n <;> cases s <;> simp [classify, Is]

/-- **Cover.** Every observation is in some state — no row can fail to be
described. -/
theorem cover (o : Obs) : ∃ s, Is s o := ⟨classify o, (classify_iff o _).mp rfl⟩

/-- **Disjoint.** No observation is in two states — two rows showing the
same glyph really are in the same state. -/
theorem disjoint (o : Obs) (s t : Status) (hs : Is s o) (ht : Is t o) : s = t :=
  ((classify_iff o s).mpr hs).symm.trans ((classify_iff o t).mpr ht)

/-- **Sound.** The cascade computes the legend: what `classify` returns is
the state the row is actually in. This is the claim that would break if a
guard were mis-ordered. -/
theorem classify_sound (o : Obs) : Is (classify o) o := (classify_iff o _).mp rfl

/-- **Complete.** `classify` is the *only* function agreeing with the
legend, so the cascade is not one choice among several. Cover + disjoint +
sound, combined. -/
theorem classify_unique (o : Obs) (s : Status) (h : Is s o) : classify o = s :=
  (classify_iff o s).mpr h

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

/-- Porcelain names carry no separator or newline, so a row stays one
unambiguous record — the invariant that makes tab-separated output safe
without an escaping pass. -/
theorem name_clean (s : Status) : ∀ c ∈ (name s).toList, c ≠ '\t' ∧ c ≠ '\n' := by
  cases s <;> simp [name] <;> decide

/-- `ofName` is a left inverse of `name`, so the human column and the
porcelain column can never disagree about a row. -/
theorem ofName_name (s : Status) : ofName (name s) = s := by cases s <;> rfl

/-- The same for the porcelain names, which recipes parse. -/
theorem name_injective (s t : Status) (h : name s = name t) : s = t := by
  simpa only [ofName_name] using congrArg ofName h

/-- The complete style vocabulary contains standard foreground SGRs only; its
quiet style adds dim and explicitly selects the default foreground. -/
theorem style_palette (s : Status) :
    Linger.Core.Status.style s ∈
      ["\x1b[36m", "\x1b[33m", "\x1b[32m", "\x1b[31m", "\x1b[2;39m"] := by
  cases s <;> decide

/-- Positive counts appear once in attention order, independent of input order. -/
theorem attentionCounts_exact (statuses : List Status) :
    Linger.Core.Status.attentionCounts statuses =
      (if statuses.count .wantsYou = 0 then [] else [(.wantsYou, statuses.count .wantsYou)]) ++
        (if statuses.count .exitedBad = 0 then [] else [(.exitedBad, statuses.count .exitedBad)]) ++
        (if statuses.count .unknown = 0 then [] else [(.unknown, statuses.count .unknown)]) := by
  simp only [attentionCounts, List.filterMap_cons, List.filterMap_nil]
  split <;> split <;> split <;> simp_all

/-- Neither zero counts nor ordinary activity can occur in an attention group. -/
theorem attentionCounts_mem (statuses : List Status) (s : Status) (n : Nat) :
    (s, n) ∈ Linger.Core.Status.attentionCounts statuses ↔
      s ∈ [.wantsYou, .exitedBad, .unknown] ∧ n = statuses.count s ∧ n ≠ 0 := by
  simp only [attentionCounts, List.mem_filterMap]
  constructor
  · rintro ⟨st, hm, he⟩
    split at he
    · contradiction
    · simp only [Option.some.injEq, Prod.mk.injEq] at he
      rcases he with ⟨rfl, rfl⟩
      exact ⟨hm, rfl, by simpa using ‹¬(statuses.count st == 0) = true›⟩
  · rintro ⟨hm, rfl, hn⟩
    exact ⟨s, hm, by simp [hn]⟩

/-- The public string is precisely the three positive-count groups with their
canonical icons, separated by one space. -/
theorem summary_exact (statuses : List Status) :
    Linger.Core.Status.summary statuses =
      String.intercalate " "
        ((if statuses.count .wantsYou = 0 then []
          else [(toString (statuses.count .wantsYou)).push (icon .wantsYou)]) ++
          (if statuses.count .exitedBad = 0 then []
          else [(toString (statuses.count .exitedBad)).push (icon .exitedBad)]) ++
          (if statuses.count .unknown = 0 then []
          else [(toString (statuses.count .unknown)).push (icon .unknown)])) := by
  rw [summary, attentionCounts_exact]
  split <;> split <;> split <;> simp_all

/-- With no attention counts, the summary has no placeholder or separator. -/
theorem summary_omits_zero (statuses : List Status) (hw : statuses.count .wantsYou = 0)
    (hb : statuses.count .exitedBad = 0) (hu : statuses.count .unknown = 0) :
    Linger.Core.Status.summary statuses = "" := by simp [summary_exact, hw, hb, hu]

private theorem summary_token_clean (statuses : List Status) (s : Status) (n : Nat)
    (h : (s, n) ∈ attentionCounts statuses) :
    ∀ c ∈ ((toString n).push (icon s)).toList, c.isDigit = true ∨ c ∈ ['⣿', '!', '?'] := by
  intro c hc
  simp only [String.toList_push, List.mem_append, List.mem_singleton] at hc
  rcases hc with hc | rfl
  · left
    rw [Nat.toString_eq_repr, Nat.toList_repr] at hc
    exact Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
  · right
    have hs := ((attentionCounts_mem statuses s n).mp h).1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl <;> decide

/-- Summary text contains only decimal digits, spaces and attention glyphs.
This is stronger than absence of newline or terminal escapes. -/
theorem summary_alphabet (statuses : List Status) :
    ∀ c ∈ (Linger.Core.Status.summary statuses).toList,
      c.isDigit = true ∨ c ∈ [' ', '⣿', '!', '?'] := by
  have joinClean (strings : List String)
    (hs : ∀ text ∈ strings, ∀ c ∈ text.toList, c.isDigit = true ∨ c ∈ [' ', '⣿', '!', '?']) :
    ∀ c ∈ (String.intercalate " " strings).toList, c.isDigit = true ∨ c ∈ [' ', '⣿', '!', '?'] := by
    induction strings with
    | nil => simp
    | cons text rest ih =>
      cases rest with
      | nil => simpa using hs text (by simp)
      | cons next tail =>
        intro c hc
        simp only [String.intercalate_cons_cons, String.toList_append, List.mem_append] at hc
        rcases hc with (hc | hc) | hc
        · exact hs text (by simp) c hc
        · have space : (" " : String).toList = [' '] := by decide
          rw [space, List.mem_singleton] at hc
          subst c
          exact Or.inr (by simp)
        · exact ih (fun value hm => hs value (by simp [hm])) c hc
  apply joinClean
  intro text ht c hc
  obtain ⟨⟨s, n⟩, hm, rfl⟩ := List.mem_map.mp ht
  rcases summary_token_clean statuses s n hm c hc with hd | hi
  · exact Or.inl hd
  · exact Or.inr (by simp_all)

/-- A prompt or title can embed the summary verbatim: no controls, DEL or C1. -/
theorem summary_printable (statuses : List Status) :
    ∀ c ∈ (Linger.Core.Status.summary statuses).toList,
      32 ≤ c.toNat ∧ (c.toNat < 127 ∨ 160 ≤ c.toNat) := by
  intro c hc
  rcases summary_alphabet statuses c hc with hd | hi
  · have := Char.isDigit_iff_toNat.mp hd
    change 48 ≤ c.toNat ∧ c.toNat ≤ 57 at this
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> decide

end Linger.Core.Status
