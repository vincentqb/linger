module

public import Linger.Core.Name
import all Linger.Core.Name

public section

/-! # §Name — session names cannot escape the socket directory

`check` accepts exactly names that `sanitize` would leave unchanged.
Accepted names are nonempty, short, made only of `okChar`s (no `/`,
NUL or controls), and do not begin with a dot. Invalid names are
rejected without manufacturing another session's identity.
-/

namespace Linger.Core.Name

/-- Both interactive entry paths share a default that path sanitization preserves. -/
theorem defaultName_canonical : defaultName = "main" ∧ sanitize defaultName = defaultName := by
  decide

theorem okChar_no_slash (c : Char) (h : okChar c = true) : c ≠ '/' := by
  intro he
  subst he
  simp [okChar] at h

theorem okChar_no_nul (c : Char) (h : okChar c = true) : c ≠ '\x00' := by
  intro he
  subst he
  simp [okChar] at h

theorem okChar_no_at (c : Char) (h : okChar c = true) : c ≠ '@' := by
  intro he
  subst he
  simp [okChar] at h

/-- The mapped character is always in the alphabet. -/
theorem mapChar_ok (c : Char) : okChar (if okChar c then c else '_') = true := by
  by_cases h : okChar c <;> simp [h] <;> decide

/-- §Name, the main statement: `sanitize` establishes `Valid` for any
input whatsoever. -/
theorem sanitize_valid (s : String) : Valid (sanitize s) := by
  unfold sanitize Valid
  dsimp only
  simp only [String.toList_ofList]
  generalize hbase : (s.toList.take maxLen).map (fun c => if okChar c then c else '_') = base
  have hb_ok : ∀ c ∈ base, okChar c = true := by
    intro c hc
    rw [← hbase] at hc
    obtain ⟨c0, -, heq⟩ := List.mem_map.mp hc
    rw [← heq]
    exact mapChar_ok c0
  have hb_len : base.length ≤ maxLen := by
    rw [← hbase]
    simp only [List.length_map]
    exact List.length_take_le _ _
  rcases base with - | ⟨c0, rest⟩
  · refine ⟨by simp, by simp [maxLen], ?_, by simp⟩
    intro c hc
    simp only [List.mem_singleton] at hc
    subst hc
    decide
  · simp only [List.length_cons] at hb_len ⊢
    refine ⟨by simp, hb_len, ?_, ?_⟩
    · intro c hc
      rcases List.mem_cons.mp hc with hc | hc
      · subst hc
        by_cases hdot : c0 == '.'
        · simp [hdot]
          decide
        · simp only [Bool.not_eq_true] at hdot
          simp only [hdot, Bool.false_eq_true, ite_false]
          exact hb_ok c0 List.mem_cons_self
      · exact hb_ok c (List.mem_cons_of_mem _ hc)
    · simp only [List.head?_cons, ne_eq, Option.some.injEq]
      by_cases hdot : c0 == '.'
      · simp [hdot]
      · simp only [Bool.not_eq_true] at hdot
        simp only [hdot, Bool.false_eq_true, ite_false]
        intro he
        subst he
        simp at hdot

/-- Sanitization preserves every valid name, which lets the validator accept
exactly the structural validity predicate without rewriting the input. -/
theorem sanitize_eq_self_of_valid (s : String) (h : Valid s) : sanitize s = s := by
  obtain ⟨hne, hlen, hok, hhead⟩ := h
  have hm : s.toList.map (fun c => if okChar c then c else '_') = s.toList := by
    calc
      _ = s.toList.map id := List.map_congr_left (fun c hc => by simp [hok c hc])
      _ = _ := List.map_id s.toList
  unfold sanitize
  rw [List.take_of_length_le hlen, hm]
  cases hs : s.toList with
  | nil => simp [hs] at hne
  | cons c cs =>
    have hdot : c ≠ '.' := by simpa [hs] using hhead
    simp [hdot, ← hs]

/-- Canonical-name checks and the structural validity predicate agree. -/
theorem sanitize_eq_self_iff (s : String) : sanitize s = s ↔ Valid s := by
  constructor
  · intro h
    rw [← h]
    exact sanitize_valid s
  · exact sanitize_eq_self_of_valid s

/-- Command validation accepts exactly valid names and preserves their spelling. -/
theorem check_eq_some_iff (s result : String) : check s = some result ↔ result = s ∧ Valid s := by
  simp only [check]
  split
  · rename_i h
    have valid : Valid s := (sanitize_eq_self_iff s).mp (by simpa using h)
    simp [valid, eq_comm]
  · rename_i h
    have invalid : ¬Valid s := by simpa [sanitize_eq_self_iff] using h
    simp [invalid]

/-- Distinct accepted names never alias through the validator. -/
theorem check_no_alias {a b name : String}
    (ha : check a = some name) (hb : check b = some name) : a = b :=
  ((check_eq_some_iff a name).mp ha).1.symm.trans ((check_eq_some_iff b name).mp hb).1

/-- Every entry path may sanitize independently without changing its target. -/
theorem sanitize_idempotent (s : String) : sanitize (sanitize s) = sanitize s :=
  sanitize_eq_self_of_valid _ (sanitize_valid s)

/-- The §Name corollary the runtime actually leans on: no character of
a sanitized name is a path separator or NUL. -/
theorem sanitize_no_escape (s : String) : ∀ c ∈ (sanitize s).toList, c ≠ '/' ∧ c ≠ '\x00' := by
  intro c hc
  obtain ⟨-, -, hok, -⟩ := sanitize_valid s
  exact ⟨okChar_no_slash c (hok c hc), okChar_no_nul c (hok c hc)⟩

/-- `@` is reserved as the `name@host` remote-attach delimiter, so no
sanitized session name ever contains it. This is what makes `attach
name@host` unambiguous: any `@` in the argument means "remote", and the
host is everything after the first one (it may itself be `user@host`).
It also holds for remote-supplied names, which are sanitized on parse.
(This theorem only closes because `okChar` excludes `@`; re-adding it
breaks the proof.) -/
theorem sanitize_no_at (s : String) : ∀ c ∈ (sanitize s).toList, c ≠ '@' := by
  intro c hc
  obtain ⟨-, -, hok, -⟩ := sanitize_valid s
  exact okChar_no_at c (hok c hc)

/-- **The length cap, said at the top level.** `Valid` carries `≤ maxLen` as a field and
`sanitize_valid` proves `Valid`, so the bound was reachable but never stated — and it is the
half every path caller depends on, because a sanitized name becomes a filename.

Note what is *not* true and was tried: `sanitize` is not length-non-increasing. The empty
name becomes `"_"`, so the only honest bound is against the cap, not against the input. -/
theorem sanitize_length_le (s : String) : (sanitize s).toList.length ≤ maxLen :=
  (sanitize_valid s).2.1

end Linger.Core.Name
