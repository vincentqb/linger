module

public import Linger.Core.Name
import all Linger.Core.Name

public section

/-! # §Name — session names cannot escape the socket directory

`sanitize` output lands in `<dir>/<name>.sock` and `<name>.ckpt`
paths. The theorem: for ANY input string — including ones arriving
from a hostile remote listing — the sanitized name is nonempty, short,
made only of `okChar`s (no `/`, no NUL, no controls), and does not
begin with a dot (no `.`/`..`/hidden files). Path escape is impossible
because `/` is simply not in the alphabet.
-/

namespace Linger.Core.Name

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
