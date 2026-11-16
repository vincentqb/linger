module

public import Linger.Target.CoreCode.Name
public import Linger.Target.CoreSpec
import all Linger.Target.CoreCode.Name

public section

/-! # Session names cannot escape the socket directory

`check` accepts exactly names that `sanitize` would leave unchanged.
Accepted names are nonempty, short, made only of `okChar`s (no `/`,
NUL or controls), and do not begin with a dot. Invalid names are
rejected without manufacturing another session's identity. `check_eq_some_iff` and
`check_no_alias` below prove the headlines of those names (`Challenge.lean`, part 3).
-/

namespace Linger.Target.Name

/-- Both interactive entry paths share a default that path sanitization preserves. -/
theorem defaultName_canonical : defaultName = "main" ∧ sanitize defaultName = defaultName := by
  decide

theorem okChar_no_slash (c : Char) (h : okChar c = true) : c ≠ '/' := by
  rintro rfl
  simp [okChar] at h

theorem okChar_no_nul (c : Char) (h : okChar c = true) : c ≠ '\x00' := by
  rintro rfl
  simp [okChar] at h

theorem okChar_no_at (c : Char) (h : okChar c = true) : c ≠ '@' := by
  rintro rfl
  simp [okChar] at h

/-- The mapped character is always in the alphabet. -/
theorem mapChar_ok (c : Char) : okChar (if okChar c then c else '_') = true := by
  by_cases h : okChar c <;> simp [h]; decide

/-- The main statement: `sanitize` establishes `Valid` for any
input whatsoever. -/
theorem sanitize_valid (s : String) : Valid (sanitize s) := by
  unfold sanitize Valid
  simp only [String.toList_ofList]
  split
  · simp [maxLen, okChar]
  · grind [mapChar_ok, List.length_map, List.length_take, okChar]

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

/-- The corollary the runtime actually leans on: no character of
a sanitized name is a path separator or NUL. -/
theorem sanitize_no_escape (s : String) : ∀ c ∈ (sanitize s).toList, c ≠ '/' ∧ c ≠ '\x00' := by
  intro c hc
  obtain ⟨-, -, hok, -⟩ := sanitize_valid s
  exact ⟨okChar_no_slash c (hok c hc), okChar_no_nul c (hok c hc)⟩

/-- `@` is reserved as the `name@host` remote-attach delimiter, so no
sanitized session name ever contains it. This is what makes `attach
name@host` unambiguous: any `@` in the argument means "remote", and the
host is everything after the first one (it may itself be `user@host`).
It also holds for remote-supplied names, which parse accepts only when `sanitize` leaves
them unchanged.
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

/-- `usable` decides `Usable`. -/
theorem usable_iff (s : String) : usable s = true ↔ Usable s := by
  simp [usable, Usable, List.all_eq_true, and_assoc]

/-- `check` decides `Valid`. -/
theorem check_isSome_iff (s : String) : (check s).isSome = true ↔ Valid s := by
  cases h : check s with
  | none =>
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    intro v
    have := (check_eq_some_iff s s).mpr ⟨rfl, v⟩
    rw [h] at this
    cases this
  | some r => simpa using ((check_eq_some_iff s r).mp h).2

/-- **A name is accepted exactly as it is, when it is clean text or an older key.** -/
theorem accept_eq_some_iff (s result : String) :
    accept s = some result ↔ result = s ∧ Accepted s := by
  unfold accept Accepted
  rw [← usable_iff, ← check_isSome_iff]
  constructor
  · intro h
    split at h
    · rename_i ok
      exact ⟨(Option.some.inj h).symm, by simpa using ok⟩
    · cases h
  · rintro ⟨rfl, h⟩
    have ok : (usable result || (check result).isSome) = true := by simpa using h
    simp only [ok, ↓reduceIte]

/-- No name holds `@`, which marks a host. -/
theorem accepted_no_at (s : String) (h : Accepted s) : ∀ c ∈ s.toList, c ≠ '@' := by
  intro c hc heq
  subst heq
  rcases h with h | h
  · have := h.2.2.1 '@' hc
    simp [textChar] at this
  · exact okChar_no_at '@' (h.2.2.1 '@' hc) rfl

end Linger.Target.Name
