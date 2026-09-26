module

public import Tools.Picker
import all Tools.Picker
import Theorems.Name

public section

/-! Selection contracts for one immutable listing snapshot.

These proofs do not assert that a listed session remains available until the
executor attaches it. They constrain the exact target and permitted outcomes.
-/

namespace Tools.Picker

/-- Complete equivalence to subsequence matching after ASCII lowercase conversion. -/
theorem matches_iff_sublist (query target : String) :
    Tools.Picker.matches query target = true ↔
      (query.toList.map Char.toLower).Sublist (target.toList.map Char.toLower) := by
  exact List.isSublist_iff_sublist

theorem matches_empty (target : String) : Tools.Picker.matches "" target = true := by
  simp [Tools.Picker.matches]

/-- Repeated query characters need separate source positions. -/
theorem matches_length_le (query target : String) (h : Tools.Picker.matches query target = true) :
    query.length ≤ target.length := by
  simpa only [List.length_map, String.length_toList] using
    ((matches_iff_sublist query target).mp h).length_le

private theorem printable_iff (char : Char) :
    printable char = true ↔ 32 ≤ char.toNat ∧ (char.toNat < 127 ∨ 160 ≤ char.toNat) := by
  simp [printable]

private theorem validTarget_sound (target : String) (h : validTarget target = true) :
    target ≠ "" ∧
      Linger.Core.Name.sanitize ((target.splitOn "@").headD "") = (target.splitOn "@").headD "" ∧
      (∀ char ∈ target.toList, 32 ≤ char.toNat ∧ (char.toNat < 127 ∨ 160 ≤ char.toNat)) ∧
      ((target.splitOn "@").tail = [] ∨ String.intercalate "@" (target.splitOn "@").tail ≠ "") := by
  simpa [validTarget, printable_iff, and_assoc] using h

private theorem parseRow_some (fields : List String) (target : String)
    (h : parseRow fields = .ok (some target)) :
    fields = ["name", target] ∧ validTarget target = true := by
  unfold parseRow at h
  repeat' (split at h <;> (try simp_all))
  all_goals
    cases h
    simp_all

private theorem parseRow_none (fields : List String) (h : parseRow fields = .ok none) :
    fields.head? ≠ some "name" := by
  unfold parseRow at h
  repeat' (split at h <;> (try simp_all))

private theorem parseRow_error (fields : List String) (error : String)
    (h : parseRow fields = .error error) :
    error = "invalid session target in listing" ∨ error = "malformed name record in listing" := by
  unfold parseRow at h
  repeat' (split at h <;> (try simp_all))

private theorem parseRows_sound (seen rows targets : List String)
    (h : parseRows seen rows = .ok targets) :
    (∀ target ∈ targets, validTarget target = true) ∧
      targets.Nodup ∧
      (∀ target ∈ targets, target ∉ seen) ∧
      targets.map (fun target => ["name", target]) =
        (rows.map (·.splitOn "\t")).filter (fun fields => fields.head? == some "name") := by
  induction rows generalizing seen targets with
  | nil =>
    simp only [parseRows, Except.ok.injEq] at h
    subst targets
    simp
  | cons row rows ih =>
    simp only [parseRows] at h
    cases hrow : parseRow (row.splitOn "\t") with
    | error error => simp [hrow] at h
    | ok result =>
      cases result with
      | none =>
        simp only [hrow] at h
        obtain ⟨valid, distinct, fresh, records⟩ := ih seen targets h
        refine ⟨valid, distinct, fresh, ?_⟩
        simpa [parseRow_none _ hrow] using records
      | some target =>
        simp only [hrow] at h
        split at h
        · cases h
        · rename_i hskip
          cases hrest : parseRows (target :: seen) rows with
          | error error => simp [hrest, Except.map] at h
          | ok rest =>
            simp only [hrest, Except.map, Except.ok.injEq] at h
            subst targets
            obtain ⟨valid, distinct, fresh, records⟩ := ih (target :: seen) rest hrest
            obtain ⟨fields, targetValid⟩ := parseRow_some _ target hrow
            refine ⟨?_, ?_, ?_, ?_⟩
            · intro t ht
              rcases List.mem_cons.mp ht with rfl | ht
              · exact targetValid
              · exact valid t ht
            · exact List.nodup_cons.mpr ⟨fun ht => fresh target ht (by simp), distinct⟩
            · intro t ht
              rcases List.mem_cons.mp ht with rfl | ht
              · simpa using hskip
              · intro hs
                exact fresh t ht (List.mem_cons_of_mem _ hs)
            · simp [fields, records]

private theorem parseRows_error (seen rows : List String) (error : String)
    (h : parseRows seen rows = .error error) :
    error = "invalid session target in listing" ∨
      error = "malformed name record in listing" ∨
      error = "duplicate session target in listing" := by
  induction rows generalizing seen with
  | nil => simp [parseRows] at h
  | cons row rows ih =>
    simp only [parseRows] at h
    cases hrow : parseRow (row.splitOn "\t") with
    | error reason =>
      simp only [hrow, Except.error.injEq] at h
      subst reason
      rcases parseRow_error _ error hrow with invalid | malformed
      · exact Or.inl invalid
      · exact Or.inr (Or.inl malformed)
    | ok result =>
      cases result with
      | none =>
        simp only [hrow] at h
        exact ih seen h
      | some target =>
        simp only [hrow] at h
        split at h
        · cases h
          exact Or.inr (Or.inr rfl)
        · cases hrest : parseRows (target :: seen) rows with
          | error reason =>
            simp only [hrest, Except.map, Except.error.injEq] at h
            subst reason
            exact ih (target :: seen) hrest
          | ok rest => simp [hrest, Except.map] at h

/-- Successful parsing retains every name record, in order, with its exact target.
The equality also excludes silently dropping valid records or accepting partial ones. -/
theorem parseListing_records (text : String) (targets : List String)
    (h : parseListing text = .ok targets) :
    targets.map (fun target => ["name", target]) =
      ((text.splitOn "\n").map (·.splitOn "\t")).filter
        (fun fields => fields.head? == some "name") := (parseRows_sound [] _ targets h).2.2.2

/-- Parsing supplies unique identities, canonical local names, and printable exact
targets. A present remote suffix is nonempty; additional `@` characters are retained. -/
theorem parseListing_valid (text : String) (targets : List String)
    (h : parseListing text = .ok targets) :
    targets.Nodup ∧
      ∀ target ∈ targets,
        target ≠ "" ∧
          Linger.Core.Name.sanitize ((target.splitOn "@").headD "") =
            (target.splitOn "@").headD "" ∧
          Linger.Core.Name.Valid ((target.splitOn "@").headD "") ∧
          (∀ char ∈ target.toList, 32 ≤ char.toNat ∧ (char.toNat < 127 ∨ 160 ≤ char.toNat)) ∧
          ((target.splitOn "@").tail = [] ∨
            String.intercalate "@" (target.splitOn "@").tail ≠ "") := by
  obtain ⟨valid, distinct, -⟩ := parseRows_sound [] _ targets h
  refine ⟨distinct, ?_⟩
  intro target ht
  obtain ⟨nonempty, canonical, clean, host⟩ := validTarget_sound target (valid target ht)
  refine ⟨nonempty, canonical, ?_, clean, host⟩
  rw [← canonical]
  exact Linger.Core.Name.sanitize_valid _

theorem parseListing_provenance (text : String) (targets : List String)
    (h : parseListing text = .ok targets) (target : String) (ht : target ∈ targets) :
    ∃ row ∈ text.splitOn "\n", row.splitOn "\t" = ["name", target] := by
  have hm : ["name", target] ∈ targets.map (fun target => ["name", target]) :=
    List.mem_map.mpr ⟨target, ht, rfl⟩
  rw [parseListing_records text targets h] at hm
  exact List.mem_map.mp (List.mem_filter.mp hm).1

/-- Diagnostics use a fixed vocabulary; untrusted target text is never echoed. -/
theorem parseListing_error_safe (text error : String) (h : parseListing text = .error error) :
    ∀ char ∈ error.toList, 32 ≤ char.toNat ∧ char.toNat < 127 := by
  rcases parseRows_error [] _ error h with rfl | rfl | rfl <;> decide

theorem mem_visible (candidates : List String) (query target : String) :
    target ∈ visible candidates query ↔
      target ∈ candidates ∧ Tools.Picker.matches query target = true := by
  simp [visible]

/-- Sublist preservation states order and multiplicity, not just set membership. -/
theorem visible_order (candidates : List String) (query : String) :
    (visible candidates query).Sublist candidates := List.filter_sublist

theorem visible_empty_query (candidates : List String) : visible candidates "" = candidates := by
  simp [visible, matches_empty]

theorem selected_mem (s : State) (target : String) (h : selected s = some target) :
    target ∈ s.candidates ∧ Tools.Picker.matches s.query target = true :=
  (mem_visible _ _ _).mp (List.mem_of_getElem? h)

theorem selected_empty (s : State) (h : visible s.candidates s.query = []) : selected s = none := by
  simp [selected, h]

theorem init_valid (candidates : List String) : (init candidates).Valid := by
  simp [init, State.Valid, maxQueryLength]

/-- The arithmetic invariant means either an in-range cursor or the unique empty cursor. -/
theorem valid_cursor (s : State) (h : s.Valid) :
    s.cursor < (visible s.candidates s.query).length ∨
      (visible s.candidates s.query = [] ∧ s.cursor = 0) := by
  obtain ⟨cursor, -⟩ := h
  cases hs : visible s.candidates s.query with
  | nil =>
    right
    simp only [hs, List.length_nil, Nat.zero_sub] at cursor
    exact ⟨rfl, Nat.eq_zero_of_le_zero cursor⟩
  | cons head tail =>
    left
    simp only [hs, List.length_cons] at cursor ⊢
    omega

/-- Every continuing transition preserves bounds established by `init`. -/
theorem step_stay_valid (s next : State) (key : Tools.Key) (hs : s.Valid)
    (h : step s key = .stay next) : next.Valid := by
  obtain ⟨cursor, query⟩ := hs
  cases key with
  | text char =>
    simp only [step] at h
    split at h
    · rename_i edit
      cases h
      refine ⟨Nat.zero_le _, ?_⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq] at edit
      simp only [String.length_push]
      omega
    · cases h
      exact ⟨cursor, query⟩
  | backspace =>
    cases h
    refine ⟨Nat.zero_le _, ?_⟩
    simp only [String.length_ofList, List.length_dropLast, String.length_toList]
    omega
  | clear =>
    cases h
    exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  | up =>
    cases h
    exact ⟨Nat.le_trans (Nat.sub_le _ _) cursor, query⟩
  | down =>
    cases h
    exact ⟨Nat.min_le_right _ _, query⟩
  | first =>
    cases h
    exact ⟨Nat.zero_le _, query⟩
  | last =>
    cases h
    exact ⟨Nat.le_refl _, query⟩
  | accept =>
    simp only [step] at h
    cases he : selected s with
    | none =>
      simp only [he] at h
      cases h
      exact ⟨cursor, query⟩
    | some target => simp [he] at h
  | cancel => cases h
  | refresh => cases h

theorem step_query_bound (s next : State) (key : Tools.Key) (hs : s.Valid)
    (h : step s key = .stay next) : next.query.length ≤ maxQueryLength :=
  (step_stay_valid s next key hs h).2

/-- Editing and navigation cannot change the listing snapshot. -/
theorem step_stay_candidates (s next : State) (key : Tools.Key) (h : step s key = .stay next) :
    next.candidates = s.candidates := by
  cases key <;> simp only [step] at h
  all_goals
    repeat' split at h
    all_goals cases h <;> rfl

/-- Acceptance is the only attachment-producing event, and its target is selected verbatim. -/
theorem step_attach_iff (s : State) (key : Tools.Key) (target : String) :
    step s key = .attach target ↔ key = .accept ∧ selected s = some target := by
  cases key <;> simp [step]
  all_goals split <;> simp_all

/-- No valid-state premise: even a forged or stale cursor cannot manufacture a target. -/
theorem step_attach_mem (s : State) (key : Tools.Key) (target : String)
    (h : step s key = .attach target) :
    target ∈ s.candidates ∧ Tools.Picker.matches s.query target = true :=
  selected_mem s target ((step_attach_iff s key target).mp h).2

theorem step_empty_accept (s : State) (h : visible s.candidates s.query = []) :
    step s .accept = .stay s := by simp [step, selected_empty s h]

theorem step_cancel (s : State) : step s .cancel = .cancel := by simp [step]

theorem step_refresh (s : State) : step s .refresh = .refresh := by simp [step]

theorem step_control_ignored (s : State) (char : Char)
    (h : char.toNat < 32 ∨ (127 ≤ char.toNat ∧ char.toNat < 160)) :
    step s (.text char) = .stay s := by
  have hc : printable char = false := by
    simp only [Bool.eq_false_iff]
    intro hp
    have clean := (printable_iff char).mp hp
    omega
  simp [step, hc]

theorem step_full_query (s : State) (char : Char) (h : maxQueryLength ≤ s.query.length) :
    step s (.text char) = .stay s := by
  have hn : ¬s.query.length < maxQueryLength := by omega
  simp [step, hn]

end Tools.Picker
