module

public import Tools.Picker
import all Tools.Picker
import all Linger.Core.Name
import all Linger.Core.Listing
import all Init.Data.String.Legacy
import Theorems.Name

public section

/-! Selection contracts within and between listing snapshots.

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

/-- Validation accepts exactly canonical local names with printable targets and
nonempty remote suffixes. It never repairs a target on its way to acceptance. -/
private theorem validTarget_iff (target : String) :
    validTarget target = true ↔
      target ≠ "" ∧
        Linger.Core.Name.Valid ((target.splitOn "@").headD "") ∧
        (∀ char ∈ target.toList, 32 ≤ char.toNat ∧ (char.toNat < 127 ∨ 160 ≤ char.toNat)) ∧
        ((target.splitOn "@").tail = [] ∨
          String.intercalate "@" (target.splitOn "@").tail ≠ "") := by
  simp [validTarget, printable_iff, Linger.Core.Name.sanitize_eq_self_iff, and_assoc]

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
  obtain ⟨nonempty, nameValid, clean, host⟩ := (validTarget_iff target).mp (valid target ht)
  exact ⟨nonempty, (Linger.Core.Name.sanitize_eq_self_iff _).mpr nameValid, nameValid, clean, host⟩

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

/-- Metadata publication is conditional on complete exact-target validation, and
retains every original record rather than synthesizing missing observations. -/
theorem parseSnapshot_complete (text : String) (snapshot : Snapshot)
    (h : Tools.Picker.parseSnapshot text = .ok snapshot) :
    parseListing text = .ok snapshot.candidates ∧
      snapshot.records = (text.splitOn "\n").map (·.splitOn "\t") := by
  unfold parseSnapshot at h
  cases hp : parseListing text with
  | error error => simp [hp, Except.map] at h
  | ok candidates =>
    simp only [hp, Except.map, Except.ok.injEq] at h
    cases h
    exact ⟨rfl, rfl⟩

/-- Any malformed target anywhere rejects the metadata snapshot too. -/
theorem parseSnapshot_rejects (text error : String) (h : parseListing text = .error error) :
    Tools.Picker.parseSnapshot text = .error error := by simp [parseSnapshot, h, Except.map]

/-- The identity comes from the validated selection; metadata cannot rename it. -/
theorem snapshot_row_name (snapshot : Snapshot) (target : String) :
    (Tools.Picker.Snapshot.row snapshot target).lookup "name" = some target := by
  simp [Snapshot.row]

/-- The selected existing row has precisely the listing's badge, aligned name,
details, labels and watchers, with the same style boundaries. -/
theorem presentation_existing (snapshot : Snapshot) (nameCol : Nat) (target : String) :
    Tools.Picker.presentation snapshot nameCol (.existing target) =
      Linger.Core.Listing.rowPieces nameCol (snapshot.row target) := by
  simp [presentation]

/-- Equivalence includes all rendered plain bytes, beyond status glyphs. Clipping
and selection reverse are applied by the terminal executor after this shared row. -/
theorem presentation_existing_humanRow (snapshot : Snapshot) (nameCol : Nat) (target : String) :
    Linger.Core.Render.utf8s
        ((Tools.Picker.presentation snapshot nameCol (.existing target)).flatMap (·.text)) =
      Linger.Core.Listing.humanRow nameCol (snapshot.row target) := by
  simp [presentation, Linger.Core.Listing.humanRow]

/-- Creation never masquerades as a listed session status. -/
theorem presentation_creation (snapshot : Snapshot) (nameCol : Nat) (target : String) :
    Tools.Picker.presentation snapshot nameCol (.create target) =
      [{ text := s!"+ Create {target}".toList }] := by
  simp [presentation]

theorem mem_visible (candidates : List String) (query target : String) :
    target ∈ visible candidates query ↔
      target ∈ candidates ∧ Tools.Picker.matches query target = true := by
  simp [visible]

/-- Sublist preservation states order and multiplicity, not just set membership. -/
theorem visible_order (candidates : List String) (query : String) :
    (visible candidates query).Sublist candidates := List.filter_sublist

theorem visible_empty_query (candidates : List String) : visible candidates "" = candidates := by
  simp [visible, matches_empty]

/-- All existing matches precede the optional creation choice. -/
theorem items_existing_prefix (candidates : List String) (query : String) :
    ((visible candidates query).map Item.existing).IsPrefix (items candidates query) := by
  unfold items
  exact List.prefix_append _ _

theorem mem_items_existing (candidates : List String) (query target : String) :
    Item.existing target ∈ items candidates query ↔
      target ∈ candidates ∧ Tools.Picker.matches query target = true := by
  unfold items
  split <;> simp [mem_visible]

/-- Creation is offered iff the exact target is valid and absent, independently
of whether the query also matches any existing targets. -/
private theorem mem_items_create (candidates : List String) (query target : String) :
    Item.create target ∈ items candidates query ↔
      target = (if query.isEmpty then Linger.Core.Name.defaultName else query) ∧
        validTarget target = true ∧ target ∉ candidates := by
  unfold items
  split <;> simp_all
  all_goals
    constructor
    · rintro ⟨⟨valid, absent⟩, rfl⟩
      exact ⟨rfl, valid, absent⟩
    · rintro ⟨rfl, valid, absent⟩
      exact ⟨⟨valid, absent⟩, rfl⟩

theorem selected_mem (s : State) (target : String) (h : selected s = some (.existing target)) :
    target ∈ s.candidates ∧ Tools.Picker.matches s.query target = true :=
  (mem_items_existing _ _ _).mp (List.mem_of_getElem? h)

theorem selected_empty (s : State) (h : items s.candidates s.query = []) : selected s = none := by
  simp [selected, h]

/-- Identity is the exact target, independent of whether Enter creates or attaches. -/
theorem item_target (target : String) :
    Item.target (.existing target) = target ∧ Item.target (.create target) = target := ⟨rfl, rfl⟩

theorem refresh_query (s : State) (candidates : List String) :
    (refresh s candidates).query = s.query := by simp [refresh]

theorem refresh_candidates (s : State) (candidates : List String) :
    (refresh s candidates).candidates = candidates := by simp [refresh]

/-- Refresh clamps even a forged cursor; it never changes query length. -/
theorem refresh_valid (s : State) (candidates : List String)
    (hquery : s.query.length ≤ maxQueryLength) : (refresh s candidates).Valid := by
  simp only [refresh, State.Valid]
  refine ⟨?_, hquery⟩
  cases hf :
    (items candidates s.query).findIdx?
      (fun item => some item.target == (selected s).map Item.target) with
  | none => exact Nat.min_le_right _ _
  | some index =>
    have bound := (List.findIdx?_eq_some_iff_findIdx_eq.mp hf).1
    simpa using (show index ≤ (items candidates s.query).length - 1 by omega)

/-- A surviving target stays selected even after reordering or changing row kind. -/
theorem refresh_selected (s : State) (candidates : List String) (item : Item)
    (hselected : selected s = some item)
    (hpresent : ∃ next ∈ items candidates s.query, next.target = item.target) :
    (selected (refresh s candidates)).map Item.target = some item.target := by
  let choices := items candidates s.query
  let predicate := fun next : Item => some next.target == (selected s).map Item.target
  have found : ∃ next, next ∈ choices ∧ predicate next = true := by
    obtain ⟨next, member, target⟩ := hpresent
    exact ⟨next, member, by simp [predicate, hselected, target]⟩
  have hf := List.findIdx?_eq_some_of_exists found
  have bound := List.findIdx_lt_length_of_exists found
  have target := List.findIdx_getElem (xs := choices) (p := predicate) (w := bound)
  change
    (some choices[choices.findIdx predicate].target == (selected s).map Item.target) =
      true at target
  simp only [hselected, Option.map_some, beq_iff_eq, Option.some.injEq] at target
  change
    (choices[(choices.findIdx? predicate).getD (min s.cursor (choices.length - 1))]?).map
        Item.target =
      some item.target
  rw [hf]
  simpa only [Option.getD_some, List.getElem?_eq_getElem bound, Option.map_some] using
    congrArg some target

/-- When the former target is gone, refresh keeps its row when possible. -/
theorem refresh_missing (s : State) (candidates : List String)
    (hmissing :
      ∀ item ∈ items candidates s.query, some item.target ≠ (selected s).map Item.target) :
    (refresh s candidates).cursor = min s.cursor ((items candidates s.query).length - 1) := by
  have hf :
    (items candidates s.query).findIdx?
        (fun item => some item.target == (selected s).map Item.target) =
      none :=
    List.findIdx?_eq_none_iff.mpr (by simpa using hmissing)
  simp [refresh, hf]

theorem init_valid (candidates : List String) : (init candidates).Valid := by
  simp [init, State.Valid, maxQueryLength]

/-- The arithmetic invariant means either an in-range cursor or the unique empty cursor. -/
theorem valid_cursor (s : State) (h : s.Valid) :
    s.cursor < (items s.candidates s.query).length ∨
      (items s.candidates s.query = [] ∧ s.cursor = 0) := by
  obtain ⟨cursor, -⟩ := h
  cases hs : items s.candidates s.query with
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
    | some item => cases item <;> simp [he] at h
  | cancel => cases h

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
    step s key = .attach target ↔ key = .accept ∧ selected s = some (.existing target) := by
  cases key <;> simp [step]
  all_goals split <;> simp_all

/-- Creation also requires acceptance of its own highlighted row. -/
theorem step_create_iff (s : State) (key : Tools.Key) (target : String) :
    step s key = .create target ↔ key = .accept ∧ selected s = some (.create target) := by
  cases key <;> simp [step]
  all_goals split <;> simp_all

/-- No valid-state premise: even a forged or stale cursor cannot manufacture a target. -/
theorem step_attach_mem (s : State) (key : Tools.Key) (target : String)
    (h : step s key = .attach target) :
    target ∈ s.candidates ∧ Tools.Picker.matches s.query target = true :=
  selected_mem s target ((step_attach_iff s key target).mp h).2

/-- No state-validity premise: even a forged cursor cannot create a rewritten,
noncanonical or already listed target. Absence refers to the snapshot only. -/
theorem step_create_valid (s : State) (key : Tools.Key) (target : String)
    (h : step s key = .create target) :
    target = (if s.query.isEmpty then Linger.Core.Name.defaultName else s.query) ∧
      target ∉ s.candidates ∧
      target ≠ "" ∧
      Linger.Core.Name.sanitize ((target.splitOn "@").headD "") = (target.splitOn "@").headD "" ∧
      Linger.Core.Name.Valid ((target.splitOn "@").headD "") ∧
      (∀ char ∈ target.toList, 32 ≤ char.toNat ∧ (char.toNat < 127 ∨ 160 ≤ char.toNat)) ∧
      ((target.splitOn "@").tail = [] ∨ String.intercalate "@" (target.splitOn "@").tail ≠ "") := by
  have selected := ((step_create_iff s key target).mp h).2
  obtain ⟨exactTarget, valid, absent⟩ := (mem_items_create _ _ _).mp (List.mem_of_getElem? selected)
  obtain ⟨nonempty, nameValid, printable, suffix⟩ := (validTarget_iff target).mp valid
  exact
    ⟨exactTarget, absent, nonempty, (Linger.Core.Name.sanitize_eq_self_iff _).mpr nameValid,
      nameValid, printable, suffix⟩

theorem step_empty_accept (s : State) (h : items s.candidates s.query = []) :
    step s .accept = .stay s := by simp [step, selected_empty s h]

/-- An empty listing has a usable creation choice, using the attach default. -/
theorem step_init_empty : step (init []) .accept = .create Linger.Core.Name.defaultName := by cbv

theorem step_cancel (s : State) : step s .cancel = .cancel := by simp [step]

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
