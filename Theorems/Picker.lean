module

import all Linger.Tools.Picker
import all Linger.Core.Name
import all Linger.Core.Listing
import all Linger.Core.Remote
import all Init.Data.String.Legacy
import Theorems.Name
import Theorems.Fuzzy
import Theorems.Remote
import Theorems.Input

/-! Selection contracts within and between listing snapshots.

These proofs do not assert that a listed session remains available until the
executor attaches it. They constrain the exact target and permitted outcomes.
-/

namespace Linger.Tools.Picker

/-- Complete equivalence to subsequence matching after ASCII lowercase conversion. -/
theorem matches_iff_sublist (query target : String) :
    Linger.Tools.Picker.matches query target = true ↔
      (query.toList.map Char.toLower).Sublist (target.toList.map Char.toLower) := by
  exact List.isSublist_iff_sublist

/-- Scoring changes emphasis without changing which targets the filter accepts. -/
theorem align_isSome_iff_matches (query target : String) :
    (Linger.Tools.Fuzzy.align query target).isSome = true ↔
      Linger.Tools.Picker.matches query target = true :=
  (Linger.Tools.Fuzzy.align_isSome_iff_sublist query target).trans
    (matches_iff_sublist query target).symm

theorem matches_empty (target : String) : Linger.Tools.Picker.matches "" target = true := by
  simp [Linger.Tools.Picker.matches]

/-- Repeated query characters need separate source positions. -/
theorem matches_length_le (query target : String)
    (h : Linger.Tools.Picker.matches query target = true) : query.length ≤ target.length := by
  simpa only [List.length_map, String.length_toList] using
    ((matches_iff_sublist query target).mp h).length_le

theorem parseRow_some (fields : List String) (target : String)
    (h : parseRow fields = .ok (some target)) :
    fields = ["name", target] ∧ Linger.Core.Remote.targetValid target = true := by
  unfold parseRow at h
  repeat' (split at h <;> (try simp_all))

theorem parseRow_none (fields : List String) (h : parseRow fields = .ok none) :
    fields.head? ≠ some "name" := by
  unfold parseRow at h
  repeat' (split at h <;> (try simp_all))

theorem parseRow_error (fields : List String) (error : String)
    (h : parseRow fields = .error error) :
    error = "invalid session target in listing" ∨ error = "malformed name record in listing" := by
  unfold parseRow at h
  repeat' (split at h <;> (try simp_all))

theorem parseRows_sound (seen rows targets : List String) (h : parseRows seen rows = .ok targets) :
    (∀ target ∈ targets, Linger.Core.Remote.targetValid target = true) ∧
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

theorem parseRows_error (seen rows : List String) (error : String)
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
  obtain ⟨nonempty, nameValid, clean, host⟩ :=
    (Linger.Core.Remote.targetValid_iff target).mp (valid target ht)
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
    (h : Linger.Tools.Picker.parseSnapshot text = .ok snapshot) :
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
    Linger.Tools.Picker.parseSnapshot text = .error error := by simp [parseSnapshot, h, Except.map]

/-- The identity comes from the validated selection; metadata cannot rename it. -/
theorem snapshot_row_name (snapshot : Snapshot) (target : String) :
    (Linger.Tools.Picker.Snapshot.row snapshot target).lookup "name" = some target := by
  simp [Snapshot.row]

/-- The selected existing row has precisely the listing's badge, aligned name,
details, labels and watchers, with the same style boundaries. -/
theorem presentation_existing (snapshot : Snapshot) (nameCol : Nat) (target : String) :
    Linger.Tools.Picker.presentation snapshot nameCol (.existing target) =
      Linger.Core.Listing.rowPieces nameCol (snapshot.row target) := by
  simp [presentation]

/-- Equivalence includes all rendered plain bytes, beyond status glyphs. Clipping
and selection reverse are applied by the terminal executor after this shared row. -/
theorem presentation_existing_humanRow (snapshot : Snapshot) (nameCol : Nat) (target : String) :
    Linger.Core.Render.utf8s
        ((Linger.Tools.Picker.presentation snapshot nameCol (.existing target)).flatMap (·.text)) =
      Linger.Core.Listing.humanRow nameCol (snapshot.row target) := by
  simp [presentation, Linger.Core.Listing.humanRow]

/-- Creation never masquerades as a listed session status. -/
theorem presentation_creation (snapshot : Snapshot) (nameCol : Nat) (target : String) :
    Linger.Tools.Picker.presentation snapshot nameCol (.create target) =
      [{ text := s!"+ Create {target}".toList }] := by
  simp [presentation]

/-- Annotation preserves each scalar and its status, in the original order. -/
theorem markPiece_projection (marks : Array Bool) (piece : Linger.Core.Listing.RowPiece) :
    (markPiece marks piece).map (fun char => (char.char, char.status)) =
      piece.text.map (fun char => (char, piece.status)) := by
  simpa only [markPiece, List.map_map, Function.comp_def] using
    congrArg (List.map (fun char => (char, piece.status))) (List.zipIdx_map_fst 0 piece.text)

/-- The scalar index is measured within the piece, not in UTF-8 bytes or cells. -/
theorem markPiece_at (marks : Array Bool) (piece : Linger.Core.Listing.RowPiece) (index : Nat) :
    (markPiece marks piece)[index]? =
      piece.text[index]?.map fun char =>
        { char, status := piece.status,
          matched :=
            match piece.nameSpan with
            | none => false
            | some (start, count) =>
              index ≥ start && index - start < count && marks[index - start]?.getD false } := by
  simp only [markPiece, ge_iff_le, List.getElem?_map, List.getElem?_zipIdx, Nat.zero_add,
    Option.map_map, Function.comp_def]
  rfl

/-- Every emphasized scalar lies inside the declared name span and corresponds
to a true alignment mark; absent or out-of-range marks never emphasize text. -/
theorem markPiece_marked_iff (marks : Array Bool) (piece : Linger.Core.Listing.RowPiece)
    (index : Nat) (char : HighlightedChar) (h : (markPiece marks piece)[index]? = some char) :
    char.matched = true ↔
      ∃ start count,
        piece.nameSpan = some (start, count) ∧
          start ≤ index ∧ index < start + count ∧ marks[index - start]? = some true := by
  rw [markPiece_at] at h
  obtain ⟨raw, _, rfl⟩ := Option.map_eq_some_iff.mp h
  cases hs : piece.nameSpan with
  | none => simp
  | some span =>
    obtain ⟨start, count⟩ := span
    cases hm : marks[index - start]? with
    | none => simp [hm]
    | some
      mark =>
      cases mark <;>
        simp_all only [ge_iff_le, Option.getD_some, Bool.and_false, Bool.and_true, Option.map_some,
          Bool.false_eq_true, Bool.and_eq_true, decide_eq_true_eq, Option.some.injEq, Prod.mk.injEq,
          false_iff, not_exists, not_and, and_imp, forall_apply_eq_imp_iff, forall_eq',
          not_false_eq_true, implies_true]
      constructor
      · rintro ⟨lower, upper⟩
        exact ⟨start, count, ⟨rfl, rfl⟩, lower, by omega, hm⟩
      · rintro ⟨_, _, ⟨rfl, rfl⟩, lower, upper, _⟩
        exact ⟨lower, by omega⟩

/-- Query emphasis preserves the shared text and status for every row, including
creation. Scores cannot change a character, badge, or attachment target. -/
theorem highlightedPresentation_projection (snapshot : Snapshot) (nameCol : Nat) (query : String)
    (item : Item) :
    (highlightedPresentation snapshot nameCol query item).map
        (fun char => (char.char, char.status)) =
      (presentation snapshot nameCol item).flatMap fun piece =>
        piece.text.map (fun char => (char, piece.status)) := by
  simp [highlightedPresentation, List.map_flatMap, markPiece_projection]

theorem highlightedPresentation_text (snapshot : Snapshot) (nameCol : Nat) (query : String)
    (item : Item) :
    (highlightedPresentation snapshot nameCol query item).map (·.char) =
      (presentation snapshot nameCol item).flatMap (·.text) := by
  simpa [List.map_map, List.map_flatMap, Function.comp_def] using
    congrArg (List.map Prod.fst) (highlightedPresentation_projection snapshot nameCol query item)

/-- Removing emphasis yields exactly the same human row that `linger ls` uses. -/
theorem highlightedPresentation_existing_humanRow (snapshot : Snapshot) (nameCol : Nat)
    (query target : String) :
    Linger.Core.Render.utf8s
        ((highlightedPresentation snapshot nameCol query (.existing target)).map (·.char)) =
      Linger.Core.Listing.humanRow nameCol (snapshot.row target) := by
  rw [highlightedPresentation_text]
  exact presentation_existing_humanRow snapshot nameCol target

/-- A displayed scalar is emphasized exactly when the chosen alignment marks
that position in the original target. The badge and separator occupy two
scalars; padding and metadata are outside the name span. -/
theorem highlightedPresentation_existing_marked_iff (snapshot : Snapshot) (nameCol : Nat)
    (query target : String) (index : Nat) (char : HighlightedChar)
    (h : (highlightedPresentation snapshot nameCol query (.existing target))[index]? = some char) :
    char.matched = true ↔
      ∃ alignment,
        Linger.Tools.Fuzzy.align query target = some alignment ∧
          2 ≤ index ∧ index < 2 + target.length ∧ alignment.marks[index - 2]? = some true := by
  let marks := ((Linger.Tools.Fuzzy.align query target).map (·.marks)).getD []
  let body :=
    ((Linger.Core.Listing.rowPieces nameCol (snapshot.row target))[1]?).getD { text := [] }
  have span : body.nameSpan = some (1, target.length) := by
    simp [body, Linger.Core.Listing.rowPieces, snapshot_row_name, String.length_toList]
  cases index with
  | zero =>
    simp only [highlightedPresentation, presentation, Linger.Core.Listing.rowPieces, ge_iff_le,
      Bool.and_eq_true, ↓Char.isValue, List.cons_append, List.nil_append, List.append_assoc,
      beq_iff_eq, String.isEmpty_iff, String.startsWith_string_iff, String.reduceToList,
      String.Slice.toString_eq, List.isEmpty_iff, List.filterMap_eq_nil_iff, ite_eq_right_iff,
      reduceCtorEq, imp_false, Prod.forall, Bool.or_eq_true, String.toList_append,
      List.flatMap_cons, markPiece, List.zipIdx_cons, Nat.zero_add, List.zipIdx_nil, List.map_cons,
      List.map_nil, List.getElem?_toArray, List.flatMap_nil, List.append_nil, List.length_cons,
      List.length_map, List.length_zipIdx, Nat.zero_lt_succ, getElem?_pos, List.getElem_cons_zero,
      Option.some.injEq] at h
    subst char
    simp
  | succ
    index =>
    have row :
      (highlightedPresentation snapshot nameCol query (.existing target))[index + 1]? =
        (markPiece marks.toArray body)[index]? := by
      simp [highlightedPresentation, presentation, body, Linger.Core.Listing.rowPieces, markPiece,
        marks]
    rw [row] at h
    rw [markPiece_marked_iff marks.toArray body index char h]
    simp only [span, Option.some.injEq, Prod.mk.injEq]
    cases ha : Linger.Tools.Fuzzy.align query target with
    | none => simp [marks, ha]
    | some
      a =>
      simp only [ha, Option.map_some, Option.getD_some, List.getElem?_toArray, Option.some.injEq,
        Nat.reduceLeDiff, Nat.reduceSubDiff, exists_eq_left', marks]
      constructor
      · rintro ⟨_, _, ⟨rfl, rfl⟩, lower, upper, marked⟩
        exact ⟨lower, by omega, marked⟩
      · rintro ⟨lower, upper, marked⟩
        exact ⟨1, target.length, ⟨rfl, rfl⟩, lower, by omega, marked⟩

/-- Creation is a labelled action with neither matching emphasis nor a status badge. -/
theorem highlightedPresentation_creation (snapshot : Snapshot) (nameCol : Nat)
    (query target : String) :
    (highlightedPresentation snapshot nameCol query (.create target)).all
        (fun char => !char.matched && char.status.isNone) =
      true := by
  simp [highlightedPresentation, presentation, markPiece]

theorem emphasizeCells_head?_any (chars : List HighlightedChar) :
    (emphasizeCells chars).head?.any
        (fun char => Linger.Core.Vt.charWidth char.char == 0 && char.matched) =
      (chars.takeWhile (fun char => Linger.Core.Vt.charWidth char.char == 0)).any (·.matched) := by
  induction chars with
  | nil => rfl
  | cons char chars ih =>
    cases hz : (Linger.Core.Vt.charWidth char.char == 0) <;> simp [emphasizeCells, hz, ih]

/-- Cell emphasis is exactly the union of a scalar's match and the following
zero-width matches. It stops at the next cell, including a wide character. -/
theorem emphasizeCells_at (chars : List HighlightedChar) (index : Nat) :
    (emphasizeCells chars)[index]? =
      chars[index]?.map fun char =>
        { char with
          matched :=
            char.matched ||
              ((chars.drop (index + 1)).takeWhile
                    (fun next => Linger.Core.Vt.charWidth next.char == 0)).any
                (·.matched) } := by
  induction chars generalizing index with
  | nil => simp [emphasizeCells]
  | cons char chars ih =>
    cases index with
    | zero => simp [emphasizeCells, emphasizeCells_head?_any]
    | succ index => simpa [emphasizeCells] using ih index

/-- Sharing emphasis across a cell never changes its text or status palette. -/
theorem emphasizeCells_projection (chars : List HighlightedChar) :
    (emphasizeCells chars).map (fun char => (char.char, char.status)) =
      chars.map (fun char => (char.char, char.status)) := by
  induction chars with
  | nil => rfl
  | cons char chars ih => simp [emphasizeCells, ih]

theorem mem_visible (candidates : List String) (query target : String) :
    target ∈ visible candidates query ↔
      target ∈ candidates ∧ Linger.Tools.Picker.matches query target = true := by
  simp [visible]

/-- Sublist preservation states order and multiplicity, not just set membership. -/
theorem visible_order (candidates : List String) (query : String) :
    (visible candidates query).Sublist candidates := List.filter_sublist

theorem visible_empty_query (candidates : List String) : visible candidates "" = candidates := by
  simp [visible, matches_empty]

/-- All existing matches precede the optional creation choice. -/
theorem items_existing_prefix (candidates : List String) (query : String)
    (allowCreate : Bool := true) :
    ((visible candidates query).map Item.existing).IsPrefix
      (items candidates query allowCreate) := by
  unfold items
  exact List.prefix_append _ _

theorem mem_items_existing (candidates : List String) (query target : String)
    (allowCreate : Bool := true) :
    Item.existing target ∈ items candidates query allowCreate ↔
      target ∈ candidates ∧ Linger.Tools.Picker.matches query target = true := by
  unfold items
  split <;> simp [mem_visible]

/-- Creation requires the enabled mode and an exact valid, absent target,
independently of whether the query also matches any existing targets. -/
theorem mem_items_create (candidates : List String) (query target : String)
    (allowCreate : Bool := true) :
    Item.create target ∈ items candidates query allowCreate ↔
      allowCreate = true ∧
        target = (if query.isEmpty then Linger.Core.Name.defaultName else query) ∧
        Linger.Core.Remote.targetValid target = true ∧ target ∉ candidates := by
  unfold items
  split <;>
    simp_all only [String.isEmpty_iff, List.contains_eq_mem, Bool.and_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, List.mem_append, List.mem_map,
      reduceCtorEq, and_false, exists_const, List.mem_ite_nil_right, List.mem_cons,
      Item.create.injEq, List.not_mem_nil, or_false, false_or]
  all_goals
    constructor
    · rintro ⟨⟨⟨enabled, valid⟩, absent⟩, rfl⟩
      exact ⟨enabled, rfl, valid, absent⟩
    · rintro ⟨enabled, rfl, valid, absent⟩
      exact ⟨⟨⟨enabled, valid⟩, absent⟩, rfl⟩

/-- Disabling creation leaves exactly the existing matches in their displayed order. -/
theorem items_disabled (candidates : List String) (query : String) :
    items candidates query false = (visible candidates query).map Item.existing := by simp [items]

theorem selected_mem (s : State) (target : String) (h : selected s = some (.existing target)) :
    target ∈ s.candidates ∧ Linger.Tools.Picker.matches s.query target = true :=
  (mem_items_existing _ _ _ s.allowCreate).mp (List.mem_of_getElem? h)

theorem selected_empty (s : State) (h : items s.candidates s.query s.allowCreate = []) :
    selected s = none := by simp [selected, h]

/-- This holds even for a forged cursor, without a state-validity premise. -/
theorem selected_no_create (s : State) (target : String) (disabled : s.allowCreate = false) :
    selected s ≠ some (.create target) := by
  intro h
  have enabled := ((mem_items_create _ _ _ s.allowCreate).mp (List.mem_of_getElem? h)).1
  simp [disabled] at enabled

/-- Identity is the exact target, independent of whether Enter creates or attaches. -/
theorem item_target (target : String) :
    Item.target (.existing target) = target ∧ Item.target (.create target) = target := ⟨rfl, rfl⟩

theorem refresh_query (s : State) (candidates : List String) :
    (refresh s candidates).query = s.query := by simp [refresh]

theorem refresh_candidates (s : State) (candidates : List String) :
    (refresh s candidates).candidates = candidates := by simp [refresh]

theorem refresh_allowCreate (s : State) (candidates : List String) :
    (refresh s candidates).allowCreate = s.allowCreate := by simp [refresh]

/-- Refresh clamps even a forged cursor; it never changes query length. -/
theorem refresh_valid (s : State) (candidates : List String)
    (hquery : s.query.length ≤ maxQueryLength) : (refresh s candidates).Valid := by
  simp only [refresh, State.Valid]
  refine ⟨?_, hquery⟩
  cases hf :
    (items candidates s.query s.allowCreate).findIdx?
      (fun item => some item.target == (selected s).map Item.target) with
  | none => exact Nat.min_le_right _ _
  | some index =>
    have bound := (List.findIdx?_eq_some_iff_findIdx_eq.mp hf).1
    simpa using (show index ≤ (items candidates s.query s.allowCreate).length - 1 by omega)

/-- A surviving target stays selected even after reordering or changing row kind. -/
theorem refresh_selected (s : State) (candidates : List String) (item : Item)
    (hselected : selected s = some item)
    (hpresent : ∃ next ∈ items candidates s.query s.allowCreate, next.target = item.target) :
    (selected (refresh s candidates)).map Item.target = some item.target := by
  let choices := items candidates s.query s.allowCreate
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
      ∀ item ∈ items candidates s.query s.allowCreate,
        some item.target ≠ (selected s).map Item.target) :
    (refresh s candidates).cursor =
      min s.cursor ((items candidates s.query s.allowCreate).length - 1) := by
  have hf :
    (items candidates s.query s.allowCreate).findIdx?
        (fun item => some item.target == (selected s).map Item.target) =
      none :=
    List.findIdx?_eq_none_iff.mpr (by simpa using hmissing)
  simp [refresh, hf]

theorem init_valid (candidates : List String) (allowCreate : Bool := true) :
    (init candidates allowCreate).Valid := by simp [init, State.Valid, maxQueryLength]

theorem init_allowCreate (candidates : List String) (allowCreate : Bool) :
    (init candidates allowCreate).allowCreate = allowCreate := by simp [init]

/-- The arithmetic invariant means either an in-range cursor or the unique empty cursor. -/
theorem valid_cursor (s : State) (h : s.Valid) :
    s.cursor < (items s.candidates s.query s.allowCreate).length ∨
      (items s.candidates s.query s.allowCreate = [] ∧ s.cursor = 0) := by
  obtain ⟨cursor, -⟩ := h
  cases hs : items s.candidates s.query s.allowCreate with
  | nil =>
    right
    simp only [hs, List.length_nil, Nat.zero_sub] at cursor
    exact ⟨rfl, Nat.eq_zero_of_le_zero cursor⟩
  | cons head tail =>
    left
    simp only [hs, List.length_cons] at cursor ⊢
    omega

/-- Every continuing transition preserves bounds established by `init`. -/
theorem step_stay_valid (s next : State) (key : Linger.Tools.Key) (hs : s.Valid)
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

/-- Editing and navigation cannot change the listing snapshot. -/
theorem step_stay_candidates (s next : State) (key : Linger.Tools.Key)
    (h : step s key = .stay next) : next.candidates = s.candidates := by
  cases key <;> simp only [step] at h
  all_goals
    repeat' split at h
    all_goals cases h <;> rfl

/-- Editing and navigation cannot enable creation in a saved catalog. -/
theorem step_stay_allowCreate (s next : State) (key : Linger.Tools.Key)
    (h : step s key = .stay next) : next.allowCreate = s.allowCreate := by
  cases key <;> simp only [step] at h
  all_goals
    repeat' split at h
    all_goals cases h <;> rfl

/-- Acceptance is the only attachment-producing event, and its target is selected verbatim. -/
theorem step_attach_iff (s : State) (key : Linger.Tools.Key) (target : String) :
    step s key = .attach target ↔ key = .accept ∧ selected s = some (.existing target) := by
  cases key <;>
    simp only [step, Bool.and_eq_true, decide_eq_true_eq, reduceCtorEq, false_and, iff_false,
      true_and]
  all_goals split <;> simp_all

/-- Creation also requires acceptance of its own highlighted row. -/
theorem step_create_iff (s : State) (key : Linger.Tools.Key) (target : String) :
    step s key = .create target ↔ key = .accept ∧ selected s = some (.create target) := by
  cases key <;>
    simp only [step, Bool.and_eq_true, decide_eq_true_eq, reduceCtorEq, false_and, iff_false,
      true_and]
  all_goals split <;> simp_all

/-- No key can produce creation in disabled mode, including with an invalid cursor. -/
theorem step_no_create (s : State) (key : Linger.Tools.Key) (target : String)
    (disabled : s.allowCreate = false) : step s key ≠ .create target := by
  intro h
  exact selected_no_create s target disabled ((step_create_iff s key target).mp h).2

/-- Acceptance uses the exact existing target at the displayed filtered index.
An empty result or out-of-range cursor leaves the picker editable. -/
theorem step_accept_disabled (s : State) (disabled : s.allowCreate = false) :
    step s .accept =
      match (visible s.candidates s.query)[s.cursor]? with
      | some target => .attach target
      | none => .stay s := by
  simp only [step, selected, disabled, items_disabled, List.getElem?_map]
  cases (visible s.candidates s.query)[s.cursor]? <;> rfl

/-- No valid-state premise: even a forged or stale cursor cannot manufacture a target. -/
theorem step_attach_mem (s : State) (key : Linger.Tools.Key) (target : String)
    (h : step s key = .attach target) :
    target ∈ s.candidates ∧ Linger.Tools.Picker.matches s.query target = true :=
  selected_mem s target ((step_attach_iff s key target).mp h).2

/-- No state-validity premise: even a forged cursor cannot create a rewritten,
noncanonical or already listed target. Absence refers to the snapshot only. -/
theorem step_create_valid (s : State) (key : Linger.Tools.Key) (target : String)
    (h : step s key = .create target) :
    target = (if s.query.isEmpty then Linger.Core.Name.defaultName else s.query) ∧
      target ∉ s.candidates ∧
      target ≠ "" ∧
      Linger.Core.Name.sanitize ((target.splitOn "@").headD "") = (target.splitOn "@").headD "" ∧
      Linger.Core.Name.Valid ((target.splitOn "@").headD "") ∧
      (∀ char ∈ target.toList, 32 ≤ char.toNat ∧ (char.toNat < 127 ∨ 160 ≤ char.toNat)) ∧
      ((target.splitOn "@").tail = [] ∨ String.intercalate "@" (target.splitOn "@").tail ≠ "") := by
  have selected := ((step_create_iff s key target).mp h).2
  obtain ⟨_, exactTarget, valid, absent⟩ :=
    (mem_items_create _ _ _ s.allowCreate).mp (List.mem_of_getElem? selected)
  obtain ⟨nonempty, nameValid, printable, suffix⟩ :=
    (Linger.Core.Remote.targetValid_iff target).mp valid
  exact
    ⟨exactTarget, absent, nonempty, (Linger.Core.Name.sanitize_eq_self_iff _).mpr nameValid,
      nameValid, printable, suffix⟩

theorem step_empty_accept (s : State) (h : items s.candidates s.query s.allowCreate = []) :
    step s .accept = .stay s := by simp [step, selected_empty s h]

/-- An empty listing offers the default session name for explicit creation. -/
theorem step_init_empty : step (init []) .accept = .create Linger.Core.Name.defaultName := by cbv

theorem step_cancel (s : State) : step s .cancel = .cancel := by simp [step]

theorem step_control_ignored (s : State) (char : Char)
    (h : char.toNat < 32 ∨ (127 ≤ char.toNat ∧ char.toNat < 160)) :
    step s (.text char) = .stay s := by
  have hc : Linger.Tools.Input.printable char = false := by
    simp only [Bool.eq_false_iff]
    intro hp
    have clean := (Linger.Tools.Input.printable_iff char).mp hp
    omega
  simp [step, hc]

theorem step_full_query (s : State) (char : Char) (h : maxQueryLength ≤ s.query.length) :
    step s (.text char) = .stay s := by
  have hn : ¬s.query.length < maxQueryLength := by omega
  simp [step, hn]

end Linger.Tools.Picker
