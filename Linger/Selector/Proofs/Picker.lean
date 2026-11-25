module

import all Linger.Selector.CoreCode.Picker
import all Linger.Target.CoreCode.Name
import all Linger.Display.CoreCode.Listing
import all Linger.Target.CoreCode.Remote
import all Init.Data.String.Legacy
import Linger.Target.Proofs.Name
import Fuzzy.Proofs
import Linger.Target.Proofs.Remote
import Input.Proofs
import all Linger.Display.Proofs.View
import all Linger.Display.Proofs.Listing
public import Linger.Selector.CoreSpec

/-! Selection contracts within and between listing snapshots.

These proofs do not assert that a listed session remains available until the
executor attaches it. They constrain the exact target and permitted outcomes.
-/

namespace Linger.Selector.Picker

/-- Complete equivalence to subsequence matching after ASCII lowercase conversion. -/
theorem matches_iff_sublist (query target : String) :
    Linger.Selector.Picker.matches query target = true ↔
      (query.toList.map Char.toLower).Sublist (target.toList.map Char.toLower) := by
  exact List.isSublist_iff_sublist

/-- Scoring changes emphasis without changing which targets the filter accepts. -/
theorem align_isSome_iff_matches (query target : String) :
    (Fuzzy.align query target).isSome = true ↔ Linger.Selector.Picker.matches query target = true :=
  (Fuzzy.align_isSome_iff_sublist query target).trans (matches_iff_sublist query target).symm

theorem matches_empty (target : String) : Linger.Selector.Picker.matches "" target = true := by
  simp [Linger.Selector.Picker.matches]

/-- Repeated query characters need separate source positions. -/
theorem matches_length_le (query target : String)
    (h : Linger.Selector.Picker.matches query target = true) : query.length ≤ target.length := by
  simpa only [List.length_map, String.length_toList] using
    ((matches_iff_sublist query target).mp h).length_le

/-- A listing's diagnostic is one fixed sentence, naming no text of the listing. -/
theorem listingRows_error (text error : String) (h : listingRows text = .error error) :
    error = "a listing that is not the JSON Lines of session records" := by
  unfold listingRows at h
  split at h
  · cases h
  · cases h; rfl

/-- **The targets of records**: each record's name, in order, each a valid target that no record
before it, nor any of `seen`, names. -/
theorem targets_sound (seen : List String) (records : List (List (String × String)))
    (ts : List String) (h : targets seen records = .ok ts) :
    (∀ t ∈ ts, Linger.Target.Remote.targetValid t = true) ∧
      ts.Nodup ∧ (∀ t ∈ ts, t ∉ seen) ∧ ts = records.filterMap (·.lookup "name") := by
  induction records generalizing seen ts with
  | nil =>
    simp only [targets, Except.ok.injEq] at h
    subst ts
    simp
  | cons record rest ih =>
    simp only [targets] at h
    cases hname : record.lookup "name" with
    | none =>
      simp only [hname] at h
      obtain ⟨valid, distinct, fresh, eq⟩ := ih seen ts h
      exact ⟨valid, distinct, fresh, by simp [hname, eq]⟩
    | some target =>
      simp only [hname] at h
      split at h
      · cases h
      · rename_i valid
        split at h
        · cases h
        · rename_i fresh
          cases hrest : targets (target :: seen) rest with
          | error e => simp [hrest, Except.map] at h
          | ok more =>
            simp only [hrest, Except.map, Except.ok.injEq] at h
            subst ts
            obtain ⟨valids, distinct, freshes, eq⟩ := ih (target :: seen) more hrest
            refine ⟨?_, ?_, ?_, by simp [hname, eq]⟩
            · intro t member
              rcases List.mem_cons.mp member with rfl | member
              · simpa using valid
              · exact valids t member
            · exact List.nodup_cons.mpr ⟨fun inMore => freshes target inMore (by simp), distinct⟩
            · intro t member
              rcases List.mem_cons.mp member with rfl | member
              · simpa using fresh
              · exact fun inSeen => freshes t member (List.mem_cons_of_mem _ inSeen)

/-- The targets' diagnostics use a fixed vocabulary, naming no target. -/
theorem targets_error (seen : List String) (records : List (List (String × String)))
    (error : String) (h : targets seen records = .error error) :
    error = "invalid session target in listing" ∨
      error = "duplicate session target in listing" := by
  induction records generalizing seen with
  | nil => simp [targets] at h
  | cons record rest ih =>
    simp only [targets] at h
    cases hname : record.lookup "name" with
    | none =>
      simp only [hname] at h; exact ih seen h
    | some target =>
      simp only [hname] at h
      split at h
      · cases h; exact .inl rfl
      · split at h
        · cases h; exact .inr rfl
        · cases hrest : targets (target :: seen) rest with
          | error e =>
            simp only [hrest, Except.map, Except.error.injEq] at h
            subst e
            exact ih (target :: seen) hrest
          | ok more => simp [hrest, Except.map] at h

/-- Metadata publication is conditional on complete exact-target validation: a snapshot holds
every line's record, and its targets are their names. -/
theorem parseSnapshot_complete (text : String) (snapshot : Snapshot)
    (h : Linger.Selector.Picker.parseSnapshot text = .ok snapshot) :
    listingRows text = .ok snapshot.records ∧
      targets [] snapshot.records = .ok snapshot.candidates := by
  unfold parseSnapshot at h
  cases hr : listingRows text with
  | error e => simp [hr, bind, Except.bind] at h
  | ok records =>
    simp only [hr, bind, Except.bind] at h
    cases ht : targets [] records with
    | error e => simp [ht] at h
    | ok candidates =>
      simp only [ht, pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact ⟨rfl, ht⟩

/-- Parsing supplies unique identities, canonical local names, and printable exact
targets. A present remote suffix is nonempty; additional `@` characters are retained. -/
theorem parseSnapshot_valid (text : String) (snapshot : Snapshot)
    (h : Linger.Selector.Picker.parseSnapshot text = .ok snapshot) :
    snapshot.candidates.Nodup ∧
      ∀ target ∈ snapshot.candidates,
        target ≠ "" ∧
          Linger.Target.Name.Accepted ((target.splitOn "@").headD "") ∧
          (∀ char ∈ target.toList, 32 ≤ char.toNat ∧ (char.toNat < 127 ∨ 160 ≤ char.toNat)) ∧
          ((target.splitOn "@").tail = [] ∨
            String.intercalate "@" (target.splitOn "@").tail ≠ "") := by
  obtain ⟨valid, distinct, -⟩ := targets_sound [] _ _ (parseSnapshot_complete text snapshot h).2
  refine ⟨distinct, ?_⟩
  intro target ht
  obtain ⟨nonempty, nameValid, clean, host⟩ :=
    (Linger.Target.Remote.targetValid_iff target).mp (valid target ht)
  exact ⟨nonempty, nameValid, clean, host⟩

/-- Every target is the name of a record the listing holds. -/
theorem parseSnapshot_provenance (text : String) (snapshot : Snapshot)
    (h : Linger.Selector.Picker.parseSnapshot text = .ok snapshot) (target : String)
    (ht : target ∈ snapshot.candidates) :
    ∃ record ∈ snapshot.records, record.lookup "name" = some target := by
  obtain ⟨-, -, -, eq⟩ := targets_sound [] _ _ (parseSnapshot_complete text snapshot h).2
  rw [eq] at ht
  obtain ⟨record, member, named⟩ := List.mem_filterMap.mp ht
  exact ⟨record, member, named⟩

/-- Diagnostics use a fixed vocabulary; untrusted listing text is never echoed. -/
theorem parseSnapshot_error_safe (text error : String)
    (h : Linger.Selector.Picker.parseSnapshot text = .error error) :
    ∀ char ∈ error.toList, 32 ≤ char.toNat ∧ char.toNat < 127 := by
  unfold parseSnapshot at h
  cases hr : listingRows text with
  | error e =>
    simp only [hr, bind, Except.bind] at h
    cases h
    rw [listingRows_error _ _ hr]
    decide
  | ok records =>
    simp only [hr, bind, Except.bind] at h
    cases ht : targets [] records with
    | error e =>
      simp only [ht] at h
      cases h
      rcases targets_error [] records _ ht with rfl | rfl <;> decide
    | ok candidates => simp [ht, pure, Except.pure] at h

/-- The identity comes from the validated selection; metadata cannot rename it. -/
theorem snapshot_row_name (snapshot : Snapshot) (target : String) :
    (Linger.Selector.Picker.Snapshot.row snapshot target).lookup "name" = some target := by
  unfold Snapshot.row
  cases found : snapshot.records.find? (fun record => record.lookup "name" == some target) with
  | none => simp
  | some record =>
    have := List.find?_some found
    simpa using this

/-! Remote rows refresh from the latest listing that queried remote hosts, and local
rows from the latest listing; each row keeps exactly the metadata its source reported. -/

/-- A local session name never names a remote row. -/
theorem remoteTarget_check (name : String) (h : Linger.Target.Name.check name = some name) :
    remoteTarget name = false := by
  have hvalid := ((Linger.Target.Name.check_eq_some_iff name name).mp h).2
  unfold remoteTarget
  cases hc : name.toList.contains '@' with
  | false => rfl
  | true =>
    have hmem : '@' ∈ name.toList := by simpa using hc
    exact absurd rfl (Linger.Target.Name.okChar_no_at '@' (hvalid.2.2.1 '@' hmem))

/-- A search that every match of keeps passes a filter finds what it finds without the filter. -/
theorem find?_filter_of_imp {α : Type} (p q : α → Bool) (xs : List α)
    (imp : ∀ x, p x = true → q x = true) : (xs.filter q).find? p = xs.find? p := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    by_cases hp : p x = true
    · simp [imp x hp, hp]
    · by_cases hq : q x = true
      · simp [hq, hp, ih]
      · simp [hq, hp, ih]

/-- A search that no element a filter keeps matches finds nothing there. -/
theorem find?_filter_none {α : Type} (p q : α → Bool) (xs : List α)
    (none' : ∀ x, p x = true → q x = false) : (xs.filter q).find? p = none := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    by_cases hq : q x = true
    · have hp : p x = false := by
        cases h : p x with
        | false => rfl
        | true => exact absurd hq (by simp [none' x h])
      simp [hq, hp, ih]
    · simp [hq, ih]

/-- A record named `target` is a remote host's exactly when the target is remote. -/
theorem remoteRecord_named (record : List (String × String)) (target : String)
    (named : (record.lookup "name" == some target) = true) :
    remoteRecord record = remoteTarget target := by
  have : record.lookup "name" = some target := by simpa using named
  simp [remoteRecord, this]

/-- The merged targets are the latest listing's local targets and the full listing's
remote ones. -/
theorem mem_withRemote (latest full : Snapshot) (target : String) :
    target ∈ (latest.withRemote full).candidates ↔
      target ∈ latest.candidates ∧ remoteTarget target = false ∨
        target ∈ full.candidates ∧ remoteTarget target = true := by
  simp [Snapshot.withRemote, List.mem_filter]

/-- Duplicate-free listings merge without duplicates: the two parts are disjoint. -/
theorem withRemote_nodup (latest full : Snapshot) (hlatest : latest.candidates.Nodup)
    (hfull : full.candidates.Nodup) : (latest.withRemote full).candidates.Nodup := by
  simp only [Snapshot.withRemote]
  rw [List.nodup_append]
  refine ⟨hlatest.filter _, hfull.filter _, ?_⟩
  intro a ha b hb hab
  subst hab
  simp only [List.mem_filter] at ha hb
  rw [hb.2] at ha
  exact absurd ha.2 (by decide)

/-- A local row reads exactly what the latest listing reported. -/
theorem withRemote_row_local (latest full : Snapshot) (target : String)
    (hlocal : remoteTarget target = false) :
    (latest.withRemote full).row target = latest.row target := by
  simp only [Snapshot.row, Snapshot.withRemote, List.find?_append]
  rw [find?_filter_of_imp _ _ _ fun record named => by
      simp [remoteRecord_named record target named, hlocal],
    find?_filter_none _ _ _ fun record named => by
      simp [remoteRecord_named record target named, hlocal]]
  simp

/-- A remote row reads exactly what the latest full listing reported. -/
theorem withRemote_row_remote (latest full : Snapshot) (target : String)
    (hremote : remoteTarget target = true) :
    (latest.withRemote full).row target = full.row target := by
  simp only [Snapshot.row, Snapshot.withRemote, List.find?_append]
  rw [find?_filter_none _ _ _ fun record named => by
      simp [remoteRecord_named record target named, hremote],
    find?_filter_of_imp _ _ _ fun record named => by
      simp [remoteRecord_named record target named, hremote]]
  simp

/-- The selected existing row has precisely the listing's badge, aligned name,
details, labels and watchers, with the same style boundaries. -/
theorem presentation_existing (snapshot : Snapshot) (nameCol : Linger.Display.Listing.Layout)
    (target : String) :
    Linger.Selector.Picker.presentation snapshot nameCol (.existing target) =
      Linger.Display.Listing.rowPieces nameCol (snapshot.row target) := by
  simp [presentation]

/-- Equivalence includes all rendered plain bytes, beyond status glyphs. Clipping
and selection reverse are applied by the terminal executor after this shared row. -/
theorem presentation_existing_humanRow (snapshot : Snapshot)
    (nameCol : Linger.Display.Listing.Layout) (target : String) :
    Terminal.Render.utf8s
        ((Linger.Selector.Picker.presentation snapshot nameCol (.existing target)).flatMap
          (·.text)) =
      Linger.Display.Listing.humanRow nameCol (snapshot.row target) := by
  simp [presentation, Linger.Display.Listing.humanRow]

/-- Creation never masquerades as a listed session status. -/
theorem presentation_creation (snapshot : Snapshot) (nameCol : Linger.Display.Listing.Layout)
    (target : String) :
    Linger.Selector.Picker.presentation snapshot nameCol (.create target) =
      [{ text := s!"+ Create {target}".toList }] := by
  simp [presentation]

/-- Annotation preserves each scalar and its status, in the original order. -/
theorem markPiece_projection (marks : Array Bool) (piece : Linger.Display.Listing.RowPiece) :
    (markPiece marks piece).map (fun char => (char.char, char.style)) =
      piece.text.map (fun char => (char, piece.style)) := by
  simpa only [markPiece, List.map_map, Function.comp_def] using
    congrArg (List.map (fun char => (char, piece.style))) (List.zipIdx_map_fst 0 piece.text)

/-- The scalar index is measured within the piece, not in UTF-8 bytes or cells. -/
theorem markPiece_at (marks : Array Bool) (piece : Linger.Display.Listing.RowPiece) (index : Nat) :
    (markPiece marks piece)[index]? =
      piece.text[index]?.map fun char =>
        { char, style := piece.style,
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
theorem markPiece_marked_iff (marks : Array Bool) (piece : Linger.Display.Listing.RowPiece)
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
theorem highlightedPresentation_projection (snapshot : Snapshot)
    (nameCol : Linger.Display.Listing.Layout) (query : String) (item : Item) :
    (highlightedPresentation snapshot nameCol query item).map
        (fun char => (char.char, char.style)) =
      (presentation snapshot nameCol item).flatMap fun piece =>
        piece.text.map (fun char => (char, piece.style)) := by
  simp [highlightedPresentation, List.map_flatMap, markPiece_projection]

theorem highlightedPresentation_text (snapshot : Snapshot) (nameCol : Linger.Display.Listing.Layout)
    (query : String) (item : Item) :
    (highlightedPresentation snapshot nameCol query item).map (·.char) =
      (presentation snapshot nameCol item).flatMap (·.text) := by
  simpa [List.map_map, List.map_flatMap, Function.comp_def] using
    congrArg (List.map Prod.fst) (highlightedPresentation_projection snapshot nameCol query item)

/-- Removing emphasis yields exactly the same human row that `linger ls` uses. -/
theorem highlightedPresentation_existing_humanRow (snapshot : Snapshot)
    (nameCol : Linger.Display.Listing.Layout) (query target : String) :
    Terminal.Render.utf8s
        ((highlightedPresentation snapshot nameCol query (.existing target)).map (·.char)) =
      Linger.Display.Listing.humanRow nameCol (snapshot.row target) := by
  rw [highlightedPresentation_text]
  exact presentation_existing_humanRow snapshot nameCol target

/-- A displayed scalar is emphasized exactly when the chosen alignment marks
that position in the original target. The two badges and their separators occupy four
scalars; padding and metadata are outside the name span. -/
theorem highlightedPresentation_existing_marked_iff (snapshot : Snapshot)
    (nameCol : Linger.Display.Listing.Layout) (query target : String) (index : Nat)
    (char : HighlightedChar)
    (h : (highlightedPresentation snapshot nameCol query (.existing target))[index]? = some char) :
    char.matched = true ↔
      ∃ alignment,
        Fuzzy.align query target = some alignment ∧
          4 ≤ index ∧ index < 4 + target.length ∧ alignment.marks[index - 4]? = some true := by
  let marks := ((Fuzzy.align query target).map (·.marks)).getD []
  obtain ⟨text, hrow⟩ := Linger.Display.Listing.rowPieces_eq nameCol (snapshot.row target)
  let body :=
    ((Linger.Display.Listing.rowPieces nameCol (snapshot.row target))[3]?).getD { text := [] }
  have span : body.nameSpan = some (1, target.length) := by
    simp [body, hrow, snapshot_row_name, String.length_toList]
  match index, h with
  | 0, h | 1, h | 2,
    h =>
    simp only [highlightedPresentation, presentation, hrow, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, markPiece, List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.some.injEq] at h
    subst char
    simp
  | index + 3,
    h =>
    have row :
      (highlightedPresentation snapshot nameCol query (.existing target))[index + 3]? =
        (markPiece marks.toArray body)[index]? := by
      simp [highlightedPresentation, presentation, body, hrow, markPiece, marks]
    rw [row] at h
    rw [markPiece_marked_iff marks.toArray body index char h]
    simp only [span, Option.some.injEq, Prod.mk.injEq]
    cases ha : Fuzzy.align query target with
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
theorem highlightedPresentation_creation (snapshot : Snapshot)
    (nameCol : Linger.Display.Listing.Layout) (query target : String) :
    (highlightedPresentation snapshot nameCol query (.create target)).all
        (fun char => !char.matched && char.style.isNone) =
      true := by
  simp [highlightedPresentation, presentation, markPiece]

theorem emphasizeCells_head?_any (chars : List HighlightedChar) :
    (emphasizeCells chars).head?.any
        (fun char => Terminal.Vt.charWidth char.char == 0 && char.matched) =
      (chars.takeWhile (fun char => Terminal.Vt.charWidth char.char == 0)).any (·.matched) := by
  induction chars with
  | nil => rfl
  | cons char chars ih =>
    cases hz : (Terminal.Vt.charWidth char.char == 0) <;> simp [emphasizeCells, hz, ih]

/-- Cell emphasis is exactly the union of a scalar's match and the following
zero-width matches. It stops at the next cell, including a wide character. -/
theorem emphasizeCells_at (chars : List HighlightedChar) (index : Nat) :
    (emphasizeCells chars)[index]? =
      chars[index]?.map fun char =>
        { char with
          matched :=
            char.matched ||
              ((chars.drop (index + 1)).takeWhile
                    (fun next => Terminal.Vt.charWidth next.char == 0)).any
                (·.matched) } := by
  induction chars generalizing index with
  | nil => simp [emphasizeCells]
  | cons char chars ih =>
    cases index with
    | zero => simp [emphasizeCells, emphasizeCells_head?_any]
    | succ index => simpa [emphasizeCells] using ih index

/-- Sharing emphasis across a cell never changes its text or status palette. -/
theorem emphasizeCells_projection (chars : List HighlightedChar) :
    (emphasizeCells chars).map (fun char => (char.char, char.style)) =
      chars.map (fun char => (char.char, char.style)) := by
  induction chars with
  | nil => rfl
  | cons char chars ih => simp [emphasizeCells, ih]

theorem mem_visible (candidates : List String) (query target : String)
    (descriptions : List (String × String) := []) :
    target ∈ visible candidates query descriptions ↔
      target ∈ candidates ∧ found descriptions query target = true := by
  simp [visible]

/-- Sublist preservation states order and multiplicity, not just set membership. -/
theorem visible_order (candidates : List String) (query : String)
    (descriptions : List (String × String) := []) :
    (visible candidates query descriptions).Sublist candidates := List.filter_sublist

theorem visible_empty_query (candidates : List String)
    (descriptions : List (String × String) := []) :
    visible candidates "" descriptions = candidates := by simp [visible, found, matches_empty]

/-- All existing matches precede the optional creation choice. -/
theorem items_existing_prefix (candidates : List String) (query : String)
    (allowCreate : Bool := true) (descriptions : List (String × String) := []) :
    ((visible candidates query descriptions).map Item.existing).IsPrefix
      (items candidates query allowCreate descriptions) := by
  unfold items
  exact List.prefix_append _ _

theorem mem_items_existing (candidates : List String) (query target : String)
    (allowCreate : Bool := true) (descriptions : List (String × String) := []) :
    Item.existing target ∈ items candidates query allowCreate descriptions ↔
      target ∈ candidates ∧ found descriptions query target = true := by
  unfold items
  split <;> simp [mem_visible]

/-- Creation requires the enabled mode and an exact valid, absent target,
independently of whether the query also matches any existing targets. -/
theorem mem_items_create (candidates : List String) (query target : String)
    (allowCreate : Bool := true) (descriptions : List (String × String) := []) :
    Item.create target ∈ items candidates query allowCreate descriptions ↔
      allowCreate = true ∧
        target = (if query.isEmpty then Linger.Target.Name.defaultName else query) ∧
        Linger.Target.Remote.targetValid target = true ∧ target ∉ candidates := by
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
theorem items_disabled (candidates : List String) (query : String)
    (descriptions : List (String × String) := []) :
    items candidates query false descriptions =
      (visible candidates query descriptions).map Item.existing := by
  simp [items]

theorem selected_mem (s : State) (target : String) (h : selected s = some (.existing target)) :
    target ∈ s.candidates ∧ found s.descriptions s.query target = true :=
  (mem_items_existing _ _ _ s.allowCreate s.descriptions).mp (List.mem_of_getElem? h)

theorem selected_empty (s : State)
    (h : items s.candidates s.query s.allowCreate s.descriptions = []) : selected s = none := by
  simp [selected, h]

/-- This holds even for a forged cursor, without a state-validity premise. -/
theorem selected_no_create (s : State) (target : String) (disabled : s.allowCreate = false) :
    selected s ≠ some (.create target) := by
  intro h
  have enabled :=
    ((mem_items_create _ _ _ s.allowCreate s.descriptions).mp (List.mem_of_getElem? h)).1
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
    (items candidates s.query s.allowCreate s.descriptions).findIdx?
      (fun item => some item.target == (selected s).map Item.target) with
  | none => exact Nat.min_le_right _ _
  | some index =>
    have bound := (List.findIdx?_eq_some_iff_findIdx_eq.mp hf).1
    simpa using
      (show index ≤ (items candidates s.query s.allowCreate s.descriptions).length - 1 by omega)

/-- A surviving target stays selected even after reordering or changing row kind. -/
theorem refresh_selected (s : State) (candidates : List String) (item : Item)
    (hselected : selected s = some item)
    (hpresent :
      ∃ next ∈ items candidates s.query s.allowCreate s.descriptions, next.target = item.target) :
    (selected (refresh s candidates)).map Item.target = some item.target := by
  let choices := items candidates s.query s.allowCreate s.descriptions
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
      ∀ item ∈ items candidates s.query s.allowCreate s.descriptions,
        some item.target ≠ (selected s).map Item.target) :
    (refresh s candidates).cursor =
      min s.cursor ((items candidates s.query s.allowCreate s.descriptions).length - 1) := by
  have hf :
    (items candidates s.query s.allowCreate s.descriptions).findIdx?
        (fun item => some item.target == (selected s).map Item.target) =
      none :=
    List.findIdx?_eq_none_iff.mpr (by simpa using hmissing)
  simp [refresh, hf]

/-- A listing keeps the rows a view shows unless it sorts them again: it sorts them when asked
to, and otherwise keeps each row still listed where it was, then adds the new ones. -/
theorem relist_rows (s : State) (resort : Bool) (ordered : List String)
    (descriptions : List (String × String)) :
    (relist s resort ordered descriptions).candidates =
        (if resort then ordered
        else
          s.candidates.filter (fun t => ordered.contains t) ++
            ordered.filter fun t => !s.candidates.contains t) ∧
      (relist s resort ordered descriptions).query = s.query ∧
      (relist s resort ordered descriptions).descriptions = descriptions := by
  simp [relist, refresh, arrange]

/-- **Returning is the inverse of leaving**: a visit enters with the rows the view it left
showed, where they were, the new ones last, and with an empty query selects the session it
returns from, or the one it was opened inside, while the listing has it; else the first row. -/
theorem enter_returns (s : State) (shown : List String) (focus : Option String)
    (ordered : List String) (descriptions : List (String × String)) :
    (enter s shown focus ordered descriptions).candidates =
        shown.filter (fun t => ordered.contains t) ++ ordered.filter (fun t => !shown.contains t) ∧
      (enter s shown focus ordered descriptions).query = s.query ∧
      (∀ t,
        focus = some t →
          s.query = "" →
          t ∈ ordered →
          (enter s shown focus ordered
                  descriptions).candidates[(enter s shown focus ordered descriptions).cursor]? =
            some t) ∧
      ((∀ t, focus = some t → s.query = "" → t ∉ ordered) →
        (enter s shown focus ordered descriptions).cursor = 0) := by
  have listed (t : String) : (arrange shown ordered).contains t = true ↔ t ∈ ordered := by
    simp only [arrange, List.contains_iff_mem, List.mem_append, List.mem_filter]
    constructor
    · rintro (⟨_, h⟩ | ⟨h, _⟩) <;> simpa using h
    · intro h
      by_cases hs : t ∈ shown
      · exact Or.inl ⟨hs, by simpa using h⟩
      · exact Or.inr ⟨h, by simpa using hs⟩
  refine ⟨by simp [enter, arrange], by simp [enter], ?_, ?_⟩
  · intro t hfocus hquery hmem
    have hc := (listed t).mpr hmem
    have bound := List.idxOf_lt_length_of_mem (List.contains_iff_mem.mp hc)
    simp only [enter, hfocus, hquery, hc]
    simp [List.getElem?_eq_getElem bound, List.getElem_idxOf bound]
  · intro hnone
    cases hfocus : focus with
    | none => simp [enter]
    | some t =>
      by_cases hquery : s.query = ""
      · have hc : (arrange shown ordered).contains t = false := by
          cases h : (arrange shown ordered).contains t
          · rfl
          · exact absurd ((listed t).mp h) (hnone t hfocus hquery)
        simp only [enter, hc]
        simp
      · simp [enter, hquery]

theorem init_valid (candidates : List String) (allowCreate : Bool := true) :
    (init candidates allowCreate).Valid := by simp [init, State.Valid, maxQueryLength]

theorem init_allowCreate (candidates : List String) (allowCreate : Bool) :
    (init candidates allowCreate).allowCreate = allowCreate := by simp [init]

/-- The arithmetic invariant means either an in-range cursor or the unique empty cursor. -/
theorem valid_cursor (s : State) (h : s.Valid) :
    s.cursor < (items s.candidates s.query s.allowCreate s.descriptions).length ∨
      (items s.candidates s.query s.allowCreate s.descriptions = [] ∧ s.cursor = 0) := by
  obtain ⟨cursor, -⟩ := h
  cases hs : items s.candidates s.query s.allowCreate s.descriptions with
  | nil =>
    right
    simp only [hs, List.length_nil, Nat.zero_sub] at cursor
    exact ⟨rfl, Nat.eq_zero_of_le_zero cursor⟩
  | cons head tail =>
    left
    simp only [hs, List.length_cons] at cursor ⊢
    omega

/-- Every continuing transition preserves bounds established by `init`. -/
theorem step_stay_valid (s next : State) (key : Linger.Selector.Key) (hs : s.Valid)
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
    split
    · exact ⟨cursor, query⟩
    · rename_i rows
      have :=
        Nat.mod_lt (s.cursor + (items s.candidates s.query s.allowCreate s.descriptions).length - 1)
          (Nat.pos_of_ne_zero rows)
      refine ⟨?_, query⟩
      dsimp only
      omega
  | down =>
    cases h
    split
    · exact ⟨cursor, query⟩
    · rename_i rows
      have := Nat.mod_lt (s.cursor + 1) (Nat.pos_of_ne_zero rows)
      refine ⟨?_, query⟩
      dsimp only
      omega
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
  | deleteCharEof =>
    simp only [step] at h
    split at h
    · cases h
    · cases h
      exact ⟨cursor, query⟩
  | refresh =>
    cases h
    exact ⟨cursor, query⟩

/-- Editing and navigation cannot change the listing snapshot. -/
theorem step_stay_candidates (s next : State) (key : Linger.Selector.Key)
    (h : step s key = .stay next) : next.candidates = s.candidates := by
  cases key <;> simp only [step] at h
  all_goals
    repeat' split at h
    all_goals cases h <;> rfl

/-- Editing and navigation cannot enable creation in a saved catalog. -/
theorem step_stay_allowCreate (s next : State) (key : Linger.Selector.Key)
    (h : step s key = .stay next) : next.allowCreate = s.allowCreate := by
  cases key <;> simp only [step] at h
  all_goals
    repeat' split at h
    all_goals cases h <;> rfl

/-- Acceptance is the only attachment-producing event, and its target is selected verbatim. -/
theorem step_attach_iff (s : State) (key : Linger.Selector.Key) (target : String) :
    step s key = .attach target ↔ key = .accept ∧ selected s = some (.existing target) := by
  cases key <;>
    simp only [step, Bool.and_eq_true, decide_eq_true_eq, reduceCtorEq, false_and, iff_false,
      true_and]
  all_goals split <;> simp_all

/-- Creation also requires acceptance of its own highlighted row. -/
theorem step_create_iff (s : State) (key : Linger.Selector.Key) (target : String) :
    step s key = .create target ↔ key = .accept ∧ selected s = some (.create target) := by
  cases key <;>
    simp only [step, Bool.and_eq_true, decide_eq_true_eq, reduceCtorEq, false_and, iff_false,
      true_and]
  all_goals split <;> simp_all

/-- No key can produce creation in disabled mode, including with an invalid cursor. -/
theorem step_no_create (s : State) (key : Linger.Selector.Key) (target : String)
    (disabled : s.allowCreate = false) : step s key ≠ .create target := by
  intro h
  exact selected_no_create s target disabled ((step_create_iff s key target).mp h).2

/-- Acceptance uses the exact existing target at the displayed filtered index.
An empty result or out-of-range cursor leaves the picker editable. -/
theorem step_accept_disabled (s : State) (disabled : s.allowCreate = false) :
    step s .accept =
      match (visible s.candidates s.query s.descriptions)[s.cursor]? with
      | some target => .attach target
      | none => .stay s := by
  simp only [step, selected, disabled, items_disabled, List.getElem?_map]
  cases (visible s.candidates s.query s.descriptions)[s.cursor]? <;> rfl

/-- No valid-state premise: even a forged or stale cursor cannot manufacture a target. -/
theorem step_attach_mem (s : State) (key : Linger.Selector.Key) (target : String)
    (h : step s key = .attach target) :
    target ∈ s.candidates ∧ found s.descriptions s.query target = true :=
  selected_mem s target ((step_attach_iff s key target).mp h).2

/-- No state-validity premise: even a forged cursor cannot create a rewritten,
noncanonical or already listed target. Absence refers to the snapshot only. -/
theorem step_create_valid (s : State) (key : Linger.Selector.Key) (target : String)
    (h : step s key = .create target) :
    target = (if s.query.isEmpty then Linger.Target.Name.defaultName else s.query) ∧
      target ∉ s.candidates ∧
      target ≠ "" ∧
      Linger.Target.Name.Accepted ((target.splitOn "@").headD "") ∧
      (∀ char ∈ target.toList, 32 ≤ char.toNat ∧ (char.toNat < 127 ∨ 160 ≤ char.toNat)) ∧
      ((target.splitOn "@").tail = [] ∨ String.intercalate "@" (target.splitOn "@").tail ≠ "") := by
  have selected := ((step_create_iff s key target).mp h).2
  obtain ⟨_, exactTarget, valid, absent⟩ :=
    (mem_items_create _ _ _ s.allowCreate s.descriptions).mp (List.mem_of_getElem? selected)
  obtain ⟨nonempty, nameValid, printable, suffix⟩ :=
    (Linger.Target.Remote.targetValid_iff target).mp valid
  exact ⟨exactTarget, absent, nonempty, nameValid, printable, suffix⟩

theorem step_empty_accept (s : State)
    (h : items s.candidates s.query s.allowCreate s.descriptions = []) :
    step s .accept = .stay s := by simp [step, selected_empty s h]

/-- An empty listing offers the default session name for explicit creation. -/
theorem step_init_empty : step (init []) .accept = .create Linger.Target.Name.defaultName := by cbv

theorem step_cancel (s : State) : step s .cancel = .cancel := by simp [step]

/-- **Ctrl-D ends only an empty line.** `deleteCharEof` deletes the character under the cursor,
which sits after the query, so there is none: an empty query ends the visit, as cancelling does,
and any other leaves the state as it is. -/
theorem step_deleteCharEof (s : State) :
    step s .deleteCharEof = if s.query = "" then .cancel else .stay s := by
  simp [step, String.isEmpty_iff]

/-- The rows Enter acts on are the first cursor positions, as many as `items` lists: Enter keeps
the chooser open exactly from the position after the last row on. -/
theorem accept_stays_iff (s : State) (i : Nat) :
    (∃ next, step { s with cursor := i } .accept = .stay next) ↔
      (items s.candidates s.query s.allowCreate s.descriptions).length ≤ i := by
  simp only [step, selected]
  cases hi : (items s.candidates s.query s.allowCreate s.descriptions)[i]? with
  | none => exact ⟨fun _ => List.getElem?_eq_none_iff.mp hi, fun _ => ⟨_, rfl⟩⟩
  | some item =>
    have bound := (List.getElem?_eq_some_iff.mp hi).1
    constructor
    · rintro ⟨next, h⟩
      cases item <;> simp at h
    · intro hle
      omega

/-- Only the number of rows is the `n` from which Enter keeps the chooser open. -/
theorem rows_eq (s : State) (n : Nat)
    (rows : ∀ i, (∃ next, step { s with cursor := i } .accept = .stay next) ↔ n ≤ i) :
    n = (items s.candidates s.query s.allowCreate s.descriptions).length := by
  have past := (accept_stays_iff s n).mp ((rows n).mpr (Nat.le_refl n))
  have last := (rows _).mp ((accept_stays_iff s _).mpr (Nat.le_refl _))
  omega

/-- Down selects the next row, the first after the last, and with no row changes nothing. -/
theorem step_down (s : State) (cursor : Nat) :
    step { s with cursor } .down =
      .stay
        (if (items s.candidates s.query s.allowCreate s.descriptions).length = 0 then
          { s with cursor }
        else
          { s with
            cursor :=
              (cursor + 1) % (items s.candidates s.query s.allowCreate s.descriptions).length }) :=
  rfl

/-- Up selects the row before, the last before the first, and with no row changes nothing. -/
theorem step_up (s : State) (cursor : Nat) :
    step { s with cursor } .up =
      .stay
        (if (items s.candidates s.query s.allowCreate s.descriptions).length = 0 then
          { s with cursor }
        else
          { s with
            cursor :=
              (cursor + (items s.candidates s.query s.allowCreate s.descriptions).length - 1) %
                (items s.candidates s.query s.allowCreate s.descriptions).length }) := rfl

/-- `k` moves down from row `cursor` of the rows select row `(cursor + k) % n`; with no row,
they change nothing. -/
theorem press_down (s : State) (cursor k : Nat)
    (row :
      cursor < (items s.candidates s.query s.allowCreate s.descriptions).length ∨
        (items s.candidates s.query s.allowCreate s.descriptions).length = 0) :
    press step { s with cursor } (List.replicate k .down) =
      .stay
        (if (items s.candidates s.query s.allowCreate s.descriptions).length = 0 then
          { s with cursor }
        else
          { s with
            cursor :=
              (cursor + k) %
                (items s.candidates s.query s.allowCreate s.descriptions).length }) := by
  induction k generalizing cursor with
  | zero =>
    simp only [List.replicate_zero, press, Nat.add_zero]
    split
    · rfl
    · rename_i rows
      rw [Nat.mod_eq_of_lt (row.resolve_right rows)]
  | succ k ih =>
    rw [List.replicate_succ, press, step_down]
    by_cases rows : (items s.candidates s.query s.allowCreate s.descriptions).length = 0
    · rw [ite_eq_left rows, ite_eq_left rows]
      dsimp only
      rw [ih cursor row, ite_eq_left rows]
    · rw [ite_eq_right rows, ite_eq_right rows]
      dsimp only
      rw [ih _ (Or.inl (Nat.mod_lt _ (Nat.pos_of_ne_zero rows))), ite_eq_right rows,
        Nat.mod_add_mod, show cursor + 1 + k = cursor + (k + 1) by omega]

/-- `k` moves up from row `cursor` of the `n` rows select row `(cursor - k) % n`, the remainder
`%` gives on `Int`; with no row, they change nothing. -/
theorem press_up (s : State) (cursor k : Nat)
    (row :
      cursor < (items s.candidates s.query s.allowCreate s.descriptions).length ∨
        (items s.candidates s.query s.allowCreate s.descriptions).length = 0) :
    press step { s with cursor } (List.replicate k .up) =
      .stay
        (if (items s.candidates s.query s.allowCreate s.descriptions).length = 0 then
          { s with cursor }
        else
          { s with
            cursor :=
              ((cursor - k : Int) %
                  (items s.candidates s.query s.allowCreate s.descriptions).length).toNat }) := by
  induction k generalizing cursor with
  | zero =>
    simp only [List.replicate_zero, press, Int.natCast_zero, Int.sub_zero]
    split
    · rfl
    · rename_i rows
      have bound := row.resolve_right rows
      rw [Int.emod_eq_of_lt (by omega) (by omega), Int.toNat_natCast]
  | succ k ih =>
    rw [List.replicate_succ, press, step_up]
    by_cases rows : (items s.candidates s.query s.allowCreate s.descriptions).length = 0
    · rw [ite_eq_left rows, ite_eq_left rows]
      dsimp only
      rw [ih cursor row, ite_eq_left rows]
    · rw [ite_eq_right rows, ite_eq_right rows]
      dsimp only
      have positive := Nat.pos_of_ne_zero rows
      rw [ih _ (Or.inl (Nat.mod_lt _ positive)), ite_eq_right rows]
      congr 3
      rw [Int.natCast_emod, Int.sub_emod, Int.emod_emod, ← Int.sub_emod]
      have shift :
        ((cursor + (items s.candidates s.query s.allowCreate s.descriptions).length - 1 : Nat) :
              Int) -
            k =
          (cursor - (k + 1 : Nat) : Int) +
            (items s.candidates s.query s.allowCreate s.descriptions).length := by
        omega
      rw [shift, Int.add_emod_right]

/-- **The moves cycle**, around the `n` rows Enter acts on, the creation row among them when the
chooser offers one: `k` moves down from row `i` select row `(i + k) % n`, and `k` moves up select
row `(i - k) % n`, so up undoes down; with no row, a move changes nothing. -/
theorem moves_cycle (s : State) (n k : Nat)
    (rows : ∀ i, (∃ next, step { s with cursor := i } .accept = .stay next) ↔ n ≤ i)
    (row : s.cursor < n ∨ n = 0) :
    press step s (List.replicate k .down) =
        .stay (if n = 0 then s else { s with cursor := (s.cursor + k) % n }) ∧
      press step s (List.replicate k .up) =
        .stay (if n = 0 then s else { s with cursor := ((s.cursor - k : Int) % n).toNat }) := by
  obtain rfl := rows_eq s n rows
  exact ⟨press_down s s.cursor k row, press_up s s.cursor k row⟩

/-- **Clamped moves are no cycle.** Of two rows, with the second selected, a clamped move down
stays there, where the cycle selects the first row. -/
theorem clamped_not_cycle :
    ¬∀ (s : State) (n k : Nat),
        (∀ i, (∃ next, clamped step { s with cursor := i } .accept = .stay next) ↔ n ≤ i) →
          s.cursor < n ∨ n = 0 →
          press (clamped step) s (List.replicate k .down) =
              .stay (if n = 0 then s else { s with cursor := (s.cursor + k) % n }) ∧
            press (clamped step) s (List.replicate k .up) =
              .stay
                (if n = 0 then s else { s with cursor := ((s.cursor - k : Int) % n).toNat }) := by
  intro h
  have two : (items ["a", "b"] "" false []).length = 2 := by
    simp [items_disabled, visible_empty_query]
  have rows (i : Nat) :
    (∃ next,
        clamped step
            { ({ candidates := ["a", "b"], cursor := 1, allowCreate := false } : State) with
              cursor := i }
            .accept =
          .stay next) ↔
      2 ≤ i := by
    rw [← two]
    exact accept_stays_iff { candidates := ["a", "b"], cursor := 1, allowCreate := false } i
  have down :=
    (h { candidates := ["a", "b"], cursor := 1, allowCreate := false } 2 1 rows
        (Or.inl (by decide))).1
  obtain ⟨next, past⟩ :=
    (accept_stays_iff { candidates := ["a", "b"], cursor := 1, allowCreate := false } 2).mpr
      (Nat.le_of_eq two)
  simp only [List.replicate, press, clamped] at down
  rw [past] at down
  simp at down

theorem step_control_ignored (s : State) (char : Char)
    (h : char.toNat < 32 ∨ (127 ≤ char.toNat ∧ char.toNat < 160)) :
    step s (.text char) = .stay s := by
  have hc : Input.printable char = false := by
    simp only [Bool.eq_false_iff]
    intro hp
    have clean := (Input.printable_iff char).mp hp
    omega
  simp [step, hc]

theorem step_full_query (s : State) (char : Char) (h : maxQueryLength ≤ s.query.length) :
    step s (.text char) = .stay s := by
  have hn : ¬s.query.length < maxQueryLength := by omega
  simp [step, hn]

/-- A character added to a query matches only targets the shorter query matched. -/
theorem matches_push (query target : String) (c : Char)
    (h : Linger.Selector.Picker.matches (query.push c) target = true) :
    Linger.Selector.Picker.matches query target = true := by
  rw [matches_iff_sublist] at h ⊢
  refine List.Sublist.trans ?_ h
  simp only [String.toList_push, List.map_append]
  exact List.sublist_append_left _ _

/-- **Typing narrows**: a character added to the query keeps only rows the shorter query kept,
in their order. -/
theorem visible_push_sublist (candidates : List String) (query : String) (c : Char)
    (descriptions : List (String × String) := []) :
    (visible candidates (query.push c) descriptions).Sublist
      (visible candidates query descriptions) := by
  have heq :
    visible candidates (query.push c) descriptions =
      (visible candidates query descriptions).filter (found descriptions (query.push c)) := by
    unfold visible
    rw [List.filter_filter]
    apply List.filter_congr
    intro x _
    cases h : found descriptions (query.push c) x
    · simp
    · simp only [found, Bool.or_eq_true] at h
      simp only [found, Bool.true_and]
      rcases h with h | h
      · simp [matches_push _ _ c h]
      · simp [matches_push _ _ c h]
  rw [heq]
  exact List.filter_sublist

/-- …so the count beside the query never grows as it is typed. -/
theorem matchCount_push (s : State) (c : Char) :
    matchCount { s with query := s.query.push c } ≤ matchCount s :=
  (visible_push_sublist s.candidates s.query c s.descriptions).length_le

/-- **Groups are typeable**: typing a group's name keeps every row of the group. -/
theorem stem_visible (candidates : List String) (target : String) (depth : Nat)
    (h : target ∈ candidates) (descriptions : List (String × String) := []) :
    target ∈ visible candidates (Linger.Display.View.stem depth target) descriptions := by
  rw [mem_visible candidates _ target descriptions]
  refine ⟨h, ?_⟩
  simp only [found, Bool.or_eq_true]
  left
  rw [matches_iff_sublist]
  exact (Linger.Display.View.stem_prefix depth target).sublist.map _

/-- …so a group's name, typed as the query, leaves each of its rows to choose. -/
theorem stem_items (candidates : List String) (target : String) (depth : Nat) (allowCreate : Bool)
    (h : target ∈ candidates) (descriptions : List (String × String) := []) :
    Item.existing target ∈
      items candidates (Linger.Display.View.stem depth target) allowCreate descriptions :=
  (mem_items_existing candidates _ target allowCreate descriptions).mpr
    ((mem_visible candidates _ target descriptions).mp
      (stem_visible candidates target depth h descriptions))

/-- **A frame never has more lines than the terminal.** -/
theorem frameLines_length (state : State) (snapshot : Snapshot)
    (statusOf : String → Linger.Display.Status.Status) (loaded withColor savedTmux : Bool)
    (remoteAge : Option Nat) (rows : Nat) :
    (frameLines state snapshot statusOf loaded withColor savedTmux remoteAge rows).length ≤
      max 1 rows := by
  unfold frameLines
  exact List.length_take_le _ _

end Linger.Selector.Picker
