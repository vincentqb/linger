module

public import Linger.Tools.Fuzzy
import all Linger.Tools.Fuzzy

public section

/-! A declarative weighted subsequence semantics, independent of the table.

Every legal path consumes one original target position at a time. A gap earns
the configured score while a query remains; completing the query leaves the
trailing positions unmarked and free. Taking a character earns its word bonus
and the configured adjacency score when the previous position was taken.
The certificate covers every integer scoring policy.
-/

namespace Linger.Tools.Fuzzy

/-- Legal alignments over folded characters carrying their original word bonuses. -/
inductive Walk (scoring : Scoring) : List Char → List (Char × Int) → Bool → Alignment → Prop where
  |
  empty (target : List (Char × Int)) (adjacent : Bool) :
    Walk scoring [] target adjacent ⟨0, List.replicate target.length false⟩
  |
  gap {q : Char} {qs : List Char} {c : Char} {bonus : Int} {target : List (Char × Int)}
    {adjacent : Bool} {a : Alignment} (rest : Walk scoring (q :: qs) target false a) :
    Walk scoring (q :: qs) ((c, bonus) :: target) adjacent ⟨a.score + scoring.gap, false :: a.marks⟩
  |
  take {q : Char} {qs : List Char} {bonus : Int} {target : List (Char × Int)} {adjacent : Bool}
    {a : Alignment} (rest : Walk scoring qs target true a) :
    Walk scoring (q :: qs) ((q, bonus) :: target) adjacent
      ⟨a.score + (bonus + if adjacent then scoring.adjacent else 0), true :: a.marks⟩

/-- True-first lexicographic order on masks, including equality. -/
private def MaskLE (left right : List Bool) : Prop :=
  left = right ∨ List.Lex (fun a b => a = true ∧ b = false) left right

private theorem MaskLE.cons (mark : Bool) {left right : List Bool} (h : MaskLE left right) :
    MaskLE (mark :: left) (mark :: right) := by
  rcases h with rfl | h
  · exact .inl rfl
  · exact .inr (.cons h)

private def Optimal (legal : Alignment → Prop) : Option Alignment → Prop
  | none => ∀ a, ¬legal a
  | some a =>
    legal a ∧
      (∀ b, legal b → b.score ≤ a.score) ∧ ∀ b, legal b → b.score = a.score → MaskLE a.marks b.marks

private theorem optimal_sound {legal : Alignment → Prop} {answer : Option Alignment}
    (h : Optimal legal answer) {a : Alignment} (ha : answer = some a) : legal a := by
  subst answer
  exact h.1

private theorem optimal_complete {legal : Alignment → Prop} {answer : Option Alignment}
    (h : Optimal legal answer) {a : Alignment} (ha : legal a) :
    ∃ b, answer = some b ∧ a.score ≤ b.score := by
  cases answer with
  | none => exact False.elim (h a ha)
  | some b => exact ⟨b, rfl, h.2.1 a ha⟩

private theorem best_optimal (left right : Option Alignment) (p q : Alignment → Prop)
    (hl : Optimal p left) (hr : Optimal q right)
    (ordered : ∀ a, p a → ∀ b, q b → MaskLE a.marks b.marks) :
    Optimal (fun a => p a ∨ q a) (best left right) := by
  cases left <;> cases right <;>
    simp_all only [Optimal, best, ge_iff_le, or_self, or_true, or_false, false_or, and_self,
      not_false_eq_true, implies_true]
  split <;> simp_all only [Int.not_le, true_or, or_true, true_and] <;> grind

/-- Equal scores always retain the left candidate, the current-position match. -/
private theorem best_left_tie (a b : Alignment) (h : a.score = b.score) :
    best (some a) (some b) = some a := by simp [best, h]

private theorem prepend_optimal (mark : Bool) (score : Int) (answer : Option Alignment)
    (p : Alignment → Prop) (h : Optimal p answer) :
    Optimal (fun b => ∃ a, p a ∧ b = ⟨a.score + score, mark :: a.marks⟩)
      (prepend mark score answer) := by
  cases answer with
  | none => simp_all [Optimal, prepend]
  | some a =>
    refine ⟨⟨a, h.1, rfl⟩, ?_, ?_⟩
    · rintro b ⟨c, hc, rfl⟩
      exact Int.add_le_add_right (h.2.1 c hc) score
    · rintro b ⟨c, hc, rfl⟩ heq
      exact (h.2.2 c hc (by simpa using heq)).cons mark

theorem Walk.sublist {scoring : Scoring} {query : List Char} {target : List (Char × Int)}
    {adjacent : Bool} {a : Alignment} (h : Walk scoring query target adjacent a) :
    query.Sublist (target.map Prod.fst) := by
  induction h with
  | empty => exact List.nil_sublist _
  | gap _ ih => exact ih.cons _
  | take _ ih => exact ih.cons_cons _

theorem Walk.length {scoring : Scoring} {query : List Char} {target : List (Char × Int)}
    {adjacent : Bool} {a : Alignment} (h : Walk scoring query target adjacent a) :
    a.marks.length = target.length := by induction h <;> simp_all

private theorem unmarked {α β : Type} (target : List α) (f : α → β) :
    ((target.zip (List.replicate target.length false)).filterMap fun (c, marked) =>
        if marked then some (f c) else none) =
      [] := by
  induction target with
  | nil => rfl
  | cons c target ih =>
    simpa only [List.length_cons, List.replicate_succ, List.zip_cons_cons, List.filterMap_cons,
      Bool.false_eq_true, ↓reduceIte] using ih

/-- True mask positions spell the query in order, with no duplication or omission. -/
theorem Walk.spells {scoring : Scoring} {query : List Char} {target : List (Char × Int)}
    {adjacent : Bool} {a : Alignment} (h : Walk scoring query target adjacent a) :
    ((target.zip a.marks).filterMap fun (c, marked) => if marked then some c.1 else none) =
      query := by
  induction h with
  | empty => exact unmarked _ _
  | gap _ ih => simpa using ih
  | take _ ih => simpa using ih

private theorem walk_empty_iff (scoring : Scoring) (target : List (Char × Int)) (adjacent : Bool)
    (a : Alignment) :
    Walk scoring [] target adjacent a ↔ a = ⟨0, List.replicate target.length false⟩ := by
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    exact .empty _ _

private theorem walk_exists (scoring : Scoring) (query : List Char) (target : List (Char × Int))
    (adjacent : Bool) (h : query.Sublist (target.map Prod.fst)) :
    ∃ a, Walk scoring query target adjacent a := by
  induction target generalizing query adjacent with
  | nil =>
    have : query = [] := List.sublist_nil.mp h
    subst query
    exact ⟨_, .empty _ _⟩
  | cons c target ih =>
    cases query with
    | nil => exact ⟨_, .empty _ _⟩
    | cons q qs =>
      rcases List.sublist_cons_iff.mp h with hgap | ⟨rest, heq, htake⟩
      · obtain ⟨a, ha⟩ := ih _ false hgap
        exact ⟨_, .gap ha⟩
      · cases c with
        | mk c bonus =>
          cases heq
          obtain ⟨a, ha⟩ := ih _ true htake
          exact ⟨_, .take ha⟩

private theorem walk_cons_iff (scoring : Scoring) (q c : Char) (qs : List Char) (bonus : Int)
    (target : List (Char × Int)) (adjacent : Bool) (a : Alignment) :
    Walk scoring (q :: qs) ((c, bonus) :: target) adjacent a ↔
      (q = c ∧
          ∃ b,
            Walk scoring qs target true b ∧
              a = ⟨b.score + (bonus + if adjacent then scoring.adjacent else 0), true :: b.marks⟩) ∨
        (∃ b,
          Walk scoring (q :: qs) target false b ∧
            a = ⟨b.score + scoring.gap, false :: b.marks⟩) := by
  constructor
  · intro h
    cases h with
    | gap h => exact .inr ⟨_, h, rfl⟩
    | take h => exact .inl ⟨rfl, _, h, rfl⟩
  · rintro (⟨rfl, b, h, rfl⟩ | ⟨b, h, rfl⟩)
    · exact .take h
    · exact .gap h

private theorem optimal_congr (p q : Alignment → Prop) (answer : Option Alignment)
    (h : ∀ a, p a ↔ q a) : Optimal p answer ↔ Optimal q answer := by
  cases answer <;> simp only [Optimal] <;> grind

private theorem advance_optimal (scoring : Scoring) (q c : Char) (qs : List Char) (bonus : Int)
    (target : List (Char × Int)) (adjacent : Bool) (taken skipped : Option Alignment)
    (ht : Optimal (Walk scoring qs target true) taken)
    (hs : Optimal (Walk scoring (q :: qs) target false) skipped) :
    Optimal (Walk scoring (q :: qs) ((c, bonus) :: target) adjacent)
      (best
        (prepend true (bonus + if adjacent then scoring.adjacent else 0)
          (if q == c then taken else none))
        (prepend false scoring.gap skipped)) := by
  apply (optimal_congr _ _ _ (walk_cons_iff scoring q c qs bonus target adjacent)).mpr
  apply best_optimal
  · by_cases h : q = c
    · simpa [h] using
        prepend_optimal true (bonus + if adjacent then scoring.adjacent else 0) taken
          (Walk scoring qs target true) ht
    · simp [h, prepend, Optimal]
  · exact prepend_optimal false scoring.gap skipped (Walk scoring (q :: qs) target false) hs
  · rintro a ⟨_, x, _, rfl⟩ b ⟨y, _, rfl⟩
    exact .inr (.rel ⟨rfl, rfl⟩)

private def CellOptimal (scoring : Scoring) (query : List Char) (target : List (Char × Int))
    (cell : Cell) : Prop :=
  Optimal (Walk scoring query target false) cell.gap ∧
    Optimal (Walk scoring query target true) cell.adjacent

/-- The row has exactly one certified answer pair for each target suffix. -/
private inductive TableOptimal (scoring : Scoring) (query : List Char) :
    List (Char × Int) → List Cell → Prop where
  | nil {cell : Cell} : CellOptimal scoring query [] cell → TableOptimal scoring query [] [cell]
  |
  cons {c : Char × Int} {target : List (Char × Int)} {cell : Cell} {tail : List Cell} :
    CellOptimal scoring query (c :: target) cell →
      TableOptimal scoring query target tail →
      TableOptimal scoring query (c :: target) (cell :: tail)

private theorem TableOptimal.head {scoring : Scoring} {query : List Char}
    {target : List (Char × Int)} {cells : List Cell} (h : TableOptimal scoring query target cells) :
    CellOptimal scoring query target (cells.headD default) := by cases h <;> assumption

private theorem emptyRow_head (n : Nat) :
    (emptyRow n).headD default =
      { gap := some ⟨0, List.replicate n false⟩,
        adjacent := some ⟨0, List.replicate n false⟩ } := by
  induction n with
  | zero => rfl
  | succ n
    ih =>
    change
      Cell.mk (prepend false 0 ((emptyRow n).headD default).gap)
          (prepend false 0 ((emptyRow n).headD default).gap) =
        _
    rw [ih]
    rfl

private theorem emptyRow_optimal (scoring : Scoring) (target : List (Char × Int)) :
    TableOptimal scoring [] target (emptyRow target.length) := by
  induction target with
  | nil =>
    apply TableOptimal.nil
    simp [CellOptimal, Optimal, walk_empty_iff, MaskLE]
  | cons c target ih =>
    simp only [List.length_cons, emptyRow]
    refine TableOptimal.cons ?_ ih
    rw [emptyRow_head]
    simp [prepend, CellOptimal, Optimal, walk_empty_iff, List.replicate_succ, MaskLE]

private theorem row_optimal (scoring : Scoring) (q : Char) (qs : List Char)
    (target : List (Char × Int)) (next : List Cell) (h : TableOptimal scoring qs target next) :
    TableOptimal scoring (q :: qs) target (row scoring q target next) := by
  induction target generalizing next with
  | nil =>
    apply TableOptimal.nil
    constructor <;> intro a ha <;> cases ha
  | cons c target ih =>
    cases c with
    | mk c bonus =>
      cases h with
      | cons head tail =>
        have rest := ih _ tail
        refine TableOptimal.cons ?_ rest
        constructor
        · simpa using advance_optimal scoring q c qs bonus target false _ _ tail.head.2 rest.head.1
        · simpa using advance_optimal scoring q c qs bonus target true _ _ tail.head.2 rest.head.1

private theorem table_optimal (scoring : Scoring) (query : List Char) (target : List (Char × Int)) :
    TableOptimal scoring query target (table scoring query target) := by
  induction query with
  | nil => exact emptyRow_optimal scoring target
  | cons q qs ih => exact row_optimal scoring q qs target _ ih

/-- Original characters and their original predecessors define word bonuses.
The independent specification zips the input rather than recursively tokenizing it. -/
def weighted (word : Int) (fold : Char → Char) (previous : Char) (target : List Char) :
    List (Char × Int) :=
  ((previous :: target).zip target).map fun (p, c) =>
    (fold c,
      if p ∈ [' ', '-', '_', '.', '/', '@', ':'] ∨ (p.isLower = true ∧ c.isUpper = true) then word
      else 0)

private theorem letters_weighted (word : Int) (fold : Char → Char) (previous : Char)
    (target : List Char) :
    letters word fold previous target = weighted word fold previous target := by
  induction target generalizing previous with
  | nil => rfl
  | cons c target ih =>
    simp only [letters, weighted, List.zip_cons_cons, List.map_cons]
    rw [ih]
    simp [weighted]

theorem weighted_chars (word : Int) (fold : Char → Char) (previous : Char) (target : List Char) :
    (weighted word fold previous target).map Prod.fst = target.map fold := by
  calc
    _ = (((previous :: target).zip target).map Prod.snd).map fold := by
      simp [weighted, List.map_map]
    _ = _ := by rw [List.map_snd_zip (by simp)]

private theorem weighted_length (word : Int) (fold : Char → Char) (previous : Char)
    (target : List Char) : (weighted word fold previous target).length = target.length := by
  simpa using congrArg List.length (weighted_chars word fold previous target)

private theorem alignWith_certificate (config : Config) (query target : String) :
    Optimal
      (Walk config.scoring (query.toList.map (config.caseMode.fold query))
        (weighted config.scoring.word (config.caseMode.fold query) ' ' target.toList) false)
      (alignWith config query target) := by
  simpa only [alignWith, letters_weighted] using
    (table_optimal config.scoring (query.toList.map (config.caseMode.fold query))
        (letters config.scoring.word (config.caseMode.fold query) ' ' target.toList)).head.1

/-- Failure excludes every legal path. Success maximizes score over all legal
alignments for the chosen case and scoring policy. -/
theorem alignWith_optimal (config : Config) (query target : String) :
    match alignWith config query target with
    | none =>
      ∀ a,
        ¬Walk config.scoring (query.toList.map (config.caseMode.fold query))
            (weighted config.scoring.word (config.caseMode.fold query) ' ' target.toList) false a
    | some a =>
      Walk config.scoring (query.toList.map (config.caseMode.fold query))
          (weighted config.scoring.word (config.caseMode.fold query) ' ' target.toList) false a ∧
        ∀ b,
          Walk config.scoring (query.toList.map (config.caseMode.fold query))
              (weighted config.scoring.word (config.caseMode.fold query) ' ' target.toList) false
              b →
            b.score ≤ a.score := by
  have h := alignWith_certificate config query target
  cases he : alignWith config query target with
  | none => simpa only [he, Optimal] using h
  | some a =>
    rw [he] at h
    exact ⟨h.1, h.2.1⟩

/-- Acceptance depends on case policy alone, regardless of the scoring weights. -/
theorem alignWith_isSome_iff_sublist (config : Config) (query target : String) :
    (alignWith config query target).isSome = true ↔
      (query.toList.map (config.caseMode.fold query)).Sublist
        (target.toList.map (config.caseMode.fold query)) := by
  have h := alignWith_certificate config query target
  constructor
  · intro hs
    cases ha : alignWith config query target with
    | none => simp [ha] at hs
    | some a => simpa only [weighted_chars] using (optimal_sound h ha).sublist
  · intro hs
    obtain ⟨a, ha⟩ :=
      walk_exists config.scoring _
        (weighted config.scoring.word (config.caseMode.fold query) ' ' target.toList) false
        (by simpa only [weighted_chars] using hs)
    obtain ⟨b, hb, _⟩ := optimal_complete h ha
    simp [hb]

/-- Every mode returns one Boolean per original Unicode scalar. -/
theorem alignWith_marks_length (config : Config) (query target : String) (a : Alignment)
    (h : alignWith config query target = some a) : a.marks.length = target.length := by
  simpa only [weighted_length, String.length_toList] using
    (optimal_sound (alignWith_certificate config query target) h).length

/-- The original marked characters spell exactly the normalized query. -/
theorem alignWith_spells (config : Config) (query target : String) (a : Alignment)
    (h : alignWith config query target = some a) :
    ((target.toList.zip a.marks).filterMap fun (c, marked) =>
        if marked then some (config.caseMode.fold query c) else none) =
      query.toList.map (config.caseMode.fold query) := by
  have hs := (optimal_sound (alignWith_certificate config query target) h).spells
  have hm :
    (((weighted config.scoring.word (config.caseMode.fold query) ' ' target.toList).map
                Prod.fst).zip
            a.marks).filterMap
        (fun (c, marked) => if marked then some c else none) =
      query.toList.map (config.caseMode.fold query) := by
    simpa only [List.zip_map_left, List.filterMap_map, Function.comp_def, Prod.map, id] using hs
  rw [weighted_chars] at hm
  simpa only [List.zip_map_left, List.filterMap_map, Function.comp_def, Prod.map, id] using hm

theorem alignWith_score_max (config : Config) (query target : String) (a b : Alignment)
    (h : alignWith config query target = some a)
    (hb :
      Walk config.scoring (query.toList.map (config.caseMode.fold query))
        (weighted config.scoring.word (config.caseMode.fold query) ' ' target.toList) false b) :
    b.score ≤ a.score := by
  have ho := alignWith_optimal config query target
  rw [h] at ho
  exact ho.2 b hb

/-- The chosen mask is globally earliest among every equally scoring legal path. -/
theorem alignWith_earliest (config : Config) (query target : String) (a b : Alignment)
    (h : alignWith config query target = some a)
    (hb :
      Walk config.scoring (query.toList.map (config.caseMode.fold query))
        (weighted config.scoring.word (config.caseMode.fold query) ' ' target.toList) false b)
    (tie : b.score = a.score) :
    a.marks = b.marks ∨ List.Lex (fun x y => x = true ∧ y = false) a.marks b.marks := by
  have ho := alignWith_certificate config query target
  rw [h] at ho
  exact ho.2.2 b hb tie

theorem CaseMode.fold_sensitive (query : String) : CaseMode.fold .sensitive query = id := by rfl

theorem CaseMode.fold_insensitive (query : String) :
    CaseMode.fold .insensitive query = Char.toLower := by rfl

theorem CaseMode.fold_smart_upper (query : String) (h : query.toList.any Char.isUpper = true) :
    CaseMode.fold .smart query = id := by simp [CaseMode.fold, h]

theorem CaseMode.fold_smart_no_upper (query : String) (h : query.toList.any Char.isUpper = false) :
    CaseMode.fold .smart query = Char.toLower := by simp [CaseMode.fold, h]

theorem alignWith_smart_sensitive (scoring : Scoring) (query target : String)
    (h : query.toList.any Char.isUpper = true) :
    alignWith { caseMode := .smart, scoring } query target =
      alignWith { caseMode := .sensitive, scoring } query target := by
  simp only [alignWith, CaseMode.fold_smart_upper query h, CaseMode.fold_sensitive]

theorem alignWith_smart_insensitive (scoring : Scoring) (query target : String)
    (h : query.toList.any Char.isUpper = false) :
    alignWith { caseMode := .smart, scoring } query target =
      alignWith { caseMode := .insensitive, scoring } query target := by
  simp only [alignWith, CaseMode.fold_smart_no_upper query h, CaseMode.fold_insensitive]

theorem alignWith_scoring_irrelevant (caseMode : CaseMode) (left right : Scoring)
    (query target : String) :
    (alignWith { caseMode, scoring := left } query target).isSome =
      (alignWith { caseMode, scoring := right } query target).isSome := by
  apply Bool.eq_iff_iff.mpr
  rw [alignWith_isSome_iff_sublist, alignWith_isSome_iff_sublist]

/-- The selector retains its original case policy and all three scoring weights. -/
theorem align_default (query target : String) :
    align query target =
      alignWith { caseMode := .insensitive, scoring := { word := 4, adjacent := 8, gap := -1 } }
        query target := by
  rfl

/-- Existing default semantic contracts are instances of the general certificate. -/
theorem align_optimal (query target : String) :
    match align query target with
    | none =>
      ∀ a,
        ¬Walk {} (query.toList.map Char.toLower) (weighted 4 Char.toLower ' ' target.toList) false a
    | some a =>
      Walk {} (query.toList.map Char.toLower) (weighted 4 Char.toLower ' ' target.toList) false a ∧
        ∀ b,
          Walk {} (query.toList.map Char.toLower) (weighted 4 Char.toLower ' ' target.toList) false
              b →
            b.score ≤ a.score := by
  simpa only [align, CaseMode.fold] using alignWith_optimal {} query target

theorem align_isSome_iff_sublist (query target : String) :
    (align query target).isSome = true ↔
      (query.toList.map Char.toLower).Sublist (target.toList.map Char.toLower) :=
  alignWith_isSome_iff_sublist {} query target

theorem align_marks_length (query target : String) (a : Alignment)
    (h : align query target = some a) : a.marks.length = target.length :=
  alignWith_marks_length {} query target a h

theorem align_spells (query target : String) (a : Alignment) (h : align query target = some a) :
    ((target.toList.zip a.marks).filterMap fun (c, marked) =>
        if marked then some c.toLower else none) = query.toList.map Char.toLower :=
  alignWith_spells {} query target a h

theorem align_score_max (query target : String) (a b : Alignment) (h : align query target = some a)
    (hb : Walk {} (query.toList.map Char.toLower) (weighted 4 Char.toLower ' ' target.toList) false b) :
    b.score ≤ a.score := alignWith_score_max {} query target a b h hb

theorem align_earliest (query target : String) (a b : Alignment) (h : align query target = some a)
    (hb : Walk {} (query.toList.map Char.toLower) (weighted 4 Char.toLower ' ' target.toList) false b)
    (tie : b.score = a.score) :
    a.marks = b.marks ∨ List.Lex (fun x y => x = true ∧ y = false) a.marks b.marks :=
  alignWith_earliest {} query target a b h hb tie

end Linger.Tools.Fuzzy
