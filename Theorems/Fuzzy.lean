module

public import Tools.Fuzzy
import all Tools.Fuzzy

public section

/-! A declarative weighted subsequence semantics, independent of the table.

Every legal path consumes one original target position at a time. A gap costs
one point while a query remains; completing the query leaves the trailing
positions unmarked and free. Taking a character earns its word-boundary bonus
and, precisely when the previous position was taken, eight adjacency points.
-/

namespace Tools.Fuzzy

/-- Legal alignments over folded characters carrying their original word bonuses. -/
inductive Walk : List Char → List (Char × Int) → Bool → Alignment → Prop where
  |
  empty (target : List (Char × Int)) (adjacent : Bool) :
    Walk [] target adjacent ⟨0, List.replicate target.length false⟩
  |
  gap {q : Char} {qs : List Char} {c : Char} {bonus : Int} {target : List (Char × Int)}
    {adjacent : Bool} {a : Alignment} (rest : Walk (q :: qs) target false a) :
    Walk (q :: qs) ((c, bonus) :: target) adjacent ⟨a.score + (-1), false :: a.marks⟩
  |
  take {q : Char} {qs : List Char} {bonus : Int} {target : List (Char × Int)} {adjacent : Bool}
    {a : Alignment} (rest : Walk qs target true a) :
    Walk (q :: qs) ((q, bonus) :: target) adjacent
      ⟨a.score + (bonus + if adjacent then 8 else 0), true :: a.marks⟩

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
  cases left <;> cases right <;> simp_all [Optimal, best]
  split <;> simp_all <;> grind

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

theorem Walk.sublist {query : List Char} {target : List (Char × Int)} {adjacent : Bool}
    {a : Alignment} (h : Walk query target adjacent a) : query.Sublist (target.map Prod.fst) := by
  induction h with
  | empty => exact List.nil_sublist _
  | gap _ ih => exact ih.cons _
  | take _ ih => exact ih.cons_cons _

theorem Walk.length {query : List Char} {target : List (Char × Int)} {adjacent : Bool}
    {a : Alignment} (h : Walk query target adjacent a) : a.marks.length = target.length := by
  induction h <;> simp_all

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
theorem Walk.spells {query : List Char} {target : List (Char × Int)} {adjacent : Bool}
    {a : Alignment} (h : Walk query target adjacent a) :
    ((target.zip a.marks).filterMap fun (c, marked) => if marked then some c.1 else none) =
      query := by
  induction h with
  | empty => exact unmarked _ _
  | gap _ ih => simpa using ih
  | take _ ih => simpa using ih

private theorem walk_empty_iff (target : List (Char × Int)) (adjacent : Bool) (a : Alignment) :
    Walk [] target adjacent a ↔ a = ⟨0, List.replicate target.length false⟩ := by
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    exact .empty _ _

private theorem walk_exists (query : List Char) (target : List (Char × Int)) (adjacent : Bool)
    (h : query.Sublist (target.map Prod.fst)) : ∃ a, Walk query target adjacent a := by
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

private theorem walk_cons_iff (q c : Char) (qs : List Char) (bonus : Int)
    (target : List (Char × Int)) (adjacent : Bool) (a : Alignment) :
    Walk (q :: qs) ((c, bonus) :: target) adjacent a ↔
      (q = c ∧
          ∃ b,
            Walk qs target true b ∧
              a = ⟨b.score + (bonus + if adjacent then 8 else 0), true :: b.marks⟩) ∨
        (∃ b, Walk (q :: qs) target false b ∧ a = ⟨b.score + (-1), false :: b.marks⟩) := by
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

private theorem advance_optimal (q c : Char) (qs : List Char) (bonus : Int)
    (target : List (Char × Int)) (adjacent : Bool) (taken skipped : Option Alignment)
    (ht : Optimal (Walk qs target true) taken)
    (hs : Optimal (Walk (q :: qs) target false) skipped) :
    Optimal (Walk (q :: qs) ((c, bonus) :: target) adjacent)
      (best (prepend true (bonus + if adjacent then 8 else 0) (if q == c then taken else none))
        (prepend false (-1) skipped)) := by
  apply (optimal_congr _ _ _ (walk_cons_iff q c qs bonus target adjacent)).mpr
  apply best_optimal
  · by_cases h : q = c
    · simpa [h] using
        prepend_optimal true (bonus + if adjacent then 8 else 0) taken (Walk qs target true) ht
    · simp [h, prepend, Optimal]
  · exact prepend_optimal false (-1) skipped (Walk (q :: qs) target false) hs
  · rintro a ⟨_, x, _, rfl⟩ b ⟨y, _, rfl⟩
    exact .inr (.rel ⟨rfl, rfl⟩)

private def CellOptimal (query : List Char) (target : List (Char × Int)) (cell : Cell) : Prop :=
  Optimal (Walk query target false) cell.gap ∧ Optimal (Walk query target true) cell.adjacent

/-- The row has exactly one certified answer pair for each target suffix. -/
private inductive TableOptimal (query : List Char) : List (Char × Int) → List Cell → Prop where
  | nil {cell : Cell} : CellOptimal query [] cell → TableOptimal query [] [cell]
  |
  cons {c : Char × Int} {target : List (Char × Int)} {cell : Cell} {tail : List Cell} :
    CellOptimal query (c :: target) cell →
      TableOptimal query target tail → TableOptimal query (c :: target) (cell :: tail)

private theorem TableOptimal.head {query : List Char} {target : List (Char × Int)}
    {cells : List Cell} (h : TableOptimal query target cells) :
    CellOptimal query target (cells.headD default) := by cases h <;> assumption

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

private theorem emptyRow_optimal (target : List (Char × Int)) :
    TableOptimal [] target (emptyRow target.length) := by
  induction target with
  | nil =>
    apply TableOptimal.nil
    simp [CellOptimal, Optimal, walk_empty_iff, MaskLE]
  | cons c target ih =>
    simp only [List.length_cons, emptyRow]
    refine TableOptimal.cons ?_ ih
    rw [emptyRow_head]
    simp [prepend, CellOptimal, Optimal, walk_empty_iff, List.replicate_succ, MaskLE]

private theorem row_optimal (q : Char) (qs : List Char) (target : List (Char × Int))
    (next : List Cell) (h : TableOptimal qs target next) :
    TableOptimal (q :: qs) target (row q target next) := by
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
        · simpa using advance_optimal q c qs bonus target false _ _ tail.head.2 rest.head.1
        · simpa using advance_optimal q c qs bonus target true _ _ tail.head.2 rest.head.1

private theorem table_optimal (query : List Char) (target : List (Char × Int)) :
    TableOptimal query target (table query target) := by
  induction query with
  | nil => exact emptyRow_optimal target
  | cons q qs ih => exact row_optimal q qs target _ ih

/-- The scoring specification labels original positions using their original
predecessors. It is a zip of the input, independent of the recursive tokenizer. -/
def weighted (previous : Char) (target : List Char) : List (Char × Int) :=
  ((previous :: target).zip target).map fun (p, c) =>
    (c.toLower,
      if p ∈ [' ', '-', '_', '.', '/', '@', ':'] ∨ (p.isLower = true ∧ c.isUpper = true) then 4
      else 0)

private theorem letters_weighted (previous : Char) (target : List Char) :
    letters previous target = weighted previous target := by
  induction target generalizing previous with
  | nil => rfl
  | cons c target ih =>
    simp only [letters, weighted, List.zip_cons_cons, List.map_cons]
    rw [ih]
    simp [weighted]

theorem weighted_chars (previous : Char) (target : List Char) :
    (weighted previous target).map Prod.fst = target.map Char.toLower := by
  calc
    _ = (((previous :: target).zip target).map Prod.snd).map Char.toLower := by
      simp [weighted, List.map_map]
    _ = _ := by rw [List.map_snd_zip (by simp)]

private theorem weighted_length (previous : Char) (target : List Char) :
    (weighted previous target).length = target.length := by
  simpa using congrArg List.length (weighted_chars previous target)

private theorem align_certificate (query target : String) :
    Optimal (Walk (query.toList.map Char.toLower) (weighted ' ' target.toList) false)
      (align query target) := by
  have h :
    Optimal (Walk (query.toList.map Char.toLower) (letters ' ' target.toList) false)
      (align query target) :=
    (table_optimal _ _).head.1
  rw [letters_weighted] at h
  exact h

/-- Failure excludes every legal path. Success witnesses a legal path whose
score is at least that of every legal alignment under the declared bonuses. -/
theorem align_optimal (query target : String) :
    match align query target with
    | none => ∀ a, ¬Walk (query.toList.map Char.toLower) (weighted ' ' target.toList) false a
    | some a =>
      Walk (query.toList.map Char.toLower) (weighted ' ' target.toList) false a ∧
        ∀ b,
          Walk (query.toList.map Char.toLower) (weighted ' ' target.toList) false b →
            b.score ≤ a.score := by
  have h := align_certificate query target
  cases he : align query target with
  | none => simpa only [he, Optimal] using h
  | some a =>
    rw [he] at h
    exact ⟨h.1, h.2.1⟩

/-- The alignment algorithm accepts exactly the existing folded subsequence
language, independent of the scoring choices and the number of competing paths. -/
theorem align_isSome_iff_sublist (query target : String) :
    (align query target).isSome = true ↔
      (query.toList.map Char.toLower).Sublist (target.toList.map Char.toLower) := by
  have h :
    Optimal (Walk (query.toList.map Char.toLower) (weighted ' ' target.toList) false)
      (align query target) :=
    align_certificate query target
  constructor
  · intro hs
    cases ha : align query target with
    | none => simp [ha] at hs
    | some a => simpa only [weighted_chars] using (optimal_sound h ha).sublist
  · intro hs
    obtain ⟨a, ha⟩ :=
      walk_exists _ (weighted ' ' target.toList) false (by simpa only [weighted_chars] using hs)
    obtain ⟨b, hb, _⟩ := optimal_complete h ha
    simp [hb]

/-- One Boolean per Unicode scalar in the original target. -/
theorem align_marks_length (query target : String) (a : Alignment)
    (h : align query target = some a) : a.marks.length = target.length := by
  have ho :
    Optimal (Walk (query.toList.map Char.toLower) (weighted ' ' target.toList) false)
      (align query target) :=
    align_certificate query target
  simpa only [weighted_length, String.length_toList] using (optimal_sound ho h).length

/-- Filtering the original target with the returned mask spells exactly the
folded query. Positions are never UTF-8 byte offsets. -/
theorem align_spells (query target : String) (a : Alignment) (h : align query target = some a) :
    ((target.toList.zip a.marks).filterMap fun (c, marked) =>
        if marked then some c.toLower else none) =
      query.toList.map Char.toLower := by
  have ho :
    Optimal (Walk (query.toList.map Char.toLower) (weighted ' ' target.toList) false)
      (align query target) :=
    align_certificate query target
  have hs := (optimal_sound ho h).spells
  have hm :
    (((weighted ' ' target.toList).map Prod.fst).zip a.marks).filterMap
        (fun (c, marked) => if marked then some c else none) =
      query.toList.map Char.toLower := by
    simpa only [List.zip_map_left, List.filterMap_map, Function.comp_def, Prod.map, id] using hs
  rw [weighted_chars] at hm
  simpa only [List.zip_map_left, List.filterMap_map, Function.comp_def, Prod.map, id] using hm

theorem align_score_max (query target : String) (a b : Alignment) (h : align query target = some a)
    (hb : Walk (query.toList.map Char.toLower) (weighted ' ' target.toList) false b) :
    b.score ≤ a.score := by
  have ho := align_optimal query target
  rw [h] at ho
  exact ho.2 b hb

/-- Among all equally scoring legal alignments, the returned mask is globally
earliest: at the first differing target position it selects the character. -/
theorem align_earliest (query target : String) (a b : Alignment) (h : align query target = some a)
    (hb : Walk (query.toList.map Char.toLower) (weighted ' ' target.toList) false b)
    (tie : b.score = a.score) :
    a.marks = b.marks ∨ List.Lex (fun x y => x = true ∧ y = false) a.marks b.marks := by
  have ho := align_certificate query target
  rw [h] at ho
  exact ho.2.2 b hb tie

end Tools.Fuzzy
