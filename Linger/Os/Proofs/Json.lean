module

public import Linger.Os.CoreCode.Json
import all Linger.Os.CoreSpec
import all Linger.Os.CoreCode.Json

/-! # Canonical JSON, written and read

The writer writes canonical text only, and writes a value as the value its text holds
(`render_canonical`, `chars_sorted`); every canonical text is a valid value's (`text_written`); and
the reader reads a text exactly when it is a valid value's text, as that value
(`parse_eq_ok_iff`). -/

public section

namespace Linger.Json

/-! ## Members by key -/

/-- A key not less than another and not equal to it is greater. -/
theorem key_gt {a b : String} (notLt : ¬a < b) (ne : a ≠ b) : b < a :=
  Std.lt_of_le_of_ne (String.not_lt.mp notLt) (Ne.symm ne)

/-- A member `insertMember` gives is the one it inserts or one it was given. -/
theorem mem_insertMember {α : Type} (member : String × α) :
    ∀ (members : List (String × α)) (m : String × α),
      m ∈ insertMember member members → m = member ∨ m ∈ members
  | [], m, h => by
    simp [insertMember] at h; exact .inl h
  | first :: rest, m, h => by
    simp only [insertMember] at h
    split at h
    · simpa using h
    · split at h
      · exact .inr h
      · simp only [List.mem_cons] at h
        rcases h with rfl | h
        · exact .inr (by simp)
        · rcases mem_insertMember member rest m h with rfl | h
          · exact .inl rfl
          · exact .inr (by simp [h])

/-- `insertMember` keeps members' keys strictly increasing. -/
theorem insertMember_pairwise {α : Type} (member : String × α) :
    ∀ (members : List (String × α)),
      (members.map (·.1)).Pairwise (· < ·) →
        ((insertMember member members).map (·.1)).Pairwise (· < ·)
  | [], _ => by simp [insertMember]
  | first :: rest, sorted => by
    have whole := sorted
    simp only [List.map_cons, List.pairwise_cons, List.mem_map] at sorted
    obtain ⟨below, sortedRest⟩ := sorted
    simp only [insertMember]
    split
    · rename_i lt
      simp only [List.map_cons, List.pairwise_cons, List.mem_cons, List.mem_map]
      refine ⟨?_, ?_, sortedRest⟩
      · rintro k (rfl | ⟨m, inRest, rfl⟩)
        · exact lt
        · exact String.lt_trans lt (below m.1 ⟨m, inRest, rfl⟩)
      · rintro k ⟨m, inRest, rfl⟩
        exact below m.1 ⟨m, inRest, rfl⟩
    · split
      · exact whole
      · rename_i notLt ne
        have gt : first.1 < member.1 := key_gt notLt ne
        simp only [List.map_cons, List.pairwise_cons, List.mem_map]
        refine ⟨?_, insertMember_pairwise member rest sortedRest⟩
        rintro k ⟨m, inserted, rfl⟩
        rcases mem_insertMember member rest m inserted with rfl | inRest
        · exact gt
        · exact below m.1 ⟨m, inRest, rfl⟩

/-- Inserting a member whose key is greater than every key puts it last. -/
theorem insertMember_last {α : Type} (member : String × α) :
    ∀ (members : List (String × α)),
      (∀ m ∈ members, m.1 < member.1) → insertMember member members = members ++ [member]
  | [], _ => rfl
  | first :: rest, below => by
    have firstBelow := below first (by simp)
    simp only [insertMember, String.lt_asymm firstBelow, ↓reduceIte,
      (String.ne_of_lt firstBelow).symm, List.cons_append]
    rw [insertMember_last member rest fun m inRest => below m (by simp [inRest])]

/-- `sortMembers`'s fold, from members already sorted. -/
theorem foldl_insertMember_mem {α : Type} :
    ∀ (members acc : List (String × α)) (m : String × α),
      m ∈ members.foldl (fun sorted member => insertMember member sorted) acc →
        m ∈ acc ∨ m ∈ members
  | [], acc, m, h => .inl h
  | first :: rest, acc, m, h => by
    rcases foldl_insertMember_mem rest (insertMember first acc) m h with inserted | inRest
    · rcases mem_insertMember first acc m inserted with rfl | inAcc
      · exact .inr (by simp)
      · exact .inl inAcc
    · exact .inr (by simp [inRest])

/-- A member `sortMembers` gives is one it was given. -/
theorem mem_sortMembers {α : Type} {members : List (String × α)} {m : String × α}
    (h : m ∈ sortMembers members) : m ∈ members := by
  rcases foldl_insertMember_mem members [] m h with inAcc | inMembers
  · simp at inAcc
  · exact inMembers

/-- `sortMembers`'s fold keeps keys strictly increasing. -/
theorem foldl_insertMember_pairwise {α : Type} :
    ∀ (members acc : List (String × α)),
      (acc.map (·.1)).Pairwise (· < ·) →
        ((members.foldl (fun sorted member => insertMember member sorted) acc).map (·.1)).Pairwise
          (· < ·)
  | [], _, sorted => sorted
  | first :: rest, acc, sorted =>
    foldl_insertMember_pairwise rest (insertMember first acc)
      (insertMember_pairwise first acc sorted)

/-- **`sortMembers` lists keys strictly increasing.** -/
theorem sortMembers_pairwise {α : Type} (members : List (String × α)) :
    ((sortMembers members).map (·.1)).Pairwise (· < ·) :=
  foldl_insertMember_pairwise members [] (by simp)

/-- `sortMembers`'s fold, over members whose keys increase past those already sorted, appends
them. -/
theorem foldl_insertMember_sorted {α : Type} :
    ∀ (members acc : List (String × α)),
      (members.map (·.1)).Pairwise (· < ·) →
        (∀ a ∈ acc, ∀ m ∈ members, a.1 < m.1) →
        members.foldl (fun sorted member => insertMember member sorted) acc = acc ++ members
  | [], acc, _, _ => by simp
  | first :: rest, acc, sorted, below => by
    simp only [List.map_cons, List.pairwise_cons, List.mem_map] at sorted
    obtain ⟨firstBelow, sortedRest⟩ := sorted
    simp only [List.foldl_cons]
    rw [insertMember_last first acc fun a inAcc => below a inAcc first (by simp)]
    rw [foldl_insertMember_sorted rest (acc ++ [first]) sortedRest]
    · simp
    · intro a inAcc m inRest
      simp only [List.mem_append, List.mem_singleton] at inAcc
      rcases inAcc with inAcc | rfl
      · exact below a inAcc m (by simp [inRest])
      · exact firstBelow m.1 ⟨m, inRest, rfl⟩

/-- **`sortMembers` keeps members whose keys strictly increase as they are.** -/
theorem sortMembers_of_pairwise {α : Type} {members : List (String × α)}
    (sorted : (members.map (·.1)).Pairwise (· < ·)) : sortMembers members = members := by
  unfold sortMembers
  rw [foldl_insertMember_sorted members [] sorted (by simp)]
  simp

/-- `sortMembers` of sorted members is the same. -/
theorem sortMembers_sortMembers {α : Type} (members : List (String × α)) :
    sortMembers (sortMembers members) = sortMembers members :=
  sortMembers_of_pairwise (sortMembers_pairwise members)

/-- `insertMember` looks only at keys. -/
theorem insertMember_map {α β : Type} (f : α → β) (member : String × α) :
    ∀ (members : List (String × α)),
      insertMember (member.1, f member.2) (members.map fun m => (m.1, f m.2)) =
        (insertMember member members).map fun m => (m.1, f m.2)
  | [] => rfl
  | first :: rest => by
    simp only [List.map_cons, insertMember]
    split
    · simp
    · split
      · simp
      · simp [insertMember_map f member rest]

/-- `sortMembers` looks only at keys. -/
theorem sortMembers_map {α β : Type} (f : α → β) (members : List (String × α)) :
    sortMembers (members.map fun m => (m.1, f m.2)) =
      (sortMembers members).map fun m => (m.1, f m.2) := by
  unfold sortMembers
  suffices h :
    ∀ (ms : List (String × α)) (acc : List (String × α)),
      (ms.map fun m => (m.1, f m.2)).foldl (fun sorted member => insertMember member sorted)
          (acc.map fun m => (m.1, f m.2)) =
        (ms.foldl (fun sorted member => insertMember member sorted) acc).map fun m => (m.1, f m.2)
    by simpa using h members []
  intro ms
  induction ms with
  | nil =>
    intro acc; rfl
  | cons first rest ih =>
    intro acc
    simp only [List.map_cons, List.foldl_cons]
    rw [insertMember_map f first acc, ih]

/-! ## The writer's texts -/

/-- Each item's text, in order. -/
theorem itemChars_eq : ∀ items : List Json, itemChars items = items.map chars
  | [] => rfl
  | item :: rest => by simp [itemChars, itemChars_eq rest]

/-- Each member's key and its value's text, in order. -/
theorem memberChars_eq :
    ∀ members : List (String × Json), memberChars members = members.map fun m => (m.1, chars m.2)
  | [] => rfl
  | (key, value) :: rest => by simp [memberChars, memberChars_eq rest]

/-- Texts joined by commas: the first, then a comma before each other. -/
theorem joined_cons (text : List Char) :
    ∀ rest : List (List Char), joined (text :: rest) = text ++ rest.flatMap (',' :: ·)
  | [] => by simp [joined]
  | next :: more => by
    simp only [joined, List.flatMap_cons, List.cons_append]
    rw [joined_cons next more]

/-- Texts joined by commas, one more at the end. -/
theorem joined_append_one :
    ∀ (texts : List (List Char)) (text : List Char),
      joined (texts ++ [text]) = joined texts ++ (if texts = [] then [] else [',']) ++ text
  | [], text => by simp [joined]
  | [first], text => by simp [joined]
  | first :: second :: more, text => by
    have := joined_append_one (second :: more) text
    simp only [List.cons_append, joined] at this ⊢
    rw [this]
    simp

/-- A character's order is its code point's. -/
theorem char_le (c d : Char) : c ≤ d ↔ c.toNat ≤ d.toNat := by
  rw [Char.le_def, UInt32.le_iff_toNat_le]; rfl

/-- A character whose code point is a literal's is that literal. -/
theorem char_of_toNat {c d : Char} (same : c.toNat = d.toNat) : c = d := Char.toNat_inj.mp same

/-- A character `escape` writes as itself is `unescaped`, and any other is written as its
`escape`. -/
theorem escape_spec (c : Char) : (Unescaped c ∧ escape c = [c]) ∨ Escape (escape c) c := by
  unfold escape
  by_cases quote : c = '"'
  · subst quote; exact .inr .quote
  rw [ite_eq_right quote]
  by_cases slash : c = '\\'
  · subst slash; exact .inr .backslash
  rw [ite_eq_right slash]
  by_cases b : c = '\x08'
  · subst b; exact .inr .backspace
  rw [ite_eq_right b]
  by_cases t : c = '\t'
  · subst t; exact .inr .tab
  rw [ite_eq_right t]
  by_cases n : c = '\n'
  · subst n; exact .inr .newline
  rw [ite_eq_right n]
  by_cases f : c = '\x0c'
  · subst f; exact .inr .formFeed
  rw [ite_eq_right f]
  by_cases r : c = '\r'
  · subst r; exact .inr .carriageReturn
  rw [ite_eq_right r]
  by_cases below : c.toNat < 0x20
  · rw [ite_eq_left below]
    refine .inr (.control c below ⟨?_, ?_, ?_, ?_, ?_⟩)
    · exact fun same => b (char_of_toNat same)
    · exact fun same => t (char_of_toNat same)
    · exact fun same => n (char_of_toNat same)
    · exact fun same => f (char_of_toNat same)
    · exact fun same => r (char_of_toNat same)
  · rw [ite_eq_right below]
    exact .inl ⟨⟨quote, slash, by omega⟩, rfl⟩

/-- A string's characters' texts spell them. -/
theorem body_escaped : ∀ cs : List Char, Body (cs.flatMap escape) cs
  | [] => .nil
  | c :: rest => by
    rw [List.flatMap_cons]
    rcases escape_spec c with ⟨plain, same⟩ | escaped
    · rw [same]; exact .unescaped plain (body_escaped rest)
    · exact .escape escaped (body_escaped rest)

/-- **A string's text is a canonical `string` that spells it.** -/
theorem quote_text (s : String) : StringText (quote s) s :=
  ⟨s.toList.flatMap escape, rfl, body_escaped s.toList⟩

/-- A digit's character is a digit. -/
theorem digitChar_digit (m : Nat) (h : m < 10) : '0' ≤ Nat.digitChar m ∧ Nat.digitChar m ≤ '9' := by
  have := Nat.isDigit_digitChar (n := m)
  simp only [h, decide_true, Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at this
  rw [Char.le_def, Char.le_def]
  exact this

/-- A nonzero digit's character is a digit other than `0`. -/
theorem digitChar_nonzero (m : Nat) (h : m < 10) (nonzero : m ≠ 0) :
    '1' ≤ Nat.digitChar m ∧ Nat.digitChar m ≤ '9' := by
  have digit := digitChar_digit m h
  have notZero : (Nat.digitChar m).toNat ≠ 48 := fun same =>
    nonzero (Nat.digitChar_eq_zero.mp (char_of_toNat same))
  rw [char_le, char_le] at digit ⊢
  exact
    ⟨by
      have := digit.1; show 49 ≤ _; revert this notZero; show _ → 48 ≤ _ → _; omega, digit.2⟩

/-- A natural number's decimal digits: `0` alone, or digits whose first is not `0`. -/
theorem toDigits_shape (m : Nat) :
    (m = 0 ∧ Nat.toDigits 10 m = ['0']) ∨
      ∃ (first : Char) (digits : List Char),
        '1' ≤ first ∧
          first ≤ '9' ∧
          (∀ d ∈ digits, '0' ≤ d ∧ d ≤ '9') ∧ Nat.toDigits 10 m = first :: digits := by
  induction m using Nat.strongRecOn with
  | ind m ih =>
    rw [Nat.toDigits_eq_ite (by decide)]
    split
    · rename_i small
      by_cases zero : m = 0
      · subst zero; exact .inl ⟨rfl, by rw [Nat.digitChar_eq_zero.mpr rfl]⟩
      · exact
          .inr
            ⟨_, [], (digitChar_nonzero m small zero).1, (digitChar_nonzero m small zero).2, by simp,
              rfl⟩
    · rename_i large
      have pos : 0 < m / 10 := Nat.div_pos (by omega) (by decide)
      rcases ih (m / 10) (Nat.div_lt_self (by omega) (by decide)) with ⟨zero, -⟩ |
        ⟨first, digits, low, high, all, eq⟩
      · omega
      · refine
          .inr
            ⟨first, digits ++ [Nat.digitChar (m % 10)], low, high, ?_, by
              rw [eq]; simp⟩
        intro d member
        simp only [List.mem_append, List.mem_singleton] at member
        rcases member with member | rfl
        · exact all d member
        · exact digitChar_digit (m % 10) (Nat.mod_lt m (by decide))

/-- **An integer's text is a canonical `integer`.** -/
theorem integer_text (n : Int) : IntegerText (toString n).toList := by
  show IntegerText n.repr.toList
  rw [Int.repr_eq_ite]
  split
  · rw [Nat.toList_repr]
    rcases toDigits_shape n.toNat with ⟨-, eq⟩ | ⟨first, digits, low, high, all, eq⟩
    · exact .inl eq
    · exact
        .inr
          ⟨[], first, digits, .inl rfl, low, high, all, by
            rw [eq]; rfl⟩
  · rename_i negative
    rw [String.toList_append, Nat.toList_repr]
    rcases toDigits_shape (-n).toNat with ⟨zero, -⟩ | ⟨first, digits, low, high, all, eq⟩
    · omega
    · exact
        .inr
          ⟨['-'], first, digits, .inr rfl, low, high, all, by
            rw [eq]; rfl⟩

/-- Texts each a `value`, joined by commas between brackets, are an `array`. -/
theorem array_text :
    ∀ texts : List (List Char), (∀ t ∈ texts, Text t) → Text ('[' :: joined texts ++ [']'])
  | [], _ => .emptyArray
  | first :: rest, each => by
    rw [joined_cons]
    have more :
      ∀ (ts : List (List Char)), (∀ t ∈ ts, Text t) → MoreValues (ts.flatMap (',' :: ·)) := by
      intro ts
      induction ts with
      | nil =>
        intro _; exact .nil
      | cons t ts ih =>
        intro each
        rw [List.flatMap_cons]
        exact .cons (each t (by simp)) (ih fun u member => each u (by simp [member]))
    have := Text.array (each first (by simp)) (more rest fun u member => each u (by simp [member]))
    simpa [List.append_assoc] using this

/-- Members whose values' texts are each a `value`, by strictly increasing key, joined by commas
between braces, are a `table`. -/
theorem table_text :
    ∀ members : List (String × List Char),
      (∀ m ∈ members, Text m.2) →
        (members.map (·.1)).Pairwise (· < ·) →
        Text ('{' :: joined (members.map memberText) ++ ['}'])
  | [], _, _ => .emptyTable
  | first :: rest, each, sorted => by
    rw [List.map_cons, joined_cons]
    have more :
      ∀ (ms : List (String × List Char)),
        (∀ m ∈ ms, Text m.2) →
          MoreMembers ((ms.map memberText).flatMap (',' :: ·)) (ms.map (·.1)) := by
      intro ms
      induction ms with
      | nil =>
        intro _; exact .nil
      | cons m ms ih =>
        intro each
        simp only [List.map_cons, List.flatMap_cons, memberText]
        have :=
          MoreMembers.cons (quote_text m.1) (each m (by simp))
            (ih fun u member => each u (by simp [member]))
        simpa [List.append_assoc] using this
    have :=
      Text.table (quote_text first.1) (each first (by simp))
        (more rest fun u member => each u (by simp [member])) (by simpa using sorted)
    simpa [memberText, List.append_assoc] using this

mutual
/-- **Every text the writer writes is a canonical `value`.** -/
theorem chars_text : ∀ v : Json, Text (chars v)
  | .null => .nullWord
  | .bool true => .trueWord
  | .bool false => .falseWord
  | .int n => .integer (integer_text n)
  | .str s => .string (quote_text s)
  | .arr items => array_text (itemChars items) (items_text items)
  | .obj members =>
    table_text (sortMembers (memberChars members))
      (fun m member => members_text members m (mem_sortMembers member)) (sortMembers_pairwise _)
/-- Each item's text is a `value`. -/
theorem items_text : ∀ items : List Json, ∀ t ∈ itemChars items, Text t
  | [], t, member => by simp [itemChars] at member
  | item :: rest, t, member => by
    simp only [itemChars, List.mem_cons] at member
    rcases member with rfl | member
    · exact chars_text item
    · exact items_text rest t member
/-- Each member's value's text is a `value`. -/
theorem members_text : ∀ members : List (String × Json), ∀ m ∈ memberChars members, Text m.2
  | [], m, member => by simp [memberChars] at member
  | (key, value) :: rest, m, member => by
    simp only [memberChars, List.mem_cons] at member
    rcases member with rfl | member
    · exact chars_text value
    · exact members_text rest m member
end

/-- **The writer writes canonical text only.** -/
theorem render_canonical (v : Json) : Canonical (render v) := by
  unfold Canonical render
  rw [String.toList_ofList]
  exact chars_text v

/-! ## The value a text holds -/

/-- Items are valid exactly when each is. -/
theorem validItems_iff : ∀ items : List Json, ValidItems items ↔ ∀ item ∈ items, item.Valid
  | [] => by simp [ValidItems]
  | item :: rest => by simp [ValidItems, validItems_iff rest]

/-- Members' values are valid exactly when each is. -/
theorem validMembers_iff :
    ∀ members : List (String × Json), ValidMembers members ↔ ∀ m ∈ members, m.2.Valid
  | [] => by simp [ValidMembers]
  | (key, value) :: rest => by simp [ValidMembers, validMembers_iff rest]

mutual
/-- **The writer writes a value as the value its text holds.** -/
theorem chars_sorted : ∀ v : Json, chars v.sorted = chars v
  | .null => rfl
  | .bool _ => rfl
  | .int _ => rfl
  | .str _ => rfl
  | .arr items => by simp only [sorted, chars, itemChars_eq, sortedItems_chars items]
  | .obj members => by
    simp only [sorted, chars, memberChars_eq]
    rw [← sortMembers_map, sortedMembers_chars members, sortMembers_sortMembers]
/-- Sorted items have the same texts. -/
theorem sortedItems_chars : ∀ items : List Json, (sortedItems items).map chars = items.map chars
  | [] => rfl
  | item :: rest => by simp [sortedItems, chars_sorted item, sortedItems_chars rest]
/-- Sorted members have the same keys and texts. -/
theorem sortedMembers_chars :
    ∀ members : List (String × Json),
      ((sortedMembers members).map fun m => (m.1, chars m.2)) =
        members.map fun m => (m.1, chars m.2)
  | [] => rfl
  | (key, value) :: rest => by simp [sortedMembers, chars_sorted value, sortedMembers_chars rest]
end

mutual
/-- **A sorted value is valid.** -/
theorem sorted_valid : ∀ v : Json, v.sorted.Valid
  | .null => trivial
  | .bool _ => trivial
  | .int _ => trivial
  | .str _ => trivial
  | .arr items => by
    simp only [sorted, Valid]
    exact (validItems_iff _).mpr (sortedItems_valid items)
  | .obj members => by
    simp only [sorted, Valid]
    exact
      ⟨sortMembers_pairwise _,
        (validMembers_iff _).mpr fun m member =>
          sortedMembers_valid members m (mem_sortMembers member)⟩
/-- Sorted items are valid. -/
theorem sortedItems_valid : ∀ items : List Json, ∀ item ∈ sortedItems items, item.Valid
  | [], _, member => by simp [sortedItems] at member
  | item :: rest, x, member => by
    simp only [sortedItems, List.mem_cons] at member
    rcases member with rfl | member
    · exact sorted_valid item
    · exact sortedItems_valid rest x member
/-- Sorted members' values are valid. -/
theorem sortedMembers_valid :
    ∀ members : List (String × Json), ∀ m ∈ sortedMembers members, m.2.Valid
  | [], _, member => by simp [sortedMembers] at member
  | (key, value) :: rest, m, member => by
    simp only [sortedMembers, List.mem_cons] at member
    rcases member with rfl | member
    · exact sorted_valid value
    · exact sortedMembers_valid rest m member
end

/-! ## Every canonical text is a valid value's -/

/-- No escaped character is one a canonical string holds as itself. -/
theorem escape_not_unescaped {e : List Char} {c : Char} (h : Escape e c) : ¬Unescaped c := by
  intro ⟨notQuote, notSlash, high⟩
  cases h with
  | quote => exact notQuote rfl
  | backslash => exact notSlash rfl
  | backspace => simp at high
  | tab => simp at high
  | newline => simp at high
  | formFeed => simp at high
  | carriageReturn => simp at high
  | control _ below _ => omega

/-- A character a canonical string holds as itself is written as itself. -/
theorem escape_of_unescaped {c : Char} (h : Unescaped c) : escape c = [c] := by
  rcases escape_spec c with ⟨-, same⟩ | escaped
  · exact same
  · exact absurd h (escape_not_unescaped escaped)

/-- A character's one escape is the one written. -/
theorem escape_of_escape {e : List Char} {c : Char} (h : Escape e c) : escape c = e := by
  cases h with
  | quote => decide
  | backslash => decide
  | backspace => decide
  | tab => decide
  | newline => decide
  | formFeed => decide
  | carriageReturn => decide
  | control c below other =>
    obtain ⟨b, t, n, f, r⟩ := other
    unfold escape
    have quote : c ≠ '"' := fun same => by
      subst same; simp at below
    have slash : c ≠ '\\' := fun same => by
      subst same; simp at below
    rw [ite_eq_right quote, ite_eq_right slash,
      ite_eq_right fun same =>
        b
          (by
            subst same; rfl),
      ite_eq_right fun same =>
        t
          (by
            subst same; rfl),
      ite_eq_right fun same =>
        n
          (by
            subst same; rfl),
      ite_eq_right fun same =>
        f
          (by
            subst same; rfl),
      ite_eq_right fun same =>
        r
          (by
            subst same; rfl),
      ite_eq_left below]

/-- A canonical string's text between its quotes is its characters' texts. -/
theorem body_eq {text chars : List Char} (h : Body text chars) : text = chars.flatMap escape := by
  induction h with
  | nil => rfl
  | unescaped plain _ ih =>
    rw [List.flatMap_cons, escape_of_unescaped plain, ih]; rfl
  | escape escaped _ ih => rw [List.flatMap_cons, escape_of_escape escaped, ih]

/-- **A canonical `string` is the text the writer writes of the string it spells.** -/
theorem string_written {text : List Char} {s : String} (h : StringText text s) :
    quote s = text := by
  obtain ⟨body, rfl, spelled⟩ := h
  rw [body_eq spelled]
  rfl

/-- A digit character's value, as a digit, gives it back. -/
theorem digitChar_value {d : Char} (low : '0' ≤ d) (high : d ≤ '9') :
    Nat.digitChar (d.toNat - 48) = d := by
  rw [char_le] at low high
  simp only [Char.reduceToNat] at low high
  have small : d.toNat - 48 < 10 := by omega
  apply char_of_toNat
  have := Nat.toNat_digitChar_sub_48_of_lt_ten small
  have digit := (digitChar_digit (d.toNat - 48) small).1
  rw [char_le] at digit
  simp only [Char.reduceToNat] at digit
  omega

/-- Digits after a positive number's: the digits of the number they spell. -/
theorem toDigits_ofDigitChars :
    ∀ (digits : List Char) (init : Nat),
      0 < init →
        (∀ d ∈ digits, '0' ≤ d ∧ d ≤ '9') →
        Nat.toDigits 10 (Nat.ofDigitChars 10 digits init) = Nat.toDigits 10 init ++ digits
  | [], init, _, _ => by simp
  | d :: rest, init, pos, all => by
    obtain ⟨low, high⟩ := all d (by simp)
    have small : d.toNat - 48 < 10 := by
      rw [char_le] at high; simp only [Char.reduceToNat] at high; omega
    rw [Nat.ofDigitChars_cons]
    show Nat.toDigits 10 (Nat.ofDigitChars 10 rest (10 * init + (d.toNat - 48))) = _
    rw [toDigits_ofDigitChars rest _ (by omega) fun x member => all x (by simp [member]), ←
      Nat.toDigits_append_toDigits (by decide) pos small, Nat.toDigits_of_lt_base small,
      digitChar_value low high]
    simp

/-- Zero's text. -/
theorem zero_text : (toString (0 : Int)).toList = ['0'] := by
  show (Int.repr 0).toList = _
  rw [Int.repr_eq_ite, ite_eq_left (by decide)]
  simp [Nat.toList_repr, Nat.toDigits_zero]

/-- **A canonical `integer` is the text the writer writes of the integer it spells.** -/
theorem integer_written {text : List Char} (h : IntegerText text) :
    ∃ n : Int, (toString n).toList = text := by
  rcases h with rfl | ⟨sign, first, digits, signed, low, high, all, rfl⟩
  · exact ⟨0, zero_text⟩
  · have lowNat := low
    have highNat := high
    rw [char_le] at lowNat highNat
    simp only [Char.reduceToNat] at lowNat highNat
    have value : Nat.toDigits 10 (Nat.ofDigitChars 10 (first :: digits) 0) = first :: digits := by
      rw [Nat.ofDigitChars_cons]
      have small : first.toNat - 48 < 10 := by omega
      have pos : 0 < 10 * 0 + (first.toNat - 48) := by omega
      show Nat.toDigits 10 (Nat.ofDigitChars 10 digits (10 * 0 + (first.toNat - 48))) = _
      rw [toDigits_ofDigitChars digits _ pos all]
      simp only [Nat.mul_zero, Nat.zero_add]
      have zeroLow : '0' ≤ first := by
        rw [char_le]; simp only [Char.reduceToNat]; omega
      rw [Nat.toDigits_of_lt_base small, digitChar_value zeroLow high]
      rfl
    have pos : 0 < Nat.ofDigitChars 10 (first :: digits) 0 := by
      apply Nat.pos_of_ne_zero
      intro zero
      rw [zero, Nat.toDigits_zero] at value
      cases digits with
      | nil =>
        simp only [List.cons.injEq, and_true] at value
        subst value; simp at lowNat
      | cons _ _ => simp at value
    rcases signed with rfl | rfl
    · refine ⟨(Nat.ofDigitChars 10 (first :: digits) 0 : Int), ?_⟩
      show (Int.repr _).toList = _
      rw [Int.repr_eq_ite, ite_eq_left (by omega)]
      simp only [Int.toNat_natCast, Nat.toList_repr, value, List.nil_append]
    · refine ⟨-(Nat.ofDigitChars 10 (first :: digits) 0 : Int), ?_⟩
      show (Int.repr _).toList = _
      rw [Int.repr_eq_ite, ite_eq_right (by omega)]
      simp only [Int.neg_neg, Int.toNat_natCast, String.toList_append, Nat.toList_repr, value]
      rfl

/-- Members' keys, their values' texts in place of their values. -/
theorem keys_memberTexts (ms : List (String × Json)) :
    ((ms.map fun m => (m.1, chars m.2)).map (·.1)) = ms.map (·.1) := by
  simp [List.map_map, Function.comp_def]

mutual
/-- **Every canonical text is the text the writer writes of a valid value.** -/
theorem text_written : ∀ {text : List Char}, Text text → ∃ v : Json, v.Valid ∧ chars v = text
  | _, .nullWord => ⟨.null, trivial, rfl⟩
  | _, .trueWord => ⟨.bool true, trivial, rfl⟩
  | _, .falseWord => ⟨.bool false, trivial, rfl⟩
  | _, .integer h => by
    obtain ⟨n, eq⟩ := integer_written h
    exact ⟨.int n, trivial, eq⟩
  | _, .string h => ⟨.str _, trivial, string_written h⟩
  | _, .emptyArray => ⟨.arr [], trivial, rfl⟩
  | _, .array first more => by
    obtain ⟨v, valid, eq⟩ := text_written first
    obtain ⟨vs, allValid, eqs⟩ := moreValues_written more
    refine ⟨.arr (v :: vs), ?_, ?_⟩
    · simp only [Valid]
      exact
        (validItems_iff _).mpr fun x member => by
          simp only [List.mem_cons] at member
          rcases member with rfl | member
          · exact valid
          · exact allValid x member
    · simp only [chars, itemChars_eq, List.map_cons, joined_cons, eq, eqs]
      simp
  | _, .emptyTable => ⟨.obj [], ⟨by simp, trivial⟩, rfl⟩
  | _, @Text.table _ _ _ s _ key value more sorted => by
    obtain ⟨x, valid, eq⟩ := text_written value
    obtain ⟨ms, allValid, keys, eqs⟩ := moreMembers_written more
    have allKeys : (((s, x) :: ms).map (·.1)) = s :: ms.map (·.1) := rfl
    rw [keys] at allKeys
    refine
      ⟨.obj ((s, x) :: ms),
        ⟨by
          rw [allKeys]; exact sorted, ?_⟩,
        ?_⟩
    · exact
        (validMembers_iff _).mpr fun m member => by
          simp only [List.mem_cons] at member
          rcases member with rfl | member
          · exact valid
          · exact allValid m member
    · simp only [chars, memberChars_eq]
      rw [sortMembers_of_pairwise
          (by
            rw [keys_memberTexts, allKeys]; exact sorted)]
      simp only [List.map_cons, joined_cons, memberText, string_written key, eq, eqs,
        List.append_assoc, List.cons_append]
/-- **Every canonical `*( "," value )` is the texts of valid values, each after a comma.** -/
theorem moreValues_written :
    ∀ {text : List Char},
      MoreValues text →
        ∃ vs : List Json, (∀ v ∈ vs, v.Valid) ∧ (vs.map chars).flatMap (',' :: ·) = text
  | _, .nil => ⟨[], by simp, rfl⟩
  | _, .cons value more => by
    obtain ⟨v, valid, eq⟩ := text_written value
    obtain ⟨vs, allValid, eqs⟩ := moreValues_written more
    refine ⟨v :: vs, ?_, ?_⟩
    · intro x member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact valid
      · exact allValid x member
    · simp [eq, eqs]
/-- **Every canonical `*( "," member )` is the texts of valid members, each after a comma.** -/
theorem moreMembers_written :
    ∀ {text : List Char} {keys : List String},
      MoreMembers text keys →
        ∃ ms : List (String × Json),
          (∀ m ∈ ms, m.2.Valid) ∧
            ms.map (·.1) = keys ∧
            ((ms.map fun m => (m.1, chars m.2)).map memberText).flatMap (',' :: ·) = text
  | _, _, .nil => ⟨[], by simp, rfl, rfl⟩
  | _, _, @MoreMembers.cons _ _ _ s _ key value more => by
    obtain ⟨x, valid, eq⟩ := text_written value
    obtain ⟨ms, allValid, keys, eqs⟩ := moreMembers_written more
    refine ⟨(s, x) :: ms, ?_, by simp [keys], ?_⟩
    · intro m member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact valid
      · exact allValid m member
    · rw [← eqs]
      simp [memberText, string_written key, eq]
end

/-! ## What the reader read: its state spells the text so far -/

/-- A member's text, of its key and its value. -/
def pairText (member : String × Json) : List Char := quote member.1 ++ ':' :: chars member.2

/-- A comma before what follows members, unless there are none. -/
def sep {α : Type} (members : List α) : List Char := if members = [] then [] else [',']

/-- The text an open array or object stands for: its bracket and what it holds so far. -/
def Frame.text : Frame → List Char
  | .arr items next =>
    '[' :: joined (items.reverse.map chars) ++
      (match next with
      | .item => [',']
      | _ => [])
  | .obj members next =>
    '{' :: joined (members.reverse.map pairText) ++
      match next with
      | .first | .after => []
      | .key => [',']
      | .colon key => sep members ++ quote key
      | .value key => sep members ++ quote key ++ [':']

/-- The text the open arrays and objects stand for, outermost first. -/
def stackText : List Frame → List Char
  | [] => []
  | frame :: rest => stackText rest ++ frame.text

/-- The text a tree stands for. -/
def Tree.text (t : Tree) : List Char :=
  stackText t.stack ++
    match t.whole with
    | some whole => chars whole
    | none => []

/-- The text a token stands for. -/
def Token.text : Token → List Char
  | .opens true => ['[']
  | .opens false => ['{']
  | .closes true => [']']
  | .closes false => ['}']
  | .colon => [':']
  | .comma => [',']
  | .scalar value => chars value

/-- An open array or object as the reader keeps one: an array holds items exactly after its first,
each valid; an object's keys so far strictly increase and are below a key waiting for its value,
and it holds members exactly where it waits for a key or a comma. -/
def Frame.Good : Frame → Prop
  | .arr items next => (next = .first ↔ items = []) ∧ ∀ item ∈ items, item.Valid
  | .obj members next =>
    (members.reverse.map (·.1)).Pairwise (· < ·) ∧
      (∀ m ∈ members, m.2.Valid) ∧
      match next with
      | .first => members = []
      | .key | .after => members ≠ []
      | .colon key | .value key => ∀ m ∈ members, m.1 < key

/-- A tree as the reader keeps one: each open frame good, and a whole value only once every frame
has closed, valid. -/
def Tree.Good (t : Tree) : Prop :=
  (∀ frame ∈ t.stack, frame.Good) ∧ ∀ whole, t.whole = some whole → t.stack = [] ∧ whole.Valid

/-- Where the reader is within a token, as it keeps it: a word's characters read and to come
are the word's, and a `\u` escape's digits are those canonical text has so far. -/
def Lex.Good : Lex → Prop
  | .word value done rest =>
    done ++ rest = chars value ∧ rest ≠ [] ∧ (value = .null ∨ ∃ b, value = .bool b)
  | .unicode _ digits =>
    digits = [] ∨
      digits = ['0'] ∨ digits = ['0', '0'] ∨ digits = ['0', '0', '0'] ∨ digits = ['0', '0', '1']
  | _ => True

/-- The text where the reader is within a token stands for. -/
def Lex.spelled : Lex → List Char
  | .ready => []
  | .text cs => '"' :: cs.reverse.flatMap escape
  | .escaped cs => '"' :: cs.reverse.flatMap escape ++ ['\\']
  | .unicode cs digits => '"' :: cs.reverse.flatMap escape ++ '\\' :: 'u' :: digits
  | .number cs => cs.reverse
  | .word _ done _ => done

/-- The text a reader stands for. -/
def Reader.text (r : Reader) : List Char := r.tree.text ++ r.lex.spelled

/-- A reader as it keeps itself. -/
def Reader.Good (r : Reader) : Prop := r.tree.Good ∧ r.lex.Good

/-- The tokens canonical text has: a scalar's value is valid. -/
def Token.Valid : Token → Prop
  | .scalar value => value.Valid
  | _ => True

/-- Members' texts joined, one more at the end. -/
theorem joined_pairText_append (members : List (String × Json)) (m : String × Json) :
    joined ((members.reverse ++ [m]).map pairText) =
      joined (members.reverse.map pairText) ++ sep members ++ pairText m := by
  rw [List.map_append, List.map_singleton, joined_append_one]
  simp [sep]

/-- Items' texts joined, one more at the end. -/
theorem joined_chars_append (items : List Json) (v : Json) :
    joined ((items.reverse ++ [v]).map chars) =
      joined (items.reverse.map chars) ++ sep items ++ chars v := by
  rw [List.map_append, List.map_singleton, joined_append_one]
  simp [sep]

/-- A tree with an open frame holds no whole value. -/
theorem Tree.Good.whole_none {t : Tree} (good : t.Good) {frame : Frame} {rest : List Frame}
    (stack : t.stack = frame :: rest) : t.whole = none := by
  cases h : t.whole with
  | none => rfl
  | some whole => exact absurd ((good.2 whole h).1.symm.trans stack) (by simp)

/-- A good tree's text, with an open frame on top. -/
theorem Tree.Good.text_cons {t : Tree} (good : t.Good) {frame : Frame} {rest : List Frame}
    (stack : t.stack = frame :: rest) : t.text = stackText rest ++ frame.text := by
  simp [Tree.text, stack, good.whole_none stack, stackText]

/-- **Adding a value to a good tree**, where it takes one, keeps it good, and its text grows by the
value's. -/
theorem Tree.add_good {t t' : Tree} {v : Json} (good : t.Good) (valid : v.Valid)
    (added : t.add v = .ok t') : t'.Good ∧ t'.text = t.text ++ chars v := by
  unfold Tree.add at added
  split at added
  · rename_i empty
    split at added
    · rename_i none'
      cases added
      refine ⟨⟨by simp [empty], fun whole same => ?_⟩, ?_⟩
      · cases same; exact ⟨empty, valid⟩
      · have : t.whole = none := by simpa using none'
        simp [Tree.text, empty, this, stackText]
    · simp [Tree.refuse] at added
  · rename_i items rest stack
    cases added
    obtain ⟨frames, wholes⟩ := good
    have noWhole := Tree.Good.whole_none ⟨frames, wholes⟩ stack
    have frameGood := frames (.arr items .first) (by simp [stack])
    simp only [Frame.Good, true_iff] at frameGood
    obtain ⟨empty, itemsValid⟩ := frameGood
    subst empty
    refine ⟨⟨?_, fun whole same => by simp [noWhole] at same⟩, ?_⟩
    · intro frame member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨by simp, by simpa using valid⟩
      · exact frames frame (by simp [stack, member])
    · rw [Tree.Good.text_cons ⟨frames, wholes⟩ stack]
      simp [Tree.text, stackText, Frame.text, joined, noWhole]
  · rename_i items rest stack
    cases added
    obtain ⟨frames, wholes⟩ := good
    have noWhole := Tree.Good.whole_none ⟨frames, wholes⟩ stack
    have frameGood := frames (.arr items .item) (by simp [stack])
    simp only [Frame.Good] at frameGood
    obtain ⟨notEmpty, itemsValid⟩ := frameGood
    have nonempty : items ≠ [] := fun empty => absurd (notEmpty.mpr empty) (by simp)
    refine ⟨⟨?_, fun whole same => by simp [noWhole] at same⟩, ?_⟩
    · intro frame member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · refine ⟨by simp, ?_⟩
        intro item inItems
        simp only [List.mem_cons] at inItems
        rcases inItems with rfl | inItems
        · exact valid
        · exact itemsValid item inItems
      · exact frames frame (by simp [stack, member])
    · rw [Tree.Good.text_cons ⟨frames, wholes⟩ stack]
      simp only [Tree.text, stackText, Frame.text, List.reverse_cons, joined_chars_append, sep,
        nonempty, ↓reduceIte, noWhole]
      simp
  · rename_i members key rest stack
    cases added
    obtain ⟨frames, wholes⟩ := good
    have noWhole := Tree.Good.whole_none ⟨frames, wholes⟩ stack
    have frameGood := frames (.obj members (.value key)) (by simp [stack])
    simp only [Frame.Good] at frameGood
    obtain ⟨sorted, valuesValid, below⟩ := frameGood
    refine ⟨⟨?_, fun whole same => by simp [noWhole] at same⟩, ?_⟩
    · intro frame member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · refine ⟨?_, ?_, by simp⟩
        · simp only [List.reverse_cons, List.map_append, List.map_singleton]
          rw [List.pairwise_append]
          refine ⟨sorted, by simp, ?_⟩
          intro a inA b inB
          simp only [List.mem_singleton] at inB
          subst inB
          simp only [List.mem_map, List.mem_reverse] at inA
          obtain ⟨m, inMembers, rfl⟩ := inA
          exact below m inMembers
        · intro m member
          simp only [List.mem_cons] at member
          rcases member with rfl | member
          · exact valid
          · exact valuesValid m member
      · exact frames frame (by simp [stack, member])
    · rw [Tree.Good.text_cons ⟨frames, wholes⟩ stack]
      simp only [Tree.text, stackText, Frame.text, List.reverse_cons, joined_pairText_append,
        pairText, noWhole]
      simp
  · simp [Tree.refuse] at added

/-- A key that `keyAfter` takes is greater than every key read so far. -/
theorem keyAfter_below {members : List (String × Json)} {key : String}
    (sorted : (members.reverse.map (·.1)).Pairwise (· < ·))
    (after : keyAfter members key = .ok ()) : ∀ m ∈ members, m.1 < key := by
  cases members with
  | nil => simp
  | cons last older =>
    simp only [keyAfter] at after
    split at after
    · rename_i lt
      intro m member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact lt
      · simp only [List.reverse_cons, List.map_append, List.map_singleton] at sorted
        rw [List.pairwise_append] at sorted
        exact
          String.lt_trans
            (sorted.2.2 m.1
              (by
                simp; exact ⟨m.2, member⟩)
              last.1 (by simp))
            lt
    · split at after <;> cases after

/-- A good tree that takes a value holds no whole value. -/
theorem Tree.Good.wants_none {t : Tree} (good : t.Good) (wants : t.wantsValue = true) :
    t.whole = none := by
  cases stack : t.stack with
  | nil =>
    simp only [Tree.wantsValue, stack] at wants
    simpa using wants
  | cons frame rest => exact good.whole_none stack

/-- Members' texts as the writer writes an object's, of members by strictly increasing key. -/
theorem chars_obj_sorted {members : List (String × Json)}
    (sorted : (members.map (·.1)).Pairwise (· < ·)) :
    chars (.obj members) = '{' :: joined (members.map pairText) ++ ['}'] := by
  simp only [chars, memberChars_eq]
  rw [sortMembers_of_pairwise
      (by
        rw [keys_memberTexts]; exact sorted)]
  simp only [List.map_map]
  rfl

/-- **Taking a token, a good tree stays good, and its text grows by the token's.** -/
theorem Tree.take_good {t t' : Tree} {token : Token} (good : t.Good) (valid : token.Valid)
    (taken : t.take token = .ok t') : t'.Good ∧ t'.text = t.text ++ token.text := by
  cases token with
  | scalar value =>
    cases value with
    | str s =>
      simp only [Tree.take] at taken
      split at taken
      · rename_i members rest stack
        cases after : keyAfter members s with
        | error e => simp [after, Except.map] at taken
        | ok u =>
          cases u
          simp only [after, Except.map] at taken
          cases taken
          obtain ⟨frames, wholes⟩ := good
          have noWhole := Tree.Good.whole_none ⟨frames, wholes⟩ stack
          have frameGood := frames (.obj members .first) (by simp [stack])
          simp only [Frame.Good] at frameGood
          obtain ⟨sorted, valuesValid, empty⟩ := frameGood
          subst empty
          refine ⟨⟨?_, fun whole same => by simp [noWhole] at same⟩, ?_⟩
          · intro frame member
            simp only [List.mem_cons] at member
            rcases member with rfl | member
            · exact ⟨by simp, by simp, by simp⟩
            · exact frames frame (by simp [stack, member])
          · rw [Tree.Good.text_cons ⟨frames, wholes⟩ stack]
            simp [Tree.text, stackText, Frame.text, joined, sep, noWhole, Token.text, chars]
      · rename_i members rest stack
        cases after : keyAfter members s with
        | error e => simp [after, Except.map] at taken
        | ok u =>
          cases u
          simp only [after, Except.map] at taken
          cases taken
          obtain ⟨frames, wholes⟩ := good
          have noWhole := Tree.Good.whole_none ⟨frames, wholes⟩ stack
          have frameGood := frames (.obj members .key) (by simp [stack])
          simp only [Frame.Good] at frameGood
          obtain ⟨sorted, valuesValid, nonempty⟩ := frameGood
          refine ⟨⟨?_, fun whole same => by simp [noWhole] at same⟩, ?_⟩
          · intro frame member
            simp only [List.mem_cons] at member
            rcases member with rfl | member
            · exact ⟨sorted, valuesValid, keyAfter_below sorted after⟩
            · exact frames frame (by simp [stack, member])
          · rw [Tree.Good.text_cons ⟨frames, wholes⟩ stack]
            simp [Tree.text, stackText, Frame.text, sep, nonempty, noWhole, Token.text, chars]
      · exact Tree.add_good good valid taken
    | null => exact Tree.add_good good valid taken
    | bool b => exact Tree.add_good good valid taken
    | int n => exact Tree.add_good good valid taken
    | arr items => exact Tree.add_good good valid taken
    | obj members => exact Tree.add_good good valid taken
  | opens array =>
    simp only [Tree.take] at taken
    split at taken
    · rename_i wants
      cases taken
      have noWhole := good.wants_none wants
      refine ⟨⟨?_, fun whole same => by simp [noWhole] at same⟩, ?_⟩
      · intro frame member
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · cases array <;> simp [Frame.Good]
        · exact good.1 frame member
      · cases array <;> simp [Tree.text, stackText, Frame.text, joined, noWhole, Token.text]
    · simp [Tree.refuse] at taken
  | closes array =>
    cases array with
    | true =>
      simp only [Tree.take] at taken
      split at taken
      · rename_i items rest stack
        have noWhole := good.whole_none stack
        have frameGood := good.1 (.arr items .first) (by simp [stack])
        simp only [Frame.Good, true_iff] at frameGood
        obtain ⟨empty, -⟩ := frameGood
        subst empty
        have restGood : ({ t with stack := rest } : Tree).Good :=
          ⟨fun frame member => good.1 frame (by simp [stack, member]), fun whole same => by
            simp [noWhole] at same⟩
        obtain ⟨good', text'⟩ := Tree.add_good restGood (by simp [Valid, ValidItems]) taken
        refine ⟨good', ?_⟩
        rw [text', good.text_cons stack]
        simp [Tree.text, noWhole, Frame.text, joined, chars, itemChars, Token.text]
      · rename_i items rest stack
        have noWhole := good.whole_none stack
        have frameGood := good.1 (.arr items .after) (by simp [stack])
        simp only [Frame.Good] at frameGood
        obtain ⟨-, itemsValid⟩ := frameGood
        have restGood : ({ t with stack := rest } : Tree).Good :=
          ⟨fun frame member => good.1 frame (by simp [stack, member]), fun whole same => by
            simp [noWhole] at same⟩
        obtain ⟨good', text'⟩ :=
          Tree.add_good restGood
            (by
              simp only [Valid];
              exact
                (validItems_iff _).mpr fun x member => itemsValid x (List.mem_reverse.mp member))
            taken
        refine ⟨good', ?_⟩
        rw [text', good.text_cons stack]
        simp [Tree.text, noWhole, Frame.text, chars, itemChars_eq, Token.text]
      · simp [Tree.refuse] at taken
    | false =>
      simp only [Tree.take] at taken
      split at taken
      · rename_i members rest stack
        have noWhole := good.whole_none stack
        have frameGood := good.1 (.obj members .first) (by simp [stack])
        simp only [Frame.Good] at frameGood
        obtain ⟨-, -, empty⟩ := frameGood
        subst empty
        have restGood : ({ t with stack := rest } : Tree).Good :=
          ⟨fun frame member => good.1 frame (by simp [stack, member]), fun whole same => by
            simp [noWhole] at same⟩
        obtain ⟨good', text'⟩ := Tree.add_good restGood (by simp [Valid, ValidMembers]) taken
        refine ⟨good', ?_⟩
        rw [text', good.text_cons stack]
        simp [Tree.text, noWhole, Frame.text, joined, chars, memberChars, sortMembers, Token.text]
      · rename_i members rest stack
        have noWhole := good.whole_none stack
        have frameGood := good.1 (.obj members .after) (by simp [stack])
        simp only [Frame.Good] at frameGood
        obtain ⟨sorted, valuesValid, -⟩ := frameGood
        have restGood : ({ t with stack := rest } : Tree).Good :=
          ⟨fun frame member => good.1 frame (by simp [stack, member]), fun whole same => by
            simp [noWhole] at same⟩
        obtain ⟨good', text'⟩ :=
          Tree.add_good restGood
            (show (Json.obj members.reverse).Valid from
              ⟨sorted,
                (validMembers_iff _).mpr fun m member =>
                  valuesValid m (List.mem_reverse.mp member)⟩)
            taken
        refine ⟨good', ?_⟩
        rw [text', good.text_cons stack, chars_obj_sorted sorted]
        simp [Tree.text, noWhole, Frame.text, Token.text]
      · simp [Tree.refuse] at taken
  | colon =>
    simp only [Tree.take] at taken
    split at taken
    · rename_i members key rest stack
      cases taken
      have noWhole := good.whole_none stack
      have frameGood := good.1 (.obj members (.colon key)) (by simp [stack])
      refine ⟨⟨?_, fun whole same => by simp [noWhole] at same⟩, ?_⟩
      · intro frame member
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · exact frameGood
        · exact good.1 frame (by simp [stack, member])
      · rw [good.text_cons stack]
        simp [Tree.text, stackText, Frame.text, noWhole, Token.text]
    · simp [Tree.refuse] at taken
  | comma =>
    simp only [Tree.take] at taken
    split at taken
    · rename_i items rest stack
      cases taken
      have noWhole := good.whole_none stack
      have frameGood := good.1 (.arr items .after) (by simp [stack])
      simp only [Frame.Good] at frameGood
      obtain ⟨notEmpty, itemsValid⟩ := frameGood
      refine ⟨⟨?_, fun whole same => by simp [noWhole] at same⟩, ?_⟩
      · intro frame member
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · refine ⟨?_, itemsValid⟩
          simp only [reduceCtorEq, false_iff]
          exact fun empty => absurd (notEmpty.mpr empty) (by simp)
        · exact good.1 frame (by simp [stack, member])
      · rw [good.text_cons stack]
        simp [Tree.text, stackText, Frame.text, noWhole, Token.text]
    · rename_i members rest stack
      cases taken
      have noWhole := good.whole_none stack
      have frameGood := good.1 (.obj members .after) (by simp [stack])
      refine ⟨⟨?_, fun whole same => by simp [noWhole] at same⟩, ?_⟩
      · intro frame member
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · exact frameGood
        · exact good.1 frame (by simp [stack, member])
      · rw [good.text_cons stack]
        simp [Tree.text, stackText, Frame.text, noWhole, Token.text]
    · simp [Tree.refuse] at taken

/-- A code point below the surrogates is its character's. -/
theorem char_ofNat_toNat {n : Nat} (h : n < 0xD800) : (Char.ofNat n).toNat = n := by
  unfold Char.ofNat
  rw [dite_eq_left
      (by
        unfold Nat.isValidChar; omega)]
  simp [Char.ofNatAux, Char.toNat]

/-- A one-letter escape's character is written as that escape. -/
theorem shortEscape_escape {c d : Char} (h : shortEscape c = some d) : escape d = ['\\', c] := by
  unfold shortEscape at h
  split at h
  · rename_i same; cases h; subst same; decide
  · split at h
    · rename_i _ same; cases h; subst same; decide
    · split at h
      · rename_i _ _ same; cases h; subst same; decide
      · split at h
        · rename_i _ _ _ same; cases h; subst same; decide
        · split at h
          · rename_i _ _ _ _ same; cases h; subst same; decide
          · split at h
            · rename_i _ _ _ _ _ same; cases h; subst same; decide
            · split at h
              · rename_i _ _ _ _ _ _ same; cases h; subst same; decide
              · cases h

/-- A lowercase hexadecimal digit's value is below 16 and gives it back. -/
theorem lowerHex_hexDigit {c : Char} {low : Nat} (h : lowerHex c = some low) :
    low < 16 ∧ hexDigit low = c := by
  unfold lowerHex at h
  split at h
  · rename_i digit
    cases h
    obtain ⟨l, r⟩ := digit
    simp only [char_le, Char.reduceToNat] at l r
    refine ⟨by omega, ?_⟩
    unfold hexDigit
    rw [ite_eq_left (by omega)]
    apply char_of_toNat
    rw [char_ofNat_toNat (by omega)]
    omega
  · split at h
    · rename_i _ letter
      cases h
      obtain ⟨l, r⟩ := letter
      simp only [char_le, Char.reduceToNat] at l r
      refine ⟨by omega, ?_⟩
      unfold hexDigit
      rw [ite_eq_right (by omega)]
      apply char_of_toNat
      rw [char_ofNat_toNat (by omega)]
      omega
    · cases h

/-- A control character without a one-letter escape is written as `\u00` and its two digits. -/
theorem escape_control {code : Nat} (below : code < 0x20) (other : ¬code ∈ [8, 9, 10, 12, 13]) :
    escape (Char.ofNat code) =
      ['\\', 'u', '0', '0', hexDigit (code / 16), hexDigit (code % 16)] := by
  have same : (Char.ofNat code).toNat = code := char_ofNat_toNat (by omega)
  simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at other
  obtain ⟨b, t, n, f, r⟩ := other
  unfold escape
  have ne : ∀ d : Char, d.toNat ≠ code → Char.ofNat code ≠ d := fun d differ eq => by
    subst eq; exact differ same
  rw [ite_eq_right
      (ne '"'
        (by
          simp; omega)),
    ite_eq_right
      (ne '\\'
        (by
          simp; omega)),
    ite_eq_right
      (ne '\x08'
        (by
          simp; omega)),
    ite_eq_right
      (ne '\t'
        (by
          simp; omega)),
    ite_eq_right
      (ne '\n'
        (by
          simp; omega)),
    ite_eq_right
      (ne '\x0c'
        (by
          simp; omega)),
    ite_eq_right
      (ne '\r'
        (by
          simp; omega)),
    ite_eq_left
      (by
        rw [same]; exact below),
    same]

/-- **A token the reader takes** keeps it good, between tokens, its text grown by the token's. -/
theorem Reader.token_good {r r' : Reader} {token : Token} (good : r.Good)
    (taken : r.token token = .ok r') (valid : token.Valid) :
    r'.Good ∧ r'.text = r.tree.text ++ token.text ∧ r'.lex = .ready := by
  unfold Reader.token at taken
  cases h : r.tree.take token with
  | error e => simp [h, Except.map] at taken
  | ok t' =>
    simp only [h, Except.map] at taken
    cases taken
    obtain ⟨good', text'⟩ := Tree.take_good good.1 valid h
    refine ⟨⟨good', trivial⟩, ?_, rfl⟩
    show t'.text ++ [] = _
    rw [text', List.append_nil]

/-- **A character read between tokens** keeps the reader good, its text grown by the character. -/
theorem Reader.start_good {r r' : Reader} {c : Char} (good : r.Good) (ready : r.lex = .ready)
    (started : r.start c = .ok r') : r'.Good ∧ r'.text = r.text ++ [c] := by
  have text : r.text = r.tree.text := by simp [Reader.text, ready, Lex.spelled]
  rw [text]
  have tokenCase :
    ∀ (token : Token),
      r.token token = .ok r' →
        token.Valid → token.text = [c] → r'.Good ∧ r'.text = r.tree.text ++ [c] := by
    intro token taken valid spelled
    obtain ⟨g, t, -⟩ := Reader.token_good good taken valid
    exact ⟨g, by rw [t, spelled]⟩
  unfold Reader.start at started
  by_cases ws : c = ' ' ∨ c = '\t' ∨ c = '\n' ∨ c = '\r'
  · rw [ite_eq_left ws] at started; cases started
  rw [ite_eq_right ws] at started
  by_cases quote : c = '"'
  · rw [ite_eq_left quote] at started
    cases started; subst quote
    exact ⟨⟨good.1, trivial⟩, by simp [Reader.text, Lex.spelled]⟩
  rw [ite_eq_right quote] at started
  by_cases h : c = '['
  · rw [ite_eq_left h] at started; subst h; exact tokenCase _ started trivial rfl
  rw [ite_eq_right h] at started
  by_cases h : c = '{'
  · rw [ite_eq_left h] at started; subst h; exact tokenCase _ started trivial rfl
  rw [ite_eq_right h] at started
  by_cases h : c = ']'
  · rw [ite_eq_left h] at started; subst h; exact tokenCase _ started trivial rfl
  rw [ite_eq_right h] at started
  by_cases h : c = '}'
  · rw [ite_eq_left h] at started; subst h; exact tokenCase _ started trivial rfl
  rw [ite_eq_right h] at started
  by_cases h : c = ':'
  · rw [ite_eq_left h] at started; subst h; exact tokenCase _ started trivial rfl
  rw [ite_eq_right h] at started
  by_cases h : c = ','
  · rw [ite_eq_left h] at started; subst h; exact tokenCase _ started trivial rfl
  rw [ite_eq_right h] at started
  by_cases h : c = 't'
  · rw [ite_eq_left h] at started
    cases started; subst h
    exact ⟨⟨good.1, rfl, by simp, .inr ⟨true, rfl⟩⟩, by simp [Reader.text, Lex.spelled]⟩
  rw [ite_eq_right h] at started
  by_cases h : c = 'f'
  · rw [ite_eq_left h] at started
    cases started; subst h
    exact ⟨⟨good.1, rfl, by simp, .inr ⟨false, rfl⟩⟩, by simp [Reader.text, Lex.spelled]⟩
  rw [ite_eq_right h] at started
  by_cases h : c = 'n'
  · rw [ite_eq_left h] at started
    cases started; subst h
    exact ⟨⟨good.1, rfl, by simp, .inl rfl⟩, by simp [Reader.text, Lex.spelled]⟩
  rw [ite_eq_right h] at started
  by_cases h : c = '-' ∨ '0' ≤ c ∧ c ≤ '9'
  · rw [ite_eq_left h] at started
    cases started
    exact ⟨⟨good.1, trivial⟩, by simp [Reader.text, Lex.spelled]⟩
  rw [ite_eq_right h] at started
  cases started

/-- **A number's end, spelled as canonical text spells its integer**, keeps the reader good, between
tokens, its text the same. -/
theorem Reader.endNumber_good {r r' : Reader} {cs : List Char} (good : r.Good)
    (ended : r.endNumber cs = .ok r') :
    r'.Good ∧ r'.text = r.tree.text ++ cs.reverse ∧ r'.lex = .ready := by
  unfold Reader.endNumber at ended
  split at ended
  · rename_i spelled
    obtain ⟨g, t, l⟩ := Reader.token_good good ended trivial
    refine ⟨g, ?_, l⟩
    rw [t]
    simp only [Token.text, chars, spelled]
  · cases ended

/-- **Each character the reader takes keeps it good, its text grown by the character.** -/
theorem Reader.step_good {r r' : Reader} {c : Char} (good : r.Good) (stepped : r.step c = .ok r') :
    r'.Good ∧ r'.text = r.text ++ [c] := by
  unfold Reader.step at stepped
  split at stepped
  · rename_i ready
    exact Reader.start_good good ready stepped
  · rename_i cs lex
    split at stepped
    · rename_i quote
      subst quote
      obtain ⟨g, t, -⟩ := Reader.token_good good stepped trivial
      refine ⟨g, ?_⟩
      rw [t]
      simp [Reader.text, lex, Lex.spelled, Token.text, chars, Json.quote]
    · split at stepped
      · rename_i _ slash
        cases stepped; subst slash
        exact ⟨⟨good.1, trivial⟩, by simp [Reader.text, lex, Lex.spelled]⟩
      · split at stepped
        · cases stepped
        · rename_i notQuote notSlash notControl
          cases stepped
          refine ⟨⟨good.1, trivial⟩, ?_⟩
          simp only [Reader.text, lex, Lex.spelled, List.reverse_cons, List.flatMap_append,
            List.flatMap_cons, List.flatMap_nil, List.append_nil]
          rw [escape_of_unescaped ⟨notQuote, notSlash, by omega⟩]
          simp
  · rename_i cs lex
    split at stepped
    · rename_i d short
      cases stepped
      refine ⟨⟨good.1, trivial⟩, ?_⟩
      simp only [Reader.text, lex, Lex.spelled, List.reverse_cons, List.flatMap_append,
        List.flatMap_cons, List.flatMap_nil, List.append_nil, shortEscape_escape short]
      simp
    · split at stepped
      · rename_i u
        cases stepped; subst u
        exact ⟨⟨good.1, .inl rfl⟩, by simp [Reader.text, lex, Lex.spelled]⟩
      · split at stepped <;> cases stepped
  · rename_i cs digits lex
    have digitsGood := good.2
    rw [lex] at digitsGood
    split at stepped
    · split at stepped
      · rename_i zero
        cases stepped; subst zero
        exact ⟨⟨good.1, .inr (.inl rfl)⟩, by simp [Reader.text, lex, Lex.spelled]⟩
      · cases stepped
    · split at stepped
      · rename_i zero
        cases stepped; subst zero
        exact ⟨⟨good.1, .inr (.inr (.inl rfl))⟩, by simp [Reader.text, lex, Lex.spelled]⟩
      · cases stepped
    · split at stepped
      · rename_i which
        cases stepped
        refine ⟨⟨good.1, ?_⟩, by simp [Reader.text, lex, Lex.spelled]⟩
        rcases which with rfl | rfl
        · exact .inr (.inr (.inr (.inl rfl)))
        · exact .inr (.inr (.inr (.inr rfl)))
      · cases stepped
    · rename_i high
      split at stepped
      · cases stepped
      · rename_i low hex
        split at stepped
        · cases stepped
        · rename_i other
          cases stepped
          obtain ⟨lowSmall, lowDigit⟩ := lowerHex_hexDigit hex
          have highDigit : high = '0' ∨ high = '1' := by
            simp [Lex.Good] at digitsGood
            rcases digitsGood with h | h
            · exact .inl h
            · exact .inr h
          have code : unicodeCode high low < 0x20 := by
            unfold unicodeCode; split <;> omega
          refine ⟨⟨good.1, trivial⟩, ?_⟩
          simp only [Reader.text, lex, Lex.spelled, List.reverse_cons, List.flatMap_append,
            List.flatMap_cons, List.flatMap_nil, List.append_nil, escape_control code other]
          have high16 : unicodeCode high low / 16 = if high = '1' then 1 else 0 := by
            unfold unicodeCode; split <;> omega
          have low16 : unicodeCode high low % 16 = low := by
            unfold unicodeCode; split <;> omega
          rw [high16, low16, lowDigit]
          rcases highDigit with rfl | rfl <;> simp [hexDigit]
    · cases stepped
  · rename_i cs lex
    split at stepped
    · rename_i digit
      cases stepped
      exact ⟨⟨good.1, trivial⟩, by simp [Reader.text, lex, Lex.spelled]⟩
    · split at stepped
      · cases stepped
      · cases ended : r.endNumber cs with
        | error e =>
          simp only [ended, Except.bind] at stepped; cases stepped
        | ok r'' =>
          simp only [ended, Except.bind] at stepped
          obtain ⟨g, t, l⟩ := Reader.endNumber_good good ended
          obtain ⟨g', t'⟩ := Reader.start_good g l stepped
          refine ⟨g', ?_⟩
          rw [t', t]
          simp [Reader.text, lex, Lex.spelled]
  · rename_i value done rest lex
    have wordGood := good.2
    rw [lex] at wordGood
    obtain ⟨spelled, nonempty, word⟩ := wordGood
    split at stepped
    · rename_i next more
      split at stepped
      · rename_i same
        subst same
        split at stepped
        · rename_i last
          subst last
          have valid : value.Valid := by rcases word with rfl | ⟨b, rfl⟩ <;> trivial
          obtain ⟨g, t, -⟩ := Reader.token_good good stepped valid
          refine ⟨g, ?_⟩
          rw [t]
          simp [Reader.text, lex, Lex.spelled, Token.text, ← spelled]
        · rename_i notLast
          cases stepped
          refine ⟨⟨good.1, by simpa using spelled, notLast, word⟩, ?_⟩
          simp [Reader.text, lex, Lex.spelled]
      · cases stepped
    · cases stepped

/-- **Reading characters keeps a good reader good, its text grown by them.** -/
theorem run_good :
    ∀ (cs : List Char) (r r' : Reader) (pos : Nat),
      r.Good → run r pos cs = .ok r' → r'.Good ∧ r'.text = r.text ++ cs
  | [], r, r', _, good, ran => by
    simp only [run] at ran
    cases ran
    exact ⟨good, by simp⟩
  | c :: rest, r, r', pos, good, ran => by
    simp only [run] at ran
    split at ran
    · rename_i next stepped
      obtain ⟨g, t⟩ := Reader.step_good good stepped
      obtain ⟨g', t'⟩ := run_good rest next r' (pos + 1) g ran
      exact
        ⟨g', by
          rw [t', t]; simp⟩
    · cases ran

/-- **The value a good reader finishes with is valid, and its text is the reader's.** -/
theorem Reader.finish_good {r : Reader} {v : Json} (good : r.Good) (finished : r.finish = .ok v) :
    v.Valid ∧ chars v = r.text := by
  unfold Reader.finish at finished
  have whole :
    ∀ (ended : Reader),
      ended.Good →
        ended.lex = .ready →
        (match ended.tree.stack, ended.tree.whole with
          | [], some whole => (Except.ok whole : Except String Json)
          | [], none => .error "the end of the text, which holds no value"
          | _ :: _, _ => .error "the end of the text, where an array or an object is still open") =
          .ok v →
        v.Valid ∧ chars v = ended.text := by
    intro ended g l h
    split at h
    · rename_i stack w
      cases h
      have := (g.1.2 v w).2
      exact ⟨this, by simp [Reader.text, Tree.text, stack, w, stackText, l, Lex.spelled]⟩
    · cases h
    · cases h
  cases lex : r.lex with
  | ready =>
    simp only [lex] at finished
    exact whole r good lex finished
  | number cs =>
    simp only [lex] at finished
    cases ended : r.endNumber cs with
    | error e => simp [ended, bind, Except.bind] at finished
    | ok r'' =>
      simp only [ended] at finished
      obtain ⟨g, t, l⟩ := Reader.endNumber_good good ended
      obtain ⟨valid, text⟩ := whole r'' g l finished
      exact
        ⟨valid, by
          rw [text, t]; simp [Reader.text, lex, Lex.spelled]⟩
  | text _ => simp [lex, bind, Except.bind] at finished
  | escaped _ => simp [lex, bind, Except.bind] at finished
  | unicode _ _ => simp [lex, bind, Except.bind] at finished
  | word _ _ _ => simp [lex, bind, Except.bind] at finished

/-- **What the reader reads is a valid value whose text is the text read.** -/
theorem parse_sound {text : String} {v : Json} (parsed : parse text = .ok v) :
    v.Valid ∧ render v = text := by
  unfold parse at parsed
  split at parsed
  · cases parsed
  · rename_i r ran
    split at parsed
    · rename_i finished
      cases parsed
      obtain ⟨g, t⟩ := run_good text.toList {} r 0 ⟨⟨by simp, by simp⟩, trivial⟩ ran
      obtain ⟨valid, chars⟩ := Reader.finish_good g finished
      refine ⟨valid, ?_⟩
      unfold render
      rw [chars, t]
      simp [Reader.text, Tree.text, stackText, Lex.spelled]
    · cases parsed

/-! ## The reader reads every valid value's text -/

/-- Reading characters, then more. -/
theorem run_append :
    ∀ (cs more : List Char) (r r' : Reader) (pos : Nat),
      run r pos cs = .ok r' → run r pos (cs ++ more) = run r' (pos + cs.length) more
  | [], more, r, r', pos, ran => by
    simp only [run] at ran
    cases ran
    simp
  | c :: rest, more, r, r', pos, ran => by
    simp only [run] at ran
    split at ran
    · rename_i next stepped
      simp only [List.cons_append, run, stepped]
      rw [run_append rest more next r' (pos + 1) ran]
      congr 1
      simp only [List.length_cons]
      omega
    · cases ran

/-- A reader that has read a value into `t`, or is in a number that spells, as canonical text
does, the integer that reads into `t` once the number ends. -/
def Settled (r : Reader) (t : Tree) : Prop :=
  r = { lex := .ready, tree := t } ∨
    ∃ cs, r.lex = .number cs ∧ r.endNumber cs = .ok { lex := .ready, tree := t }

/-- A settled reader takes a character no number goes on with as the reader with the value read
does. -/
theorem Settled.step {r : Reader} {t : Tree} (settled : Settled r t) {c : Char}
    (notDigit : ¬('0' ≤ c ∧ c ≤ '9')) (notFloat : ¬(c = '.' ∨ c = 'e' ∨ c = 'E')) :
    r.step c = ({ lex := .ready, tree := t } : Reader).step c := by
  rcases settled with rfl | ⟨cs, lex, ended⟩
  · rfl
  · unfold Reader.step
    rw [lex]
    simp only [notDigit, notFloat, ↓reduceIte, ended, Except.bind]

/-- A settled reader reads a comma or a closing bracket as the reader with the value read does. -/
theorem Settled.run {r : Reader} {t : Tree} (settled : Settled r t) {c : Char}
    (delimiter : c = ',' ∨ c = ']' ∨ c = '}') (cs : List Char) (pos : Nat) :
    run r pos (c :: cs) = run { lex := .ready, tree := t } pos (c :: cs) := by
  have notDigit : ¬('0' ≤ c ∧ c ≤ '9') := by rcases delimiter with rfl | rfl | rfl <;> decide
  have notFloat : ¬(c = '.' ∨ c = 'e' ∨ c = 'E') := by
    rcases delimiter with rfl | rfl | rfl <;> decide
  simp only [Linger.Json.run, settled.step notDigit notFloat]

/-- A settled reader finishes as the reader with the value read does. -/
theorem Settled.finish {r : Reader} {t : Tree} (settled : Settled r t) :
    r.finish = ({ lex := .ready, tree := t } : Reader).finish := by
  rcases settled with rfl | ⟨cs, lex, ended⟩
  · rfl
  · unfold Reader.finish
    rw [lex]
    simp only [ended]

/-- A tree that takes a value as a whole value takes it as a token too. -/
theorem take_scalar {t t' : Tree} {v : Json} (added : t.add v = .ok t') :
    t.take (.scalar v) = .ok t' := by
  cases v with
  | str s =>
    simp only [Tree.take]
    split
    · rename_i members rest stack
      simp [Tree.add, stack, Tree.refuse] at added
    · rename_i members rest stack
      simp [Tree.add, stack, Tree.refuse] at added
    · exact added
  | _ =>
    simp only [Tree.take]; exact added

/-- A tree that takes a value takes an array's or an object's opening bracket. -/
theorem add_wantsValue {t t' : Tree} {v : Json} (added : t.add v = .ok t') :
    t.wantsValue = true := by
  unfold Tree.add at added
  split at added
  · rename_i stack
    split at added
    · rename_i none'
      simp [Tree.wantsValue, stack, none']
    · simp [Tree.refuse] at added
  · rename_i stack; simp [Tree.wantsValue, stack]
  · rename_i stack; simp [Tree.wantsValue, stack]
  · rename_i stack; simp [Tree.wantsValue, stack]
  · simp [Tree.refuse] at added

/-- The reader reads a character as itself or by its escape, within a string. -/
theorem escape_read (c : Char) (acc : List Char) (tree : Tree) (pos : Nat) :
    run { lex := .text acc, tree } pos (escape c) = .ok { lex := .text (c :: acc), tree } := by
  rcases escape_spec c with ⟨⟨notQuote, notSlash, high⟩, same⟩ | escaped
  · rw [same]
    simp [Linger.Json.run, Reader.step, notQuote, notSlash, show ¬c.toNat < 32 by omega]
  · obtain ⟨e, written, escaped⟩ : ∃ e, escape c = e ∧ Escape e c := ⟨_, rfl, escaped⟩
    rw [written]
    cases escaped with
    | quote => simp [Linger.Json.run, Reader.step, shortEscape]
    | backslash => simp [Linger.Json.run, Reader.step, shortEscape]
    | backspace => simp [Linger.Json.run, Reader.step, shortEscape]
    | tab => simp [Linger.Json.run, Reader.step, shortEscape]
    | newline => simp [Linger.Json.run, Reader.step, shortEscape]
    | formFeed => simp [Linger.Json.run, Reader.step, shortEscape]
    | carriageReturn => simp [Linger.Json.run, Reader.step, shortEscape]
    | control c below other =>
      obtain ⟨b, t, n, f, r⟩ := other
      have highDigit : hexDigit (c.toNat / 16) = '0' ∨ hexDigit (c.toNat / 16) = '1' := by
        have : c.toNat / 16 = 0 ∨ c.toNat / 16 = 1 := by omega
        rcases this with h | h <;> rw [h] <;> decide
      have lowHex : lowerHex (hexDigit (c.toNat % 16)) = some (c.toNat % 16) :=
        (show ∀ k < 16, lowerHex (hexDigit k) = some k by decide) (c.toNat % 16)
          (Nat.mod_lt _ (by decide))
      have code : unicodeCode (hexDigit (c.toNat / 16)) (c.toNat % 16) = c.toNat := by
        unfold unicodeCode
        have : c.toNat / 16 = 0 ∨ c.toNat / 16 = 1 := by omega
        rcases this with h | h
        · rw [h, show hexDigit 0 = '0' by decide]; simp; omega
        · rw [h, show hexDigit 1 = '1' by decide]; simp; omega
      have notShort :
        ¬unicodeCode (hexDigit (c.toNat / 16)) (c.toNat % 16) ∈ [8, 9, 10, 12, 13] := by
        rw [code]; simp; omega
      have slash :
        ({ lex := .text acc, tree } : Reader).step '\\' = .ok { lex := .escaped acc, tree } := by
        simp [Reader.step]
      have u :
        ({ lex := .escaped acc, tree } : Reader).step 'u' =
          .ok { lex := .unicode acc [], tree } := by
        simp [Reader.step, shortEscape]
      have zero :
        ({ lex := .unicode acc [], tree } : Reader).step '0' =
          .ok { lex := .unicode acc ['0'], tree } := by
        simp [Reader.step]
      have zeroZero :
        ({ lex := .unicode acc ['0'], tree } : Reader).step '0' =
          .ok { lex := .unicode acc ['0', '0'], tree } := by
        simp [Reader.step]
      have high :
        ({ lex := .unicode acc ['0', '0'], tree } : Reader).step (hexDigit (c.toNat / 16)) =
          .ok { lex := .unicode acc ['0', '0', hexDigit (c.toNat / 16)], tree } := by
        simp only [Reader.step]
        rw [ite_eq_left highDigit]
        rfl
      have low :
        ({ lex := .unicode acc ['0', '0', hexDigit (c.toNat / 16)], tree } : Reader).step
            (hexDigit (c.toNat % 16)) =
          .ok { lex := .text (c :: acc), tree } := by
        simp only [Reader.step, lowHex]
        rw [ite_eq_right notShort, code, Char.ofNat_toNat]
      simp only [Linger.Json.run, slash, u, zero, zeroZero, high, low]

/-- The reader reads a string's characters within it. -/
theorem escapes_read :
    ∀ (cs acc : List Char) (tree : Tree) (pos : Nat),
      ∃ pos',
        run { lex := .text acc, tree } pos (cs.flatMap escape) =
            .ok { lex := .text (cs.reverse ++ acc), tree } ∧
          pos' = pos
  | [], acc, tree, pos => ⟨pos, by simp [Linger.Json.run], rfl⟩
  | c :: rest, acc, tree, pos => by
    refine ⟨pos, ?_, rfl⟩
    rw [List.flatMap_cons, run_append _ _ _ _ _ (escape_read c acc tree pos)]
    obtain ⟨_, ran, -⟩ := escapes_read rest (c :: acc) tree (pos + (escape c).length)
    rw [ran]
    simp

/-- **The reader reads a string's text**, as the token its tree takes. -/
theorem quote_read (s : String) (r : Reader) (t : Tree) (pos : Nat) (ready : r.lex = .ready)
    (taken : r.tree.take (.scalar (.str s)) = .ok t) :
    run r pos (quote s) = .ok { lex := .ready, tree := t } := by
  have opened : r.step '"' = .ok { lex := .text [], tree := r.tree } := by
    unfold Reader.step; rw [ready]; simp [Reader.start]
  unfold quote
  simp only [List.cons_append, Linger.Json.run, opened]
  obtain ⟨_, ran, -⟩ := escapes_read s.toList [] r.tree (pos + 1)
  rw [run_append _ _ _ _ _ ran]
  simp [Linger.Json.run, Reader.step, Reader.token, taken, Except.map]

/-- The reader reads digits within a number. -/
theorem digits_read :
    ∀ (ds : List Char),
      (∀ d ∈ ds, '0' ≤ d ∧ d ≤ '9') →
        ∀ (acc : List Char) (tree : Tree) (pos : Nat),
          run { lex := .number acc, tree } pos ds = .ok { lex := .number (ds.reverse ++ acc), tree }
  | [], _, acc, tree, pos => by simp [Linger.Json.run]
  | d :: rest, digits, acc, tree, pos => by
    simp only [Linger.Json.run, Reader.step, digits d (by simp), and_self, ↓reduceIte]
    rw [digits_read rest (fun x member => digits x (by simp [member])) (d :: acc) tree (pos + 1)]
    simp

/-- The integer an integer's text spells is the integer. -/
theorem numberValue_toString (n : Int) : numberValue (toString n).toList = n := by
  show numberValue (Int.repr n).toList = n
  rw [Int.repr_eq_ite]
  split
  · rename_i nonneg
    rw [Nat.toList_repr]
    rcases toDigits_shape n.toNat with ⟨zero, eq⟩ | ⟨first, digits, low, high, all, eq⟩
    · rw [eq]
      show (Nat.ofDigitChars 10 ['0'] 0 : Int) = n
      have : Nat.ofDigitChars 10 ['0'] 0 = 0 := by simp [Nat.ofDigitChars_cons]
      omega
    · have notMinus : first ≠ '-' := by
        rintro rfl; simp [char_le] at low
      have value := Nat.ofDigitChars_ten_toDigits (n := n.toNat)
      rw [eq] at value ⊢
      simp only [numberValue]
      split
      · rename_i same; simp at same; exact absurd same.1 notMinus
      · omega
  · rename_i negative
    rw [String.toList_append, Nat.toList_repr]
    simp only [show ("-" : String).toList = ['-'] from rfl, List.cons_append, List.nil_append,
      numberValue, Nat.ofDigitChars_ten_toDigits]
    omega

/-- **The reader reads an integer's text**, settled into the tree that takes it. -/
theorem int_read (n : Int) (r : Reader) (t : Tree) (pos : Nat) (ready : r.lex = .ready)
    (added : r.tree.add (.int n) = .ok t) :
    ∃ r', run r pos (chars (.int n)) = .ok r' ∧ Settled r' t := by
  have shape :
    ∃ first rest,
      (toString n).toList = first :: rest ∧
        (first = '-' ∨ '0' ≤ first ∧ first ≤ '9') ∧ ∀ d ∈ rest, '0' ≤ d ∧ d ≤ '9' := by
    rcases integer_text n with eq | ⟨sign, first, digits, signed, low, high, all, eq⟩
    · exact ⟨'0', [], eq, .inr (by decide), by simp⟩
    · rcases signed with rfl | rfl
      · refine ⟨first, digits, eq, .inr ⟨?_, high⟩, all⟩
        rw [char_le] at low ⊢; simp only [Char.reduceToNat] at low ⊢; omega
      · refine ⟨'-', first :: digits, eq, .inl rfl, ?_⟩
        intro d member
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · refine ⟨?_, high⟩; rw [char_le] at low ⊢; simp only [Char.reduceToNat] at low ⊢; omega
        · exact all d member
  obtain ⟨first, rest, eq, start, digits⟩ := shape
  have started : r.step first = .ok { lex := .number [first], tree := r.tree } := by
    unfold Reader.step; rw [ready]; unfold Reader.start
    rcases start with rfl | ⟨low, high⟩
    · simp
    · have lowN : 48 ≤ first.toNat := by
        have := low; rw [char_le] at this; simpa using this
      have highN : first.toNat ≤ 57 := by
        have := high; rw [char_le] at this; simpa using this
      have notSpace : ¬(first = ' ' ∨ first = '\t' ∨ first = '\n' ∨ first = '\r') := by
        intro h; rcases h with rfl | rfl | rfl | rfl <;> simp at lowN
      have nots : ∀ d : Char, d.toNat < 48 ∨ 57 < d.toNat → first ≠ d := by
        intro d far same; subst same; omega
      rw [ite_eq_right notSpace, ite_eq_right (nots '"' (by decide)),
        ite_eq_right (nots '[' (by decide)), ite_eq_right (nots '{' (by decide)),
        ite_eq_right (nots ']' (by decide)), ite_eq_right (nots '}' (by decide)),
        ite_eq_right (nots ':' (by decide)), ite_eq_right (nots ',' (by decide)),
        ite_eq_right (nots 't' (by decide)), ite_eq_right (nots 'f' (by decide)),
        ite_eq_right (nots 'n' (by decide)), ite_eq_left (.inr ⟨low, high⟩)]
  refine ⟨{ lex := .number (rest.reverse ++ [first]), tree := r.tree }, ?_, .inr ⟨_, rfl, ?_⟩⟩
  · show run r pos (toString n).toList = _
    rw [eq]
    simp only [Linger.Json.run, started]
    exact digits_read rest digits [first] r.tree (pos + 1)
  · have reversed : (rest.reverse ++ [first]).reverse = (toString n).toList := by
      rw [eq]; simp
    unfold Reader.endNumber
    rw [reversed, numberValue_toString, ite_eq_left rfl]
    simp [Reader.token, take_scalar added, Except.map]

/-- **The reader reads `null`, `true` and `false`**, into the tree that takes them. -/
theorem word_read (v : Json) (word : v = .null ∨ ∃ b, v = .bool b) (r : Reader) (t : Tree)
    (pos : Nat) (ready : r.lex = .ready) (added : r.tree.add v = .ok t) :
    run r pos (chars v) = .ok { lex := .ready, tree := t } := by
  have taken := take_scalar added
  rcases word with rfl | ⟨b, rfl⟩
  · simp [chars, Linger.Json.run, Reader.step, ready, Reader.start, Reader.token, taken, Except.map]
  · cases b <;>
      simp [chars, Linger.Json.run, Reader.step, ready, Reader.start, Reader.token, taken,
        Except.map]

/-- An array waiting for an item takes it, and then waits for a comma or its end. -/
theorem add_item (up : Tree) (acc : List Json) (next : ArrayNext)
    (fits : next = .first ∨ next = .item) (v : Json) :
    Tree.add { stack := .arr acc next :: up.stack, whole := up.whole } v =
      .ok { stack := .arr (v :: acc) .after :: up.stack, whole := up.whole } := by
  rcases fits with rfl | rfl <;> simp [Tree.add]

/-- A reader between tokens reads a bracket, a comma or a colon as its tree takes it. -/
theorem step_token {tree tree' : Tree} {c : Char} {token : Token}
    (spelled :
      c = ',' ∧ token = .comma ∨
        c = ':' ∧ token = .colon ∨ c = ']' ∧ token = .closes true ∨ c = '}' ∧ token = .closes false)
    (taken : tree.take token = .ok tree') :
    ({ lex := .ready, tree } : Reader).step c = .ok { lex := .ready, tree := tree' } := by
  rcases spelled with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [Reader.step, Reader.start, Reader.token, taken, Except.map]

/-- An object waiting for a key takes one above the keys it holds. -/
theorem key_taken (up : Tree) (acc : List (String × Json)) (next : ObjectNext) (key : String)
    (fits : next = .first ∨ next = .key) (above : ∀ a ∈ acc.head?, a.1 < key) :
    Tree.take { stack := .obj acc next :: up.stack, whole := up.whole } (.scalar (.str key)) =
      .ok { stack := .obj acc (.colon key) :: up.stack, whole := up.whole } := by
  have after : keyAfter acc key = .ok () := by
    cases acc with
    | nil => rfl
    | cons last older =>
      have lt := above last (by simp)
      simp [keyAfter, lt]
  rcases fits with rfl | rfl <;> simp [Tree.take, after, Except.map]

/-- An object waiting for a key's colon takes it, and then waits for the key's value. -/
theorem colon_step (up : Tree) (acc : List (String × Json)) (key : String) :
    ({ lex := .ready, tree := { stack := .obj acc (.colon key) :: up.stack, whole := up.whole } } :
            Reader).step
        ':' =
      .ok
        { lex := .ready,
          tree := { stack := .obj acc (.value key) :: up.stack, whole := up.whole } } :=
  step_token (.inr (.inl ⟨rfl, rfl⟩)) (by simp [Tree.take])

/-- An object waiting for a key's value takes it, and then waits for a comma or its end. -/
theorem add_member (up : Tree) (acc : List (String × Json)) (key : String) (v : Json) :
    Tree.add { stack := .obj acc (.value key) :: up.stack, whole := up.whole } v =
      .ok { stack := .obj ((key, v) :: acc) .after :: up.stack, whole := up.whole } := by
  simp [Tree.add]

mutual
/-- **The reader reads a valid value's text**, settled into the tree that takes the value. -/
theorem value_read :
    ∀ (v : Json),
      v.Valid →
        ∀ (r : Reader) (t : Tree) (pos : Nat),
          r.lex = .ready → r.tree.add v = .ok t → ∃ r', run r pos (chars v) = .ok r' ∧ Settled r' t
  | .null, _, r, t, pos, ready, added =>
    ⟨_, word_read .null (.inl rfl) r t pos ready added, .inl rfl⟩
  | .bool b, _, r, t, pos, ready, added =>
    ⟨_, word_read (.bool b) (.inr ⟨b, rfl⟩) r t pos ready added, .inl rfl⟩
  | .int n, _, r, t, pos, ready, added => int_read n r t pos ready added
  | .str s, _, r, t, pos, ready, added =>
    ⟨_, quote_read s r t pos ready (take_scalar added), .inl rfl⟩
  | .arr items, valid, r, t, pos, ready, added => by
    have wants := add_wantsValue added
    have opened : r.step '[' = .ok ⟨.ready, ⟨.arr [] .first :: r.tree.stack, r.tree.whole⟩⟩ := by
      unfold Reader.step; rw [ready]
      simp [Reader.start, Reader.token, Tree.take, wants, Except.map]
    have itemsValid : ∀ x ∈ items, x.Valid := (validItems_iff items).mp valid
    refine ⟨{ lex := .ready, tree := t }, ?_, .inl rfl⟩
    simp only [chars, itemChars_eq, List.cons_append, Linger.Json.run, opened]
    cases items with
    | nil =>
      simp only [List.map_nil, joined, List.nil_append]
      rw [Linger.Json.run,
        step_token (.inr (.inr (.inl ⟨rfl, rfl⟩))) (by simpa [Tree.take] using added)]
      rfl
    | cons x
      rest =>
      obtain ⟨r1, ran1, settled1⟩ :=
        items_read (x :: rest) itemsValid (by simp) r.tree [] .first (pos + 1) (.inl rfl)
      rw [run_append _ _ _ _ _ ran1, settled1.run (.inr (.inl rfl))]
      rw [Linger.Json.run,
        step_token (.inr (.inr (.inl ⟨rfl, rfl⟩))) (by simpa [Tree.take] using added)]
      rfl
  | .obj members, valid, r, t, pos, ready, added => by
    have wants := add_wantsValue added
    have opened : r.step '{' = .ok ⟨.ready, ⟨.obj [] .first :: r.tree.stack, r.tree.whole⟩⟩ := by
      unfold Reader.step; rw [ready]
      simp [Reader.start, Reader.token, Tree.take, wants, Except.map]
    obtain ⟨sorted, valuesValid⟩ := valid
    have membersValid := (validMembers_iff members).mp valuesValid
    refine ⟨{ lex := .ready, tree := t }, ?_, .inl rfl⟩
    rw [chars_obj_sorted sorted]
    simp only [List.cons_append, Linger.Json.run, opened]
    cases members with
    | nil =>
      simp only [List.map_nil, joined, List.nil_append]
      rw [Linger.Json.run,
        step_token (.inr (.inr (.inr ⟨rfl, rfl⟩))) (by simpa [Tree.take] using added)]
      rfl
    | cons m
      rest =>
      obtain ⟨r1, ran1, settled1⟩ :=
        members_read (m :: rest) membersValid sorted (by simp) r.tree [] .first (pos + 1) (.inl rfl)
          (by simp)
      rw [run_append _ _ _ _ _ ran1, settled1.run (.inr (.inr rfl))]
      rw [Linger.Json.run,
        step_token (.inr (.inr (.inr ⟨rfl, rfl⟩))) (by simpa [Tree.take] using added)]
      rfl
/-- **The reader reads items' texts, joined by commas**, settled into the array they fill. -/
theorem items_read :
    ∀ (items : List Json),
      (∀ x ∈ items, x.Valid) →
        items ≠ [] →
        ∀ (up : Tree) (acc : List Json) (next : ArrayNext) (pos : Nat),
          (next = .first ∨ next = .item) →
            ∃ r',
              run
                    { lex := .ready,
                      tree := { stack := .arr acc next :: up.stack, whole := up.whole } }
                    pos (joined (items.map chars)) =
                  .ok r' ∧
                Settled r'
                  { stack := .arr (items.reverse ++ acc) .after :: up.stack, whole := up.whole }
  | [], _, nonempty, _, _, _, _, _ => absurd rfl nonempty
  | [x], valid, _, up, acc, next, pos, fits => by
    obtain ⟨r1, ran1, settled1⟩ :=
      value_read x (valid x (by simp)) ⟨.ready, ⟨.arr acc next :: up.stack, up.whole⟩⟩ _ pos rfl
        (add_item up acc next fits x)
    exact ⟨r1, by simpa [joined] using ran1, by simpa using settled1⟩
  | x :: y :: more, valid, _, up, acc, next, pos, fits => by
    obtain ⟨r1, ran1, settled1⟩ :=
      value_read x (valid x (by simp)) ⟨.ready, ⟨.arr acc next :: up.stack, up.whole⟩⟩ _ pos rfl
        (add_item up acc next fits x)
    obtain ⟨r2, ran2, settled2⟩ :=
      items_read (y :: more) (fun z member => valid z (List.mem_cons_of_mem x member)) (by simp) up
        (x :: acc) .item (pos + (chars x).length + 1) (.inr rfl)
    refine ⟨r2, ?_, by simpa using settled2⟩
    simp only [List.map_cons, joined]
    rw [run_append _ _ _ _ _ ran1, settled1.run (.inl rfl)]
    rw [Linger.Json.run,
      step_token (tree' := ⟨.arr (x :: acc) .item :: up.stack, up.whole⟩) (.inl ⟨rfl, rfl⟩)
        (by simp [Tree.take])]
    simpa using ran2
/-- **The reader reads members' texts, joined by commas**, settled into the object they fill, their
keys strictly increasing and above the keys already read. -/
theorem members_read :
    ∀ (members : List (String × Json)),
      (∀ m ∈ members, m.2.Valid) →
        (members.map (·.1)).Pairwise (· < ·) →
        members ≠ [] →
        ∀ (up : Tree) (acc : List (String × Json)) (next : ObjectNext) (pos : Nat),
          (next = .first ∨ next = .key) →
            (∀ a ∈ acc.head?, ∀ m ∈ members, a.1 < m.1) →
            ∃ r',
              run
                    { lex := .ready,
                      tree := { stack := .obj acc next :: up.stack, whole := up.whole } }
                    pos (joined (members.map pairText)) =
                  .ok r' ∧
                Settled r'
                  { stack := .obj (members.reverse ++ acc) .after :: up.stack, whole := up.whole }
  | [], _, _, nonempty, _, _, _, _, _, _ => absurd rfl nonempty
  | (key, x) :: more, valid, sorted, _, up, acc, next, pos, fits, above => by
    have keyRead :=
      quote_read key ⟨.ready, ⟨.obj acc next :: up.stack, up.whole⟩⟩ _ pos rfl
        (key_taken up acc next key fits fun a inHead => above a inHead (key, x) (by simp))
    obtain ⟨r1, ran1, settled1⟩ :=
      value_read x (valid (key, x) (by simp))
        ⟨.ready, ⟨.obj acc (.value key) :: up.stack, up.whole⟩⟩ _ (pos + (quote key).length + 1) rfl
        (add_member up acc key x)
    cases more with
    | nil =>
      refine ⟨r1, ?_, by simpa using settled1⟩
      simp only [List.map_cons, List.map_nil, joined, pairText]
      rw [run_append _ _ _ _ _ keyRead, Linger.Json.run, colon_step]
      simpa using ran1
    | cons n
      rest =>
      have sortedTail : ((n :: rest).map (·.1)).Pairwise (· < ·) := (List.pairwise_cons.mp sorted).2
      obtain ⟨r2, ran2, settled2⟩ :=
        members_read (n :: rest) (fun m member => valid m (List.mem_cons_of_mem _ member))
          sortedTail (by simp) up ((key, x) :: acc) .key
          (pos + (quote key).length + 1 + (chars x).length + 1) (.inr rfl)
          (fun a inHead m member => by
            simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at inHead
            subst inHead
            exact (List.pairwise_cons.mp sorted).1 m.1 (List.mem_map.mpr ⟨m, member, rfl⟩))
      refine ⟨r2, ?_, by simpa using settled2⟩
      simp only [List.map_cons, joined, pairText, List.append_assoc, List.cons_append]
      rw [run_append _ _ _ _ _ keyRead, Linger.Json.run, colon_step]
      dsimp only
      rw [run_append _ _ _ _ _ ran1, settled1.run (.inl rfl)]
      rw [Linger.Json.run,
        step_token (tree' := ⟨.obj ((key, x) :: acc) .key :: up.stack, up.whole⟩) (.inl ⟨rfl, rfl⟩)
          (by simp [Tree.take])]
      simpa [pairText] using ran2
end

/-- **The reader reads a valid value's text as the value.** -/
theorem parse_complete {v : Json} (valid : v.Valid) : parse (render v) = .ok v := by
  obtain ⟨r', ran, settled⟩ := value_read v valid {} { whole := some v } 0 rfl rfl
  unfold parse render
  rw [String.toList_ofList, ran]
  simp only [settled.finish]
  rfl

/-- **Reading and writing are inverse on canonical texts**: the reader reads a text exactly when it
is a valid value's text, as that value. -/
theorem parse_eq_ok_iff (text : String) (v : Json) :
    parse text = .ok v ↔ v.Valid ∧ render v = text :=
  ⟨parse_sound, fun ⟨valid, rendered⟩ => rendered ▸ parse_complete valid⟩

/-- **The reader takes exactly the canonical texts.** -/
theorem parse_ok_iff_canonical (text : String) : (∃ v, parse text = .ok v) ↔ Canonical text := by
  constructor
  · rintro ⟨v, parsed⟩
    rw [← (parse_sound parsed).2]
    exact render_canonical v
  · intro canonical
    obtain ⟨v, valid, written⟩ := text_written canonical
    refine ⟨v, (parse_eq_ok_iff text v).mpr ⟨valid, ?_⟩⟩
    unfold render
    rw [written, String.ofList_toList]

/-- **The writer writes a value as the value its text holds.** -/
theorem render_sorted (v : Json) : render v = render v.sorted := by
  unfold render
  rw [chars_sorted]

/-! ## One line -/

/-- Each character `escape` writes is at U+0020 or above. -/
theorem escape_no_control (c : Char) : ∀ d ∈ escape c, 0x20 ≤ d.toNat := by
  rcases escape_spec c with ⟨⟨_, _, high⟩, same⟩ | escaped
  · rw [same]; simpa using high
  · obtain ⟨e, written, escaped⟩ : ∃ e, escape c = e ∧ Escape e c := ⟨_, rfl, escaped⟩
    rw [written]
    cases escaped with
    | quote => decide
    | backslash => decide
    | backspace => decide
    | tab => decide
    | newline => decide
    | formFeed => decide
    | carriageReturn => decide
    | control c below
      other =>
      have hex : ∀ k < 16, 0x20 ≤ (hexDigit k).toNat := by decide
      intro d member
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl
      · decide
      · decide
      · decide
      · decide
      · exact hex _ (by omega)
      · exact hex _ (Nat.mod_lt _ (by decide))

/-- Texts at U+0020 or above, joined by commas, are at U+0020 or above. -/
theorem joined_no_control :
    ∀ texts : List (List Char),
      (∀ t ∈ texts, ∀ c ∈ t, 0x20 ≤ c.toNat) → ∀ c ∈ joined texts, 0x20 ≤ c.toNat
  | [], _ => by simp [joined]
  | [t], each => by simpa [joined] using each t (by simp)
  | t :: u :: more, each => by
    intro c member
    simp only [joined, List.mem_append, List.mem_cons] at member
    rcases member with member | rfl | member
    · exact each t (by simp) c member
    · decide
    · exact
        joined_no_control (u :: more) (fun x inX => each x (List.mem_cons_of_mem t inX)) c member

/-- A string's text is at U+0020 or above. -/
theorem quote_no_control (s : String) : ∀ c ∈ quote s, 0x20 ≤ c.toNat := by
  intro c member
  simp only [quote, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_nil_iff,
    or_false] at member
  rcases member with (rfl | ⟨x, -, inEscape⟩) | rfl
  · decide
  · exact escape_no_control x c inEscape
  · decide

mutual
/-- **No text the writer writes holds a character below U+0020**, a line feed among them: a text is
one line. -/
theorem chars_no_control : ∀ v : Json, ∀ c ∈ chars v, 0x20 ≤ c.toNat
  | .null => by decide
  | .bool true => by decide
  | .bool false => by decide
  | .int n => by
    intro c member
    rcases integer_text n with eq | ⟨sign, first, digits, signed, low, high, all, eq⟩
    · simp only [chars, eq, List.mem_singleton] at member; subst member; decide
    · simp only [chars, eq, List.mem_append, List.mem_cons] at member
      rw [char_le] at low
      simp only [Char.reduceToNat] at low
      rcases member with inSign | rfl | inDigits
      · rcases signed with rfl | rfl
        · simp at inSign
        · simp only [List.mem_singleton] at inSign; subst inSign; decide
      · omega
      · have := (all c inDigits).1; rw [char_le] at this; simp only [Char.reduceToNat] at this;
        omega
  | .str s => quote_no_control s
  | .arr items => by
    intro c member
    simp only [chars, List.cons_append, List.mem_cons, List.mem_append, List.mem_nil_iff,
      or_false] at member
    rcases member with rfl | member | rfl
    · decide
    · exact joined_no_control _ (items_no_control items) c member
    · decide
  | .obj members => by
    intro c member
    simp only [chars, List.cons_append, List.mem_cons, List.mem_append, List.mem_nil_iff,
      or_false] at member
    rcases member with rfl | member | rfl
    · decide
    · refine joined_no_control _ ?_ c member
      intro t inTexts d inT
      simp only [List.mem_map] at inTexts
      obtain ⟨m, inSorted, rfl⟩ := inTexts
      simp only [memberText, List.mem_append, List.mem_cons] at inT
      rcases inT with inKey | rfl | inValue
      · exact quote_no_control m.1 d inKey
      · decide
      · exact members_no_control members m (mem_sortMembers inSorted) d inValue
    · decide
/-- Each item's text is at U+0020 or above. -/
theorem items_no_control : ∀ items : List Json, ∀ t ∈ itemChars items, ∀ c ∈ t, 0x20 ≤ c.toNat
  | [], t, member => by simp [itemChars] at member
  | item :: rest, t, member => by
    simp only [itemChars, List.mem_cons] at member
    rcases member with rfl | member
    · exact chars_no_control item
    · exact items_no_control rest t member
/-- Each member's value's text is at U+0020 or above. -/
theorem members_no_control :
    ∀ members : List (String × Json), ∀ m ∈ memberChars members, ∀ c ∈ m.2, 0x20 ≤ c.toNat
  | [], m, member => by simp [memberChars] at member
  | (key, value) :: rest, m, member => by
    simp only [memberChars, List.mem_cons] at member
    rcases member with rfl | member
    · exact chars_no_control value
    · exact members_no_control rest m member
end

/-- **A text the writer writes is one line**, and holds no character below U+0020. -/
theorem render_no_control (v : Json) : ∀ c ∈ (render v).toList, 0x20 ≤ c.toNat := by
  unfold render
  rw [String.toList_ofList]
  exact chars_no_control v

/-! ## Facts the kills use -/

/-- A string's text holds a quote. -/
theorem stringText_quote {text : List Char} {s : String} (h : StringText text s) : '"' ∈ text := by
  obtain ⟨body, rfl, -⟩ := h
  simp

/-- An integer's text holds no space and no quote. -/
theorem integerText_plain {text : List Char} (h : IntegerText text) : ' ' ∉ text := by
  rcases h with rfl | ⟨sign, first, digits, signed, low, high, all, rfl⟩
  · decide
  · intro member
    simp only [List.mem_append, List.mem_cons] at member
    rw [char_le] at low
    simp only [Char.reduceToNat] at low
    rcases member with inSign | same | inDigits
    · rcases signed with rfl | rfl <;> simp at inSign
    · subst same; simp at low
    · have := (all ' ' inDigits).1; rw [char_le] at this; simp at this

mutual
/-- **A canonical text without a quote holds no space**: its only spaces are within strings. -/
theorem text_no_space : ∀ {text : List Char}, Text text → '"' ∉ text → ' ' ∉ text
  | _, .nullWord, _ => by decide
  | _, .trueWord, _ => by decide
  | _, .falseWord, _ => by decide
  | _, .integer h, _ => integerText_plain h
  | _, .string h, noQuote => absurd (stringText_quote h) noQuote
  | _, .emptyArray, _ => by decide
  | _, .array first more, noQuote => by
    intro space
    simp only [List.cons_append, List.mem_cons, List.mem_append] at space noQuote
    rcases space with same | (inFirst | inMore) | same | nil
    · exact absurd same (by decide)
    · exact text_no_space first (fun q => noQuote (.inr (.inl (.inl q)))) inFirst
    · exact moreValues_no_space more (fun q => noQuote (.inr (.inl (.inr q)))) inMore
    · exact absurd same (by decide)
    · simp at nil
  | _, .emptyTable, _ => by decide
  | _, .table key _ _ _, noQuote => by exact absurd (by simp [stringText_quote key]) noQuote
/-- A canonical `*( "," value )` without a quote holds no space. -/
theorem moreValues_no_space : ∀ {text : List Char}, MoreValues text → '"' ∉ text → ' ' ∉ text
  | _, .nil, _ => by simp
  | _, .cons value more, noQuote => by
    intro space
    simp only [List.cons_append, List.mem_cons, List.mem_append] at space noQuote
    rcases space with same | inValue | inMore
    · exact absurd same (by decide)
    · exact text_no_space value (fun q => noQuote (.inr (.inl q))) inValue
    · exact moreValues_no_space more (fun q => noQuote (.inr (.inr q))) inMore
end

/-- Every text the writer writes holds a character. -/
theorem chars_ne_nil (v : Json) : chars v ≠ [] := by
  cases v with
  | null => decide
  | bool b => cases b <;> decide
  | int n =>
    show (toString n).toList ≠ []
    rcases integer_text n with eq | ⟨sign, first, digits, -, -, -, -, eq⟩
    · rw [eq]; simp
    · rw [eq]; simp
  | str s => simp [chars, quote]
  | arr items => simp [chars]
  | obj members => simp [chars]

/-- A text the reader reads, it reads through. -/
theorem parse_run {text : String} {v : Json} (parsed : parse text = .ok v) :
    ∃ r, run {} 0 text.toList = .ok r := by
  unfold parse at parsed
  split at parsed
  · cases parsed
  · rename_i r ran
    exact ⟨r, ran⟩

end Linger.Json
