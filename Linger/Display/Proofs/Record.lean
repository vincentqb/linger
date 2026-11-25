module

public import Linger.Display.CoreSpec
public import ExactJSON.Lawful
public import ExactJSON.Canonical
public import Linger.Display.CoreCode.Listing
import all Linger.Display.CoreCode.Listing
import all Terminal.Proofs.Render.Ends

/-! # A session's record as JSON

A field's codec reads back what it writes, as a valid value, so a record, ExactJSON's dictionary of
fields, does too (`ExactJSON.LawfulValue`); and a record's fields as a row holds them hold each
field's text under its key, the one field there. -/

public section

namespace Linger.Display.Listing

open ExactJSON (LawfulValue toValue fromValue?)

/-- **A field's codec is lawful**: it reads back each field it writes, as a valid value. -/
instance : LawfulValue Field where
  fromValue_toValue f := by cases f <;> simp [toValue, fromValue?]
  toValue_valid f := by cases f <;> rfl

/-- A list of pairs whose keys are distinct looks a key up as the pair that holds it. -/
theorem lookup_of_mem {β : Type} :
    ∀ (l : List (String × β)),
      l.Pairwise (fun a b => a.1 ≠ b.1) →
        ∀ (key : String) (value : β), (key, value) ∈ l → l.lookup key = some value
  | [], _, _, _, member => by simp at member
  | (k, v) :: rest, distinct, key, value, member => by
    rcases List.mem_cons.mp member with same | inRest
    · cases same
      simp [List.lookup]
    · have differ : k ≠ key := fun same =>
        (List.pairwise_cons.mp distinct).1 (key, value) inRest (by simp [same])
      have : (key == k) = false := beq_eq_false_iff_ne.mpr fun same => differ same.symm
      simp only [List.lookup, this]
      exact lookup_of_mem rest (List.pairwise_cons.mp distinct).2 key value inRest

/-- A list of pairs whose keys are distinct looks a key up as none when no pair holds it. -/
theorem lookup_of_not_mem {β : Type} :
    ∀ (l : List (String × β)) (key : String), (∀ value, (key, value) ∉ l) → l.lookup key = none
  | [], _, _ => rfl
  | (k, v) :: rest, key, absent => by
    have differ : k ≠ key := fun same => absent v (by simp [same])
    have : (key == k) = false := beq_eq_false_iff_ne.mpr fun same => differ same.symm
    simp only [List.lookup, this]
    exact
      lookup_of_not_mem rest key fun value member => absent value (List.mem_cons_of_mem _ member)

/-- A record's fields, by increasing key, look a key up as the record holds it. -/
theorem lookup_toList (record : Record) (key : String) :
    record.toList.lookup key = record[key]? := by
  have distinct : record.toList.Pairwise (fun a b => a.1 ≠ b.1) :=
    Std.ExtTreeMap.distinct_keys_toList.imp fun differ same => differ (by simp [same])
  cases held : record[key]? with
  | some value =>
    exact
      lookup_of_mem _ distinct key value (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr held)
  | none =>
    exact
      lookup_of_not_mem _ key fun value member => by
        rw [Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some] at member
        rw [held] at member
        cases member

/-- **A record's fields as a row holds them** look a key up as the text of the field the record
holds there. -/
theorem lookup_fields (record : Record) (key : String) :
    record.fields.lookup key = record[key]?.map Field.render := by
  unfold Record.fields
  rw [← lookup_toList]
  generalize record.toList = l
  induction l with
  | nil => rfl
  | cons first rest ih =>
    obtain ⟨k, f⟩ := first
    simp only [List.map_cons, List.lookup]
    split <;> simp_all

/-- A record whose key is a valid name holds its name, as text, under `name`. -/
theorem name_field (record : Record) (named : record.key ≠ "") :
    record.fields.lookup "name" = some record.key := by
  rw [lookup_fields]
  unfold Record.key Record.text? at *
  split at named
  · rename_i name held
    simp [held, Field.render]
  · exact absurd rfl named

/-- The fields after the first a row's record reads leave every key it holds as it holds it. -/
theorem ofRow_keeps (rest : List (String × String)) (record : Record) (key : String) (field : Field)
    (held : record[key]? = some field) : (rest.foldl Record.add record)[key]? = some field := by
  induction rest generalizing record with
  | nil => exact held
  | cons first rest ih =>
    simp only [List.foldl_cons]
    apply ih
    unfold Record.add
    split
    · rw [Std.ExtTreeMap.getElem?_insertIfNew]
      have present : key ∈ record := Std.ExtTreeMap.mem_iff_isSome_getElem?.mpr (by simp [held])
      split
      · rename_i fresh
        exact absurd (Std.LawfulEqCmp.eq_of_compare fresh.1 ▸ present) fresh.2
      · exact held
    · exact held

/-- **A row named first keys its record by that name.** -/
theorem ofRow_key (name : String) (rest : List (String × String)) :
    (Record.ofRow (("name", name) :: rest)).key = name := by
  have first : Field.of "name" name = some (.text name) := by simp [Field.of, flagKeys, countKeys]
  unfold Record.ofRow Record.key Record.text?
  simp only [List.foldl_cons]
  rw [ofRow_keeps rest _ "name" (.text name)
      (by
        simp only [Record.add, first, Std.ExtTreeMap.getElem?_insertIfNew, Std.compare_self,
          Std.ExtTreeMap.not_mem_empty, not_false_eq_true, and_self, ↓reduceIte])]
  rfl

/-- A row's first field read under a key is the field its record holds there. -/
theorem ofRow_head (key value : String) (field : Field) (rest : List (String × String))
    (read : Field.of key value = some field) :
    (Record.ofRow ((key, value) :: rest))[key]? = some field := by
  unfold Record.ofRow
  simp only [List.foldl_cons]
  exact
    ofRow_keeps rest _ key field
      (by
        simp only [Record.add, read, Std.ExtTreeMap.getElem?_insertIfNew, Std.compare_self,
          Std.ExtTreeMap.not_mem_empty, not_false_eq_true, and_self, ↓reduceIte])

/-- What a record a row's fields add to holds: what it held, or a field the row reads under its
key. -/
theorem foldl_add_from (row : List (String × String)) (record : Record) (key : String)
    (field : Field) (held : (row.foldl Record.add record)[key]? = some field) :
    record[key]? = some field ∨ ∃ value, (key, value) ∈ row ∧ Field.of key value = some field := by
  induction row generalizing record with
  | nil => exact .inl held
  | cons first rest
    ih =>
    rcases ih (Record.add record first) held with before | ⟨value, member, read⟩
    · unfold Record.add at before
      split at before
      · rename_i read readIs
        rw [Std.ExtTreeMap.getElem?_insertIfNew] at before
        split at before
        · rename_i fresh
          have same : first.1 = key := Std.LawfulEqCmp.eq_of_compare fresh.1
          cases before
          exact .inr ⟨first.2, by simp [← same], same ▸ readIs⟩
        · exact .inl before
      · exact .inl before
    · exact .inr ⟨value, List.mem_cons_of_mem _ member, read⟩

/-- **A row's record holds only the row's fields**: each key with the field `Field.of` reads of a
value the row holds under it. -/
theorem ofRow_from (row : List (String × String)) (key : String) (field : Field)
    (held : (Record.ofRow row)[key]? = some field) :
    ∃ value, (key, value) ∈ row ∧ Field.of key value = some field := by
  rcases foldl_add_from row ∅ key field held with empty | found
  · simp at empty
  · exact found

/-- Clean text is printable. -/
theorem clean_printable (text : String) : ∀ c ∈ (clean text).toList, Printable c := by
  intro c member
  simp only [clean, String.toList_map, List.mem_map] at member
  obtain ⟨d, -, rfl⟩ := member
  exact Terminal.Render.textChar_safe d

/-- A field read from clean text renders as printable text. -/
theorem render_printable (key value : String) (field : Field)
    (clean : ∀ c ∈ value.toList, Printable c) (read : Field.of key value = some field) :
    ∀ c ∈ field.render.toList, Printable c := by
  unfold Field.of at read
  split at read
  · split at read
    · cases read
      intro c member
      have : c ∈ ['t', 'r', 'u', 'e'] := by simpa [Field.render] using member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      rcases this with rfl | rfl | rfl | rfl <;> simp only [Printable] <;> decide
    · split at read
      · cases read
        intro c member
        have : c ∈ ['f', 'a', 'l', 's', 'e'] := by simpa [Field.render] using member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at this
        rcases this with rfl | rfl | rfl | rfl | rfl <;> simp only [Printable] <;> decide
      · cases read
  · split at read
    · simp only [Option.map_eq_some_iff] at read
      obtain ⟨n, -, rfl⟩ := read
      intro c member
      simp only [Field.render, toString, Nat.toList_repr] at member
      have digit := Nat.isDigit_of_mem_toDigits (by decide) (by decide) member
      simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at digit
      simp only [Printable]
      have low : (48 : Nat) ≤ c.toNat := by
        simpa [Char.le_def, UInt32.le_iff_toNat_le] using digit.1
      have high : c.toNat ≤ 57 := by simpa [Char.le_def, UInt32.le_iff_toNat_le] using digit.2
      omega
    · cases read
      exact clean

/-- A printable character ExactJSON escapes is a line or paragraph separator. -/
theorem mustEscape_printable {c : Char} (printable : Printable c)
    (escaped : ExactJSON.mustEscape c = true) : c = '\u2028' ∨ c = '\u2029' := by
  simp only [ExactJSON.mustEscape, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true,
    beq_iff_eq] at escaped
  simp only [Printable] at printable
  rcases escaped with ((low | control) | separator) | separator
  · omega
  · omega
  · left; exact Char.ext (UInt32.toNat_inj.mp (by simpa using separator))
  · right; exact Char.ext (UInt32.toNat_inj.mp (by simpa using separator))

/-- **Every key and field of a listing's records is clean text**: printable, so of the characters
ExactJSON escapes (`ExactJSON.mustEscape`) it holds only the line and paragraph separators. -/
theorem records_clean (rows : List (List (String × String))) (record : Record) (key : String)
    (field : Field) (listed : record ∈ records rows) (held : record[key]? = some field) :
    ∀ c ∈ key.toList ++ field.render.toList,
      Printable c ∧ (ExactJSON.mustEscape c = true → c = '\u2028' ∨ c = '\u2029') := by
  simp only [records, List.mem_map] at listed
  obtain ⟨row, -, rfl⟩ := listed
  obtain ⟨value, member, read⟩ := ofRow_from _ key field held
  simp only [List.mem_map, Prod.mk.injEq] at member
  obtain ⟨⟨k, v⟩, -, rfl, rfl⟩ := member
  intro c member
  have printable : Printable c := by
    rcases List.mem_append.mp member with inKey | inField
    · exact clean_printable k c inKey
    · exact render_printable _ _ field (clean_printable v) read c inField
  exact ⟨printable, mustEscape_printable printable⟩

end Linger.Display.Listing
