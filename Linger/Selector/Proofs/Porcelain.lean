module

public import Linger.Selector.CoreCode.Picker
public import Linger.Display.CoreCode.Listing
public import Linger.Target.CoreCode.Remote
import all Linger.Selector.CoreCode.Picker
import all Linger.Display.CoreCode.Listing
import all Terminal.Proofs.Render

/-! # The chooser reads what `ls --porcelain` prints

A listing's records (`Listing.records`), printed as `ls --porcelain` prints them
(`Listing.porcelain`), read back as the chooser reads a listing (`parseSnapshot`), give each record
back under its name, the targets in their order, when each record begins with its name, a valid
target no other record has, and holds no other `name` field. -/

public section

namespace Linger.Selector.Picker

open Linger.Display.Listing

/-- A record's key: the value of its `name` field. -/
@[expose]
def keyOf (record : List (String × String)) : String := (record.lookup "name").getD ""

/-- A record's lines of a listing: one for each field, then a blank one. -/
def recordLines (record : List (String × String)) : List (List Char) := record.map fieldLine ++ [[]]

/-- A record's fields as the chooser reads its lines: each field's key and value, then the blank
line's one empty field. -/
def recordFields (record : List (String × String)) : List (List String) :=
  record.map (fun field => [field.1, field.2]) ++ [[""]]

/-- Whether no key or value of a record holds a tab or a newline. -/
def Framed (record : List (String × String)) : Prop :=
  ∀ field ∈ record,
    '\t' ∉ field.1.toList ∧ '\n' ∉ field.1.toList ∧ '\t' ∉ field.2.toList ∧ '\n' ∉ field.2.toList

/-- Clean text holds no tab and no newline. -/
theorem clean_frames (text : String) : ∀ c ∈ (clean text).toList, c ≠ '\t' ∧ c ≠ '\n' := by
  intro c member
  simp only [clean, String.toList_map, List.mem_map] at member
  obtain ⟨raw, -, rfl⟩ := member
  have safe := (Terminal.Render.textChar_safe raw).1
  constructor <;> intro same <;> rw [same] at safe <;> simp at safe

/-- Lines each ended by `c`, and holding none, split at `c` into themselves and an empty end. -/
theorem lines_split (c : Char) :
    ∀ (lines : List (List Char)),
      (∀ line ∈ lines, c ∉ line) → (lines.flatMap (· ++ [c])).splitOn c = lines ++ [[]]
  | [], _ => by simp
  | line :: rest, clear => by
    simp only [List.flatMap_cons, List.append_assoc, List.cons_append, List.nil_append]
    rw [List.splitOn_append_cons_self_of_not_mem (clear line (by simp)),
      lines_split c rest fun other member => clear other (by simp [member])]

/-- A listing's records are framed. -/
theorem records_framed (rows : List (List (String × String))) :
    ∀ record ∈ records rows, Framed record := by
  intro record member field inRecord
  simp only [records, List.mem_map] at member
  obtain ⟨row, -, rfl⟩ := member
  simp only [List.mem_map] at inRecord
  obtain ⟨⟨key, value⟩, -, rfl⟩ := inRecord
  exact
    ⟨fun inKey => (clean_frames key _ inKey).1 rfl, fun inKey => (clean_frames key _ inKey).2 rfl,
      fun inValue => (clean_frames value _ inValue).1 rfl, fun inValue =>
      (clean_frames value _ inValue).2 rfl⟩

/-- A framed record's lines hold no newline. -/
theorem recordLines_clear {record : List (String × String)} (framed : Framed record) :
    ∀ line ∈ recordLines record, '\n' ∉ line := by
  intro line member
  simp only [recordLines, List.mem_append, List.mem_map, List.mem_singleton] at member
  rcases member with ⟨field, inRecord, rfl⟩ | rfl
  · obtain ⟨-, noKey, -, noValue⟩ := framed field inRecord
    simp only [fieldLine, List.mem_append, List.mem_cons, not_or]
    exact ⟨noKey, by decide, noValue⟩
  · simp

/-- A framed field's line read as its fields: its key and its value. -/
theorem lineFields_fieldLine {field : String × String} (noKey : '\t' ∉ field.1.toList)
    (noValue : '\t' ∉ field.2.toList) :
    lineFields (String.ofList (fieldLine field)) = [field.1, field.2] := by
  simp only [lineFields, fieldLine, String.toList_ofList]
  rw [List.splitOn_append_cons_self_of_not_mem noKey, List.splitOn_eq_singleton noValue]
  simp

/-- An empty line read as its fields: one, empty. -/
theorem lineFields_blank : lineFields "" = [""] := by simp [lineFields]

/-- **What `ls --porcelain` prints splits into its records' lines**, and an empty end. -/
theorem listingLines_porcelain (rows : List (List (String × String))) :
    listingLines (porcelain rows) =
      (((records rows).flatMap recordLines) ++ [[]]).map String.ofList := by
  simp only [listingLines, porcelain, String.toList_ofList]
  rw [lines_split '\n']
  · rfl
  · intro line member
    simp only [List.mem_flatMap] at member
    obtain ⟨record, inRecords, inLines⟩ := member
    exact recordLines_clear (records_framed rows record inRecords) line inLines

/-- Framed records' lines read as the chooser reads lines: their fields. -/
theorem lines_fields :
    ∀ (rs : List (List (String × String))),
      (∀ record ∈ rs, Framed record) →
        ((rs.flatMap recordLines).map String.ofList).map lineFields = rs.flatMap recordFields
  | [], _ => rfl
  | record :: rest, framed => by
    simp only [List.flatMap_cons, List.map_append]
    rw [lines_fields rest fun other member => framed other (by simp [member])]
    congr 1
    simp only [recordLines, recordFields, List.map_append, List.map_map, List.map_cons,
      List.map_nil]
    congr 1
    · apply List.map_congr_left
      intro field inRecord
      obtain ⟨noKey, -, noValue, -⟩ := framed record (by simp) field inRecord
      exact lineFields_fieldLine noKey noValue
    · simp [lineFields_blank]

/-- Lines the chooser takes for no target leave its parse of what follows as it is. -/
private theorem parseRows_skip (seen : List String) :
    ∀ (skipped more : List String),
      (∀ line ∈ skipped, parseRow (lineFields line) = .ok none) →
        parseRows seen (skipped ++ more) = parseRows seen more
  | [], _, _ => rfl
  | line :: rest, more, skips => by
    simp only [List.cons_append, parseRows, skips line (by simp)]
    exact parseRows_skip seen rest more fun other member => skips other (by simp [member])

/-- Every field after a record's name, and the blank line after its fields, names no target. -/
private theorem parseRow_rest {key : String} {rest : List (String × String)}
    (framed : Framed (("name", key) :: rest)) (unnamed : ∀ field ∈ rest, field.1 ≠ "name") :
    ∀ line ∈ (rest.map fieldLine ++ [[]]).map String.ofList,
      parseRow (lineFields line) = .ok none := by
  intro line member
  simp only [List.map_append, List.map_map, List.mem_append, List.mem_map, List.map_cons,
    List.map_nil, List.mem_singleton] at member
  rcases member with ⟨field, inRest, rfl⟩ | rfl
  · obtain ⟨noKey, -, noValue, -⟩ := framed field (by simp [inRest])
    simp only [Function.comp, lineFields_fieldLine noKey noValue, parseRow]
    simp [unnamed field inRest]
  · simp [lineFields_blank, parseRow]

/-- **The chooser reads a listing's targets**, in order, when each record begins with its name, a
valid target no other record has, and holds no other `name` field. -/
private theorem parseRows_records (seen : List String) :
    ∀ (rs : List (List (String × String))),
      (∀ record ∈ rs, Framed record) →
        (∀ record ∈ rs,
          ∃ rest,
            record = ("name", keyOf record) :: rest ∧
              Linger.Target.Remote.targetValid (keyOf record) = true ∧
              ∀ field ∈ rest, field.1 ≠ "name") →
        (rs.map keyOf).Nodup →
        (∀ record ∈ rs, keyOf record ∉ seen) →
        parseRows seen ((rs.flatMap recordLines ++ [[]]).map String.ofList) = .ok (rs.map keyOf)
  | [], _, _, _, _ => by simp [parseRows, lineFields_blank, parseRow]
  | record :: others, framed, named, distinct, fresh => by
    obtain ⟨rest, shape, valid, unnamed⟩ := named record (by simp)
    have recordFramed := framed record (by simp)
    rw [shape] at recordFramed
    obtain ⟨noKey, -, noValue, -⟩ := recordFramed ("name", keyOf record) (by simp)
    simp only [List.nodup_cons, List.map_cons] at distinct
    obtain ⟨other, distinct⟩ := distinct
    have later :=
      parseRows_records (keyOf record :: seen) others (fun r m => framed r (by simp [m]))
        (fun r m => named r (by simp [m])) distinct fun r m => by
        simp only [List.mem_cons, not_or]
        refine ⟨fun same => other ?_, fresh r (by simp [m])⟩
        exact List.mem_map.mpr ⟨r, m, same⟩
    have skipped :=
      parseRows_skip (keyOf record :: seen) _
        ((others.flatMap recordLines ++ [[]]).map String.ofList)
        (parseRow_rest recordFramed unnamed)
    rw [shape]
    simp only [List.flatMap_cons, recordLines, List.map_cons, List.cons_append, List.map_append,
      List.append_assoc] at skipped ⊢
    simp only [parseRows, lineFields_fieldLine noKey noValue, parseRow, List.head?_cons,
      bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, valid]
    have unseen : seen.contains (keyOf record) = false := by simpa using fresh record (by simp)
    simp only [unseen, Bool.false_eq_true, ↓reduceIte]
    simp only [List.map_append, List.map_cons, List.map_nil, List.nil_append] at later skipped ⊢
    rw [skipped, later]
    simp [Except.map, keyOf]

/-- **The chooser reads each record back under its name**: of framed records, each beginning
with its name and holding no other `name` field, no two sharing a name, the chooser's row of a
record's name, from their fields, is the record. -/
theorem row_records (rs : List (List (String × String)))
    (named :
      ∀ record ∈ rs,
        ∃ rest, record = ("name", keyOf record) :: rest ∧ ∀ field ∈ rest, field.1 ≠ "name")
    (distinct : (rs.map keyOf).Nodup) (candidates : List String) :
    ∀ record ∈ rs,
      ({ candidates, records := rs.flatMap recordFields ++ [[""]] } : Snapshot).row (keyOf record) =
        record := by
  intro record member
  obtain ⟨before, after, split⟩ := List.append_of_mem member
  obtain ⟨rest, shape, unnamed⟩ := named record member
  have apart : ∀ other ∈ before, keyOf other ≠ keyOf record := by
    rw [split, List.map_append, List.nodup_append] at distinct
    intro other inBefore same
    exact
      distinct.2.2 _ (List.mem_map.mpr ⟨other, inBefore, rfl⟩) _
        (List.mem_map.mpr ⟨record, by simp, rfl⟩) same
  generalize hk : keyOf record = key at shape apart
  have notBefore : ∀ fields ∈ before.flatMap recordFields, (fields != ["name", key]) = true := by
    intro fields inBefore
    simp only [List.mem_flatMap, recordFields, List.mem_append, List.mem_map,
      List.mem_singleton] at inBefore
    obtain ⟨other, inOthers, ⟨field, inOther, rfl⟩ | rfl⟩ := inBefore
    · simp only [bne_iff_ne, ne_eq, List.cons.injEq, and_true, not_and]
      intro isName isKey
      obtain ⟨otherRest, otherShape, otherUnnamed⟩ :=
        named other
          (by
            rw [split]; simp [inOthers])
      rw [otherShape] at inOther
      rcases List.mem_cons.mp inOther with same | inOtherRest
      · subst same
        exact apart other inOthers isKey
      · exact otherUnnamed field inOtherRest isName
    · simp
  have restKept :
    ∀ fields ∈ rest.map (fun field => [field.1, field.2]),
      (fields != [""] && fields.head? != some "name") = true := by
    intro fields inRest
    simp only [List.mem_map] at inRest
    obtain ⟨field, inRest, rfl⟩ := inRest
    simp [unnamed field inRest]
  rw [split]
  unfold Snapshot.row
  simp only [List.flatMap_append, List.flatMap_cons, List.append_assoc]
  rw [List.dropWhile_append_of_pos notBefore]
  conv =>
    rhs; rw [shape]
  simp only [shape, recordFields, List.map_cons, List.cons_append, List.dropWhile_cons,
    bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, List.tail_cons, List.append_assoc]
  rw [List.takeWhile_append_of_pos restKept]
  have paired : fieldPair ∘ (fun field : String × String => [field.1, field.2]) = some :=
    funext fun _ => rfl
  simp [List.filterMap_map, paired]

/-- **What `ls --porcelain` prints, the chooser reads back**: each record of a listing, under its
name, and the names in order, when each record begins with its name, a valid target no other has,
and holds no other `name` field. -/
theorem porcelain_read (rows : List (List (String × String)))
    (named :
      ∀ record ∈ records rows,
        ∃ rest,
          record = ("name", keyOf record) :: rest ∧
            Linger.Target.Remote.targetValid (keyOf record) = true ∧
            ∀ field ∈ rest, field.1 ≠ "name")
    (distinct : ((records rows).map keyOf).Nodup) :
    ∃ snapshot,
      parseSnapshot (porcelain rows) = .ok snapshot ∧
        snapshot.candidates = (records rows).map keyOf ∧
        ∀ record ∈ records rows, snapshot.row (keyOf record) = record := by
  have framed := records_framed rows
  have targets : parseListing (porcelain rows) = .ok ((records rows).map keyOf) := by
    unfold parseListing
    rw [listingLines_porcelain]
    exact parseRows_records [] _ framed named distinct (by simp)
  let read : Snapshot :=
    { candidates := (records rows).map keyOf
      records := (records rows).flatMap recordFields ++ [[""]] }
  refine ⟨read, ?_, rfl, ?_⟩
  · unfold parseSnapshot
    rw [targets, listingLines_porcelain, List.map_append, List.map_append, lines_fields _ framed]
    simp [Except.map, lineFields_blank]
    rfl
  · exact
      row_records _
        (fun record member => by
          obtain ⟨rest, shape, -, unnamed⟩ := named record member
          exact ⟨rest, shape, unnamed⟩)
        distinct _

end Linger.Selector.Picker
