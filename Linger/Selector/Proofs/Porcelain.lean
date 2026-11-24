module

public import Linger.Selector.CoreCode.Picker
public import Linger.Display.CoreCode.Listing
public import Linger.Target.CoreCode.Remote
import all Linger.Selector.CoreCode.Picker
import all Linger.Display.CoreCode.Listing
import all Linger.Target.CoreCode.Remote
public import Linger.Os.CoreCode.Json
import all Linger.Os.CoreCode.Json
import Linger.Os.Proofs.Json

/-! # The chooser reads what `ls --porcelain` prints

A listing's records (`Listing.records`), printed as `ls --porcelain` prints them, one line of
canonical JSON each (`Listing.porcelain`), read back as the chooser reads a listing
(`parseSnapshot`), give each record back under its name, the targets in their order, when each
record's name is a valid target no other record has. -/

public section

namespace Linger.Selector.Picker

open Linger.Display.Listing

/-- A record's key: the value of its `name` field. -/
@[expose]
def keyOf (record : List (String × String)) : String := (record.lookup "name").getD ""

/-- A listing's records list their keys strictly increasing, as canonical objects do. -/
theorem records_sorted (rows : List (List (String × String))) :
    ∀ record ∈ records rows, (record.map (·.1)).Pairwise (· < ·) := by
  intro record member
  simp only [records, List.mem_map] at member
  obtain ⟨row, -, rfl⟩ := member
  exact Json.sortMembers_pairwise _

/-- A record whose keys strictly increase is a valid object. -/
theorem recordJson_valid (record : List (String × String))
    (sorted : (record.map (·.1)).Pairwise (· < ·)) : (recordJson record).Valid := by
  refine ⟨by simpa [recordJson, List.map_map, Function.comp_def] using sorted, ?_⟩
  rw [Json.validMembers_iff]
  intro m member
  simp only [List.mem_map] at member
  obtain ⟨field, -, rfl⟩ := member
  trivial

/-- A record's strings, read as the chooser reads a listing's fields. -/
theorem mapM_fieldText (record : List (String × String)) :
    (record.map fun (key, value) => (key, Json.str value)).mapM fieldText = .ok record := by
  induction record with
  | nil => rfl
  | cons field rest ih =>
    simp only [List.map_cons, List.mapM_cons, fieldText, ih]
    rfl

/-- **A canonical record's line reads as the record.** -/
theorem lineRecord_render (record : List (String × String))
    (sorted : (record.map (·.1)).Pairwise (· < ·)) :
    lineRecord (Json.render (recordJson record)) = .ok record := by
  unfold lineRecord
  rw [Json.parse_complete (recordJson_valid record sorted)]
  exact mapM_fieldText record

/-- Lines each ended by `c`, and holding none, split at `c` into themselves and an empty end. -/
theorem lines_split (c : Char) :
    ∀ (lines : List (List Char)),
      (∀ line ∈ lines, c ∉ line) → (lines.flatMap (· ++ [c])).splitOn c = lines ++ [[]]
  | [], _ => by simp
  | line :: rest, clear => by
    simp only [List.flatMap_cons, List.append_assoc, List.cons_append, List.nil_append]
    rw [List.splitOn_append_cons_self_of_not_mem (clear line (by simp)),
      lines_split c rest fun other member => clear other (by simp [member])]

/-- A value's text holds no line feed. -/
theorem render_no_newline (v : Json) : '\n' ∉ (Json.render v).toList := fun member => by
  have := Json.render_no_control v '\n' member
  simp at this

/-- A record's line is not empty: it is an object's, which opens with `{`. -/
theorem render_record_nonempty (record : List (String × String)) :
    Json.render (recordJson record) ≠ "" := by
  intro empty
  have : (Json.render (recordJson record)).toList = [] := by
    rw [empty]; rfl
  simp [Json.render, recordJson, Json.chars] at this

/-- **What `ls --porcelain` prints splits into its records' lines.** -/
theorem listingLines_porcelain (rows : List (List (String × String))) :
    listingLines (porcelain rows) =
      (records rows).map fun record => Json.render (recordJson record) := by
  simp only [listingLines, porcelain, String.toList_join, List.flatMap_map, String.toList_push]
  have split :=
    lines_split '\n' ((records rows).map fun record => (Json.render (recordJson record)).toList)
      (fun line member => by
        simp only [List.mem_map] at member
        obtain ⟨record, -, rfl⟩ := member
        exact render_no_newline _)
  rw [List.flatMap_map] at split
  rw [split, List.map_append, List.filter_append, List.map_map]
  simp only [List.map_cons, List.map_nil, Function.comp_def, String.ofList_toList]
  rw [List.filter_eq_self.mpr fun line member => by
      simp only [List.mem_map] at member
      obtain ⟨record, -, rfl⟩ := member
      simpa using render_record_nonempty record]
  simp

/-- A listing's lines read as its records. -/
theorem mapM_lineRecord_porcelain (rows : List (List (String × String))) :
    (listingLines (porcelain rows)).mapM lineRecord = .ok (records rows) := by
  rw [listingLines_porcelain]
  have sorted := records_sorted rows
  generalize records rows = rs at sorted ⊢
  induction rs with
  | nil => rfl
  | cons record rest
    ih =>
    simp only [List.map_cons, List.mapM_cons, lineRecord_render record (sorted record (by simp)),
      ih fun r member => sorted r (List.mem_cons_of_mem _ member)]
    rfl

/-- No name is not a valid target. -/
theorem targetValid_empty : Linger.Target.Remote.targetValid "" = false := by decide

/-- A record whose key is a valid target names it. -/
theorem lookup_name {record : List (String × String)}
    (valid : Linger.Target.Remote.targetValid (keyOf record) = true) :
    record.lookup "name" = some (keyOf record) := by
  unfold keyOf at valid ⊢
  cases h : record.lookup "name" with
  | none =>
    rw [h] at valid; simp [targetValid_empty] at valid
  | some name => rfl

/-- **Records whose keys are valid targets, none repeated, read as their keys, in order.** -/
theorem targets_records :
    ∀ (rs : List (List (String × String))) (seen : List String),
      (∀ r ∈ rs, Linger.Target.Remote.targetValid (keyOf r) = true) →
        (rs.map keyOf).Nodup → (∀ r ∈ rs, keyOf r ∉ seen) → targets seen rs = .ok (rs.map keyOf)
  | [], _, _, _, _ => rfl
  | record :: rest, seen, valid, distinct, fresh => by
    have valid' := valid record (by simp)
    have named := lookup_name valid'
    have notSeen : seen.contains (keyOf record) = false := by simpa using fresh record (by simp)
    simp only [targets, named, valid', Bool.not_true, Bool.false_eq_true, ↓reduceIte, notSeen]
    rw [targets_records rest (keyOf record :: seen) (fun r member => valid r (by simp [member]))
        (List.nodup_cons.mp distinct).2]
    · rfl
    · intro r member inSeen
      simp only [List.mem_cons] at inSeen
      rcases inSeen with same | inSeen
      · exact (List.nodup_cons.mp distinct).1 (same ▸ List.mem_map.mpr ⟨r, member, rfl⟩)
      · exact fresh r (by simp [member]) inSeen

/-- **The record a target's row reads is the one record that names it.** -/
theorem find_record :
    ∀ (rs : List (List (String × String))),
      (∀ r ∈ rs, Linger.Target.Remote.targetValid (keyOf r) = true) →
        (rs.map keyOf).Nodup →
        ∀ record ∈ rs, rs.find? (fun r => r.lookup "name" == some (keyOf record)) = some record
  | [], _, _, _, member => by simp at member
  | first :: rest, valid, distinct, record, member => by
    by_cases same : record = first
    · subst same
      simp [lookup_name (valid record (by simp))]
    · have inRest : record ∈ rest := by simpa [same] using member
      have firstNamed := lookup_name (valid first (by simp))
      have differ : keyOf first ≠ keyOf record := fun keys =>
        (List.nodup_cons.mp distinct).1 (keys ▸ List.mem_map.mpr ⟨record, inRest, rfl⟩)
      have notFirst : (some (keyOf first) == some (keyOf record)) = false := by simpa using differ
      simp only [List.find?_cons, firstNamed, notFirst]
      exact
        find_record rest (fun r m => valid r (by simp [m])) (List.nodup_cons.mp distinct).2 record
          inRest

/-- **What `ls --porcelain` prints reads back** as its records, each under its name, the targets
in their order. -/
theorem porcelain_read (rows : List (List (String × String)))
    (named : ∀ record ∈ records rows, Linger.Target.Remote.targetValid (keyOf record) = true)
    (distinct : ((records rows).map keyOf).Nodup) :
    ∃ snapshot,
      parseSnapshot (porcelain rows) = .ok snapshot ∧
        snapshot.candidates = (records rows).map keyOf ∧
        ∀ record ∈ records rows, Snapshot.row snapshot (keyOf record) = record := by
  refine ⟨{ candidates := (records rows).map keyOf, records := records rows }, ?_, rfl, ?_⟩
  · unfold parseSnapshot
    rw [mapM_lineRecord_porcelain]
    simp only [bind, Except.bind]
    rw [targets_records _ [] named distinct (by simp)]
    rfl
  · intro record member
    simp only [Snapshot.row, find_record _ named distinct record member, Option.getD_some]

end Linger.Selector.Picker
