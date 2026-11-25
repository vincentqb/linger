module

public import Linger.Selector.CoreCode.Picker
public import Linger.Display.CoreCode.Listing
public import Linger.Target.CoreCode.Remote
import all Linger.Selector.CoreCode.Picker
import all Linger.Display.CoreCode.Listing
import all Linger.Target.CoreCode.Remote
public import Linger.Display.Proofs.Record
public import ExactJSON.Solution

/-! # The chooser reads what `ls --porcelain` prints

A listing's records (`Listing.records`), printed as `ls --porcelain` prints them, their JSON Lines
(`Listing.porcelain`, `ExactJSON.encodeLines`), read back as the chooser reads a listing
(`parseSnapshot`, `ExactJSON.decodeLines`), give each record back under its name, as a row holds
its fields (`Record.fields`), the targets in their order, when each record's name is a valid target
no other record has. -/

public section

namespace Linger.Selector.Picker

open Linger.Display.Listing

/-- **A listing's JSON Lines read back as its records**, each as a row holds its fields. -/
theorem listingRows_porcelain (rows : List (List (String × String))) :
    listingRows (porcelain rows) = .ok ((records rows).map Record.fields) := by
  unfold listingRows porcelain
  rw [ExactJSON.decodeLines_encode]

/-- No name is not a valid target. -/
theorem targetValid_empty : Linger.Target.Remote.targetValid "" = false := by decide

/-- A record whose key is a valid target names it, as a row holds its fields. -/
theorem lookup_name {record : Record} (valid : Linger.Target.Remote.targetValid record.key = true) :
    record.fields.lookup "name" = some record.key :=
  name_field record fun empty => by
    rw [empty, targetValid_empty] at valid; cases valid

/-- **Records whose keys are valid targets, none repeated, read as their keys, in order.** -/
theorem targets_records :
    ∀ (rs : List Record) (seen : List String),
      (∀ r ∈ rs, Linger.Target.Remote.targetValid r.key = true) →
        (rs.map Record.key).Nodup →
        (∀ r ∈ rs, r.key ∉ seen) → targets seen (rs.map Record.fields) = .ok (rs.map Record.key)
  | [], _, _, _, _ => rfl
  | record :: rest, seen, valid, distinct, fresh => by
    have valid' := valid record (by simp)
    have named := lookup_name valid'
    have notSeen : seen.contains record.key = false := by simpa using fresh record (by simp)
    simp only [List.map_cons, targets, named, valid', Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      notSeen]
    rw [targets_records rest (record.key :: seen) (fun r member => valid r (by simp [member]))
        (List.nodup_cons.mp distinct).2]
    · rfl
    · intro r member inSeen
      simp only [List.mem_cons] at inSeen
      rcases inSeen with same | inSeen
      · exact (List.nodup_cons.mp distinct).1 (same ▸ List.mem_map.mpr ⟨r, member, rfl⟩)
      · exact fresh r (by simp [member]) inSeen

/-- **The row a target reads is the one record that names it**, as a row holds its fields. -/
theorem find_record :
    ∀ (rs : List Record),
      (∀ r ∈ rs, Linger.Target.Remote.targetValid r.key = true) →
        (rs.map Record.key).Nodup →
        ∀ record ∈ rs,
          (rs.map Record.fields).find? (fun r => r.lookup "name" == some record.key) =
            some record.fields
  | [], _, _, _, member => by simp at member
  | first :: rest, valid, distinct, record, member => by
    by_cases same : record = first
    · subst same
      simp [lookup_name (valid record (by simp))]
    · have inRest : record ∈ rest := by simpa [same] using member
      have firstNamed := lookup_name (valid first (by simp))
      have differ : first.key ≠ record.key := fun keys =>
        (List.nodup_cons.mp distinct).1 (keys ▸ List.mem_map.mpr ⟨record, inRest, rfl⟩)
      have notFirst : (some first.key == some record.key) = false := by simpa using differ
      simp only [List.map_cons, List.find?_cons, firstNamed, notFirst]
      exact
        find_record rest (fun r m => valid r (by simp [m])) (List.nodup_cons.mp distinct).2 record
          inRest

/-- **What `ls --porcelain` prints reads back** as its records, each under its name, as a row
holds its fields, the targets in their order. -/
theorem porcelain_read (rows : List (List (String × String)))
    (named : ∀ record ∈ records rows, Linger.Target.Remote.targetValid record.key = true)
    (distinct : ((records rows).map Record.key).Nodup) :
    ∃ snapshot,
      parseSnapshot (porcelain rows) = .ok snapshot ∧
        snapshot.candidates = (records rows).map Record.key ∧
        ∀ record ∈ records rows, Snapshot.row snapshot record.key = record.fields := by
  refine
    ⟨{ candidates := (records rows).map Record.key, records := (records rows).map Record.fields },
      ?_, rfl, ?_⟩
  · unfold parseSnapshot
    rw [listingRows_porcelain]
    simp only [bind, Except.bind]
    rw [targets_records _ [] named distinct (by simp)]
    rfl
  · intro record member
    simp only [Snapshot.row, find_record _ named distinct record member, Option.getD_some]

end Linger.Selector.Picker
