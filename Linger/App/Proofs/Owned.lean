module

import all Linger.Session.CoreCode
import all Linger.App.CoreCode.Fields
import all Linger.Session.Proofs.Session
public import Linger.Session.CoreCode
public import Linger.App.CoreCode.Fields

/-! # A listing's program fields are readings of what the program owns

Of the fields `info` reports, those the field table gives the program are the title, the
notification's text, the last command's ending and the foreground, each read from what the session
keeps of its program (`Session.Owned`) alone; the boot metadata of a session holds none of them,
and the record's fields, a description and an import's provenance, are linger's. -/

namespace Linger.App.Fields

open Linger.Session

/-- The program's fields a listing reports of a session whose program owns `o`, in the order
`info` reports them. -/
def programFields (o : Owned) : List (String × String) :=
  titleFields o.title ++ noticeFields o.notice ++ finishedFields o.commands.finished ++
    match o.observed with
    | some obs =>
      (match obs.foreground with
        | some fg =>
          [("fg", String.intercalate " " fg.argv), ("fgpid", toString fg.pid), ("fgdir", fg.dir)]
        | none => []) ++
        match obs.echo with
        | some echo => [("echo", toString echo)]
        | none => []
    | none => []

/-- A record's own field is no program's. -/
theorem owns_recordField (key : String) (h : recordField key = true) :
    owns table .program key = false := by
  cases hk : owns table .program key
  · rfl
  · simp [owns, table] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [recordField] at h

/-- How a session ended is no program's field. -/
theorem endingFields_programs (e : Ending) :
    (endingFields e).filter (fun kv => owns table .program kv.1) = [] := by
  cases e with
  | program o => cases o <;> simp [endingFields, outcomeFields, owns, table]
  | saved n => simp [endingFields, owns, table]
  | dismissed => rfl

/-- The present `info` reports gives the program the foreground alone. -/
theorem presentFields_programs (observed : Option Observation) (lastOutMs : Option Nat) :
    (presentFields observed lastOutMs).filter (fun kv => owns table .program kv.1) =
      match observed with
      | some obs =>
        (match obs.foreground with
          | some fg =>
            [("fg", String.intercalate " " fg.argv), ("fgpid", toString fg.pid), ("fgdir", fg.dir)]
          | none => []) ++
          match obs.echo with
          | some echo => [("echo", toString echo)]
          | none => []
      | none => [] := by
  cases observed with
  | none => rfl
  | some o =>
    cases lastOutMs <;> cases hl : o.login <;> cases hf : o.foreground <;> cases he : o.echo <;>
      simp [presentFields, hl, hf, he, owns, table]

/-- The program's fields `info` reports, of a session whose boot metadata holds none, are readings
of what its program owns. -/
theorem infoFields_programs (s : State) (kept : ∀ kv ∈ s.metaKv, owns table .program kv.1 = false) :
    (infoFields s).filter (fun kv => owns table .program kv.1) = programFields s.owned := by
  have hmeta : s.metaKv.filter (fun kv => owns table .program kv.1) = [] :=
    List.filter_eq_nil_iff.mpr fun kv hkv => by simp [kept kv hkv]
  have hfields :
    (s.fields.filter (recordField ·.1)).filter (fun kv => owns table .program kv.1) = [] :=
    List.filter_eq_nil_iff.mpr fun kv hkv => by
      simp only [List.mem_filter] at hkv
      simp [owns_recordField kv.1 hkv.2]
  have htitle (t : String) :
    (titleFields t).filter (fun kv => owns table .program kv.1) = titleFields t := by
    unfold titleFields
    split <;> simp [owns, table]
  have hnotice (n : Option (List UInt8)) :
    (noticeFields n).filter (fun kv => owns table .program kv.1) = noticeFields n := by
    unfold noticeFields
    split
    · split <;> simp [owns, table]
    · rfl
  have hfinished (f : Option Finished) :
    (finishedFields f).filter (fun kv => owns table .program kv.1) = finishedFields f := by
    cases f with
    | none => rfl
    | some f =>
      cases h1 : cmdlineText f.cmdline <;> cases h2 : f.status <;>
        simp [finishedFields, h1, h2, owns, table]
  cases he : StateRec.ended s with
  | none =>
    simp only [infoFields, he, List.filter_append, hmeta, hfields, htitle, hnotice, hfinished,
      presentFields_programs, programFields, State.owned]
    simp [owns, table]
  | some
    e =>
    simp only [infoFields, he, List.filter_append, hmeta, hfields, htitle, hnotice, hfinished,
      presentFields_programs, programFields, State.owned, endingFields_programs]
    simp [owns, table]

/-- A session the daemon booted keeps its boot metadata through every trace. -/
theorem trace_metaKv (s : State) (evs : List Event) : (trace step s evs).1.metaKv = s.metaKv := by
  induction evs generalizing s with
  | nil => rfl
  | cons ev evs ih =>
    simp only [trace]
    rw [ih, step_metaKv]

end Linger.App.Fields
