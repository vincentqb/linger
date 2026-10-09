module

public import Linger.Core.Replay
public import Theorems.Render.Scrollback
import all Linger.Core.Replay
import all Linger.Core.Vt
import all Linger.Core.Render
import all Theorems.Render.Grid
import all Theorems.Render.Scrollback
import Init.Data.String.Lemmas.TakeDrop
import Init.Data.String.Lemmas.IsEmpty

/-! A replay cursor denotes the exact remaining renderer stream. These
definitions are proof observations, never runtime allocations. -/

namespace Linger.Core.Replay

open Linger.Core.Vt

def partBytes : Part → Render.Bytes
  | .bytes bytes => bytes
  | .rows rows pen => Render.joinCRLF (Render.rowsAnsi rows pen)
  | .text text => Render.utf8s text.copy.toList

def partsBytes (parts : List Part) : Render.Bytes := parts.flatMap partBytes

def remaining (p : Plan) : Render.Bytes := p.pending ++ partsBytes p.parts

/-- The snapshot cursor denotes the same stream as the complete renderer,
including both screens, inherited row pens, separators and final controls. -/
theorem start_faithful (v : Vt) : remaining (start v) = Render.restore v := by
  unfold start remaining partsBytes Render.restore Render.restoreBody Render.screensAnsi
  cases v.altGrid with
  | none => simp [partBytes, Render.gridAnsi_eq, Render.titleAnsi, List.append_assoc]
  | some saved =>
    rcases saved with ⟨grid, cur, pen⟩
    simp [partBytes, Render.gridAnsi_eq, Render.titleAnsi, List.append_assoc]

theorem text_uncons (text : String.Slice) :
    partBytes (.text text) =
      Render.utf8s (text.take 4096).copy.toList ++ partBytes (.text (text.drop 4096)) := by
  simp only [partBytes, String.Slice.toList_copy_take, String.Slice.toList_copy_drop]
  unfold Render.utf8s
  rw [← List.flatMap_append, List.take_append_drop]

theorem rows_uncons (row : Row) (rows : List Row) (pen : Pen) :
    partBytes (.rows (row :: rows) pen) =
      (Render.rowAnsi row pen).1 ++ (if rows.isEmpty then [] else [0x0D, 0x0A]) ++
        partBytes (.rows rows (Render.rowAnsi row pen).2) := by
  cases rows <;> simp [partBytes, Render.rowsAnsi, Render.joinCRLF, List.append_assoc]

/-- Every emitted piece is precisely a prefix, and the new cursor is precisely
the suffix. This also covers zero-byte transitions between stages. -/
theorem next_faithful {budget : Nat} {p q : Plan} {bytes : Render.Bytes}
    (h : next budget p = some (bytes, q)) : remaining p = bytes ++ remaining q := by
  revert h
  fun_cases next budget p
  all_goals
    intro h
    simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  all_goals obtain ⟨rfl, rfl⟩ := h
  · simp [remaining, ← List.append_assoc, List.take_append_drop]
  · simp [remaining, partsBytes, partBytes, *]
  · simp [remaining, partsBytes, partBytes, String.Slice.copy_eq_empty_iff.mpr ‹_›, Render.utf8s, *]
  · simp only [remaining, partsBytes, List.flatMap_cons, List.nil_append, *]
    rw [text_uncons]
    simp [List.append_assoc]
  · simp [remaining, partsBytes, partBytes, Render.rowsAnsi, Render.joinCRLF, *]
  · simp only [remaining, partsBytes, List.flatMap_cons, List.nil_append, *]
    rw [rows_uncons, ‹Render.rowAnsi _ _ = _›]
    simp [List.append_assoc]

/-- A step never emits more bytes than its budget. -/
public theorem next_bounded {budget : Nat} {p q : Plan} {bytes : Render.Bytes}
    (h : next budget p = some (bytes, q)) : bytes.length ≤ budget := by
  revert h
  fun_cases next budget p
  all_goals
    intro h
    simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  all_goals
    obtain ⟨rfl, rfl⟩ := h
    simp [List.length_take, Nat.min_le_left]

theorem next_done {budget : Nat} {p : Plan} (h : next budget p = none) : remaining p = [] := by
  revert h
  fun_cases next budget p
  all_goals
    intro h
    simp only [reduceCtorEq] at h
  simp [remaining, partsBytes, *]

/-- A positive step consumes bytes or one unit of structural work. The measure
does not appear in the running program; it just rules out a stuck cursor. -/
def sourceCount (parts : List Part) : Nat :=
  (parts.map
      (fun part =>
        match part with
        | .bytes _ => 0
        | .rows rows _ => rows.length
        | .text text => text.copy.toList.length)).sum

def work (p : Plan) : Nat := (remaining p).length + sourceCount p.parts + p.parts.length

theorem next_progress {budget : Nat} {p q : Plan} {bytes : Render.Bytes} (positive : 0 < budget)
    (h : next budget p = some (bytes, q)) : work q < work p := by
  have lengths := congrArg List.length (next_faithful h)
  simp only [List.length_append] at lengths
  revert h
  fun_cases next budget p
  all_goals
    intro h
    simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  all_goals obtain ⟨rfl, rfl⟩ := h
  · simp only [work]
    simp only [List.length_take, ‹p.pending = _›, List.length_cons] at lengths ⊢
    omega
  · simp_all [work, sourceCount]
  · simp_all [work, sourceCount, String.Slice.copy_eq_empty_iff.mpr ‹_›]
  · rename_i nonempty
    have pos : 0 < (‹String.Slice›).copy.toList.length :=
      List.length_pos_iff.mpr (by simpa using nonempty)
    simp_all [work, sourceCount]
    omega
  · simp_all [work, sourceCount]
  · simp_all [work, sourceCount]

/-- Sum of literal stages, independent of all screen paints. -/
def literalBytes (parts : List Part) : Nat :=
  (parts.map
      (fun part =>
        match part with
        | .bytes bytes => bytes.length
        | _ => 0)).sum

def largestRow (rows : List Row) : Nat := rows.foldr (fun row n => max (Render.sbRowCost row) n) 0

def largestPaint (parts : List Part) : Nat :=
  parts.foldr
    (fun part n =>
      match part with
      | .bytes _ => n
      | .rows rows _ => max (largestRow rows) n
      | .text _ => max 16384 n)
    0

/-- A cursor's serialized storage is paid for by its literal stages plus just
the larger of the current pending piece and the largest remaining row. -/
def storageBudget (p : Plan) : Nat :=
  literalBytes p.parts + max p.pending.length (largestPaint p.parts)

theorem next_storage {budget : Nat} {p q : Plan} {bytes : Render.Bytes}
    (h : next budget p = some (bytes, q)) : storageBudget q ≤ storageBudget p := by
  revert h
  fun_cases next budget p
  all_goals
    intro h
    simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  all_goals obtain ⟨rfl, rfl⟩ := h
  · simp only [storageBudget, List.length_drop]
    omega
  · simp_all [storageBudget, literalBytes, largestPaint]
    omega
  · simp_all [storageBudget, literalBytes, largestPaint]
    omega
  · have bound := Render.utf8s_length_le (‹String.Slice›.take 4096).copy.toList
    simp only [String.Slice.toList_copy_take, List.length_take] at bound
    simp_all [storageBudget, literalBytes, largestPaint]
    omega
  · simp_all [storageBudget, literalBytes, largestPaint, largestRow]
  · rename_i row rows pen _ _ _ _ hrow
    have cost := Render.rowAnsi_len_add_crlf_le_cost row pen
    rw [hrow] at cost
    have sep : (if rows.isEmpty = true then ([] : Render.Bytes) else [0x0D, 0x0A]).length ≤ 2 := by
      split <;> simp
    simp_all [storageBudget, literalBytes, largestPaint, largestRow]
    omega

theorem next_parts {budget : Nat} {p q : Plan} {bytes : Render.Bytes}
    (h : next budget p = some (bytes, q)) : q.parts.length ≤ p.parts.length := by
  revert h
  fun_cases next budget p
  all_goals
    intro h
    simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  all_goals
    obtain ⟨rfl, rfl⟩ := h
    simp_all

/-- Finite prefixes of actual cursor steps, with their concatenated payload. -/
inductive Steps : Plan → Render.Bytes → Plan → Prop where
  | refl (p) : Steps p [] p
  |
  step {p q r bytes rest budget} :
    next budget p = some (bytes, q) → Steps q rest r → Steps p (bytes ++ rest) r

theorem steps_faithful {p q : Plan} {bytes : Render.Bytes} (h : Steps p bytes q) :
    remaining p = bytes ++ remaining q := by
  induction h with
  | refl => simp
  | step step _ ih => rw [next_faithful step, ih, List.append_assoc]

/-- Serialized bytes retained after any prefix fit in the initial setup plus
one row or title chunk's storage budget. Advances never build a parts backlog. -/
theorem steps_storage {p q : Plan} {bytes : Render.Bytes} (h : Steps p bytes q) :
    literalBytes q.parts + q.pending.length ≤ storageBudget p ∧
      q.parts.length ≤ p.parts.length := by
  have bounds : storageBudget q ≤ storageBudget p ∧ q.parts.length ≤ p.parts.length := by
    induction h with
    | refl => exact ⟨Nat.le_refl _, Nat.le_refl _⟩
    | step step _ ih =>
      exact ⟨Nat.le_trans ih.1 (next_storage step), Nat.le_trans ih.2 (next_parts step)⟩
  refine ⟨?_, bounds.2⟩
  have retained : literalBytes q.parts + q.pending.length ≤ storageBudget q := by
    unfold storageBudget
    omega
  exact Nat.le_trans retained bounds.1

theorem start_parts (v : Vt) : (start v).parts.length ≤ 7 := by
  unfold start
  cases v.altGrid <;> simp

/-- A mathematical complete walk. The runtime never constructs this list;
termination proves that positive-budget advances always finish. -/
public def drain (budget : Nat) (positive : 0 < budget) (p : Plan) : Render.Bytes :=
  match _h : next budget p with
  | none => []
  | some (bytes, q) => bytes ++ drain budget positive q
termination_by work p
decreasing_by exact next_progress positive _h

theorem drain_faithful (budget : Nat) (positive : 0 < budget) (p : Plan) :
    drain budget positive p = remaining p := by
  rw [drain]
  split
  next h => exact (next_done h).symm
  next bytes q h =>
    rw [drain_faithful budget positive q]
    exact (next_faithful h).symm
termination_by work p
decreasing_by exact next_progress positive (by assumption)

/-- End-to-end exactness without any assumption on the snapshot's contents. -/
public theorem drain_start (budget : Nat) (positive : 0 < budget) (v : Vt) :
    drain budget positive (start v) = Render.restore v := by rw [drain_faithful, start_faithful]

end Linger.Core.Replay
