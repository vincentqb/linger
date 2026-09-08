import Linger.Core.Checkpoint
/-! # §Restore — the reboot-resume codec theorems

THEOREMS.md row: `load (save s) = some s` — exactly, for every state
whose parser is quiescent (which is what checkpoints hold, since the
codec deliberately forgets partial escape sequences); the general form
round-trips modulo `Vt.quiesce`. Totality of `load` on arbitrary bytes
is by construction (`R α = List UInt8 → Option _`, structural
recursion only) — the second half of §Restore needs no theorem.

Every combinator round-trip is unconditional: `wNat` is LEB128, so
there is no "fits in N bits" side condition anywhere in the format.
-/

namespace Linger.Core.Checkpoint

open Linger.Core.Vt

/-- "Reader `r` inverts writer `w`, leaving the rest untouched." -/
abbrev RT {α : Type} (w : α → List UInt8) (r : R α) : Prop :=
  ∀ (a : α) (rest : List UInt8), r (w a ++ rest) = some (a, rest)

theorem rt_u8 : RT wU8 rU8 := fun _ _ => rfl

theorem rt_nat : RT wNat rNat := by
  intro n rest
  induction n using wNat.induct with
  | case1 n h =>
    rw [wNat, dite_eq_left h]
    have hb : (UInt8.ofNat n) < 128 := by
      simp only [UInt8.lt_iff_toNat_lt, UInt8.toNat_ofNat',
        show (128 : UInt8).toNat = 128 from rfl]
      omega
    simp [rNat, hb, UInt8.toNat_ofNat']
    clear hb
    omega
  | case2 n h ih =>
    rw [wNat, dite_eq_right h]
    have hmod : n % 128 < 128 := Nat.mod_lt _ (by omega)
    have hb : ¬ (UInt8.ofNat (128 + n % 128)) < 128 := by
      simp only [UInt8.lt_iff_toNat_lt, UInt8.toNat_ofNat',
        show (128 : UInt8).toNat = 128 from rfl]
      omega
    simp only [rNat, List.cons_append, hb, ite_false, ih]
    clear hb
    simp only [UInt8.toNat_ofNat']
    have h1 : (128 + n % 128) % 256 = 128 + n % 128 := by omega
    rw [h1]
    have h2 : 128 + n % 128 - 128 + 128 * (n / 128) = n := by omega
    rw [h2]

theorem rt_bool : RT wBool rBool := by
  intro b rest
  cases b <;> rfl

theorem rt_char : RT wChar rChar := by
  intro c rest
  unfold wChar rChar
  rw [rt_nat c.toNat rest]
  have hv : c.toNat.isValidChar := c.valid
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [dite_eq_left hv]
  exact congrArg (fun x => some (x, rest)) (Char.ext rfl)

theorem rt_pair {α β : Type} {wa : α → List UInt8} {ra : R α}
    {wb : β → List UInt8} {rb : R β} (ha : RT wa ra) (hb : RT wb rb) :
    RT (wPair wa wb) (rPair ra rb) := by
  intro p rest
  unfold wPair rPair
  simp only [List.append_assoc, ha, hb, Option.bind_eq_bind, Option.bind_some]

theorem rt_opt {α : Type} {w : α → List UInt8} {r : R α} (h : RT w r) :
    RT (wOpt w) (rOpt r) := by
  intro o rest
  cases o with
  | none => rfl
  | some a =>
    unfold wOpt rOpt
    simp only [List.cons_append, h, Option.bind_eq_bind, Option.bind_some]

theorem rt_listAux {α : Type} {w : α → List UInt8} {r : R α} (h : RT w r) :
    ∀ (l : List α) (rest : List UInt8),
      rListAux r l.length (l.flatMap w ++ rest) = some (l, rest) := by
  intro l
  induction l with
  | nil => intro rest; rfl
  | cons x xs ih =>
    intro rest
    simp only [List.flatMap_cons, List.length_cons, rListAux, List.append_assoc,
      h, ih, Option.bind_eq_bind, Option.bind_some]

theorem rt_list {α : Type} {w : α → List UInt8} {r : R α} (h : RT w r) :
    RT (wList w) (rList r) := by
  intro l rest
  unfold wList rList
  simp only [List.append_assoc, rt_nat, Option.bind_eq_bind, Option.bind_some]
  exact rt_listAux h l rest

theorem rt_str : RT wStr rStr := by
  intro s rest
  unfold wStr rStr
  simp only [rt_list rt_char, Option.bind_eq_bind, Option.bind_some,
    String.ofList_toList]

theorem rt_color : RT wColor rColor := by
  intro c rest
  cases c <;> rfl

theorem rt_pen : RT wPen rPen := by
  intro p rest
  unfold wPen rPen
  simp only [List.append_assoc, rt_color, rt_bool, Option.bind_eq_bind, Option.bind_some]

theorem rt_cell : RT wCell rCell := by
  intro c rest
  unfold wCell rCell
  simp only [List.append_assoc, rt_char, rt_list rt_char, rt_nat, rt_pen,
    Option.bind_eq_bind, Option.bind_some]

/-- Expanding the run-length groups of a list recovers the list. -/
theorem expand_runs {α : Type} [DecidableEq α] (l : List α) : expand (runs l) = l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [runs]
    cases hrt : runs t with
    | nil =>
      rw [hrt] at ih
      simp only [expand] at ih
      -- ih : [] = t, so t is empty and the run is just [a]
      simp only [← ih, expand, List.replicate, List.append_nil]
    | cons hd tl =>
      obtain ⟨n, b⟩ := hd
      rw [hrt] at ih
      simp only [expand] at ih
      by_cases hab : a = b
      · subst hab
        simp only [reduceIte, expand, List.replicate_succ, List.cons_append, ih]
      · simp only [hab, reduceIte, expand, List.replicate,
          List.singleton_append, ih]

theorem rt_rle {α : Type} [DecidableEq α] {w : α → List UInt8} {r : R α}
    (h : RT w r) : RT (wRLE w) (rRLE r) := by
  intro l rest
  unfold wRLE rRLE
  simp only [rt_list (rt_pair rt_nat h), Option.bind_eq_bind, Option.bind_some,
    expand_runs]

theorem rt_row : RT wRow rRow := by
  intro r rest
  unfold wRow rRow
  simp only [rt_rle rt_cell, Option.bind_eq_bind, Option.bind_some]

theorem rt_cursor : RT wCursor rCursor := by
  intro c rest
  unfold wCursor rCursor
  simp only [List.append_assoc, rt_nat, rt_bool, Option.bind_eq_bind, Option.bind_some]

theorem rt_modes : RT wModes rModes := by
  intro m rest
  unfold wModes rModes
  simp only [List.append_assoc, rt_bool, rt_nat, Option.bind_eq_bind, Option.bind_some]

theorem rt_saved : RT wSaved rSaved := by
  intro s rest
  unfold wSaved rSaved
  simp only [List.append_assoc, rt_cursor, rt_pen, Option.bind_eq_bind, Option.bind_some]

theorem rt_ring : RT wRing rRing := by
  intro r rest
  unfold wRing rRing
  simp only [List.append_assoc, rt_nat, rt_list rt_row, Option.bind_eq_bind,
    Option.bind_some]

theorem rt_alt : RT wAlt rAlt := by
  unfold wAlt rAlt
  apply rt_opt
  intro x rest
  obtain ⟨g, c, p⟩ := x
  simp only [List.append_assoc, rt_list rt_row, rt_cursor, rt_pen,
    Option.bind_eq_bind, Option.bind_some]

/-- The Vt round-trip: exact modulo the deliberately-forgotten parser
state. -/
theorem rt_vt (v : Vt) (rest : List UInt8) :
    rVt (wVt v ++ rest) = some (v.quiesce, rest) := by
  unfold wVt rVt Vt.quiesce
  simp only [List.append_assoc, rt_nat, rt_list rt_row, rt_cursor, rt_pen,
    rt_modes, rt_list rt_bool, rt_ring, rt_alt, rt_saved, rt_str, rt_bool,
    Option.bind_eq_bind, Option.bind_some]

/-! ### The format tag, as a named stage

`stripMagic` is the tag check, named rather than inlined; `load_save` and `save_tag` both
go through it instead of unfolding the decision into the parser chain. -/

theorem stripMagic_magic (p : List UInt8) : stripMagic (magic ++ p) = some p := by
  unfold stripMagic
  rw [List.take_append_of_le_length (by simp [magic]),
      List.take_of_length_le (by simp [magic]),
      List.drop_append_of_le_length (by simp [magic]),
      List.drop_of_length_le (by simp [magic]), List.nil_append]
  rw [ite_eq_left (rfl : magic = magic)]

/-- §Restore, top level: a checkpoint written by `save` loads back to
exactly what was saved (parser state quiesced — which the daemon's
checkpoints already are, being taken between poll rounds). Totality on
garbage is by construction. -/
theorem load_save (c : Ckpt) :
    load (save c) = some { c with vt := c.vt.quiesce } := by
  unfold load save
  simp only [List.append_assoc]
  rw [stripMagic_magic]
  simp only [rt_vt, rt_str, Option.bind_eq_bind, Option.bind_some]
  have h := rt_list (rt_pair rt_str rt_str) c.labels []
  rw [List.append_nil] at h
  rw [h]
  rfl

/-- **The tag `save` writes.** Pinned as its own claim because the tag is the one part
of a checkpoint another program reads before trusting the rest, and because a wrong
constant here is invisible to the round trip (`load_save` would still hold of a `save`
that wrote any tag `stripMagic` accepted).

The pre-rename `"LZMX"` reader was removed on 2026-08-19, one commit after it landed:
it existed to migrate files written before the rename, `save` had already been writing
`"LNGR"` for a commit, and there were no old-tag checkpoints left on disk to orphan.
Anyone who needs to read one can check out `e1ac562`, where the reader and its two
theorems (`load_legacy_save`, `save_no_legacy`) are green — that is the escape hatch,
and it is cheaper than carrying a branch for a file nobody has. -/
theorem save_tag (c : Ckpt) : (save c).take 5 = magic := by
  unfold save
  simp only [List.append_assoc]
  rw [List.take_append_of_le_length (by simp [magic]),
      List.take_of_length_le (by simp [magic])]

/-- And when the parser is already quiescent, the round-trip is exact
— the letter of the THEOREMS.md row. -/
theorem load_save_exact (c : Ckpt) (h : c.vt.pstate = .ground)
    (h8 : c.vt.u8need = 0) (ha : c.vt.u8acc = 0) :
    load (save c) = some c := by
  rw [load_save]
  congr 1
  cases c with
  | mk vt cwd labels =>
    simp only [Ckpt.mk.injEq, and_true]
    cases vt
    simp_all [Vt.quiesce]

end Linger.Core.Checkpoint
