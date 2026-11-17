module

import all Terminal.CoreCode.Render
import all Terminal.CoreCode.Vt
import all Terminal.Proofs.Vt
import all Terminal.Proofs.Render.Ends
import all Terminal.Proofs.Render.Grid

-- Module-private by default: `Vt`'s fields are sealed (see `packages/terminal/Terminal/Proofs/Vt/State.lean`).

/-! # A repaint is one synchronized update

`Replay.start` streams `restore` between `syncBegin` and `syncEnd`. This module shows the repaint
holds neither bracket (`restore_noBracket`), so a receiver sees one update open and one close,
and that the closing bracket leaves a terminal between control sequences and characters as it
was (`feed_syncEnd`), since the emulator keeps no DEC mode 2026.

`NoBracket` is the invariant that composes over `++`: no bracket inside, and no nonempty tail a
following piece could complete to one, which is a prefix of `syncStem`. Every escape the
renderer writes begins and ends inside one emitter, and text holds no `ESC`, so each emitter keeps
it. -/

namespace Terminal.Render

open Terminal.Vt

/-- What both brackets open with: `CSI ? 2026`. -/
def syncStem : Bytes := [0x1B, 0x5B, 0x3F, 0x32, 0x30, 0x32, 0x36]

/-- Bytes with no bracket inside and no nonempty tail that bytes after them could complete to
one. -/
def NoBracket (b : Bytes) : Prop :=
  ¬syncBegin <:+: b ∧ ¬syncEnd <:+: b ∧ ∀ s, s <:+ b → s ≠ [] → ¬s <+: syncStem

theorem stem_of_prefix {X a : Bytes} (hX : X = syncBegin ∨ X = syncEnd) (ha : a <+: X)
    (hne : a ≠ X) : a <+: syncStem := by
  have h8 : X.length = 8 := by rcases hX with rfl | rfl <;> rfl
  have heq := List.prefix_iff_eq_take.mp ha
  have hlt : a.length < 8 := by
    refine Nat.lt_of_le_of_ne (h8 ▸ ha.length_le) fun h => hne ?_
    rw [heq, List.take_of_length_le (by omega)]
  rw [heq]
  rcases hX with rfl | rfl
  · exact (by decide : ∀ k < 8, syncBegin.take k <+: syncStem) _ hlt
  · exact (by decide : ∀ k < 8, syncEnd.take k <+: syncStem) _ hlt

theorem esc_mem_stem {s : Bytes} (hs : s <+: syncStem) (hne : s ≠ []) : 0x1B ∈ s := by
  have heq := List.prefix_iff_eq_take.mp hs
  have hl : s.length < 8 := Nat.lt_of_le_of_lt hs.length_le (by decide)
  have hpos : 0 < s.length := List.length_pos_iff.mpr hne
  rw [heq]
  exact (by decide : ∀ k < 8, 0 < k → 0x1B ∈ syncStem.take k) _ hl hpos

theorem esc_mem_bracket {X : Bytes} (hX : X = syncBegin ∨ X = syncEnd) : 0x1B ∈ X := by
  rcases hX with rfl | rfl <;> decide

theorem NoBracket.nil : NoBracket [] :=
  ⟨by decide, by decide, fun _ hs hne _ => hne (List.suffix_nil.mp hs)⟩

/-- Bytes with no `ESC` hold no bracket and no start of one. -/
theorem NoBracket.of_noEsc {b : Bytes} (h : 0x1B ∉ b) : NoBracket b :=
  ⟨fun hi => h (hi.subset (esc_mem_bracket (.inl rfl))), fun hi =>
    h (hi.subset (esc_mem_bracket (.inr rfl))), fun _ hs hne hp =>
    h (hs.subset (esc_mem_stem hp hne))⟩

theorem infix_append_split {X a b : Bytes} (h : X <:+: a ++ b) :
    X <:+: a ∨ X <:+: b ∨ ∃ s, s <:+ a ∧ s ≠ [] ∧ s <+: X ∧ s ≠ X := by
  obtain ⟨u, t, hut⟩ := h
  rw [List.append_assoc] at hut
  rcases List.append_eq_append_iff.mp hut with ⟨as, ha, hxt⟩ | ⟨bs, _, hb⟩
  · rcases List.append_eq_append_iff.mp hxt with ⟨cs, has, _⟩ | ⟨ds, hX, hb⟩
    · exact .inl ⟨u, cs, by rw [ha, has, List.append_assoc]⟩
    · by_cases has0 : as = []
      · subst has0
        simp only [List.nil_append] at hX
        subst hX
        exact .inr (.inl ⟨[], t, by simp [hb]⟩)
      · by_cases hds : ds = []
        · subst hds
          simp only [List.append_nil] at hX
          subst hX
          exact .inl ⟨u, [], by simp [ha]⟩
        · refine .inr (.inr ⟨as, ⟨u, ha.symm⟩, has0, ⟨ds, hX.symm⟩, fun h => hds ?_⟩)
          rw [h] at hX
          have := congrArg List.length hX
          simp only [List.length_append] at this
          exact List.eq_nil_of_length_eq_zero (by omega)
  · exact .inr (.inl ⟨bs, t, by rw [hb, List.append_assoc]⟩)

theorem suffix_append_split {s a b : Bytes} (h : s <:+ a ++ b) :
    s <:+ b ∨ ∃ a', a' <:+ a ∧ a' ≠ [] ∧ s = a' ++ b := by
  obtain ⟨u, hu⟩ := h
  rcases List.append_eq_append_iff.mp hu with ⟨as, ha, hs⟩ | ⟨bs, _, hb⟩
  · by_cases has : as = []
    · subst has
      simp only [List.nil_append] at hs
      subst hs
      exact .inl (List.suffix_refl _)
    · exact .inr ⟨as, ⟨u, ha.symm⟩, has, hs⟩
  · exact .inl ⟨bs, hb.symm⟩

/-- **The invariant composes.** A bracket in `a ++ b` lies in one of them or straddles the seam,
where `a` would end with a start of it. -/
theorem NoBracket.append {a b : Bytes} (ha : NoBracket a) (hb : NoBracket b) :
    NoBracket (a ++ b) := by
  have inside : ∀ X, (X = syncBegin ∨ X = syncEnd) → ¬X <:+: a → ¬X <:+: b → ¬X <:+: a ++ b := by
    intro X hX hna hnb hi
    rcases infix_append_split hi with h | h | ⟨s, hs, hne, hp, hneX⟩
    · exact hna h
    · exact hnb h
    · exact ha.2.2 s hs hne (stem_of_prefix hX hp hneX)
  refine ⟨inside _ (.inl rfl) ha.1 hb.1, inside _ (.inr rfl) ha.2.1 hb.2.1, fun s hs hne hp => ?_⟩
  rcases suffix_append_split hs with h | ⟨a', ha', hne', rfl⟩
  · exact hb.2.2 s h hne hp
  · exact ha.2.2 a' ha' hne' ((List.prefix_append a' b).trans hp)

theorem NoBracket.flatMap {α : Type} {f : α → Bytes} :
    ∀ {l : List α}, (∀ x ∈ l, NoBracket (f x)) → NoBracket (l.flatMap f)
  | [], _ => NoBracket.nil
  | x :: xs, h => by
    rw [List.flatMap_cons]
    exact (h x (by simp)).append (NoBracket.flatMap fun y hy => h y (by simp [hy]))

/-- One escape, `ESC` and bytes with no other: a bracket in it would start at its `ESC`. -/
theorem NoBracket.esc {r : Bytes} (hr : 0x1B ∉ r) (h1 : ¬syncBegin <+: 0x1B :: r)
    (h2 : ¬syncEnd <+: 0x1B :: r) (h3 : ¬(0x1B :: r) <+: syncStem) : NoBracket (0x1B :: r) := by
  have only : ∀ X, (X = syncBegin ∨ X = syncEnd) → ¬X <+: 0x1B :: r → ¬X <:+: 0x1B :: r := by
    intro X hX hn ⟨u, t, h⟩
    cases u with
    | nil => exact hn ⟨t, by simpa using h⟩
    | cons x u =>
      simp only [List.cons_append, List.cons.injEq] at h
      apply hr
      rw [← h.2]
      simp [esc_mem_bracket hX]
  refine ⟨only _ (.inl rfl) h1, only _ (.inr rfl) h2, fun s hs hne hp => ?_⟩
  obtain ⟨u, hu⟩ := hs
  cases u with
  | nil =>
    simp only [List.nil_append] at hu
    subst hu
    exact h3 hp
  | cons x u =>
    simp only [List.cons_append, List.cons.injEq] at hu
    apply hr
    rw [← hu.2]
    exact List.mem_append_right _ (esc_mem_stem hp hne)

/-- A control sequence whose bytes after `CSI` hold no `ESC` and no `?`: not private, so no
bracket. -/
theorem NoBracket.csi {r : Bytes} (hr : 0x1B ∉ r) (hq : 0x3F ∉ r) (hne : r ≠ []) :
    NoBracket (csiB ++ r) := by
  show NoBracket (0x1B :: 0x5B :: r)
  refine NoBracket.esc (by simpa using hr) ?_ ?_ ?_
  · rintro ⟨t, h⟩
    simp only [syncBegin, List.cons_append, List.cons.injEq] at h
    apply hq
    rw [← h.2.2]
    simp
  · rintro ⟨t, h⟩
    simp only [syncEnd, List.cons_append, List.cons.injEq] at h
    apply hq
    rw [← h.2.2]
    simp
  · rintro ⟨t, h⟩
    cases r with
    | nil => exact hne rfl
    | cons x r =>
      simp only [syncStem, List.cons_append, List.cons.injEq] at h
      exact hq (by simp [h.2.2.1])

/-- A digit is neither `ESC` nor `?`. -/
theorem digit_quiet {n : Nat} {b : UInt8} (hb : b ∈ digits n) : b ≠ 0x1B ∧ b ≠ 0x3F := by
  have := digits_range n b hb
  constructor <;> (rintro rfl; revert this; decide)

theorem joinSemi_quiet : ∀ (l : List Nat), ∀ b ∈ joinSemi l, b ≠ 0x1B ∧ b ≠ 0x3F
  | [] => by simp [joinSemi]
  | [n] => fun b hb => digit_quiet (by simpa [joinSemi] using hb)
  | n :: m :: ms => fun b hb => by
    simp only [joinSemi, List.mem_append, List.mem_singleton] at hb
    rcases hb with (hb | rfl) | hb
    · exact digit_quiet hb
    · decide
    · exact joinSemi_quiet (m :: ms) b hb

theorem utf8_noEsc (c : Char) : 0x1B ∉ utf8 (safeChar c) := fun h =>
  utf8s_no_esc [c] 0x1B (by simpa [utf8s] using h) rfl

theorem utf8s_noEsc (cs : List Char) : 0x1B ∉ utf8s cs := fun h => utf8s_no_esc cs 0x1B h rfl

theorem NoBracket.ite {c : Prop} [Decidable c] {a b : Bytes} (ha : NoBracket a) (hb : NoBracket b) :
    NoBracket (if c then a else b) := by
  split
  · exact ha
  · exact hb

/-- `CSI`, parameter bytes with no `ESC` and no `?`, then a final byte. -/
theorem params_noBracket {p : Bytes} (hp : ∀ b ∈ p, b ≠ 0x1B ∧ b ≠ 0x3F) {f : UInt8}
    (hf : f ≠ 0x1B ∧ f ≠ 0x3F) : NoBracket (csiB ++ p ++ [f]) := by
  rw [List.append_assoc]
  refine NoBracket.csi ?_ ?_ (by simp)
  · simp only [List.mem_append, List.mem_singleton, not_or]
    exact ⟨fun h => (hp _ h).1 rfl, fun h => hf.1 h.symm⟩
  · simp only [List.mem_append, List.mem_singleton, not_or]
    exact ⟨fun h => (hp _ h).2 rfl, fun h => hf.2 h.symm⟩

theorem csiNum_noBracket (n : Nat) (f : UInt8) (hf : f ≠ 0x1B ∧ f ≠ 0x3F) :
    NoBracket (csiNum n f) := params_noBracket (fun _ hb => digit_quiet hb) hf

theorem csiNum2_noBracket (a b : Nat) (f : UInt8) (hf : f ≠ 0x1B ∧ f ≠ 0x3F) :
    NoBracket (csiNum2 a b f) := by
  unfold csiNum2
  rw [show
      csiB ++ digits a ++ [0x3B] ++ digits b ++ [f] =
        csiB ++ (digits a ++ [0x3B] ++ digits b) ++ [f]
      by simp only [List.append_assoc]]
  refine params_noBracket ?_ hf
  intro x hx
  simp only [List.mem_append, List.mem_singleton] at hx
  rcases hx with (hx | rfl) | hx
  · exact digit_quiet hx
  · decide
  · exact digit_quiet hx

theorem shapeAnsi_noBracket (n : Nat) : NoBracket (shapeAnsi n) := by
  unfold shapeAnsi
  rw [List.append_assoc]
  refine NoBracket.csi ?_ ?_ (by simp)
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨fun h => (digit_quiet h).1 rfl, by decide, by decide⟩
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨fun h => (digit_quiet h).2 rfl, by decide, by decide⟩

theorem sgrOf_noBracket (codes : List Nat) : NoBracket (sgrOf codes) :=
  params_noBracket (joinSemi_quiet codes) (by decide)

theorem penSgr_noBracket (p : Pen) : NoBracket (penSgr p) := by
  have color : ∀ c isFg, NoBracket (sgrColorSeq c isFg) := by
    intro c isFg
    unfold sgrColorSeq
    split
    · exact NoBracket.nil
    · exact sgrOf_noBracket _
  exact ((sgrOf_noBracket _).append (color _ _)).append (color _ _)

/-- A DEC private mode, set or reset, whose bytes are no bracket and no start of one. -/
theorem modeSet_noBracket (n : Nat) (on : Bool)
    (h :
      ∀ on : Bool,
        ¬syncBegin <+: modeSet n on ∧ ¬syncEnd <+: modeSet n on ∧ ¬modeSet n on <+: syncStem) :
    NoBracket (modeSet n on) := by
  obtain ⟨h1, h2, h3⟩ := h on
  have hr : 0x1B ∉ 0x5B :: 0x3F :: (digits n ++ [if on then 0x68 else 0x6C]) := by
    simp only [List.mem_cons, List.mem_append, not_or]
    refine ⟨by decide, by decide, fun h => (digit_quiet h).1 rfl, ?_⟩
    cases on <;> decide
  exact NoBracket.esc hr h1 h2 h3

/-- The private modes the renderer writes, each set or reset. -/
theorem mode_noBracket (n : Nat) (hn : n ∈ [1, 6, 7, 25, 1000, 1002, 1003, 1004, 1006, 1049, 2004])
    (on : Bool) : NoBracket (modeSet n on) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact modeSet_noBracket _ on (by decide +kernel)

theorem escSeq_noBracket (f : UInt8) (hf : f ≠ 0x1B ∧ f ≠ 0x5B) : NoBracket (escSeq f) := by
  show NoBracket (0x1B :: [f])
  refine NoBracket.esc (by simpa using hf.1.symm) ?_ ?_ ?_
  · rintro ⟨t, h⟩; simp [syncBegin] at h
  · rintro ⟨t, h⟩; simp [syncEnd] at h
  · rintro ⟨t, h⟩
    simp only [syncStem, List.cons_append, List.cons.injEq] at h
    exact hf.2 h.2.1

theorem escCharset_noBracket (i x : UInt8) (hi : i ≠ 0x1B ∧ i ≠ 0x5B) (hx : x ≠ 0x1B) :
    NoBracket (escCharset i x) := by
  show NoBracket (0x1B :: [i, x])
  refine NoBracket.esc ?_ ?_ ?_ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨hi.1.symm, hx.symm⟩
  · rintro ⟨t, h⟩; simp [syncBegin] at h
  · rintro ⟨t, h⟩; simp [syncEnd] at h
  · rintro ⟨t, h⟩
    simp only [syncStem, List.cons_append, List.cons.injEq] at h
    exact hi.2 h.2.1

theorem noEsc_noBracket {b : Bytes} (h : 0x1B ∉ b) : NoBracket b := NoBracket.of_noEsc h

/-- Splits a concatenation of emitters into its pieces and closes each one. -/
macro "no_bracket" : tactic =>
  `(tactic|
    repeat'
      first
      | with_reducible apply NoBracket.append
      | with_reducible apply NoBracket.ite
      | with_reducible exact NoBracket.nil
      | (with_reducible apply csiNum_noBracket); decide
      | (with_reducible apply csiNum2_noBracket); decide
      | (with_reducible apply escSeq_noBracket); decide
      | (with_reducible apply escCharset_noBracket) <;> decide
      | (with_reducible apply mode_noBracket); decide
      | with_reducible apply penSgr_noBracket
      | with_reducible apply shapeAnsi_noBracket
      | (with_reducible apply noEsc_noBracket); decide)

theorem cellText_noBracket (c : Cell) : NoBracket (cellText c) :=
  (NoBracket.of_noEsc (utf8_noEsc c.base)).append (NoBracket.of_noEsc (utf8s_noEsc c.marks))

theorem rowSlot_noBracket (acc : Bytes × Pen × Nat) (c : Cell) (h : NoBracket acc.1) :
    NoBracket (rowSlot acc c).1 := by
  obtain ⟨s, pen, x⟩ := acc
  unfold rowSlot
  dsimp only at h ⊢
  split
  · exact h.append (NoBracket.of_noEsc (utf8s_noEsc _))
  · refine NoBracket.append (NoBracket.ite h (h.append (penSgr_noBracket _))) ?_
    refine NoBracket.ite ?_ (cellText_noBracket c)
    exact
      (((NoBracket.of_noEsc (utf8_noEsc _)).append (csiNum_noBracket _ _ (by decide))).append
            (NoBracket.of_noEsc (utf8s_noEsc _))).append
        (csiNum_noBracket _ _ (by decide))

theorem rowAnsi_noBracket (row : Row) (pen : Pen) : NoBracket (rowAnsi row pen).1 := by
  have fold :
    ∀ (l : List Cell) (acc : Bytes × Pen × Nat),
      NoBracket acc.1 → NoBracket (l.foldl rowSlot acc).1 := by
    intro l
    induction l with
    | nil => exact fun _ h => h
    | cons c cs ih => exact fun acc h => ih _ (rowSlot_noBracket acc c h)
  have h := fold row.toList ([], pen, 0) NoBracket.nil
  rw [Array.foldl_toList] at h
  unfold rowAnsi
  exact h

theorem joinCRLF_noBracket : ∀ {ls : List Bytes}, (∀ l ∈ ls, NoBracket l) → NoBracket (joinCRLF ls)
  | [], _ => NoBracket.nil
  | [l], h => by simpa [joinCRLF] using h l (by simp)
  | l :: m :: ms, h => by
    simp only [joinCRLF]
    exact
      ((h l (by simp)).append (NoBracket.of_noEsc (by decide))).append
        (joinCRLF_noBracket fun x hx => h x (by simp_all))

theorem rowsAnsi_noBracket : ∀ (rows : List Row) (pen : Pen), ∀ l ∈ rowsAnsi rows pen, NoBracket l
  | [], _ => by simp [rowsAnsi]
  | r :: rs, p => by
    intro l hl
    simp only [rowsAnsi, List.mem_cons] at hl
    rcases hl with rfl | hl
    · exact rowAnsi_noBracket r p
    · exact rowsAnsi_noBracket rs _ l hl

theorem gridAnsi_noBracket (grid : Array Row) : NoBracket (gridAnsi grid) := by
  rw [gridAnsi_eq]
  exact
    (csiNum_noBracket 0 0x6D (by decide)).append
      ((NoBracket.esc (by decide) (by decide) (by decide) (by decide) :
            NoBracket (csiB ++ [0x48])).append
        (joinCRLF_noBracket (rowsAnsi_noBracket _ _)))

theorem pendingAnsi_noBracket (cols : Nat) (grid : Array Row) (cur : Cursor) (row : Nat)
    (pen : Pen) : NoBracket (pendingAnsi cols grid cur row pen) := by
  unfold pendingAnsi
  dsimp only
  refine NoBracket.ite ?_ NoBracket.nil
  exact
    (((csiNum2_noBracket _ _ 0x48 (by decide)).append (penSgr_noBracket _)).append
          (cellText_noBracket _)).append
      (penSgr_noBracket _)

theorem parkAnsi_noBracket (cols : Nat) (grid : Array Row) (s : Saved) :
    NoBracket (parkAnsi cols grid s) := by
  unfold parkAnsi
  refine NoBracket.append ?_ (pendingAnsi_noBracket _ _ _ _ _)
  no_bracket

theorem originOffAnsi_noBracket (s : Saved) : NoBracket (originOffAnsi s) := by
  unfold originOffAnsi
  no_bracket

theorem scrollbackAnsi_noBracket (v : Vt) : NoBracket (scrollbackAnsi v) := by
  unfold scrollbackAnsi
  refine
    ((((NoBracket.ite NoBracket.nil ?_).append (csiNum_noBracket 4 0x6C (by decide))).append
          (mode_noBracket 6 (by simp) false)).append
      (mode_noBracket 7 (by simp) true))
  refine
    ((csiNum_noBracket 3 0x4A (by decide)).append (gridAnsi_noBracket _)).append
      (NoBracket.of_noEsc ?_)
  simp only [List.mem_flatten, List.mem_replicate, not_exists, not_and]
  rintro l ⟨-, rfl⟩
  decide

theorem prologueAnsi_noBracket (v : Vt) : NoBracket (prologueAnsi v) := by
  unfold prologueAnsi
  no_bracket

theorem modesAnsi_noBracket (v : Vt) : NoBracket (modesAnsi v) := by
  unfold modesAnsi
  have mouse :
    NoBracket
      (if v.modes.mouse == 1000 || v.modes.mouse == 1002 || v.modes.mouse == 1003 then
        modeSet v.modes.mouse true
      else []) := by
    split
    · rename_i h
      simp only [Bool.or_eq_true, beq_iff_eq] at h
      rcases h with (h | h) | h <;> rw [h] <;> exact mode_noBracket _ (by simp) _
    · exact NoBracket.nil
  repeat'
    first
    | exact mouse
    | with_reducible apply NoBracket.append
    | with_reducible apply NoBracket.ite
    | (with_reducible apply csiNum_noBracket); decide
    | (with_reducible apply csiNum_noBracket); split <;> decide
    | (with_reducible apply escSeq_noBracket); decide
    | (with_reducible apply mode_noBracket); decide
    | with_reducible apply shapeAnsi_noBracket

theorem titleAnsi_noBracket (v : Vt) : NoBracket (titleAnsi v) := by
  unfold titleAnsi
  show NoBracket (0x1B :: (0x5D :: 0x32 :: 0x3B :: (utf8s v.title.toList ++ [0x07])))
  refine NoBracket.esc ?_ ?_ ?_ ?_
  · simp only [List.mem_cons, List.mem_append, not_or]
    exact ⟨by decide, by decide, by decide, utf8s_noEsc _, by decide⟩
  · rintro ⟨t, h⟩; simp [syncBegin] at h
  · rintro ⟨t, h⟩; simp [syncEnd] at h
  · rintro ⟨t, h⟩; simp [syncStem] at h

theorem charsetAnsi_noBracket (v : Vt) : NoBracket (charsetAnsi v) := by
  unfold charsetAnsi
  no_bracket

theorem tabsAnsi_noBracket (v : Vt) : NoBracket (tabsAnsi v) := by
  unfold tabsAnsi
  exact
    (csiNum_noBracket 3 0x67 (by decide)).append
      (NoBracket.flatMap fun _ _ =>
        (csiNum_noBracket _ 0x47 (by decide)).append (escSeq_noBracket 0x48 (by decide)))

theorem cursorAnsi_noBracket (v : Vt) : NoBracket (cursorAnsi v) := by
  unfold cursorAnsi
  no_bracket

theorem cursorPendingAnsi_noBracket (v : Vt) : NoBracket (cursorPendingAnsi v) := by
  unfold cursorPendingAnsi
  refine NoBracket.ite ?_ NoBracket.nil
  refine (NoBracket.append ?_ (charsetAnsi_noBracket v)).append (penSgr_noBracket _)
  refine (NoBracket.append ?_ (csiNum_noBracket _ _ (by split <;> decide)))
  refine (NoBracket.append ?_ (mode_noBracket 7 (by simp) _))
  refine (NoBracket.append ?_ (pendingAnsi_noBracket _ _ _ _ _))
  no_bracket

theorem screensAnsi_noBracket (v : Vt) : NoBracket (screensAnsi v) := by
  unfold screensAnsi
  refine (scrollbackAnsi_noBracket v).append ?_
  split
  · exact gridAnsi_noBracket _
  · exact
      ((((gridAnsi_noBracket _).append (parkAnsi_noBracket _ _ _)).append
                (mode_noBracket 1049 (by simp) true)).append
            (originOffAnsi_noBracket _)).append
        (gridAnsi_noBracket _)

theorem savedAnsi_noBracket (v : Vt) : NoBracket (savedAnsi v) := by
  unfold savedAnsi
  exact
    ((parkAnsi_noBracket _ _ _).append (escSeq_noBracket 0x37 (by decide))).append
      (originOffAnsi_noBracket _)

theorem regionAnsi_noBracket (v : Vt) : NoBracket (regionAnsi v) := by
  unfold regionAnsi
  no_bracket

/-- **A repaint holds no bracket.** Neither `syncBegin` nor `syncEnd` occurs in `restore`, nor
does it end with a start of one. -/
theorem restore_noBracket (v : Vt) : NoBracket (restore v) := by
  unfold restore restoreBody
  refine (NoBracket.append ?_ (cursorPendingAnsi_noBracket v))
  refine (NoBracket.append ?_ (cursorAnsi_noBracket v))
  refine (NoBracket.append ?_ (penSgr_noBracket _))
  refine (NoBracket.append ?_ (charsetAnsi_noBracket v))
  refine (NoBracket.append ?_ (modesAnsi_noBracket v))
  refine (NoBracket.append ?_ (titleAnsi_noBracket v))
  refine (NoBracket.append ?_ (tabsAnsi_noBracket v))
  refine (NoBracket.append ?_ (regionAnsi_noBracket v))
  refine (NoBracket.append ?_ (savedAnsi_noBracket v))
  refine (NoBracket.append ?_ (screensAnsi_noBracket v))
  exact
    ((prologueAnsi_noBracket v).append (csiNum_noBracket 0 0x6D (by decide))).append
      (csiNum_noBracket 2 0x4A (by decide))

/-- **The closing bracket leaves its terminal as it was.** Between control sequences and
characters, `CSI ? 2026 l` resets a mode the emulator does not keep and returns to where it
started. -/
theorem feed_syncEnd {u : Vt} (h : u.atBoundary = true) : u.feed syncEnd = u := by
  have hp : u.pstate = .ground ∧ u.u8need = 0 := by
    unfold Vt.atBoundary at h
    simpa using h
  obtain ⟨hg, hn⟩ := hp
  cases u
  simp only at hg hn
  subst hg hn
  simp [Vt.feed, syncEnd, Vt.step, Vt.abortUtf8, Vt.stepGround, Vt.stepEsc, Vt.stepCsi,
    Vt.csiFinish, Vt.csiDispatch, Vt.setModes, Vt.setMode]

end Terminal.Render
