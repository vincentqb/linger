module

public import Linger.Core.Checkpoint
public import Theorems.Vt
import all Linger.Core.Checkpoint
import all Linger.Core.Vt
-- `Theorems.Vt` for `Good`, and for the three claims about the decoder's door
-- (`ofDecoded_good`, `ofDecoded_of_good`, `ofDecoded_none_of_cols_zero`) — the codec's
-- theorems are stated in terms of it now that `rVt` validates rather than forges
-- (`specs/archive/vt-toolkit.md` Step 2). `import all` because those declarations are
-- module-private, as the `Vt` seal forces.
import all Theorems.Vt

-- Converted from a legacy (non-`module`) file by the `Vt` seal
-- (`specs/archive/vt-toolkit.md` Step 1). Legacy files make every declaration public, and
-- a public statement may not mention a private field — `load_save_exact` mentions
-- three (`pstate`, `u8need`, `u8acc`) and `cases vt` needs the constructor. As a
-- `module` with no `public section`, the declarations are module-private and both
-- are allowed. `Theorems/Resume.lean` reaches in with `import all`.

/-! # §Restore — the reboot-resume codec theorems

THEOREMS.md row: `load (save s) = some s` — exactly, for every state
whose parser is quiescent (which is what checkpoints hold, since the
codec deliberately forgets partial escape sequences); the general form
round-trips modulo `Vt.quiesce`. Totality of `load` on arbitrary bytes
is by construction (`R α = List UInt8 → Option _`, structural
recursion only) — the second half of §Restore needs no theorem.

Every default combinator round-trip is unconditional: `wNat` is LEB128, so
there is no "fits in N bits" side condition anywhere in the format.
Optional count limits are filters on these same decoded values; `rVt_unbounded`
proves that the earlier resource guards preserve the complete decoder's result.

**The `Vt` round trip is not.** `rVt` hands its decoded fields to
`Vt.ofDecoded`, which returns `none` unless they describe a `Good` **and** `Renderable`
state with a ruler the width of the screen (`specs/archive/vt-toolkit.md` Step 2 for the first,
finding R2 for the other two), so `rt_vt` and everything above it carries those three
hypotheses — satisfied by every live session (`load_save_live`), and false of exactly the
records the validation exists to refuse. The two directions are `rVt_good`/`rVt_shape` and
`load_good`/`load_renderable`/`load_tabsOk` (nothing bad is ever decoded, for **any** byte
string) and `load_save_none_of_cols_zero` (the canonical junk record is refused rather than
clamped).
-/

namespace Linger.Core.Checkpoint

open Linger.Core.Vt

/-- "Reader `r` inverts writer `w`, leaving the rest untouched." -/
abbrev RT {α : Type} (w : α → List UInt8) (r : R α) : Prop :=
  ∀ (a : α) (rest : List UInt8), r (w a ++ rest) = some (a, rest)

theorem rt_nat : RT wNat rNat := by
  intro n rest
  induction n using wNat.induct with
  | case1 n h =>
    rw [wNat, dite_eq_left h]
    have hb : (UInt8.ofNat n) < 128 := by
      simp only [UInt8.lt_iff_toNat_lt, UInt8.toNat_ofNat', show (128 : UInt8).toNat = 128 from rfl]
      omega
    simp [rNat, hb, UInt8.toNat_ofNat']
    clear hb
    omega
  | case2 n h ih =>
    rw [wNat, dite_eq_right h]
    have hmod : n % 128 < 128 := Nat.mod_lt _ (by omega)
    have hb : ¬(UInt8.ofNat (128 + n % 128)) < 128 := by
      simp only [UInt8.lt_iff_toNat_lt, UInt8.toNat_ofNat', show (128 : UInt8).toNat = 128 from rfl]
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

theorem rt_pair {α β : Type} {wa : α → List UInt8} {ra : R α} {wb : β → List UInt8} {rb : R β}
    (ha : RT wa ra) (hb : RT wb rb) : RT (wPair wa wb) (rPair ra rb) := by
  intro p rest
  unfold wPair rPair
  simp only [List.append_assoc, ha, hb, Option.bind_eq_bind, Option.bind_some]

theorem rt_opt {α : Type} {w : α → List UInt8} {r : R α} (h : RT w r) : RT (wOpt w) (rOpt r) := by
  intro o rest
  cases o with
  | none => rfl
  | some a =>
    unfold wOpt rOpt
    simp only [List.cons_append, h, Option.bind_eq_bind, Option.bind_some]

theorem rOpt_filter {α : Type} (r : R α) (p : α → Bool) (bytes : List UInt8) :
    rOpt (fun l => (r l).filter (fun out => p out.1)) bytes =
      (rOpt r bytes).filter (fun out => out.1.all p) := by
  cases bytes with
  | nil => rfl
  | cons b bytes =>
    by_cases hz : b = 0
    · subst b; rfl
    · by_cases ho : b = 1
      · subst b
        simp only [rOpt, Option.bind_eq_bind]
        cases hr : r bytes with
        | none => rfl
        | some pair =>
          obtain ⟨x, rest⟩ := pair
          cases hp : p x <;> simp [Option.filter_some, hp]
      · simp [rOpt, hz, ho]

theorem rt_listAux {α : Type} {w : α → List UInt8} {r : R α} (h : RT w r) :
    ∀ (l : List α) (rest : List UInt8),
      rListAux r l.length (l.flatMap w ++ rest) = some (l, rest) := by
  intro l
  induction l with
  | nil =>
    intro rest; rfl
  | cons x xs ih =>
    intro rest
    simp only [List.flatMap_cons, List.length_cons, rListAux, List.append_assoc, h, ih,
      Option.bind_eq_bind, Option.bind_some]

theorem rt_list {α : Type} {w : α → List UInt8} {r : R α} (h : RT w r) :
    RT (wList w) (rList r) := by
  intro l rest
  unfold wList rList
  simp only [List.append_assoc, rt_nat, Option.bind_eq_bind, Option.bind_some]
  exact rt_listAux h l rest

/-- A successful counted read returns exactly the declared number of elements. -/
theorem rListAux_length {α : Type} (r : R α) (n : Nat) {bytes rest : List UInt8} {xs : List α}
    (h : rListAux r n bytes = some (xs, rest)) : xs.length = n := by
  induction n generalizing bytes xs with
  | zero =>
    cases h
    rfl
  | succ n ih =>
    simp only [rListAux, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨x, tail⟩, _, ⟨ys, tail'⟩, hys, he⟩ := h
    cases he
    simp only [List.length_cons, ih hys]

/-- The early count guard changes only acceptance, preserving values and suffixes. -/
theorem rList_bounded {α : Type} (r : R α) (bytes : List UInt8) (limit : Nat) :
    rList r bytes (some limit) = (rList r bytes).filter (fun out => out.1.length ≤ limit) := by
  unfold rList
  cases hn : rNat bytes with
  | none => rfl
  | some p =>
    obtain ⟨n, rest⟩ := p
    simp only [Option.bind_eq_bind, Option.bind_some, Option.all_some, Option.all_none, ite_true,
      decide_eq_true_eq]
    cases hr : rListAux r n rest with
    | none => simp
    | some p =>
      obtain ⟨xs, tail⟩ := p
      simp only [Option.filter_some, rListAux_length r n hr, decide_eq_true_eq]

/-- An excessive declared count is refused regardless of the element reader
or the remaining payload. -/
theorem rList_over_limit {α : Type} (r : R α) {bytes rest : List UInt8} {n limit : Nat}
    (hn : rNat bytes = some (n, rest)) (hlimit : limit < n) :
    rList r bytes (some limit) = none := by simp [rList, hn, Nat.not_le_of_gt hlimit]

/-- Filtering each element reader is equivalent to filtering the decoded list;
neither route changes the decoded values or unread suffix. -/
theorem rListAux_filter {α : Type} (r : R α) (p : α → Bool) (n : Nat) (bytes : List UInt8) :
    rListAux (fun l => (r l).filter (fun out => p out.1)) n bytes =
      (rListAux r n bytes).filter (fun out => out.1.all p) := by
  induction n generalizing bytes with
  | zero => rfl
  | succ n ih =>
    simp only [rListAux, Option.bind_eq_bind]
    cases hr : r bytes with
    | none => rfl
    | some pair =>
      obtain ⟨x, rest⟩ := pair
      simp only [ih]
      cases ht : rListAux r n rest with
      | none => cases hp : p x <;> simp [Option.filter_some, hp, ht]
      | some pair =>
        obtain ⟨xs, tail⟩ := pair
        cases hp : p x <;> cases hps : xs.all p <;> simp [Option.filter_some, hp, hps, ht]

theorem rList_filter {α : Type} (r : R α) (p : α → Bool) (bytes : List UInt8) :
    rList (fun l => (r l).filter (fun out => p out.1)) bytes =
      (rList r bytes).filter (fun out => out.1.all p) := by
  unfold rList
  cases hn : rNat bytes with
  | none => rfl
  | some pair =>
    obtain ⟨n, rest⟩ := pair
    exact rListAux_filter r p n rest

theorem rt_str : RT wStr rStr := by
  intro s rest
  unfold wStr rStr
  simp only [rt_list rt_char, Option.bind_eq_bind, Option.bind_some, String.ofList_toList]

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
  simp only [List.append_assoc, rt_char, rt_list rt_char, rt_nat, rt_pen, Option.bind_eq_bind,
    Option.bind_some]

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
      · simp only [hab, reduceIte, expand, List.replicate, List.singleton_append, ih]

theorem rt_rle {α : Type} [DecidableEq α] {w : α → List UInt8} {r : R α} (h : RT w r) :
    RT (wRLE w) (rRLE r) := by
  intro l rest
  unfold wRLE rRLE
  simp only [rt_list (rt_pair rt_nat h), Option.bind_eq_bind, Option.bind_some, Option.all_none,
    ite_true, expand_runs]

/-- Encoded run counts give exactly the number of expanded elements. -/
theorem expand_length {α : Type} (groups : List (Nat × α)) :
    (expand groups).length = (groups.map Prod.fst).sum := by
  induction groups with
  | nil => rfl
  | cons pair groups ih =>
    obtain ⟨n, x⟩ := pair
    simp [expand, ih]

/-- The sum check precedes expansion, but accepts exactly the expansions within
the limit, including noncanonical and zero-length runs. -/
theorem rRLE_bounded {α : Type} (r : R α) (bytes : List UInt8) (limit : Nat) :
    rRLE r bytes (some limit) = (rRLE r bytes).filter (fun out => out.1.length ≤ limit) := by
  unfold rRLE
  cases hr : rList (rPair rNat r) bytes with
  | none => rfl
  | some pair =>
    obtain ⟨groups, rest⟩ := pair
    simp only [Option.bind_eq_bind, Option.bind_some, Option.all_some, Option.all_none, ite_true,
      Option.filter_some, expand_length]

/-- The combined run count is the rejection boundary; no assumption about
individual runs being positive or maximal is needed. -/
theorem rRLE_over_limit {α : Type} (r : R α) {bytes rest : List UInt8} {groups : List (Nat × α)}
    {limit : Nat} (hg : rList (rPair rNat r) bytes = some (groups, rest))
    (hlimit : limit < (groups.map Prod.fst).sum) : rRLE r bytes (some limit) = none := by
  simp [rRLE, hg, Nat.not_le_of_gt hlimit]

theorem rt_row : RT wRow rRow := by
  intro r rest
  unfold wRow rRow
  simp only [rt_rle rt_cell, Option.bind_eq_bind, Option.bind_some]

theorem rRow_bounded (bytes : List UInt8) (limit : Nat) :
    rRow bytes (some limit) = (rRow bytes).filter (fun out => out.1.size ≤ limit) := by
  unfold rRow
  rw [rRLE_bounded]
  cases hr : rRLE rCell bytes with
  | none => rfl
  | some pair =>
    obtain ⟨cs, rest⟩ := pair
    by_cases h : cs.length ≤ limit <;> simp [Option.filter_some, h]

/-- Both live screen readers enforce the row count and every row's cell budget. -/
theorem rRows_bounded (bytes : List UInt8) (cols rows : Nat) :
    rList (fun l => rRow l (some cols)) bytes (some rows) =
      (rList rRow bytes).filter
        (fun out => out.1.all (fun row => row.size ≤ cols) && out.1.length ≤ rows) := by
  rw [rList_bounded]
  simp only [rRow_bounded]
  rw [rList_filter (fun l => rRow l) (fun row => row.size ≤ cols), Option.filter_filter]

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
  simp only [List.append_assoc, rt_nat, rt_list rt_row, Option.bind_eq_bind, Option.bind_some]

theorem rRing_bounded (bytes : List UInt8) (limit : Nat) :
    rRing bytes (some limit) = (rRing bytes).filter (fun out => out.1.size ≤ limit) := by
  unfold rRing
  cases hn : rNat bytes with
  | none => rfl
  | some pair =>
    obtain ⟨start, rest⟩ := pair
    simp only [Option.bind_eq_bind, Option.bind_some, rList_bounded]
    cases hr : rList rRow rest with
    | none => rfl
    | some pair =>
      obtain ⟨rows, tail⟩ := pair
      by_cases h : rows.length ≤ limit <;> simp [Option.filter_some, Ring.size, h]

theorem rt_alt : RT wAlt rAlt := by
  unfold wAlt rAlt
  apply rt_opt
  intro x rest
  obtain ⟨g, c, p⟩ := x
  simp only [List.append_assoc, rt_list rt_row, rt_cursor, rt_pen, Option.bind_eq_bind,
    Option.bind_some]

theorem rAlt_bounded (bytes : List UInt8) (cols rows : Nat) :
    rAlt bytes (some cols) (some rows) =
      (rAlt bytes).filter
        (fun out =>
          out.1.all
            (fun screen =>
              screen.1.toList.all (fun row => row.size ≤ cols) && screen.1.size ≤ rows)) := by
  unfold rAlt
  rw [← rOpt_filter]
  apply congrArg (fun reader => rOpt reader bytes)
  funext l
  rw [rRows_bounded]
  cases hg : rList rRow l with
  | none => rfl
  | some pair =>
    obtain ⟨grid, rest⟩ := pair
    cases h : grid.all (fun row => row.size ≤ cols) && grid.length ≤ rows <;>
      simp only [Option.filter_some, h, Bool.false_eq_true, ite_false, ite_true,
        Option.bind_eq_bind, Option.bind_none, Option.bind_some] <;>
      cases hc : rCursor rest <;>
      simp only [Option.bind_none, Option.bind_some, Option.filter_none]
    all_goals
      rename_i pair
      obtain ⟨cursor, tail⟩ := pair
      cases hp : rPen tail <;> simp only [Option.bind_none, Option.bind_some, Option.filter_none]
      rename_i pair
      obtain ⟨pen, tail⟩ := pair
      simp only [Option.filter_some, List.size_toArray, h, Bool.false_eq_true, ite_false, ite_true]

/-- Shape validation already entails the cheaper pre-expansion screen budgets. -/
theorem gridOk_bounded {cols rows : Nat} {grid : Array Row} (h : GridOk cols rows grid) :
    (grid.toList.all (fun row => row.size ≤ cols) && grid.size ≤ rows) = true := by
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨List.all_eq_true.mpr ?_, by simp [h.1]⟩
  intro row hr
  obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem (Array.mem_toList_iff.mp hr)
  have hs := (h.2 i).size
  rw [Array.getD, dite_eq_left hi] at hs
  simp only [decide_eq_true_eq]
  exact Nat.le_of_eq hs

/-- Every state accepted by the existing decoder door passes the earlier resource
guards. In particular, no bound on history row widths is inferred here. -/
theorem ofDecoded_bounds {cols rows : Nat} {grid : Array Row} {cursor : Cursor} {pen : Pen}
    {modes : Modes} {top bot : Nat} {tabs : Array Bool} {sb : Ring}
    {alt : Option (Array Row × Cursor × Pen)} {saved : Saved} {title : String}
    {g0 g1 shift bell : Bool} {v : Vt}
    (h :
      Vt.ofDecoded cols rows grid cursor pen modes top bot tabs sb alt saved title g0 g1 shift
          bell =
        some v) :
    (cols != clampDim cols || rows != clampDim rows) = false ∧
      (grid.toList.all (fun row => row.size ≤ cols) && grid.size ≤ rows) = true ∧
      tabs.size ≤ cols ∧
      sb.size ≤ sbCap ∧
      alt.all
          (fun screen => screen.1.toList.all (fun row => row.size ≤ cols) && screen.1.size ≤ rows) =
        true := by
  unfold Vt.ofDecoded at h
  split at h
  · rename_i hok
    simp only [Bool.and_eq_true] at hok
    obtain ⟨hgood, hshape⟩ := hok
    obtain ⟨hc1, hc2, hr1, hr2, -, -, -, -, -, -, hsb, -⟩ := decodedOk_iff.mp hgood
    obtain ⟨hgrid, htabs, halt⟩ := decodedRenderable_iff.mp hshape
    refine ⟨?_, gridOk_bounded hgrid, Nat.le_of_eq htabs, hsb, ?_⟩
    · simp [clampDim, Nat.max_eq_left hc1, Nat.min_eq_left hc2, Nat.max_eq_left hr1,
        Nat.min_eq_left hr2]
    · cases alt with
      | none => rfl
      | some screen =>
        obtain ⟨g, c, p⟩ := screen
        exact gridOk_bounded (halt g c p rfl)
  · contradiction

/-- Moving the existing shape and count rejection before allocation preserves
the result on every byte string, including accepted noncanonical encodings.
The right-hand side is the original unrestricted reader chain. -/
theorem rVt_unbounded (bytes : List UInt8) :
    rVt bytes =
      (do
        let (cols, l) ← rNat bytes
        let (rows, l) ← rNat l
        let (grid, l) ← rList rRow l
        let (cursor, l) ← rCursor l
        let (pen, l) ← rPen l
        let (modes, l) ← rModes l
        let (top, l) ← rNat l
        let (bot, l) ← rNat l
        let (tabs, l) ← rList rBool l
        let (sb, l) ← rRing l
        let (alt, l) ← rAlt l
        let (saved, l) ← rSaved l
        let (title, l) ← rStr l
        let (g0, l) ← rBool l
        let (g1, l) ← rBool l
        let (shift, l) ← rBool l
        let (bell, l) ← rBool l
        let v ←
          Vt.ofDecoded cols rows grid.toArray cursor pen modes top bot tabs.toArray sb alt saved
              title g0 g1 shift bell
        some (v, l)) := by
  unfold rVt
  simp only [rRows_bounded]
  simp only [rList_bounded, rRing_bounded, rAlt_bounded]
  apply Option.ext
  intro out
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff]
  constructor
  · intro h
    obtain ⟨cols, hc, rows, hr, h⟩ := h
    split at h
    · contradiction
    simp only [Option.bind_eq_some_iff, Option.filter_eq_some_iff] at h
    obtain
      ⟨grid, ⟨hg, -⟩, cursor, hcur, pen, hp, modes, hm, top, ht, bot, hb, tabs, ⟨htab, -⟩, sb,
        ⟨hsb, -⟩, alt, ⟨halt, -⟩, saved, hsave, title, htitle, g0, hg0, g1, hg1, shift, hshift,
        bell, hbell, v, hv, he⟩ :=
      h
    exact
      ⟨cols, hc, rows, hr, grid, hg, cursor, hcur, pen, hp, modes, hm, top, ht, bot, hb, tabs, htab,
        sb, hsb, alt, halt, saved, hsave, title, htitle, g0, hg0, g1, hg1, shift, hshift, bell,
        hbell, v, hv, he⟩
  · rintro
      ⟨cols, hc, rows, hr, grid, hg, cursor, hcur, pen, hp, modes, hm, top, ht, bot, hb, tabs, htab,
          sb, hsb, alt, halt, saved, hsave, title, htitle, g0, hg0, g1, hg1, shift, hshift, bell,
          hbell, v, hv, he⟩
    obtain ⟨hdims, hgrid, htabs, hsbcap, haltcap⟩ := ofDecoded_bounds hv
    refine ⟨cols, hc, rows, hr, ?_⟩
    simp only [hdims, Bool.false_eq_true, ite_false]
    simp only [Option.bind_eq_some_iff, Option.filter_eq_some_iff]
    exact
      ⟨grid, ⟨hg, by simpa using hgrid⟩, cursor, hcur, pen, hp, modes, hm, top, ht, bot, hb, tabs,
        ⟨htab, by simpa using htabs⟩, sb, ⟨hsb, by simpa using hsbcap⟩, alt, ⟨halt, haltcap⟩, saved,
        hsave, title, htitle, g0, hg0, g1, hg1, shift, hshift, bell, hbell, v, hv, he⟩

/-- **The fields round-trip unconditionally; acceptance is exactly the smart
constructor's decision.** The earlier resource guards preserve that decision by
`rVt_unbounded`; every default combinator remains an unconditional inverse.

Both of the claims above it read off this one: `rt_vt` by `ofDecoded_of_good`, and
`load_save_none_of_cols_zero` by `ofDecoded_none_of_cols_zero`. -/
theorem rVt_fields (v : Vt) (rest : List UInt8) :
    rVt (wVt v ++ rest) =
      (Vt.ofDecoded v.cols v.rows v.grid v.cursor v.pen v.modes v.top v.bot v.tabs v.sb v.altGrid
            v.saved v.title v.g0Line v.g1Line v.shiftOut v.bell).map
        (fun w => (w, rest)) := by
  rw [rVt_unbounded]
  unfold wVt
  simp only [List.append_assoc, rt_nat, rt_list rt_row, rt_cursor, rt_pen, rt_modes,
    rt_list rt_bool, rt_ring, rt_alt, rt_saved, rt_str, rt_bool, Option.bind_eq_bind,
    Option.bind_some, Array.toArray_toList]
  exact Option.map_eq_bind.symm

/-- The Vt round trip: exact modulo the deliberately-forgotten parser
state, for any state the emulator can actually be in.

`Good` is the hypothesis the smart constructor introduced, and it is not a weakening of
the format: `good_init` plus the `Pres` machinery says every live session satisfies it,
and a state that does not is precisely one a checkpoint must not restore. The old
unconditional statement was true of `cols := 0`, which is the bug.

**`hren` and `htabs` arrived with finding R2** (SCRATCHPAD.md), for the same reason and by
the same mirror: the door now also refuses a record whose grid is not the shape its
dimensions claim, so the round trip is conditional on the *input* being that shape. Same
answer to "is this a weakening" — the unconditional statement was true of a screen
`Render.restore` cannot repaint, which is what `resume_grid` was refuted at. Every live
session satisfies all three (`good_of_liveReachable`, `renderable_of_liveReachable`,
`tabsOk_of_liveReachable`), so `load_save_live` below is the honest reading of the cost. -/
theorem rt_vt (v : Vt) (h : Good v) (hren : Renderable v) (htabs : TabsOk v) (rest : List UInt8) :
    rVt (wVt v ++ rest) = some (v.quiesce, rest) := by
  rw [rVt_fields, ofDecoded_of_good h hren htabs, Option.map_some]

/-- Every accepted byte string reaches the checked constructor and starts with
an empty parser. The reader chain is destructured once here; safety, shape and
reachability below are projections of this acceptance result. -/
theorem rVt_accepted {l : List UInt8} {v : Vt} {rest : List UInt8} (h : rVt l = some (v, rest)) :
    LiveReachableVt v ∧ v.quiesce = v := by
  simp only [rVt, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, -, _, -, h⟩ := h
  split at h
  · contradiction
  simp only [Option.bind_eq_some_iff] at h
  obtain
    ⟨_, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, w,
      hw, he⟩ :=
    h
  simp only [Option.some.injEq, Prod.mk.injEq] at he
  have hlive := LiveReachableVt.ofDecoded hw
  have hquiet : w.quiesce = w := by
    unfold Vt.ofDecoded at hw
    split at hw
    · cases hw; rfl
    · contradiction
  exact he.1 ▸ ⟨hlive, hquiet⟩

/-- **Nothing bad is ever decoded, from any bytes at all.** Not "from bytes `save`
wrote" — from an arbitrary `List UInt8`, which is what a checkpoint file is: the
attacker-controlled input the `Vt` seal could not reach. If `rVt` yields a `Vt`, that
`Vt` is `Good`.

This is the theorem the step is for, and it is the one that makes every
`Good`-hypothesised claim in `Theorems/Render/*` and `Theorems/Resume.lean` reachable
from the resume path rather than merely stated. -/
theorem rVt_good {l : List UInt8} {v : Vt} {rest : List UInt8} (h : rVt l = some (v, rest)) :
    Good v := good_of_liveReachable (rVt_accepted h).1

/-- **…and nothing the emitter cannot repaint, either — finding R2.** The other half of
"nothing bad is ever decoded", from an arbitrary `List UInt8`: if `rVt` yields a `Vt`, that
`Vt`'s grid has exactly `rows` rows of exactly `cols` cells, every cell holds an emittable
base of the width it claims, every wide glyph keeps its shadow, the stashed alt screen is
the same shape, and the tab ruler is the width of the screen.

`Good` implied none of that — `decodedOk` was never passed the grid — and the gap was
observable: a real checkpoint with its `rows` byte flipped decoded to a screen whose replay
is not the screen it came from. Both properties follow from the accepted state in
`rVt_accepted`, and are projected by `load_renderable` and `load_tabsOk` below. -/
theorem rVt_shape {l : List UInt8} {v : Vt} {rest : List UInt8} (h : rVt l = some (v, rest)) :
    Renderable v ∧ TabsOk v := by
  have hlive := (rVt_accepted h).1
  exact ⟨renderable_of_liveReachable hlive, tabsOk_of_liveReachable hlive⟩

/-- **…and it is a state a live session can hold** — the third and strongest reading of
"nothing bad is ever decoded", from an arbitrary `List UInt8`. Not merely `Good` (Step 2),
not merely `Good ∧ Renderable ∧ TabsOk` (finding R2): a member of the *closure* the replay
theorems are stated over, so a decoded screen is admissible wherever a fed-and-resized one
is.

This is `LiveReachableVt`'s `ofDecoded` rung reached through the readers, and it is the
claim the rung exists for. Before it, `Theorems/Session.lean` could lift the shape
invariant to the daemon only for a session booted from `Vt.init`; `load_live` below carries
it to the resume path, where `Session.liveVt_boot_of_load` closes the gap in one step.

The rung is sound only because the *door* decides all four components — R2 is what made
this provable, and a rung premised on `Good v` instead was measured unsound (§LiveReachable
in `Theorems/Vt.lean`). -/
theorem rVt_live {l : List UInt8} {v : Vt} {rest : List UInt8} (h : rVt l = some (v, rest)) :
    LiveReachableVt v := (rVt_accepted h).1

/-! ### The format tag, as a named stage

`stripMagic` is the tag check, named rather than inlined; `load_save` and `save_tag` both
go through it instead of unfolding the decision into the parser chain. -/

theorem stripMagic_magic (p : List UInt8) : stripMagic (magic ++ p) = some p := by
  unfold stripMagic
  rw [List.take_append_of_le_length (by simp [magic]), List.take_of_length_le (by simp [magic]),
    List.drop_append_of_le_length (by simp [magic]), List.drop_of_length_le (by simp [magic]),
    List.nil_append]
  rw [ite_eq_left (rfl : magic = magic)]

/-- Acceptance at the file boundary preserves the checked state and parser
reset established by `rVt`. This applies to any bytes, including encodings that
were not produced by `save`. -/
theorem load_accepted {l : List UInt8} {c : Ckpt} (h : load l = some c) :
    LiveReachableVt c.vt ∧ c.vt.quiesce = c.vt := by
  simp only [load, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, -, ⟨vt, _⟩, hvt, _, -, _, -, h⟩ := h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    exact rVt_accepted hvt
  · exact absurd h (by simp)

/-- **The top-level no-forge claim**, and the one the runtime is entitled to lean on: a
checkpoint that loads at all loads to a `Good` screen. `Linger/Runtime/Daemon.lean`'s
resume path cites this for why the `clampDim` it still calls before `spawnPty` cannot
change the value it is given. -/
theorem load_good {l : List UInt8} {c : Ckpt} (h : load l = some c) : Good c.vt :=
  good_of_liveReachable (load_accepted h).1

/-- **The top-level shape claim, for any byte string — finding R2's payoff.** A checkpoint
that loads at all loads to a screen the emitter can reproduce and a ruler the width of that
screen. One destructuring of `load`, projected by the two claims below.

This is what makes the §Replay theorems reachable from the *resume path* rather than merely
stated over a hypothesis: `Theorems/Resume.lean`'s `resume_grid_of_load` /
`resume_tabs_of_load` / `resume_sb_of_load` need no hypothesis at all beyond
`load l = some c`, where their `save`-side twins must ask for `Renderable` because their
subject is `save`'s input. -/
theorem load_shape {l : List UInt8} {c : Ckpt} (h : load l = some c) :
    Renderable c.vt ∧ TabsOk c.vt := by
  have hlive := (load_accepted h).1
  exact ⟨renderable_of_liveReachable hlive, tabsOk_of_liveReachable hlive⟩

/-- **The twin of `load_good`**: every byte string `load` accepts decodes to a `Renderable`
screen. Named as its own claim because that is the property `Render.restore`'s theorems ask
for, and because before R2 it was false — refutably, from one flipped byte of a real
checkpoint. -/
theorem load_renderable {l : List UInt8} {c : Ckpt} (h : load l = some c) : Renderable c.vt :=
  (load_shape h).1

/-- …and the ruler, which `Renderable` does not carry (`Render.restore_tabs_any`'s
`hvtabs`, `Resume.resume_tabs`'s). Before R2 a checkpoint could name a ruler of any length
at all. -/
theorem load_tabsOk {l : List UInt8} {c : Ckpt} (h : load l = some c) : TabsOk c.vt :=
  (load_shape h).2

/-- **The top-level reachability claim: a checkpoint that loads loads to a state a live
session can hold.** Strictly stronger than `load_good`, `load_renderable` and `load_tabsOk`
together — those three are its projections (`good_of_liveReachable` and siblings), and it
additionally puts the decoded screen inside the closure every `Render.restore_*_reachable`
theorem quantifies over.

The one-line consequence worth naming: `Theorems/Session.lean`'s `LiveVt` is now provable
for a **resumed** daemon (`Session.liveVt_boot_of_load`), so `Session.run_vt_renderable` and
the shape claims beneath it stop being about fresh boots only. That is the whole reason the
`ofDecoded` rung was added; this theorem is the bridge.

`load_save_live` below still asks for `LiveReachableVt c.vt` rather than `load l = some c`
on purpose: its subject is `save`'s **input**, the state the daemon holds, which reaches
the decoder only through `load_save`'s own conclusion (the circularity SCRATCHPAD.md
measured). `load_live` is the tool for the other direction — `load`'s output. -/
theorem load_live {l : List UInt8} {c : Ckpt} (h : load l = some c) : LiveReachableVt c.vt :=
  (load_accepted h).1

/-- A decoded parser has no partial escape or UTF-8 character to carry into the
new session. Being between poll rounds does not imply this for the live source;
the reset is a deliberate property of the checkpoint format. -/
theorem load_quiescent {l : List UInt8} {c : Ckpt} (h : load l = some c) :
    c.vt.pstate = .ground ∧ c.vt.u8need = 0 ∧ c.vt.u8acc = 0 := by
  have hq := (load_accepted h).2
  exact ⟨congrArg Vt.pstate hq |>.symm, congrArg Vt.u8need hq |>.symm, congrArg Vt.u8acc hq |>.symm⟩

/-- The reader consumes a complete checkpoint, rejecting every nonempty suffix
after a valid saved record. This also rules out silently accepting concatenated
checkpoints. All parser combinators must preserve their unread suffix for this
claim to reach the final consumption check. -/
theorem load_save_append (c : Ckpt) (h : Good c.vt) (hren : Renderable c.vt) (htabs : TabsOk c.vt)
    (rest : List UInt8) :
    load (save c ++ rest) = if rest = [] then some { c with vt := c.vt.quiesce } else none := by
  unfold load save
  simp only [List.append_assoc]
  rw [stripMagic_magic]
  simp only [rt_vt _ h hren htabs, rt_str, rt_list (rt_pair rt_str rt_str), Option.bind_eq_bind,
    Option.bind_some]
  cases rest <;> rfl

/-- §Restore, top level: a checkpoint written by `save` loads back to
exactly what was saved, with parser state quiesced. A live source can be
mid-escape or mid-character even between poll rounds. `load_good` and
`load_renderable` establish the shape of every accepted record; they do not
require a canonical encoding or put a resource bound on decoding rejected bytes.

Three hypotheses, all of them the decoder's acceptance seen from this side (`rt_vt`):
`Good` since Step 2, `Renderable` and `TabsOk` since R2. `load_save_live` below is the same
claim with all three discharged from reachability, which is the answer to "what does this
cost a real session". -/
theorem load_save (c : Ckpt) (h : Good c.vt) (hren : Renderable c.vt) (htabs : TabsOk c.vt) :
    load (save c) = some { c with vt := c.vt.quiesce } := by
  simpa using load_save_append c h hren htabs []

/-- **What the three hypotheses cost a real session: nothing.** Every state a live session
can hold is `LiveReachableVt`, and that discharges `Good`, `Renderable` and `TabsOk` at
once. Stated because R2 added two binders to `load_save` and a reader is entitled to see,
in one place, that the checkpoint every daemon writes still loads — the alternative is
three lemma names in a docstring and a reader taking them on trust. -/
theorem load_save_live (c : Ckpt) (h : LiveReachableVt c.vt) :
    load (save c) = some { c with vt := c.vt.quiesce } :=
  load_save c (good_of_liveReachable h) (renderable_of_liveReachable h) (tabsOk_of_liveReachable h)

/-- Loading, saving and loading an accepted checkpoint again is exact, including
cwd and labels. Its parser is already quiescent, so subsequent checkpoints do not
lose any further state. This does not assert that the original bytes were a
canonical encoding. -/
theorem load_resave {l : List UInt8} {c : Ckpt} (h : load l = some c) : load (save c) = some c := by
  rw [load_save_live c (load_accepted h).1, (load_accepted h).2]

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
  rw [List.take_append_of_le_length (by simp [magic]), List.take_of_length_le (by simp [magic])]

/-- And when the parser is already quiescent, the round-trip is exact
— the letter of the THEOREMS.md row. `hren`/`htabs` are `load_save`'s, hence
`ofDecoded_of_good`'s; see there for why they are not a weakening. -/
theorem load_save_exact (c : Ckpt) (hg : Good c.vt) (hren : Renderable c.vt) (htabs : TabsOk c.vt)
    (h : c.vt.pstate = .ground) (h8 : c.vt.u8need = 0) (ha : c.vt.u8acc = 0) :
    load (save c) = some c := by
  rw [load_save c hg hren htabs]
  congr 1
  cases c with
  | mk vt cwd labels =>
    simp only [Ckpt.mk.injEq, and_true]
    cases vt
    simp_all [Vt.quiesce]

/-- **Junk dimensions are refused, not clamped** — the behaviour change of
`specs/archive/vt-toolkit.md` Step 2, stated at the top level rather than only fixtured.
`cols = 0` is the canonical corrupt value: no live session can hold it, `Good` is false
of it, and a decoder that accepted it would hand `Render.restore` a screen every one of
its theorems is vacuous at.

The `Ckpt` here is a *forged* one — a `Vt` no `init`/`resize`/`feed` path produces, which
is reachable in this file only because the seal's friend import is. That is the point:
the record on disk is the one input an attacker controls, and `save` of such a state is
byte-for-byte what a hostile file looks like. -/
theorem load_save_none_of_cols_zero (c : Ckpt) (h : c.vt.cols = 0) : load (save c) = none := by
  unfold load save
  simp only [List.append_assoc]
  rw [stripMagic_magic]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [rVt_fields, h, ofDecoded_none_of_cols_zero]
  rfl

end Linger.Core.Checkpoint
