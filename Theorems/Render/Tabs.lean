module

public import Theorems.Render.Grid
import all Linger.Core.Render
import all Linger.Core.Vt
import all Theorems.Render.Grid

public section

/-! # §Replay, the tab ruler

`Fixes π` — one stream predicate for any projection, the generalization `Keeps` and
`MMap id` are instances of — and the tab-ruler ladder built on it:
`restore_tabs_any`. Split out of `Theorems/Render.lean`. -/

namespace Linger.Core.Render

open Linger.Core.Vt

/-! ## `Fixes` — one stream predicate, any projection

`Keeps` (the grid), `MMap id` (the modes) and the tab-ruler family below are the
same predicate three times with a different field in the hole: *from ground, this
stream returns to ground with nothing half-decoded and leaves the field alone.*
This is that predicate with the field as a parameter, so the **plumbing** — the
`nil`/`append` laws and how a `CSI`/`OSC` construct decomposes — is written once
and each field supplies only the facts about its own dispatch.

`Keeps bs` *is* `Fixes (·.grid) bs` and `MMap id bs` *is* `Fixes (·.modes) bs`,
definitionally (`keeps_eq_fixes`). Collapsing them onto this layer is a mechanical
re-point of their call sites rather than a new proof; it is not done here because
those call sites carry the A1/A5 grid claims, and the same honesty applies as to
the third copy of the CSI walk that `csi_tail_proj` describes: file order and risk,
not the shape of the hypothesis, is why the copies survive.

The cheap constituents (`ESC x`, `ESC ( x`, `SO`) are *not* generalized: each is
eight lines of case analysis whose only field-dependent step is one `rfl`, and the
byte sets differ per field — `ESC H` (HTS) writes the ruler but no cell, so the
grid admits it and the ruler must not. Generalizing where generalization pays. -/
def Fixes {α : Type} (π : Vt → α) (bs : Bytes) : Prop :=
  ∀ v : Vt, v.pstate = .ground → v.u8need = 0 →
    ((v.feed bs).pstate = .ground ∧ (v.feed bs).u8need = 0 ∧ π (v.feed bs) = π v)

theorem Fixes.nil {α : Type} (π : Vt → α) : Fixes π [] := fun _ hg hu => ⟨hg, hu, rfl⟩

theorem Fixes.append {α : Type} {π : Vt → α} {a b : Bytes}
    (ha : Fixes π a) (hb : Fixes π b) : Fixes π (a ++ b) := by
  intro v hg hu
  rw [show v.feed (a ++ b) = (v.feed a).feed b from by simp [Vt.feed, List.foldl_append]]
  obtain ⟨h1, h2, h3⟩ := ha v hg hu
  obtain ⟨h4, h5, h6⟩ := hb _ h1 h2
  exact ⟨h4, h5, h6.trans h3⟩

theorem Fixes.streamPred {α : Type} (π : Vt → α) : StreamPred (Fixes π) :=
  ⟨Fixes.nil π, fun ha hb => Fixes.append ha hb⟩

/-- `Keeps` is this predicate at the grid — stated so the duplication is recorded
in the file rather than only in a comment. -/
theorem keeps_eq_fixes (bs : Bytes) : Keeps bs ↔ Fixes (fun v : Vt => v.grid) bs := Iff.rfl

/-- The CSI walk, for any projection: `csi_tail_proj` does the work, this adds the
`ESC [` opener. -/
theorem fixes_csi_seq {α : Type} {π : Vt → α} (hb : PsBlind π)
    (params : Bytes) (final : UInt8) (hp : ParamBytes params)
    (h1 : 0x40 ≤ final) (h2 : final ≤ 0x7E)
    (hπ : ∀ (w : Vt) (t : CsiState), π (w.csiDispatch t final) = π w) :
    Fixes π (csiB ++ params ++ [final]) := by
  intro v hg hu
  rw [show (csiB ++ params ++ [final] : Bytes) = [0x1B, 0x5B] ++ (params ++ [final]) from by
    unfold csiB; simp]
  rw [show ∀ (w : Vt), w.feed ([0x1B, 0x5B] ++ (params ++ [final]))
      = (w.feed [0x1B, 0x5B]).feed (params ++ [final]) from
    fun w => by simp [Vt.feed, List.foldl_append]]
  rw [keeps_csi_open hg hu]
  obtain ⟨hπ', hp', hu'⟩ := csi_tail_proj hb params final hp h1 h2 hπ
    (v := { v with pstate := .csi {} }) rfl (by simpa using hu) rfl
  exact ⟨hp', hu', by rw [hπ', hb v (PState.csi {})]⟩

/-- The private form (`CSI ? n h/l`), which is what a mode replay is made of. -/
theorem fixes_csi_priv_seq {α : Type} {π : Vt → α} (hb : PsBlind π)
    (params : Bytes) (final : UInt8) (hp : ParamBytes params)
    (h1 : 0x40 ≤ final) (h2 : final ≤ 0x7E)
    (hπ : ∀ (w : Vt) (t : CsiState), π (w.csiDispatch t final) = π w) :
    Fixes π (csiB ++ ([0x3F] ++ params) ++ [final]) := by
  intro v hg hu
  rw [show (csiB ++ ([0x3F] ++ params) ++ [final] : Bytes)
      = [0x1B, 0x5B, 0x3F] ++ (params ++ [final]) from by unfold csiB; simp]
  rw [show ∀ (w : Vt), w.feed ([0x1B, 0x5B, 0x3F] ++ (params ++ [final]))
      = (w.feed [0x1B, 0x5B, 0x3F]).feed (params ++ [final]) from
    fun w => by simp [Vt.feed, List.foldl_append]]
  rw [csi_priv_open_eq hg hu]
  obtain ⟨hπ', hp', hu'⟩ := csi_tail_proj hb params final hp h1 h2 hπ
    (v := { v with pstate := .csi ({ priv := 0x3F } : CsiState) }) rfl (by simpa using hu) rfl
  exact ⟨hp', hu', by rw [hπ', hb v (PState.csi ({ priv := 0x3F } : CsiState))]⟩

theorem fixes_csiNum {α : Type} {π : Vt → α} (hb : PsBlind π) (n : Nat) (final : UInt8)
    (h1 : 0x40 ≤ final) (h2 : final ≤ 0x7E)
    (hπ : ∀ (w : Vt) (t : CsiState), π (w.csiDispatch t final) = π w) :
    Fixes π (csiNum n final) :=
  fixes_csi_seq hb _ _ (paramBytes_digits n) h1 h2 hπ

theorem fixes_csiNum2 {α : Type} {π : Vt → α} (hb : PsBlind π) (a b : Nat) (final : UInt8)
    (h1 : 0x40 ≤ final) (h2 : final ≤ 0x7E)
    (hπ : ∀ (w : Vt) (t : CsiState), π (w.csiDispatch t final) = π w) :
    Fixes π (csiNum2 a b final) := by
  rw [show csiNum2 a b final = csiB ++ (digits a ++ [0x3B] ++ digits b) ++ [final] from by
    unfold csiNum2; simp]
  refine fixes_csi_seq hb _ _ (fun x hx => ?_) h1 h2 hπ
  rcases List.mem_append.mp hx with hx' | hx'
  · rcases List.mem_append.mp hx' with hx'' | hx''
    · exact paramBytes_digits a x hx''
    · rw [show x = 0x3B from by simpa using hx'']
      exact ⟨by decide, by decide⟩
  · exact paramBytes_digits b x hx'

theorem fixes_csiPriv {α : Type} {π : Vt → α} (hb : PsBlind π) (n : Nat) (final : UInt8)
    (h1 : 0x40 ≤ final) (h2 : final ≤ 0x7E)
    (hπ : ∀ (w : Vt) (t : CsiState), π (w.csiDispatch t final) = π w) :
    Fixes π (csiPriv n final) := by
  rw [show csiPriv n final = csiB ++ ([0x3F] ++ digits n) ++ [final] from by
    unfold csiPriv; simp]
  exact fixes_csi_priv_seq hb _ _ (paramBytes_digits n) h1 h2 hπ

theorem fixes_sgrOf {α : Type} {π : Vt → α} (hb : PsBlind π) (codes : List Nat)
    (hπ : ∀ (w : Vt) (t : CsiState), π (w.csiDispatch t 0x6D) = π w) :
    Fixes π (sgrOf codes) := by
  unfold sgrOf
  exact fixes_csi_seq hb _ _ (paramBytes_joinSemi codes) (by decide) (by decide) hπ

theorem fixes_sgrColorSeq {α : Type} {π : Vt → α} (hb : PsBlind π) (c : Color) (isFg : Bool)
    (hπ : ∀ (w : Vt) (t : CsiState), π (w.csiDispatch t 0x6D) = π w) :
    Fixes π (sgrColorSeq c isFg) := by
  unfold sgrColorSeq
  split
  · exact Fixes.nil π
  · exact fixes_sgrOf hb _ hπ

theorem fixes_penSgr {α : Type} {π : Vt → α} (hb : PsBlind π) (p : Pen)
    (hπ : ∀ (w : Vt) (t : CsiState), π (w.csiDispatch t 0x6D) = π w) :
    Fixes π (penSgr p) := by
  unfold penSgr
  exact ((fixes_sgrOf hb _ hπ).append (fixes_sgrColorSeq hb _ _ hπ)).append
    (fixes_sgrColorSeq hb _ _ hπ)

/-- The OSC walk, for any projection: `ESC ] 2 ;` opens the string, the scrubbed
payload accumulates without dispatching, `BEL` finishes. The only field-dependent
step is what `oscFinish` does, and `frame_oscFinish` says it moves `pstate` and
`title` and nothing else. -/
theorem fixes_osc {α : Type} {π : Vt → α} (hb : PsBlind π) (payload : List Char)
    (hπ : ∀ (w : Vt) (acc : Array UInt8), π (w.oscFinish acc) = π w) :
    Fixes π (escB ++ [0x5D, 0x32, 0x3B] ++ utf8s payload ++ [0x07]) := by
  intro v hg hu
  rw [show (escB ++ [0x5D, 0x32, 0x3B] ++ utf8s payload ++ [0x07] : Bytes)
      = [0x1B] ++ ([0x5D] ++ ([0x32, 0x3B] ++ (utf8s payload ++ [0x07]))) from by
    simp [escB]]
  rw [show ∀ (w : Vt), w.feed ([0x1B] ++ ([0x5D] ++ ([0x32, 0x3B]
        ++ (utf8s payload ++ [0x07]))))
      = ((((w.step 0x1B).step 0x5D).feed [0x32, 0x3B]).feed (utf8s payload)).step 0x07 from
    fun w => by simp [Vt.feed, List.foldl_append]]
  rw [esc_step_eq hg hu]
  rw [show ({ v with pstate := .esc } : Vt).step 0x5D
      = { v with pstate := .osc #[] false } from by
    rw [step_of_esc_quiet 0x5D rfl (by simpa using hu)]
    unfold Vt.stepEsc
    rfl]
  obtain ⟨acc1, h1⟩ := osc_accum_run [0x32, 0x3B]
    (v := { v with pstate := .osc #[] false }) (acc := #[]) rfl (by simpa using hu)
    (by intro b hb; rcases List.mem_cons.mp hb with h | h
        · subst h; exact ⟨by decide, by decide⟩
        · rw [show b = 0x3B from by simpa using h]; exact ⟨by decide, by decide⟩)
  rw [h1]
  obtain ⟨acc2, h2⟩ := osc_accum_run (utf8s payload)
    (v := { v with pstate := .osc acc1 false }) (acc := acc1) rfl (by simpa using hu)
    (by intro b hb
        obtain ⟨hge, hne⟩ := utf8s_no_ctl payload b hb
        refine ⟨?_, ?_⟩
        · intro he; rw [he] at hge; exact absurd hge (by decide)
        · intro he; rw [he] at hge; exact absurd hge (by decide))
  rw [h2]
  rw [step_of_osc_quiet (0x07 : UInt8) rfl (by simpa using hu)]
  unfold Vt.stepOsc
  rw [ite_eq_right (by decide), ite_eq_left (by decide)]
  exact ⟨ps_oscFinish' _ _, by rw [un_oscFinish']; simpa using hu,
    by rw [hπ, hb v (PState.osc acc2 false)]⟩

/-! ## §Replay, the tab ruler — `restore_tabs_any`

The last restored field whose claim was carried by fixtures alone (with the window
title and the DECSC slot). The *fix* landed earlier — `tabsAnsi` emits the ruler
unconditionally, because a client is not a reset terminal and nothing else in a
restore stream clears a tab stop — and this is the theorem that fix made provable:
as the code stood before it, `restore_tabs_any` would have been **false**.

`tabs` is an `Array Bool` of size `cols`, not a scalar, so it does not fold into
`stick`; the shape is therefore array equality via size-and-pointwise (`Array.ext`,
the same route `grid_eq_of_cells` takes) rather than a transform algebra. And it
needs no transform algebra: the only transform in the stream is inside `tabsAnsi`
itself, so a *preservation* predicate (`Fixes (·.tabs)`) plus one fold lemma is the
whole story. -/

theorem psBlind_tabs : PsBlind (fun v : Vt => v.tabs) := fun _ _ => rfl

/-! ### The ruler is untouched by everything the tail emits

`Vt.tabs` moves only under `TBC` (a CSI `g`), `HTS` (an **ESC** `H`), `RIS` and
`Vt.resize`. The tail after `tabsAnsi` emits none of them — note that `0x48` is
`HTS` only as an *ESC* final; as a CSI final it is `CUP`, which is why `savedAnsi`
and `cursorAnsi` are safe. That distinction is load-bearing: the existing
`keeps_escSeq` admits `0x48` (HTS writes no *cell*), and copying its byte list
verbatim here would give a **false** lemma. -/

theorem tabs_csiDispatch_cup (v : Vt) (s : CsiState) :
    (v.csiDispatch s 0x48).tabs = v.tabs := by
  by_cases hi : s.ignore = true
  · simp [Vt.csiDispatch, hi]
  · unfold Vt.csiDispatch
    rw [ite_eq_right hi]
    show (v.moveTo (s.arg 1 1 - 1) (s.arg 0 1 - 1)).tabs = v.tabs
    rw [frame_moveTo]

theorem tabs_csiDispatch_sgr (v : Vt) (s : CsiState) :
    (v.csiDispatch s 0x6D).tabs = v.tabs := by
  by_cases hi : s.ignore = true
  · simp [Vt.csiDispatch, hi]
  · unfold Vt.csiDispatch
    rw [ite_eq_right hi]
    show (if s.priv == 0 then v.applySgr s.sgrParams else v).tabs = v.tabs
    split
    · rw [frame_applySgr]
    · rfl

/-- **A mode set never touches the ruler** — unconditionally, for any mode number.
`setMode`'s only non-`modes` arms are `enterAlt`/`leaveAlt`/`moveTo`/the DECSC slot,
and none of them writes `tabs`. This is where the ruler's claim is *simpler* than
the grid's: `keeps_modeSet` has to exclude `47`/`1047`/`1049` (they swap the grid)
and therefore needs the digit bridge to identify the emitted number with the parsed
one, and `restore_modes_any` needs the mouse allowlist. The ruler needs neither. -/
theorem tabs_moveTo (v : Vt) (x y : Nat) : (v.moveTo x y).tabs = v.tabs := by
  rw [frame_moveTo]

theorem tabs_enterAlt (v : Vt) (s : Bool) : (v.enterAlt s).tabs = v.tabs := by
  rw [frame_enterAlt]

theorem tabs_leaveAlt (v : Vt) (s : Bool) : (v.leaveAlt s).tabs = v.tabs := by
  rw [frame_leaveAlt]

theorem tabs_setMode (v : Vt) (priv : Bool) (n : Nat) (on : Bool) :
    (v.setMode priv n on).tabs = v.tabs := by
  unfold Vt.setMode
  repeat' split
  all_goals try simp only [tabs_moveTo, tabs_enterAlt, tabs_leaveAlt]
  all_goals rfl

theorem tabs_csiDispatch_sm (v : Vt) (s : CsiState) :
    (v.csiDispatch s 0x68).tabs = v.tabs := by
  by_cases hi : s.ignore = true
  · simp [Vt.csiDispatch, hi]
  · unfold Vt.csiDispatch
    rw [ite_eq_right hi]
    show (v.setMode (s.priv == 0x3F) (s.arg 0 0) true).tabs = v.tabs
    rw [tabs_setMode]

theorem tabs_csiDispatch_rm (v : Vt) (s : CsiState) :
    (v.csiDispatch s 0x6C).tabs = v.tabs := by
  by_cases hi : s.ignore = true
  · simp [Vt.csiDispatch, hi]
  · unfold Vt.csiDispatch
    rw [ite_eq_right hi]
    show (v.setMode (s.priv == 0x3F) (s.arg 0 0) false).tabs = v.tabs
    rw [tabs_setMode]

theorem tabs_oscFinish (v : Vt) (acc : Array UInt8) : (v.oscFinish acc).tabs = v.tabs := by
  rw [frame_oscFinish]

/-- `ESC x` for the singles the tail emits. **`0x48` is deliberately absent**: as an
ESC final it is `HTS`, which sets a stop at the cursor — the one escape in this
family that moves the ruler. `0x63` (`RIS`) is absent for the same reason, and no
linger stream emits it anyway. -/
theorem fixes_tabs_escSeq (b : UInt8) (hb : b = 0x37 ∨ b = 0x3D ∨ b = 0x3E ∨ b = 0x5C) :
    Fixes (fun v : Vt => v.tabs) (escSeq b) := by
  intro v hg hu
  rw [show escSeq b = [0x1B] ++ [b] from rfl]
  rw [show ∀ (w : Vt), w.feed ([0x1B] ++ [b]) = (w.step 0x1B).step b from
    fun w => by simp [Vt.feed]]
  rw [esc_step_eq hg hu, step_of_esc_quiet b rfl (by simpa using hu)]
  rcases hb with h | h | h | h <;> subst h <;> show _ ∧ _ ∧ _ <;> unfold Vt.stepEsc <;>
    exact ⟨rfl, by simpa using hu, rfl⟩

theorem fixes_tabs_escCharset (i x : UInt8) (hi : i = 0x28 ∨ i = 0x29) :
    Fixes (fun v : Vt => v.tabs) (escCharset i x) := by
  intro v hg hu
  rw [show escCharset i x = [0x1B] ++ [i, x] from rfl]
  rw [show ∀ (w : Vt), w.feed ([0x1B] ++ [i, x]) = ((w.step 0x1B).step i).step x from
    fun w => by simp [Vt.feed]]
  rw [esc_step_eq hg hu]
  have hinter : ({ v with pstate := .esc } : Vt).step i
      = { v with pstate := .escInter i } := by
    rw [step_of_esc_quiet i rfl (by simpa using hu)]
    unfold Vt.stepEsc
    rcases hi with h | h
    · subst h; rfl
    · subst h; rfl
  rw [hinter, step_of_escInter_quiet x rfl (by simpa using hu)]
  show _ ∧ _ ∧ _
  unfold Vt.stepEscInter
  dsimp only
  repeat' split
  all_goals exact ⟨rfl, by simpa using hu, rfl⟩

theorem fixes_tabs_shiftOut : Fixes (fun v : Vt => v.tabs) [0x0E] := by
  intro v hg hu
  rw [show ∀ (w : Vt), w.feed [(0x0E : UInt8)] = w.step 0x0E from fun _ => rfl]
  rw [step_of_ground_quiet (0x0E : UInt8) hg hu]
  show _ ∧ _ ∧ _
  unfold Vt.stepGround
  rw [ite_eq_right (by decide), ite_eq_left (by decide)]
  unfold Vt.ctl
  exact ⟨hg, by simpa using hu, rfl⟩

/-- A mode set (`CSI ? n h/l`) leaves the ruler alone for **any** `n`. Contrast
`keeps_modeSet`, which needs the digit bridge to know `n ∉ {47, 1047, 1049}`. -/
theorem fixes_tabs_modeSet (n : Nat) (on : Bool) :
    Fixes (fun v : Vt => v.tabs) (modeSet n on) := by
  unfold modeSet
  cases on
  · exact fixes_csiPriv psBlind_tabs n 0x6C (by decide) (by decide) tabs_csiDispatch_rm
  · exact fixes_csiPriv psBlind_tabs n 0x68 (by decide) (by decide) tabs_csiDispatch_sm

theorem fixes_tabs_irm (on : Bool) :
    Fixes (fun v : Vt => v.tabs) (csiNum 4 (if on then 0x68 else 0x6C)) := by
  cases on
  · exact fixes_csiNum psBlind_tabs 4 0x6C (by decide) (by decide) tabs_csiDispatch_rm
  · exact fixes_csiNum psBlind_tabs 4 0x68 (by decide) (by decide) tabs_csiDispatch_sm

/-- **The mode replay leaves the ruler alone**, with no allowlist and no digit
bridge — `tabs_setMode` holds for every mode number, so every branch is the same
one-liner. -/
theorem fixes_tabs_modesAnsi (v : Vt) : Fixes (fun v : Vt => v.tabs) (modesAnsi v) := by
  unfold modesAnsi
  refine Fixes.append ?_ (fixes_tabs_irm v.modes.insert)
  refine Fixes.append ?_ (fixes_tabs_modeSet 6 _)
  refine Fixes.append ?_ (fixes_tabs_modeSet 1004 _)
  refine Fixes.append ?_ (fixes_tabs_modeSet 1006 _)
  refine Fixes.append ?_ ((Fixes.streamPred _).ite
    (fun _ => fixes_tabs_modeSet v.modes.mouse true) (fun _ => Fixes.nil _))
  refine Fixes.append ?_ (fixes_tabs_modeSet 1003 false)
  refine Fixes.append ?_ (fixes_tabs_modeSet 1002 false)
  refine Fixes.append ?_ (fixes_tabs_modeSet 1000 false)
  refine Fixes.append ?_ (fixes_tabs_modeSet 2004 _)
  refine Fixes.append ?_ (fixes_tabs_modeSet 25 _)
  refine Fixes.append ?_ ((Fixes.streamPred _).ite
    (fun _ => fixes_tabs_escSeq 0x3D (by decide))
    (fun _ => fixes_tabs_escSeq 0x3E (by decide)))
  exact (fixes_tabs_modeSet 7 _).append (fixes_tabs_modeSet 1 _)

theorem fixes_tabs_savedAnsi (v : Vt) : Fixes (fun v : Vt => v.tabs) (savedAnsi v) := by
  unfold savedAnsi
  exact ((fixes_penSgr psBlind_tabs _ tabs_csiDispatch_sgr).append
    (fixes_csiNum2 psBlind_tabs _ _ 0x48 (by decide) (by decide) tabs_csiDispatch_cup)).append
    (fixes_tabs_escSeq 0x37 (by decide))

theorem fixes_tabs_titleAnsi (v : Vt) : Fixes (fun v : Vt => v.tabs) (titleAnsi v) := by
  unfold titleAnsi
  exact fixes_osc psBlind_tabs _ tabs_oscFinish

theorem fixes_tabs_charsetAnsi (v : Vt) : Fixes (fun v : Vt => v.tabs) (charsetAnsi v) := by
  unfold charsetAnsi
  refine (((Fixes.streamPred _).ite (fun _ => fixes_tabs_escCharset 0x28 0x30 (by decide))
    (fun _ => fixes_tabs_escCharset 0x28 0x42 (by decide))).append
    ((Fixes.streamPred _).ite (fun _ => fixes_tabs_escCharset 0x29 0x30 (by decide))
      (fun _ => fixes_tabs_escCharset 0x29 0x42 (by decide)))).append ?_
  exact (Fixes.streamPred _).ite (fun _ => fixes_tabs_shiftOut) (fun _ => Fixes.nil _)

theorem fixes_tabs_cursorAnsi (v : Vt) : Fixes (fun v : Vt => v.tabs) (cursorAnsi v) := by
  unfold cursorAnsi
  exact (Fixes.streamPred _).ite
    (fun _ => fixes_csiNum2 psBlind_tabs _ _ 0x48 (by decide) (by decide) tabs_csiDispatch_cup)
    (fun _ => fixes_csiNum2 psBlind_tabs _ _ 0x48 (by decide) (by decide) tabs_csiDispatch_cup)

/-- **The ruler survives everything `restore` emits after it.** The stages between
`tabsAnsi` and the end of the stream: the DECSC slot, the title, the mode replay,
the charset designations, the trailing pen and the final cursor address. -/
theorem fixes_tabs_tail (v : Vt) :
    Fixes (fun v : Vt => v.tabs)
      (savedAnsi v ++ titleAnsi v ++ modesAnsi v ++ charsetAnsi v ++ penSgr v.pen
        ++ cursorAnsi v) :=
  (((((fixes_tabs_savedAnsi v).append (fixes_tabs_titleAnsi v)).append
    (fixes_tabs_modesAnsi v)).append (fixes_tabs_charsetAnsi v)).append
    (fixes_penSgr psBlind_tabs v.pen tabs_csiDispatch_sgr)).append (fixes_tabs_cursorAnsi v)

/-! ### The ruler, rebuilt from a cleared one

`tabsAnsi` clears every stop (`TBC 3`) and then sets the ones the session holds, one
`CHA`+`HTS` pair each. On the array side that is a fold of `setIfInBounds` over the
filtered index list, and this says the fold reproduces the session's ruler exactly.
Array equality is size-and-pointwise (`Array.ext`), the route `grid_eq_of_cells`
takes — the size half is needed internally anyway, since the cleared ruler is an
`Array.replicate`, so a pointwise-only claim would be weaker for no saving. -/

/-- A stop that reads back `true` is in range: out of range `getD` returns the
default, which is `false`. This is what lets the monotonicity step below avoid a
size side condition. -/
theorem getD_true_lt {a : Array Bool} {j : Nat} (h : a.getD j false = true) : j < a.size := by
  rcases Nat.lt_or_ge j a.size with hlt | hge
  · exact hlt
  · exfalso
    rw [Array.getD, dite_eq_right (by omega)] at h
    exact absurd h (by decide)

theorem size_foldl_setTab : ∀ (l : List Nat) (a : Array Bool),
    (l.foldl (fun b i => b.setIfInBounds i true) a).size = a.size
  | [], _ => rfl
  | i :: is, a => by
    rw [List.foldl_cons, size_foldl_setTab is, Array.size_setIfInBounds]

/-- Setting stops never clears one: a stop already set survives the rest of the fold.
Needed because the head write of `foldl_setTab_mem` has to outlive the tail. -/
theorem foldl_setTab_mono : ∀ (l : List Nat) (a : Array Bool) (j : Nat),
    a.getD j false = true →
    (l.foldl (fun b i => b.setIfInBounds i true) a).getD j false = true
  | [], _, _, h => h
  | i :: is, a, j, h => by
    rw [List.foldl_cons]
    refine foldl_setTab_mono is _ j ?_
    by_cases hij : j = i
    · rw [hij, getD_set_self a i true false (by rw [← hij]; exact getD_true_lt h)]
    · rw [getD_set_ne a i j true false hij]; exact h

theorem foldl_setTab_mem : ∀ (l : List Nat) (a : Array Bool) (j : Nat), j ∈ l → j < a.size →
    (l.foldl (fun b i => b.setIfInBounds i true) a).getD j false = true
  | [], _, _, h, _ => absurd h (by simp)
  | i :: is, a, j, hmem, hsz => by
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hmem with h | h
    · rw [h]
      exact foldl_setTab_mono is _ i (getD_set_self a i true false (by rw [← h]; exact hsz))
    · exact foldl_setTab_mem is _ j h (by rw [Array.size_setIfInBounds]; exact hsz)

theorem foldl_setTab_not_mem : ∀ (l : List Nat) (a : Array Bool) (j : Nat), j ∉ l →
    (l.foldl (fun b i => b.setIfInBounds i true) a).getD j false = a.getD j false
  | [], _, _, _ => rfl
  | i :: is, a, j, h => by
    rw [List.foldl_cons,
      foldl_setTab_not_mem is _ j (fun hm => h (List.mem_cons.mpr (Or.inr hm)))]
    exact getD_set_ne a i j true false (fun he => h (List.mem_cons.mpr (Or.inl he)))

/-- **The ruler is rebuilt exactly.** Clearing every stop and then setting the ones
the session holds gives back the session's ruler — provided it is `cols` long, which
is what makes a stop at an index outside `range cols` impossible. -/
theorem tabs_rebuilt {t : Array Bool} {cols : Nat} (hsz : t.size = cols) :
    ((List.range cols).filter (fun i => t.getD i false)).foldl
        (fun (a : Array Bool) i => a.setIfInBounds i true)
        (Array.replicate cols false) = t := by
  apply Array.ext
  · rw [size_foldl_setTab, Array.size_replicate, hsz]
  · intro j hj _
    have hjc : j < cols := by
      rw [size_foldl_setTab, Array.size_replicate] at hj; exact hj
    have hjt : j < t.size := by rw [hsz]; exact hjc
    -- both sides through `getD`, where the fold lemmas live
    rw [← getD_lt' _ j false hj, ← getD_lt' t j false hjt]
    by_cases hstop : t.getD j false = true
    · exact (foldl_setTab_mem _ _ j
        (List.mem_filter.mpr ⟨List.mem_range.mpr hjc, hstop⟩)
        (by rw [Array.size_replicate]; exact hjc)).trans hstop.symm
    · have hf : t.getD j false = false := by
        rcases Bool.eq_false_or_eq_true (t.getD j false) with h | h
        · exact absurd h hstop
        · exact h
      rw [foldl_setTab_not_mem _ _ j (fun hm => hstop (List.mem_filter.mp hm).2), hf,
        getD_lt' _ j false (by rw [Array.size_replicate]; exact hjc), Array.getElem_replicate]

/-! ### The clear, the stops, and the fold

`tabsAnsi` is `TBC 3` followed by one `CHA`+`HTS` pair per stop. Both halves get a
**state equation**, because what they do to the ruler is the claim rather than a
frame around it.

The clear asks only `pstate = .ground` of the receiver — no `u8need = 0`. The
leading `ESC` of `CSI 3 g` aborts a half-decoded character by itself
(`un_abortUtf8_esc`), and nothing about the ruler rides on the bytes it discards.
That is the same argument `SMap` makes for the sticky bundle, and it is what keeps
the ruler's claim free of the `paint_entry`/`U8Ok` apparatus the grid's needs: the
paint ends in glyph bytes, so `u8need = 0` right after it is expensive, and here it
is simply not required. -/

theorem tabs_abortUtf8 (v : Vt) (b : UInt8) : (v.abortUtf8 b).tabs = v.tabs := by
  unfold Vt.abortUtf8; split <;> rfl

theorem cols_abortUtf8 (v : Vt) (b : UInt8) : (v.abortUtf8 b).cols = v.cols := by
  unfold Vt.abortUtf8; split <;> rfl

theorem abortUtf8_of_uz {v : Vt} (b : UInt8) (h : v.u8need = 0) : v.abortUtf8 b = v := by
  unfold Vt.abortUtf8; rw [ite_eq_right (by simp [h])]

/-- Feeding `ESC` is the same as discarding a half-decoded character first: `step`
aborts before it dispatches, and a second abort at `0x1B` is the identity. -/
theorem step_esc_of_abort (u : Vt) : u.step 0x1B = (u.abortUtf8 0x1B).step 0x1B := by
  unfold Vt.step
  rw [abortUtf8_of_uz 0x1B (un_abortUtf8_esc u)]

/-- …so a stream that opens with `ESC` may as well be fed to the aborted state. -/
theorem feed_esc_of_abort (u : Vt) (rest : Bytes) :
    u.feed (0x1B :: rest) = (u.abortUtf8 0x1B).feed (0x1B :: rest) := by
  simp only [feed_cons]
  rw [step_esc_of_abort u]

/-- `CSI 3 g` (TBC 3) as a state equation: it clears every stop and touches nothing
else. -/
theorem tbc3_feed_eq {v : Vt} (hg : v.pstate = .ground) (hu : v.u8need = 0) :
    v.feed (csiNum 3 0x67) = { v with tabs := Array.replicate v.cols false } := by
  rw [show csiNum 3 0x67 = [0x1B, 0x5B] ++ (digits 3 ++ [(0x67 : UInt8)]) from by
    simp [csiNum, csiB]]
  rw [feed_append, keeps_csi_open hg hu]
  obtain ⟨s', heq, hcur', hhave, hpar, hint, hsub⟩ :=
    csi_digits_run_eq 3 (v := { v with pstate := .csi ({} : CsiState) })
      (s := ({} : CsiState)) rfl (by simpa using hu) rfl
  rw [show ∀ (u : Vt), u.feed (digits 3 ++ [(0x67 : UInt8)])
      = (u.feed (digits 3)).feed [(0x67 : UInt8)] from
    fun u => by simp [Vt.feed, List.foldl_append]]
  rw [heq, show ∀ (u : Vt), u.feed [(0x67 : UInt8)] = u.step 0x67 from fun _ => rfl]
  rw [csi_final_step_eq 0x67 rfl (by simpa using hu) (by rw [hint]) (by decide) (by decide)]
  unfold Vt.csiFinish
  rw [ite_eq_left (by simpa using hhave), ite_eq_right (by rw [hpar]; decide)]
  dsimp only
  have harg : ({ s' with params := s'.params.push (min s'.cur 65535, s'.curSub) }
      : CsiState).arg 0 0 = 3 := by
    rw [arg_of_one_of 0 (show ({ s' with params := s'.params.push (min s'.cur 65535, s'.curSub) }
        : CsiState).params = (#[] : Array (Nat × Bool)).push (3, s'.curSub) from by
      simp [hpar, hcur'])]
    simp
  rw [show ∀ (u : Vt), u.csiDispatch
      ({ s' with params := s'.params.push (min s'.cur 65535, s'.curSub) } : CsiState) 0x67
      = { u with tabs := Array.replicate u.cols false } from by
    intro u
    unfold Vt.csiDispatch
    rw [ite_eq_right (show ¬(({ s' with params := s'.params.push (min s'.cur 65535, s'.curSub) }
      : CsiState)).ignore = true from by
      show ¬(s'.ignore = true)
      rw [show s'.ignore = ({} : CsiState).ignore from by
        obtain ⟨s2, hps2, -, -, -, -, hign2, -, -⟩ := csi_digits_value 3
          (v := { v with pstate := .csi ({} : CsiState) }) (s := ({} : CsiState)) rfl rfl
        have : s' = s2 := PState.csi.inj ((by rw [heq] :
          ((({ v with pstate := .csi ({} : CsiState) } : Vt)).feed (digits 3)).pstate
            = PState.csi s').symm.trans hps2)
        rw [this]; exact hign2]
      simp)]
    show (match ({ s' with params := s'.params.push (min s'.cur 65535, s'.curSub) }
        : CsiState).arg 0 0 with
      | 0 => { u with tabs := u.tabs.setIfInBounds u.cursor.x false }
      | 3 => { u with tabs := Array.replicate u.cols false }
      | _ => u) = { u with tabs := Array.replicate u.cols false }
    rw [harg]
    rfl]
  show ({ ({ v with pstate := .csi s' } : Vt) with
    tabs := Array.replicate ({ v with pstate := .csi s' } : Vt).cols false,
    pstate := .ground } : Vt) = { v with tabs := Array.replicate v.cols false }
  rw [hg]

/-- **The clear grounds the ruler from any receiver**, whatever its decoder was
holding. -/
theorem tbc3_clears {u : Vt} (hg : u.pstate = .ground) :
    (u.feed (csiNum 3 0x67)).tabs = Array.replicate u.cols false
      ∧ (u.feed (csiNum 3 0x67)).cols = u.cols
      ∧ (u.feed (csiNum 3 0x67)).pstate = .ground
      ∧ (u.feed (csiNum 3 0x67)).u8need = 0 := by
  have hshape : u.feed (csiNum 3 0x67) = (u.abortUtf8 0x1B).feed (csiNum 3 0x67) := by
    rw [show csiNum 3 0x67 = 0x1B :: (0x5B :: (digits 3 ++ [(0x67 : UInt8)])) from by
      simp [csiNum, csiB]]
    exact feed_esc_of_abort u _
  rw [hshape, tbc3_feed_eq (by rw [ps_abortUtf8]; exact hg) (un_abortUtf8_esc u)]
  exact ⟨by rw [cols_abortUtf8], cols_abortUtf8 u 0x1B,
    by rw [ps_abortUtf8]; exact hg, un_abortUtf8_esc u⟩

/-- `ESC H` (HTS) as a state equation: it sets a stop at the cursor. -/
theorem hts_feed_eq {v : Vt} (hg : v.pstate = .ground) (hu : v.u8need = 0) :
    v.feed (escSeq 0x48) = { v with tabs := v.tabs.setIfInBounds v.cursor.x true } := by
  rw [show escSeq 0x48 = [0x1B] ++ [(0x48 : UInt8)] from rfl]
  rw [show ∀ (w : Vt), w.feed ([0x1B] ++ [(0x48 : UInt8)]) = (w.step 0x1B).step 0x48 from
    fun w => by simp [Vt.feed]]
  rw [esc_step_eq hg hu, step_of_esc_quiet (0x48 : UInt8) rfl (by simpa using hu)]
  show ({ ({ v with pstate := .esc } : Vt) with
      tabs := ({ v with pstate := .esc } : Vt).tabs.setIfInBounds
        ({ v with pstate := .esc } : Vt).cursor.x true, pstate := .ground } : Vt)
    = { v with tabs := v.tabs.setIfInBounds v.cursor.x true }
  rw [hg]

/-- **The stops, as one array fold.** Each `CHA` parks the cursor on its column and
the `HTS` after it sets the stop there, so the whole run *is* `setIfInBounds` folded
over the stop list.

The cursor is deliberately **not** part of the carried invariant: `CHA` establishes
it and `HTS` consumes it inside a single iteration, so the loop carries only
`ground`, a quiesced decoder, `cols` and the ruler. That is what makes this simpler
than `Matches`, which has to tie the cursor to the grid *across* iterations. -/
theorem hts_run : ∀ (ss : List Nat) (u : Vt), u.pstate = .ground → u.u8need = 0 →
    u.cols < 65535 → (∀ i ∈ ss, i < u.cols) →
    (u.feed (ss.flatMap (fun i => csiNum (i + 1) 0x47 ++ escSeq 0x48))).tabs
        = ss.foldl (fun (t : Array Bool) i => t.setIfInBounds i true) u.tabs
      ∧ (u.feed (ss.flatMap (fun i => csiNum (i + 1) 0x47 ++ escSeq 0x48))).cols = u.cols
      ∧ (u.feed (ss.flatMap (fun i => csiNum (i + 1) 0x47 ++ escSeq 0x48))).pstate = .ground
      ∧ (u.feed (ss.flatMap (fun i => csiNum (i + 1) 0x47 ++ escSeq 0x48))).u8need = 0
  | [], u, hg, hu, _, _ => ⟨rfl, rfl, hg, hu⟩
  | i :: is, u, hg, hu, hlt, hmem => by
    have hi : i < u.cols := hmem i (by simp)
    -- `CHA (i+1)` parks the cursor on column `i`; only the cursor moves
    have hcha : u.feed (csiNum (i + 1) 0x47) = u.setCol i := by
      rw [cha_feed_eq (i + 1) hg hu (by omega) (by omega),
        show i + 1 - 1 = i from by omega]
    have hx : (u.setCol i).cursor.x = i := by
      show min i (u.cols - 1) = i
      omega
    -- …then `HTS` sets the stop the cursor is on
    have hhts : (u.setCol i).feed (escSeq 0x48)
        = { u.setCol i with tabs := u.tabs.setIfInBounds i true } := by
      rw [hts_feed_eq (by rw [frame_setCol]; exact hg) (by rw [frame_setCol]; exact hu), hx,
        show (u.setCol i).tabs = u.tabs from by rw [frame_setCol]]
    rw [List.flatMap_cons, feed_append, feed_append, hcha, hhts, List.foldl_cons]
    obtain ⟨h1, h2, h3, h4⟩ := hts_run is
      { u.setCol i with tabs := u.tabs.setIfInBounds i true }
      (by show (u.setCol i).pstate = _; rw [frame_setCol]; exact hg)
      (by show (u.setCol i).u8need = _; rw [frame_setCol]; exact hu)
      (by show (u.setCol i).cols < _; rw [frame_setCol]; exact hlt)
      (fun j hj => by
        show j < (u.setCol i).cols
        rw [frame_setCol]
        exact hmem j (by simp [hj]))
    refine ⟨h1, ?_, h3, h4⟩
    rw [h2]
    show (u.setCol i).cols = u.cols
    rw [frame_setCol]

/-- `restore`, split at the tab ruler: the head that grounds the receiver, the clear,
the stops, and the tail that leaves the ruler alone. -/
theorem restore_tabs_split (v : Vt) :
    restore v = (prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v
        ++ regionAnsi v)
      ++ (csiNum 3 0x67
        ++ ((((List.range v.cols).filter (fun i => v.tabs.getD i false)).flatMap
              (fun i => csiNum (i + 1) 0x47 ++ escSeq 0x48))
          ++ (savedAnsi v ++ titleAnsi v ++ modesAnsi v ++ charsetAnsi v ++ penSgr v.pen
                ++ cursorAnsi v))) := by
  unfold restore restoreBody tabsAnsi
  simp only [List.append_assoc]

/-- **A5 inbound, the tab ruler.** For any receiver of the session's width, `restore`
installs the session's tab ruler — the field that was, until the emitter was fixed,
worse than unproved: `tabsAnsi` used to skip the whole thing when the session's ruler
was the default, so a client whose previous occupant had set its own stops kept them
and a `\t` landed on the wrong column. As the code stood then this theorem would have
been **false**, which is why the fix had to precede it.

`Good w` is what `dims_feed` needs of the receiver (the paint contains the byte
`0x63`, so the cheaper `dims_feed_ne_ris` does not apply). `hub` keeps the largest
emitted `CHA` parameter — one more than the last column — off the parser's 65535
clamp. `hvtabs` is the one hypothesis on the session that `Good`/`Renderable` do not
already give: a ruler longer than `cols` could hold a stop no `range cols` walk would
ever emit, and `Checkpoint.load` is total on arbitrary bytes, so it is asked for
rather than assumed. -/
theorem restore_tabs_any (v w : Vt) (hgood : Good w) (hcols : w.cols = v.cols)
    (hub : v.cols < 65535) (hvtabs : v.tabs.size = v.cols) :
    (w.feed (restore v)).tabs = v.tabs := by
  rw [restore_tabs_split, feed_append, feed_append, feed_append]
  -- the head grounds any receiver and cannot change its width
  have hhg : (w.feed (prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v
      ++ regionAnsi v)).pstate = .ground := by
    rw [show prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v ++ regionAnsi v
        = (prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v) ++ regionAnsi v
        from rfl, feed_append]
    exact ends_regionAnsi v _ (paint_grounds v w)
  have hhc : (w.feed (prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v
      ++ regionAnsi v)).cols = v.cols := by
    rw [← dims_fst, dims_feed _ hgood, dims_fst]; exact hcols
  -- the clear, then the stops
  obtain ⟨hct, hcc, hcg, hcu⟩ := tbc3_clears hhg
  obtain ⟨hrt, -, hrg, hru⟩ := hts_run
    ((List.range v.cols).filter (fun i => v.tabs.getD i false)) _ hcg hcu
    (by rw [hcc, hhc]; exact hub)
    (fun i hi => by
      rw [hcc, hhc]
      exact List.mem_range.mp (List.mem_filter.mp hi).1)
  -- the tail leaves the ruler alone, so the fold's value is the answer
  obtain ⟨-, -, htl⟩ := fixes_tabs_tail v _ hrg hru
  -- `Fixes` is parameterised by the projection, so destructuring it leaves a
  -- beta-redex where the goal has the field applied; `dsimp` lines them up.
  dsimp only at htl
  rw [htl, hrt, hct, hhc]
  exact tabs_rebuilt hvtabs

/-- The pointwise form: every column's stop is the session's. -/
theorem restore_tabs_stop_any (v w : Vt) (hgood : Good w) (hcols : w.cols = v.cols)
    (hub : v.cols < 65535) (hvtabs : v.tabs.size = v.cols) (i : Nat) :
    (w.feed (restore v)).tabs.getD i false = v.tabs.getD i false := by
  rw [restore_tabs_any v w hgood hcols hub hvtabs]

/-- A fresh ruler is exactly `cols` long — the `hvtabs` witness for a live session,
and the reason the hypothesis is discharged rather than assumed at every call site
that starts from `Vt.init`. -/
theorem size_defaultTabs (c : Nat) : (defaultTabs c).size = c := by
  unfold defaultTabs
  simp

/-- The ruler claim with the receiver's invariant discharged from reachability, the
shape `restore_grid_reachable` has. `hvtabs` stays: `Good` and `Renderable` say
nothing about the ruler's length, and proving `tabs.size = cols` an invariant of
every reachable state is a `tabs_*` frame family of its own — worth doing, not
needed here. -/
theorem restore_tabs_reachable (v w : Vt) (hw : LiveReachableVt w) (hv : LiveReachableVt v)
    (hcols : w.cols = v.cols) (hvtabs : v.tabs.size = v.cols) :
    (w.feed (restore v)).tabs = v.tabs :=
  restore_tabs_any v w (good_of_liveReachable hw) hcols
    (Nat.lt_of_le_of_lt (good_of_liveReachable hv).colsLe (by decide)) hvtabs

/-- Non-vacuity: a real 80×24 session satisfies every hypothesis, so the ruler claim
is not vacuously true. -/
example : ((Vt.init 80 24).feed (restore (Vt.init 80 24))).tabs = (Vt.init 80 24).tabs :=
  restore_tabs_any _ _ (good_init 80 24) rfl (by decide) (size_defaultTabs _)

end Linger.Core.Render
