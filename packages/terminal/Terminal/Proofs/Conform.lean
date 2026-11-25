module

import all Terminal.CoreCode.Render
import all Terminal.CoreCode.Vt
import all Terminal.Proofs.Vt
import all Terminal.Proofs.Vt.State
import all Terminal.Proofs.Render.Pen
import all Terminal.Proofs.Render.Keeps
import all Terminal.Proofs.Conform.Parse
import all Terminal.Proofs.Conform.Screen

-- Module-private by default: `Vt`'s fields are sealed (see `packages/terminal/Terminal/Proofs/Vt/State.lean`).

/-! # The emulator conforms to the reference

Each sequence of `Vt.Ref.Seq`, fed to a live terminal between control sequences and characters,
changes `screenOf` of it as the reference says: `vt_conforms`, from the parser half
(`Conform/Parse.lean`) and the screen half (`Conform/Screen.lean`). -/

namespace Terminal.Vt.Conform

open Terminal.Vt Terminal.Render

theorem boundary {v : Vt} (hb : v.atBoundary = true) : v.pstate = .ground ∧ v.u8need = 0 := by
  unfold Vt.atBoundary at hb
  simpa using hb

theorem arg_first {t : CsiState} {n : Nat} {rest : List (Nat × Bool)}
    (h : t.params.toList = (n, false) :: rest) (d : Nat) : t.arg 0 d = if n = 0 then d else n := by
  unfold CsiState.arg
  rcases t with ⟨priv, ⟨l⟩, cur, curSub, haveCur, inter, ignore⟩
  simp only at h
  subst h
  cases n <;> rfl

theorem arg_second {t : CsiState} {a b : Nat} (h : t.params.toList = [(a, false), (b, false)])
    (d : Nat) : t.arg 1 d = if b = 0 then d else b := by
  unfold CsiState.arg
  rcases t with ⟨priv, ⟨l⟩, cur, curSub, haveCur, inter, ignore⟩
  simp only at h
  subst h
  cases b <;> rfl

theorem count_eq (n : Nat) : (if n = 0 then 1 else n) = Ref.count n := rfl

/-- The screen after `{ w with pstate := .ground }` is `w`'s. -/
theorem screenOf_ground (w : Vt) : screenOf { w with pstate := .ground } = screenOf w := rfl

/-- An OSC payload without BEL or ESC, within the cap, accumulates. -/
theorem osc_run :
    ∀ (bs : List UInt8) {v : Vt} {acc : Array UInt8},
      v.pstate = .osc acc false →
        v.u8need = 0 →
        (∀ b ∈ bs, b ≠ 0x07 ∧ b ≠ 0x1B) →
        acc.size + bs.length ≤ 2048 →
        v.feed bs = { v with pstate := .osc (acc ++ bs.toArray) false }
  | [], v, acc, hg, _, _, _ => by
    rw [feed_nil]
    rcases v with ⟨⟩
    simp_all
  | b :: bs, v, acc, hg, hu, hb, hcap => by
    rw [feed_cons, step_of_osc_quiet b hg hu]
    have hb1 := hb b (by simp)
    have e : v.stepOsc acc false b = { v with pstate := .osc (acc.push b) false } := by
      unfold Vt.stepOsc
      rw [ite_eq_right (by simp), ite_eq_right (by simpa using hb1.1),
        ite_eq_right (by simpa using hb1.2),
        ite_eq_right
          (by
            simp at hcap; omega)]
    rw [e,
      osc_run bs (v := { v with pstate := .osc (acc.push b) false }) rfl hu
        (fun b' hb' => hb b' (by simp [hb']))
        (by
          simp at hcap ⊢; omega)]
    simp

theorem title_feed {v : Vt} (hg : v.pstate = .ground) (hu : v.u8need = 0) (both : Bool)
    (text : String) (hs : (Ref.Seq.title both text).Ok) :
    v.feed (Ref.Seq.title both text).bytes = { v with title := text } := by
  obtain ⟨hb, hcap⟩ := hs
  simp only [Ref.Seq.bytes]
  rw [show
      [0x1B, 0x5D, if both = true then (0x30 : UInt8) else 0x32, 0x3B] ++ text.toUTF8.data.toList ++
          [0x07] =
        [0x1B, 0x5D] ++
          (((if both = true then (0x30 : UInt8) else 0x32) :: 0x3B :: text.toUTF8.data.toList) ++
            [0x07])
      from by simp]
  rw [feed_append, feed_cons, esc_step_eq hg hu, feed_cons, feed_nil,
    step_of_esc_quiet (v := { v with pstate := .esc }) 0x5D rfl hu]
  rw [show Vt.stepEsc { v with pstate := .esc } 0x5D = { v with pstate := .osc #[] false } from rfl,
    feed_append,
    osc_run _ (v := { v with pstate := .osc #[] false }) (acc := #[]) rfl hu
      (by
        intro b hb'
        simp only [List.mem_cons] at hb'
        rcases hb' with rfl | rfl | hb'
        · split <;> decide
        · decide
        · exact hb b hb')
      (by
        simp only [List.length_cons, Array.length_toList, Array.size_empty]; omega)]
  rw [show ∀ w : Vt, w.feed [0x07] = w.step 0x07 from fun _ => rfl,
    step_of_osc_quiet (v := { v with pstate := .osc _ false }) 0x07 rfl hu]
  unfold Vt.stepOsc Vt.oscFinish
  rw [ite_eq_right (by simp), ite_eq_left (by decide)]
  have hd : String.fromUTF8? ⟨text.toByteArray.data⟩ = some text := by
    simp [String.fromUTF8?, text.isValidUTF8]
  cases both
  · simp only [Bool.false_eq_true, ↓reduceIte]
    simp
    rw [hd]
    simp [← hg]
  · simp only [↓reduceIte]
    simp
    rw [hd]
    simp [← hg]

/-- A one-parameter CSI from a quiet ground state: the dispatch of a collector whose first
argument reads as the parameter. -/
theorem csi1 {v : Vt} (n : Nat) (final : UInt8) (hn : n ≤ 65535) (h1 : 0x40 ≤ final)
    (h2 : final ≤ 0x7E) (hg : v.pstate = .ground) (hu : v.u8need = 0) :
    ∃ (t : CsiState) (p : PState),
      t.priv = 0 ∧
        t.ignore = false ∧
        (∀ d, t.arg 0 d = if n = 0 then d else n) ∧
        v.feed (Ref.csi [n] final) =
          { Vt.csiDispatch { v with pstate := p } t final with pstate := .ground } := by
  obtain ⟨t, p, hp, hi, hpar, hf⟩ :=
    csi_codes_feed [n] final (by simp) (by simp) (by simpa using hn) h1 h2 hg hu
  exact ⟨t, p, hp, hi, fun d => arg_first (rest := []) (by simpa using hpar) d, hf⟩

theorem csi2 {v : Vt} (a b : Nat) (final : UInt8) (ha : a ≤ 65535) (hb : b ≤ 65535)
    (h1 : 0x40 ≤ final) (h2 : final ≤ 0x7E) (hg : v.pstate = .ground) (hu : v.u8need = 0) :
    ∃ (t : CsiState) (p : PState),
      t.priv = 0 ∧
        t.ignore = false ∧
        (∀ d, t.arg 0 d = if a = 0 then d else a) ∧
        (∀ d, t.arg 1 d = if b = 0 then d else b) ∧
        v.feed (Ref.csi [a, b] final) =
          { Vt.csiDispatch { v with pstate := p } t final with pstate := .ground } := by
  obtain ⟨t, p, hp, hi, hpar, hf⟩ :=
    csi_codes_feed [a, b] final (by simp) (by simp)
      (by
        simp; omega)
      h1 h2 hg hu
  exact
    ⟨t, p, hp, hi, fun d => arg_first (rest := [(b, false)]) (by simpa using hpar) d, fun d =>
      arg_second (by simpa using hpar) d, hf⟩

theorem sgr_le (b : Ref.Sgr) : ∀ n ∈ b.params, n ≤ 65535 := by
  intro n hn
  cases b with
  | fg8 i
  | bg8 i =>
    simp [Ref.Sgr.params] at hn; omega
  | fg256 i
  | bg256 i =>
    have := i.toNat_lt; simp [Ref.Sgr.params] at hn; omega
  | fgRgb r g b
  | bgRgb r g b =>
    have := r.toNat_lt; have := g.toNat_lt; have := b.toNat_lt
    simp [Ref.Sgr.params] at hn; omega
  | _ =>
    simp [Ref.Sgr.params] at hn; omega

/-- **The emulator conforms.** -/
theorem conforms {v : Vt} (hv : LiveReachableVt v) (hb : v.atBoundary = true)
    (hp : Ref.Plain Vt.colCount Vt.rowCount Vt.getRow Vt.getModes stick v) (s : Ref.Seq)
    (hs : s.Ok) : Ref.Same (screenOf (v.feed s.bytes)) (Ref.Seq.apply (screenOf v) s) := by
  have hf := facts_of_live hv hp
  obtain ⟨hg, hu⟩ := boundary hb
  cases s with
  | print c =>
    obtain ⟨h1, h2⟩ := hs
    have hb' : (UInt8.ofNat c.toNat).toNat = c.toNat := by
      simp [UInt8.toNat_ofNat']; omega
    rw [Ref.Seq.bytes,
      print_feed _
        (by
          simp [UInt8.le_iff_toNat_le, hb']; omega)
        (by
          simp [UInt8.lt_iff_toNat_lt, hb']; omega)
        hg hu]
    unfold Vt.acceptChar
    rw [hb', ite_eq_left (show c.toNat.isValidChar from Or.inl (by omega)), Char.ofNat_toNat]
    exact print_ok hf c h1 h2
  | cr =>
    rw [Ref.Seq.bytes, ctl_feed _ (by decide) (by decide) hg hu]; exact same_refl _
  | lf =>
    rw [Ref.Seq.bytes, ctl_feed _ (by decide) (by decide) hg hu]; exact lineFeed_ok hf
  | bs =>
    rw [Ref.Seq.bytes, ctl_feed _ (by decide) (by decide) hg hu]
    exact same_of_eq (backspace_ok v)
  | ht =>
    rw [Ref.Seq.bytes, ctl_feed _ (by decide) (by decide) hg hu]
    exact same_of_eq (tab_ok v)
  | bel =>
    rw [Ref.Seq.bytes, ctl_feed _ (by decide) (by decide) hg hu]; exact same_refl _
  | cuu n =>
    obtain ⟨t, p, _, hi, ha, he⟩ := csi1 n 0x41 hs (by decide) (by decide) hg hu
    rw [Ref.Seq.bytes, he, screenOf_ground]
    unfold Vt.csiDispatch; rw [ite_eq_right (by simp [hi])]; dsimp only
    rw [ha 1, count_eq]
    exact same_of_eq (moveRel_up (facts_pstate hf p) _)
  | cud n =>
    obtain ⟨t, p, _, hi, ha, he⟩ := csi1 n 0x42 hs (by decide) (by decide) hg hu
    rw [Ref.Seq.bytes, he, screenOf_ground]
    unfold Vt.csiDispatch; rw [ite_eq_right (by simp [hi])]; dsimp only
    rw [ha 1, count_eq]
    exact same_of_eq (moveRel_down (facts_pstate hf p) _)
  | cuf n =>
    obtain ⟨t, p, _, hi, ha, he⟩ := csi1 n 0x43 hs (by decide) (by decide) hg hu
    rw [Ref.Seq.bytes, he, screenOf_ground]
    unfold Vt.csiDispatch; rw [ite_eq_right (by simp [hi])]; dsimp only
    rw [ha 1, count_eq]
    exact same_of_eq (moveRel_right (facts_pstate hf p) _)
  | cub n =>
    obtain ⟨t, p, _, hi, ha, he⟩ := csi1 n 0x44 hs (by decide) (by decide) hg hu
    rw [Ref.Seq.bytes, he, screenOf_ground]
    unfold Vt.csiDispatch; rw [ite_eq_right (by simp [hi])]; dsimp only
    rw [ha 1, count_eq]
    exact same_of_eq (moveRel_left (facts_pstate hf p) _)
  | il n =>
    obtain ⟨t, p, _, hi, ha, he⟩ := csi1 n 0x4C hs (by decide) (by decide) hg hu
    rw [Ref.Seq.bytes, he, screenOf_ground]
    unfold Vt.csiDispatch; rw [ite_eq_right (by simp [hi])]; dsimp only
    rw [ha 1, count_eq]
    exact insertLines_ok (facts_pstate hf p) n
  | dl n =>
    obtain ⟨t, p, _, hi, ha, he⟩ := csi1 n 0x4D hs (by decide) (by decide) hg hu
    rw [Ref.Seq.bytes, he, screenOf_ground]
    unfold Vt.csiDispatch; rw [ite_eq_right (by simp [hi])]; dsimp only
    rw [ha 1, count_eq]
    exact deleteLines_ok (facts_pstate hf p) n
  | ich n =>
    obtain ⟨t, p, _, hi, ha, he⟩ := csi1 n 0x40 hs (by decide) (by decide) hg hu
    rw [Ref.Seq.bytes, he, screenOf_ground]
    unfold Vt.csiDispatch; rw [ite_eq_right (by simp [hi])]; dsimp only
    rw [ha 1, count_eq]
    exact insertChars_ok (facts_pstate hf p) n
  | dch n =>
    obtain ⟨t, p, _, hi, ha, he⟩ := csi1 n 0x50 hs (by decide) (by decide) hg hu
    rw [Ref.Seq.bytes, he, screenOf_ground]
    unfold Vt.csiDispatch; rw [ite_eq_right (by simp [hi])]; dsimp only
    rw [ha 1, count_eq]
    exact deleteChars_ok (facts_pstate hf p) n
  | ech n =>
    obtain ⟨t, p, _, hi, ha, he⟩ := csi1 n 0x58 hs (by decide) (by decide) hg hu
    rw [Ref.Seq.bytes, he, screenOf_ground]
    unfold Vt.csiDispatch; rw [ite_eq_right (by simp [hi])]; dsimp only
    rw [ha 1, count_eq]
    exact eraseChars_ok (facts_pstate hf p) n
  | ed
    m =>
    obtain ⟨t, p, _, hi, ha, he⟩ := csi1 m.val 0x4A (by omega) (by decide) (by decide) hg hu
    rw [Ref.Seq.bytes, he, screenOf_ground]
    unfold Vt.csiDispatch; rw [ite_eq_right (by simp [hi])]; dsimp only
    rw [ha 0, show (if m.val = 0 then 0 else m.val) = m.val by split <;> omega]
    exact eraseScreen_ok (facts_pstate hf p) m
  | el
    m =>
    obtain ⟨t, p, _, hi, ha, he⟩ := csi1 m.val 0x4B (by omega) (by decide) (by decide) hg hu
    rw [Ref.Seq.bytes, he, screenOf_ground]
    unfold Vt.csiDispatch; rw [ite_eq_right (by simp [hi])]; dsimp only
    rw [ha 0, show (if m.val = 0 then 0 else m.val) = m.val by split <;> omega]
    exact eraseLine_ok (facts_pstate hf p) m
  | cha n =>
    obtain ⟨t, p, _, hi, ha, he⟩ := csi1 n 0x47 hs (by decide) (by decide) hg hu
    rw [Ref.Seq.bytes, he, screenOf_ground]
    unfold Vt.csiDispatch; rw [ite_eq_right (by simp [hi])]; dsimp only
    rw [ha 1, count_eq]
    exact same_refl _
  | vpa n =>
    obtain ⟨t, p, _, hi, ha, he⟩ := csi1 n 0x64 hs (by decide) (by decide) hg hu
    rw [Ref.Seq.bytes, he, screenOf_ground]
    unfold Vt.csiDispatch; rw [ite_eq_right (by simp [hi])]; dsimp only
    rw [ha 1, count_eq]
    refine same_of_eq ((moveTo_eq { v with pstate := p } _ _).trans ?_)
    rw [Nat.min_eq_left
        (by
          have := hf.curX; simp; omega)]
    rfl
  | cup row col =>
    obtain ⟨h1, h2⟩ := hs
    obtain ⟨t, p, _, hi, ha, hb2, he⟩ := csi2 row col 0x48 h1 h2 (by decide) (by decide) hg hu
    rw [Ref.Seq.bytes, he, screenOf_ground]
    unfold Vt.csiDispatch; rw [ite_eq_right (by simp [hi])]; dsimp only
    rw [ha 1, hb2 1, count_eq, count_eq]
    exact same_of_eq (moveTo_eq { v with pstate := p } _ _)
  | ind =>
    rw [Ref.Seq.bytes, esc_feed _ hg hu]
    exact lineFeed_ok (facts_pstate hf .esc)
  | ri =>
    rw [Ref.Seq.bytes, esc_feed _ hg hu]
    exact reverseIndex_ok (facts_pstate hf .esc)
  | decsc =>
    rw [Ref.Seq.bytes, esc_feed _ hg hu]; exact same_refl _
  | decrc =>
    rw [Ref.Seq.bytes, esc_feed _ hg hu]
    exact restoreCursor_ok (facts_pstate hf .esc)
  | title both text =>
    rw [title_feed hg hu both text hs]
    exact same_refl _
  | set m
    on =>
    obtain ⟨t, p, hpv, hi, hpar, he⟩ :=
      csi_priv_feed m.number (if on then 0x68 else 0x6C) (by cases m <;> decide)
        (by split <;> decide) (by split <;> decide) hg hu
    rw [Ref.Seq.bytes, he, screenOf_ground]
    have hset :
      ∀ (w : Vt), Vt.csiDispatch w t (if on then 0x68 else 0x6C) = w.setMode true m.number on := by
      intro w
      unfold Vt.csiDispatch
      rw [ite_eq_right (by simp [hi])]
      cases on
      · show Vt.setModes w (t.priv == 0x3F) t.params.toList false = _
        rw [hpar, hpv]; rfl
      · show Vt.setModes w (t.priv == 0x3F) t.params.toList true = _
        rw [hpar, hpv]; rfl
    rw [hset]
    cases m with
    | cursor => exact same_refl _
    | wrap => exact same_refl _
    | paste => exact same_refl _
    | sync => exact same_refl _
    | alt =>
      cases on
      · exact leaveAlt_ok (facts_pstate hf p)
      · exact enterAlt_ok (facts_pstate hf p)
  | sgr attrs =>
    cases attrs with
    | nil =>
      rw [Ref.Seq.bytes, List.flatMap_nil, csi_bare_feed _ (by decide) (by decide) hg hu,
        screenOf_ground]
      refine same_pen (facts_pstate hf (.csi {})) _ _ rfl rfl rfl rfl
    | cons a
      as =>
      have hne : (a :: as).flatMap Ref.Sgr.params ≠ [] := by
        rw [List.flatMap_cons]; cases a <;> simp [Ref.Sgr.params]
      have hle : ∀ n ∈ (a :: as).flatMap Ref.Sgr.params, n ≤ 65535 := by
        intro n hn
        simp only [List.mem_flatMap] at hn
        obtain ⟨b, _, hb⟩ := hn
        exact sgr_le b n hb
      obtain ⟨t, p, hpv, hi, hpar, he⟩ :=
        csi_codes_feed _ 0x6D hne hs hle (by decide) (by decide) hg hu
      rw [Ref.Seq.bytes, he, screenOf_ground]
      have hd :
        Vt.csiDispatch { v with pstate := p } t 0x6D =
          { v with
            pstate := p, pen := (a :: as).foldl Ref.Sgr.apply v.pen } := by
        unfold Vt.csiDispatch
        rw [ite_eq_right (by simp [hi])]
        show (if t.priv == 0 then Vt.applySgr _ t.params.toList else _) = _
        rw [hpv, hpar]
        simp only [beq_self_eq_true, ↓reduceIte]
        unfold Vt.applySgr
        simp only [List.isEmpty_iff, List.map_eq_nil_iff, hne, ↓reduceIte, go_attrs]
      rw [hd]
      exact same_pen (facts_pstate hf p) _ _ rfl rfl rfl rfl
  | decstbm a b =>
    obtain ⟨h1, h2⟩ := hs
    obtain ⟨t, p, hpv, hi, ha, hb2, he⟩ := csi2 a b 0x72 h1 h2 (by decide) (by decide) hg hu
    rw [Ref.Seq.bytes, he, screenOf_ground]
    have hd :
      Vt.csiDispatch { v with pstate := p } t 0x72 =
        if
            Ref.count a - 1 < (if b = 0 then v.rows else b) - 1 ∧
              (if b = 0 then v.rows else b) - 1 < v.rows then
          Vt.moveTo
            { v with
              pstate := p, top := Ref.count a - 1, bot := (if b = 0 then v.rows else b) - 1 }
            0 0
        else { v with pstate := p } := by
      unfold Vt.csiDispatch
      rw [ite_eq_right (by simp [hi])]
      show (if t.priv != 0 then _ else _) = _
      rw [hpv]
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      rw [ha 1, hb2 (VtRec.rows { v with pstate := p }), count_eq]
      by_cases hc :
        Ref.count a - 1 < (if b = 0 then v.rows else b) - 1 ∧
          (if b = 0 then v.rows else b) - 1 < v.rows
      · rw [ite_eq_left (by simpa using hc), ite_eq_left hc]
      · rw [ite_eq_right (by simpa using hc), ite_eq_right hc]
    rw [hd]
    simp only [Ref.Seq.apply]
    by_cases hc :
      Ref.count a - 1 < (if b = 0 then v.rows else b) - 1 ∧
        (if b = 0 then v.rows else b) - 1 < v.rows
    · rw [ite_eq_left hc, ite_eq_left hc]
      refine same_of_eq ((moveTo_eq _ _ _).trans ?_)
      simp [Ref.Screen.home, Ref.Screen.rowAt, Ref.count]
    · rw [ite_eq_right hc, ite_eq_right hc]
      exact same_refl _

/-! ## What linger keeps and skips -/

theorem str_run :
    ∀ (bs : List UInt8) {v : Vt},
      v.pstate = .str false → v.u8need = 0 → (∀ b ∈ bs, b ≠ 0x1B) → v.feed bs = v
  | [], v, _, _, _ => rfl
  | b :: bs, v, hg, hu, hb => by
    rw [feed_cons, step_of_str b hg, abortUtf8_of_uz b hu]
    have e : v.stepStr false b = v := by
      unfold Vt.stepStr
      rw [ite_eq_right (by simp), ite_eq_right (by simpa using hb b (by simp))]
      rw [← hg]
    rw [e]
    exact str_run bs hg hu fun b' hb' => hb b' (by simp [hb'])

theorem str_feed {v : Vt} (intro : List UInt8) (d : List UInt8) (hg : v.pstate = .ground)
    (hu : v.u8need = 0) (hd : ∀ b ∈ d, b ≠ 0x1B)
    (hi : v.feed intro = { v with pstate := .str false }) :
    v.feed (intro ++ d ++ [0x1B, 0x5C]) = v := by
  rw [feed_append, feed_append, hi, str_run d (v := { v with pstate := .str false }) rfl hu hd,
    feed_cons, feed_cons, feed_nil, step_of_str (v := { v with pstate := .str false }) 0x1B rfl,
    abortUtf8_of_uz (v := { v with pstate := .str false }) 0x1B hu]
  unfold Vt.stepStr
  rw [ite_eq_right (by simp), ite_eq_left (by decide)]
  rw [step_of_str (v := { v with pstate := .str true }) 0x5C rfl,
    abortUtf8_of_uz (v := { v with pstate := .str true }) 0x5C hu]
  unfold Vt.stepStr
  rw [ite_eq_left (by decide)]
  rw [← hg]

theorem osc_any :
    ∀ (bs : List UInt8) {v : Vt} {acc : Array UInt8},
      v.pstate = .osc acc false →
        v.u8need = 0 →
        (∀ b ∈ bs, b ≠ 0x07 ∧ b ≠ 0x1B) →
        ∃ extra, v.feed bs = { v with pstate := .osc (acc ++ extra) false }
  | [], v, acc, hg, _, _ =>
    ⟨#[], by
      rw [feed_nil]; rcases v with ⟨⟩; simp_all⟩
  | b :: bs, v, acc, hg, hu, hb => by
    rw [feed_cons, step_of_osc_quiet b hg hu]
    have hb1 := hb b (by simp)
    have e :
      ∃ acc',
        v.stepOsc acc false b = { v with pstate := .osc acc' false } ∧ ∃ ex, acc' = acc ++ ex := by
      unfold Vt.stepOsc
      rw [ite_eq_right (by simp), ite_eq_right (by simpa using hb1.1),
        ite_eq_right (by simpa using hb1.2)]
      split
      · exact ⟨acc, rfl, #[], by simp⟩
      · exact ⟨acc.push b, rfl, #[b], by simp⟩
    obtain ⟨acc', e, ex, rfl⟩ := e
    rw [e]
    obtain ⟨extra, he⟩ :=
      osc_any bs (v := { v with pstate := .osc (acc ++ ex) false }) rfl hu
        (fun b' hb' => hb b' (by simp [hb']))
    exact
      ⟨ex ++ extra, by
        rw [he]; simp⟩

theorem keeps {v : Vt} (hb : v.atBoundary = true) (k : Ref.Kept) (hk : k.Ok) :
    v.feed k.bytes = { v with modes := Ref.Kept.modes v.modes k } := by
  obtain ⟨hg, hu⟩ := boundary hb
  cases k with
  | shape
    k =>
    rw [Ref.Kept.bytes, dec_eq_digits,
      show [0x1B, 0x5B] ++ digits k.val ++ [0x20, 0x71] = shapeAnsi k.val from by
        simp [shapeAnsi, csiB],
      shape_feed_eq k hg hu]
    rfl
  | sixel d =>
    rw [Ref.Kept.bytes, str_feed _ d hg hu hk]
    · rfl
    · rw [feed_cons, esc_step_eq hg hu, feed_cons,
        step_of_esc_quiet (v := { v with pstate := .esc }) 0x50 rfl hu]
      show Vt.feed { v with pstate := .str false } [0x71] = _
      rw [feed_cons, feed_nil, step_of_str (v := { v with pstate := .str false }) 0x71 rfl,
        abortUtf8_of_uz (v := { v with pstate := .str false }) 0x71 hu]
      unfold Vt.stepStr
      rw [ite_eq_right (by simp), ite_eq_right (by decide)]
  | apc d =>
    rw [Ref.Kept.bytes, str_feed _ d hg hu hk]
    · rfl
    · rw [feed_cons, esc_step_eq hg hu, feed_cons, feed_nil,
        step_of_esc_quiet (v := { v with pstate := .esc }) 0x5F rfl hu]
      rfl
  | hyperlink p
    u =>
    rw [Ref.Kept.bytes,
      show
        [0x1B, 0x5D, 0x38, 0x3B] ++ p ++ [0x3B] ++ u ++ [0x07] =
          [0x1B, 0x5D] ++ (([0x38, 0x3B] ++ p ++ [0x3B] ++ u) ++ [0x07])
        from by simp]
    rw [feed_append, feed_cons, esc_step_eq hg hu, feed_cons, feed_nil,
      step_of_esc_quiet (v := { v with pstate := .esc }) 0x5D rfl hu]
    rw [show Vt.stepEsc { v with pstate := .esc } 0x5D = { v with pstate := .osc #[] false } from
        rfl,
      feed_append]
    rw [show [0x38, 0x3B] ++ p ++ [0x3B] ++ u = [0x38] ++ ([0x3B] ++ p ++ [0x3B] ++ u) from by simp,
      feed_append,
      osc_run [0x38] (v := { v with pstate := .osc #[] false }) (acc := #[]) rfl hu (by decide)
        (by decide)]
    obtain ⟨extra, he⟩ :=
      osc_any ([0x3B] ++ p ++ [0x3B] ++ u) (v :=
        { v with pstate := .osc (#[] ++ [0x38].toArray) false }) (acc := #[] ++ [0x38].toArray) rfl
        hu
        (by
          intro b hb'
          simp only [List.append_assoc, List.cons_append, List.nil_append, List.mem_cons,
            List.mem_append] at hb'
          rcases hb' with h | h | h | h <;>
            first
            | (subst h; decide)
            | exact hk b (by simp [h]))
    rw [he, show ∀ w : Vt, w.feed [0x07] = w.step 0x07 from fun _ => rfl,
      step_of_osc_quiet (v := { v with pstate := .osc _ false }) 0x07 rfl hu]
    unfold Vt.stepOsc Vt.oscFinish
    rw [ite_eq_right (by simp), ite_eq_left (by decide)]
    simp
    exact ⟨rfl, hg.symm⟩

/-! ## The headline's parts -/

theorem reads_screenOf (v : Vt) :
    Ref.Reads Vt.colCount Vt.rowCount Vt.getRow Vt.cursorPos Vt.getPen Vt.getModes stick
      Vt.windowTitle v (screenOf v) :=
  ⟨rfl, rfl, fun _ _ _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp [stick], rfl⟩

theorem keeps_all {v : Vt} (hb : v.atBoundary = true) (k : Ref.Kept) (hk : k.Ok) :
    (∀ y, (v.feed k.bytes).getRow y = v.getRow y) ∧
      (v.feed k.bytes).cursorPos = v.cursorPos ∧
      (v.feed k.bytes).getPen = v.getPen ∧
      (v.feed k.bytes).getModes = Ref.Kept.modes v.getModes k ∧
      stick (v.feed k.bytes) = stick v ∧
      (v.feed k.bytes).windowTitle = v.windowTitle ∧ (v.feed k.bytes).atBoundary = true := by
  rw [keeps hb k hk]
  exact ⟨fun _ => rfl, rfl, rfl, rfl, rfl, rfl, hb⟩

/-- A cell two agreeing screens share. -/
theorem Same.cell_at {a b : Ref.Screen} (h : Ref.Same a b) {x y : Nat} (hy : y < a.rows)
    (hx : x < a.cols) : a.cell x y = b.cell x y := h.2.2.1 y hy x hx

/-- A cell a screen reads from its terminal. -/
theorem Reads.cell_at {V : Type} {colCount rowCount : V → Nat} {getRow : V → Nat → Row}
    {cursorPos : V → Nat × Nat} {getPen : V → Pen} {getModes : V → Modes} {stick : V → Sticky}
    {windowTitle : V → String} {v : V} {s : Ref.Screen}
    (h : Ref.Reads colCount rowCount getRow cursorPos getPen getModes stick windowTitle v s)
    {x y : Nat} (hy : y < rowCount v) (hx : x < colCount v) :
    s.cell x y = (getRow v y).getD x default := h.2.2.1 y (h.2.1 ▸ hy) x (h.1 ▸ hx)

/-- A print one column before the right edge of a two-column screen leaves the cursor in the last
column, whatever the screen's deferred wrap. -/
theorem print_x (s : Ref.Screen) (c : Char) (hc : s.cols = 2) (hx : s.x = 1) :
    (s.print c).x = 1 := by
  have hl : ∀ t : Ref.Screen, t.lineFeed.x = t.x ∧ t.lineFeed.cols = t.cols := by
    intro t
    unfold Ref.Screen.lineFeed
    split
    · exact ⟨rfl, rfl⟩
    · split <;> exact ⟨rfl, rfl⟩
  unfold Ref.Screen.print
  dsimp only [Ref.Screen.put]
  split
  · have := hl s.cr
    rw [this.1, this.2]
    simp [Ref.Screen.cr, hc]
  · simp [hc, hx]

/-- IL inside the region moves the cursor to the first column. -/
theorem il_x (s : Ref.Screen) (n : Nat) (h : ¬(s.y < s.top ∨ s.bot < s.y)) :
    (Ref.Seq.apply s (.il n)).x = 0 := by simp only [Ref.Seq.apply, h, ↓reduceIte]

end Terminal.Vt.Conform
