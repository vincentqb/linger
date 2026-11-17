module

import all Terminal.CoreCode.Render
import all Terminal.CoreCode.Vt
import all Terminal.CoreCode.Mediation
import all Terminal.Proofs.Vt
import all Terminal.Proofs.Vt.State
import all Terminal.Proofs.Vt.Parser
import all Terminal.Proofs.Render.Pen
import all Terminal.Proofs.Render.Keeps
import all Terminal.Proofs.Render.Quiet
import all Terminal.Proofs.Render.Ends
import all Terminal.Proofs.Mediation
import all Terminal.Proofs.Conform.Parse
import all Terminal.Proofs.Conform

-- Module-private by default: `Vt`'s fields are sealed (see `packages/terminal/Terminal/Proofs/Vt/State.lean`).

/-! # Where the title, a bell and a notification come from, token by token

A stream of whole tokens (`Stream.Token`), fed between control sequences and characters: the
emulator's title changes only as OSC 0, OSC 2 and RIS say (`title_source`), and the mediator hears
a bell exactly for a BEL control and a notification exactly for an OSC that posts one
(`asks_exact`). -/

namespace Terminal.Vt.Conform

open Terminal.Vt Terminal.Render

/-! ## The title -/

theorem tt_foldl {α : Type} (f : Vt → α → Vt) (hf : ∀ w a, (f w a).title = w.title) (l : List α)
    (v : Vt) : (l.foldl f v).title = v.title := by
  induction l generalizing v with
  | nil => rfl
  | cons a l ih => rw [List.foldl_cons, ih, hf]

theorem tt_scrollUp (v : Vt) : v.scrollUp.title = v.title := by
  obtain ⟨sb, e⟩ := scrollUpIn_fields v v.top v.bot true
  rw [Vt.scrollUp, e]

theorem tt_lineFeed (v : Vt) : v.lineFeed.title = v.title := by rw [frame_lineFeed]

theorem tt_reverseIndex (v : Vt) : v.reverseIndex.title = v.title := by rw [frame_reverseIndex]

theorem tt_setMode (v : Vt) (p : Bool) (n : Nat) (on : Bool) :
    (v.setMode p n on).title = v.title := by
  unfold Vt.setMode
  repeat' split
  all_goals
    first
    | rfl
    | (unfold Vt.enterAlt; split <;> rfl)
    | (unfold Vt.leaveAlt; split <;> rfl)

theorem tt_tab (v : Vt) : v.tab.title = v.title := rfl

theorem tt_scrollDown (v : Vt) : v.scrollDown.title = v.title := rfl

theorem tt_backTab (v : Vt) : v.backTab.title = v.title := rfl

theorem tt_setModes (v : Vt) (p : Bool) (ps : List (Nat × Bool)) (on : Bool) :
    (v.setModes p ps on).title = v.title := by
  unfold Vt.setModes
  exact tt_foldl _ (fun w (q : Nat × Bool) => tt_setMode w _ q.1 _) _ _

theorem tt_csiDispatch (v : Vt) (s : CsiState) (final : UInt8) :
    (v.csiDispatch s final).title = v.title := by
  fun_cases Vt.csiDispatch v s final
  all_goals try simp only [Vt.repeatAtMost]
  all_goals
    first
    | rfl
    | (rw [frame_eraseScreen])
    | (rw [frame_eraseLine])
    | (rw [frame_insertLines])
    | (rw [frame_deleteLines])
    | exact tt_foldl _ (fun w _ => tt_tab w) _ _
    | exact tt_foldl _ (fun w _ => tt_scrollUp w) _ _
    | exact tt_foldl _ (fun w _ => tt_scrollDown w) _ _
    | exact tt_foldl _ (fun w _ => tt_backTab w) _ _
    | exact tt_setModes _ _ _ _

theorem atBoundary_of {v : Vt} (hg : v.pstate = .ground) (hu : v.u8need = 0) :
    v.atBoundary = true := by
  unfold Vt.atBoundary; simp [hg, hu]

theorem oscFinish_title (v : Vt) (acc : Array UInt8) (st : Bool) :
    (v.oscFinish acc).title = Stream.Token.retitle v.title (.osc acc.toList st) ∧
      (v.oscFinish acc).pstate = .ground ∧ (v.oscFinish acc).u8need = v.u8need := by
  unfold Vt.oscFinish Stream.Token.retitle
  dsimp only
  split
  all_goals (try split)
  all_goals (try split)
  all_goals simp_all

theorem tt_ctl (v : Vt) (b : UInt8) : (v.ctl b).title = v.title := by
  unfold Vt.ctl
  repeat' split
  all_goals
    first
    | rfl
    | exact tt_lineFeed v
    | (unfold Vt.backspace; split <;> rfl)

/-- A private CSI with parameters, from a quiet ground state, is one dispatch. -/
theorem csi_priv_codes_feed {v : Vt} (codes : List Nat) (final : UInt8) (hcap : codes.length ≤ 16)
    (h1 : 0x40 ≤ final) (h2 : final ≤ 0x7E) (hg : v.pstate = .ground) (hu : v.u8need = 0) :
    ∃ (t : CsiState) (p : PState),
      v.feed ([0x1B, 0x5B, 0x3F] ++ joinSemi codes ++ [final]) =
        { Vt.csiDispatch { v with pstate := p } t final with pstate := .ground } := by
  rw [List.append_assoc, feed_append, csi_priv_open_eq hg hu]
  cases codes with
  | nil =>
    rw [show joinSemi [] ++ [final] = [final] from rfl,
      show ∀ (w : Vt), w.feed [final] = w.step final from fun _ => rfl,
      csi_final_step_eq (v := { v with pstate := .csi ({ priv := 0x3F } : CsiState) }) (s :=
        ({ priv := 0x3F } : CsiState)) final rfl hu rfl h1 h2]
    exact ⟨_, _, rfl⟩
  | cons c cs =>
    rw [feed_append]
    obtain ⟨s1, hframe⟩ :=
      csi_param_run_frame (joinSemi (c :: cs)) (v :=
        { v with pstate := .csi ({ priv := 0x3F } : CsiState) }) rfl hu
        (paramBytes_joinSemi (c :: cs))
    obtain ⟨s', hs', hhave, hsub, hpriv, hinter, hign, hsize, hpush⟩ :=
      csi_joinSemi_feed (c :: cs) (v := { v with pstate := .csi ({ priv := 0x3F } : CsiState) }) rfl
        rfl rfl (by simp) (by simpa using hcap)
    have hid : s1 = s' := by
      rw [hframe] at hs'
      exact PState.csi.inj hs'
    rw [hid] at hframe
    rw [hframe, show ∀ (w : Vt), w.feed [final] = w.step final from fun _ => rfl]
    rw [csi_final_step_eq (v := { v with pstate := .csi s' }) (s := s') final rfl hu
        (by simpa using hinter) h1 h2]
    unfold Vt.csiFinish
    dsimp only
    rw [ite_eq_left hhave,
      ite_eq_right
        (by
          simp; omega)]
    exact ⟨_, _, rfl⟩

theorem esc_rest (w : Vt) (f : UInt8) (hu : w.u8need = 0) (h1 : 0x30 ≤ f) (h2 : f ≤ 0x7E)
    (h3 : f ≠ 0x50) (h4 : f ≠ 0x58) (h5 : f ≠ 0x5B) (h6 : f ≠ 0x5D) (h7 : f ≠ 0x5E) (h8 : f ≠ 0x5F)
    (hc : f ≠ 0x63) :
    (w.stepEsc f).title = w.title ∧ (w.stepEsc f).pstate = .ground ∧ (w.stepEsc f).u8need = 0 := by
  unfold Vt.stepEsc
  split
  all_goals
    first
    | (exfalso; contradiction)
    | exact ⟨rfl, rfl, hu⟩
    | exact ⟨tt_lineFeed _, rfl, (un_lineFeed _).trans hu⟩
    | exact ⟨tt_lineFeed _, rfl, (un_lineFeed _).trans hu⟩
    | exact ⟨tt_reverseIndex _, rfl, (un_reverseIndex _).trans hu⟩
    | skip
  have h1' := UInt8.le_iff_toNat_le.mp h1
  have h2' := UInt8.le_iff_toNat_le.mp h2
  have e1 : ¬((decide (f ≥ 32) && decide (f ≤ 47)) = true) := by
    simp only [Bool.and_eq_true, decide_eq_true_eq, ge_iff_le, UInt8.le_iff_toNat_le]
    simp at h1' ⊢
    omega
  have e2 : (decide (f ≥ 48) && decide (f ≤ 126)) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq, ge_iff_le, UInt8.le_iff_toNat_le]
    simp at h1' h2' ⊢
    omega
  rw [ite_eq_right e1, ite_eq_left e2]
  exact ⟨rfl, rfl, hu⟩

theorem token_title {v : Vt} (hb : v.atBoundary = true) (t : Stream.Token) (ht : t.Ok) :
    (v.feed t.bytes).title = Stream.Token.retitle v.title t ∧
      (v.feed t.bytes).atBoundary = true := by
  obtain ⟨hg, hu⟩ := boundary hb
  cases t with
  | text c =>
    obtain ⟨h1, h2⟩ := ht
    have hb' : (UInt8.ofNat c.toNat).toNat = c.toNat := by
      simp [UInt8.toNat_ofNat']; omega
    rw [Stream.Token.bytes,
      print_feed _
        (by
          simp [UInt8.le_iff_toNat_le, hb']; omega)
        (by
          simp [UInt8.lt_iff_toNat_lt, hb']; omega)
        hg hu]
    have ho : offScreen (v.acceptChar (UInt8.ofNat c.toNat).toNat) = offScreen v := by
      unfold Vt.acceptChar; split <;> exact off_print _ _
    simp only [offScreen, OffScreen.mk.injEq] at ho
    exact
      ⟨ho.2.2.2.2.2.2.2.2.1,
        atBoundary_of (ho.2.2.2.2.2.2.2.2.2.2.2.2.2.1.trans hg)
          (ho.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.trans hu)⟩
  | control b =>
    obtain ⟨h1, h2⟩ := ht
    rw [Stream.Token.bytes, ctl_feed b h1 h2 hg hu]
    exact ⟨tt_ctl v b, atBoundary_of ((ps_ctl v b).trans hg) ((un_ctl v b).trans hu)⟩
  | csi priv ps f =>
    obtain ⟨hcap, hle, h1, h2⟩ := ht
    have hd :
      ∃ (t : CsiState) (p : PState),
        v.feed (Stream.Token.csi priv ps f).bytes =
          { Vt.csiDispatch { v with pstate := p } t f with pstate := .ground } := by
      cases priv with
      | false =>
        rw [Stream.Token.bytes,
          show
            [0x1B, 0x5B] ++ (if false = true then [0x3F] else []) ++ Vt.Ref.params ps ++ [f] =
              Vt.Ref.csi ps f
            from by simp [Vt.Ref.csi]]
        cases ps with
        | nil => exact ⟨_, _, csi_bare_feed f h1 h2 hg hu⟩
        | cons c
          cs =>
          obtain ⟨t, p, -, -, -, he⟩ := csi_codes_feed (c :: cs) f (by simp) hcap hle h1 h2 hg hu
          exact ⟨t, p, he⟩
      | true =>
        rw [Stream.Token.bytes,
          show
            [0x1B, 0x5B] ++ (if true = true then [0x3F] else []) ++ Vt.Ref.params ps ++ [f] =
              [0x1B, 0x5B, 0x3F] ++ joinSemi ps ++ [f]
            from by simp [params_eq_joinSemi]]
        exact csi_priv_codes_feed ps f hcap h1 h2 hg hu
    obtain ⟨t, p, he⟩ := hd
    rw [he]
    refine
      ⟨by
        rw [show (Vt.csiDispatch { v with pstate := p } t f).title = v.title from
            tt_csiDispatch _ _ _];
        rfl, atBoundary_of rfl ?_⟩
    show (Vt.csiDispatch { v with pstate := p } t f).u8need = 0
    rw [un_csiDispatch]; exact hu
  | osc pl st =>
    obtain ⟨hp, hcap⟩ := ht
    have hcap' : pl.length + 3 ≤ 256 := hcap
    rw [Stream.Token.bytes, List.append_assoc, feed_append, feed_cons, esc_step_eq hg hu, feed_cons,
      feed_nil, step_of_esc_quiet (v := { v with pstate := .esc }) 0x5D rfl hu,
      show Vt.stepEsc { v with pstate := .esc } 0x5D = { v with pstate := .osc #[] false } from rfl,
      feed_append,
      osc_run pl (v := { v with pstate := .osc #[] false }) (acc := #[]) rfl hu hp
        (by
          simp; omega)]
    have hfin :
      ∀ (w : Vt),
        w.pstate = .osc (#[] ++ pl.toArray) false →
          w.u8need = 0 →
          w.feed (if st = true then [0x1B, 0x5C] else [0x07]) =
            w.oscFinish (#[] ++ pl.toArray) := by
      intro w hw hwu
      cases st with
      | false =>
        show w.step 0x07 = _
        rw [step_of_osc_quiet 0x07 hw hwu]
        unfold Vt.stepOsc
        rw [ite_eq_right (by simp), ite_eq_left (by decide)]
      | true =>
        show (w.step 0x1B).step 0x5C = _
        rw [step_of_osc_quiet 0x1B hw hwu]
        have e1 :
          w.stepOsc (#[] ++ pl.toArray) false 0x1B =
            { w with pstate := .osc (#[] ++ pl.toArray) true } := by
          unfold Vt.stepOsc
          rw [ite_eq_right (by simp), ite_eq_right (by decide), ite_eq_left (by decide)]
        rw [e1,
          step_of_osc_quiet (v := { w with pstate := .osc (#[] ++ pl.toArray) true }) 0x5C rfl hwu]
        unfold Vt.stepOsc
        rw [ite_eq_left (by decide)]
        rfl
    rw [hfin { v with pstate := .osc (#[] ++ pl.toArray) false } rfl hu]
    obtain ⟨e1, e2, e3⟩ :=
      oscFinish_title { v with pstate := .osc (#[] ++ pl.toArray) false } (#[] ++ pl.toArray) st
    refine ⟨?_, atBoundary_of e2 (e3.trans hu)⟩
    rw [e1]
    simp
  | str i d =>
    obtain ⟨hi, hd⟩ := ht
    rw [Stream.Token.bytes, str_feed [0x1B, i] d hg hu hd ?_]
    · exact ⟨by simp [Stream.Token.retitle], hb⟩
    · rw [esc_feed i hg hu]
      rcases hi with rfl | rfl | rfl | rfl <;> rfl
  | esc f =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := ht
    rw [Stream.Token.bytes, esc_feed f hg hu]
    by_cases hc : f = 0x63
    · subst hc
      exact ⟨rfl, rfl⟩
    · have hr : Stream.Token.retitle v.title (.esc f) = v.title := by
        unfold Stream.Token.retitle; split <;> simp_all
      rw [hr]
      have hw := esc_rest { v with pstate := .esc } f hu h1 h2 h3 h4 h5 h6 h7 h8 hc
      exact ⟨hw.1, atBoundary_of hw.2.1 hw.2.2⟩

theorem title_stream {v : Vt} (hb : v.atBoundary = true) (ts : List Stream.Token)
    (ok : ∀ t ∈ ts, t.Ok) :
    (v.feed (ts.flatMap Stream.Token.bytes)).windowTitle =
        ts.foldl Stream.Token.retitle v.windowTitle ∧
      (v.feed (ts.flatMap Stream.Token.bytes)).atBoundary = true := by
  induction ts generalizing v with
  | nil => exact ⟨rfl, hb⟩
  | cons t ts ih =>
    rw [List.flatMap_cons, feed_append]
    obtain ⟨h1, h2⟩ := token_title hb t (ok t (by simp))
    obtain ⟨h3, h4⟩ := ih h2 (fun t' ht' => ok t' (by simp [ht']))
    refine ⟨?_, h4⟩
    rw [h3, List.foldl_cons]
    exact congrArg (fun x => ts.foldl Stream.Token.retitle x) h1

end Terminal.Vt.Conform

namespace Terminal.Mediation

open Terminal.Vt Terminal.Render

/-- A byte from `0` to `?`, as CSI parameters and the private marker are. -/
def Body (bs : Bytes) : Prop := ∀ b ∈ bs, 0x30 ≤ b ∧ b ≤ 0x3F

theorem csi_body :
    ∀ (bs : Bytes) (v : Vt) (s : Scan),
      Body bs →
        (∃ rev, s = .csi rev) ∨ s = .csiPass →
        ((∃ rev, (feed v s bs).scan = .csi rev) ∨ (feed v s bs).scan = .csiPass) ∧
          (feed v s bs).asks = false ∧ (feed v s bs).notice = none ∧ (feed v s bs).progress = none
  | [], _, s, _, hs => ⟨hs, rfl, rfl, rfl⟩
  | b :: bs, v, s, hb, hs => by
    obtain ⟨h1, h2⟩ := hb b (by simp)
    have hne : b ≠ ESC := by
      intro h; rw [h] at h1; exact absurd h1 (by decide)
    have hbel : b ≠ BEL := by
      intro h; rw [h] at h1; exact absurd h1 (by decide)
    have hnf : ¬(0x40 ≤ b ∧ b ≤ 0x7E) := by
      intro h
      have := UInt8.le_iff_toNat_le.mp h.1
      have := UInt8.le_iff_toNat_le.mp h2
      simp at *; omega
    have hstep :
      (∃ rev, (s.step (v.step b) b).scan = .csi rev) ∨ (s.step (v.step b) b).scan = .csiPass := by
      rcases hs with ⟨rev, rfl⟩ | rfl
      · simp only [Scan.step, hne, beq_iff_eq, ite_false]
        rw [ite_eq_right (by simpa using hnf)]
        split
        · exact .inl ⟨_, rfl⟩
        · exact .inr rfl
      · simp only [Scan.step, beq_iff_eq, hne, ite_false]
        rw [ite_eq_right (by simpa using hnf)]
        exact .inr rfl
    have hheard : s.hears b = {} := by
      rcases hs with ⟨rev, rfl⟩ | rfl
      · exact (hears_outside b hbel rev).2.2.1
      · exact (hears_outside b hbel []).2.2.2
    obtain ⟨r1, r2, r3, r4⟩ := csi_body bs (v.step b) _ (fun c hc => hb c (by simp [hc])) hstep
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact r1
    · rw [(hears_feed_cons v s b bs).1, hheard, r2]; rfl
    · rw [(hears_feed_cons v s b bs).2, hheard, r3]; rfl
    · rw [progress_feed_cons, hheard, r4]; rfl

/-- Where a DCS, SOS, PM or APC string's scanner stands within its data. -/
def InStr (s : Scan) : Prop :=
  s = .dcsIntro ∨ (∃ k, s = .dcsKind k) ∨ (∃ k p, s = .dcs k p false) ∨ s = .strPass false

theorem str_body :
    ∀ (bs : Bytes) (v : Vt) (s : Scan),
      (∀ b ∈ bs, b ≠ ESC) →
        InStr s →
        InStr (feed v s bs).scan ∧
          (feed v s bs).asks = false ∧ (feed v s bs).notice = none ∧ (feed v s bs).progress = none
  | [], _, s, _, hs => ⟨hs, rfl, rfl, rfl⟩
  | b :: bs, v, s, hb, hs => by
    have hne : b ≠ ESC := hb b (by simp)
    have hstep : InStr (s.step (v.step b) b).scan := by
      rcases hs with rfl | ⟨k, rfl⟩ | ⟨k, p, rfl⟩ | rfl
      · simp only [Scan.step]; split
        · exact .inr (.inl ⟨_, rfl⟩)
        · simp [InStr, hne]
      · simp only [Scan.step]; split
        · exact .inr (.inr (.inl ⟨_, _, rfl⟩))
        · simp [InStr, hne]
      · simp only [Scan.step, hne, Bool.false_and, Bool.false_eq_true, ↓reduceIte, beq_iff_eq]
        split
        · exact .inr (.inr (.inl ⟨k, b :: p, by simp [hne]⟩))
        · simp [InStr, hne]
      · simp [Scan.step, InStr, hne]
    have hheard : s.hears b = {} := by rcases hs with rfl | ⟨k, rfl⟩ | ⟨k, p, rfl⟩ | rfl <;> rfl
    obtain ⟨r1, r2, r3, r4⟩ := str_body bs (v.step b) _ (fun c hc => hb c (by simp [hc])) hstep
    exact
      ⟨r1, by
        rw [(hears_feed_cons v s b bs).1, hheard, r2]; rfl, by
        rw [(hears_feed_cons v s b bs).2, hheard, r3]; rfl, by
        rw [progress_feed_cons, hheard, r4]; rfl⟩

theorem str_end (v : Vt) (s : Scan) (hs : InStr s) :
    (feed v s [ESC, STFinal]).scan = .ground ∧
      (feed v s [ESC, STFinal]).asks = false ∧
      (feed v s [ESC, STFinal]).notice = none ∧ (feed v s [ESC, STFinal]).progress = none := by
  have hend :
    (s.step (v.step ESC) ESC).scan = .strPass true ∨
      ∃ k p, (s.step (v.step ESC) ESC).scan = .dcs k p true := by
    rcases hs with rfl | ⟨k, rfl⟩ | ⟨k, p, rfl⟩ | rfl
    · simp [Scan.step, ESC]
    · simp [Scan.step, ESC]
    · simp only [Scan.step, Bool.false_and, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true]
      split
      · exact .inr ⟨_, _, rfl⟩
      · exact .inl rfl
    · simp [Scan.step]
  have hheard : s.hears ESC = {} := by rcases hs with rfl | ⟨k, rfl⟩ | ⟨k, p, rfl⟩ | rfl <;> rfl
  obtain ⟨c1, c2⟩ := hears_feed_cons v s ESC [STFinal]
  obtain ⟨e1, e2, e3⟩ := feed_single (v.step ESC) (s.step (v.step ESC) ESC).scan STFinal
  refine ⟨?_, ?_, ?_, ?_⟩
  · show (feed (v.step ESC) (s.step (v.step ESC) ESC).scan [STFinal]).scan = _
    rw [e3]
    rcases hend with h | ⟨k, p, h⟩ <;> rw [h]
    · simp [Scan.step]
    · simp only [Scan.step, beq_self_eq_true, Bool.and_self, ↓reduceIte]
      split <;> (try split) <;> exact complete_scan _ _
  · rw [c1, hheard, e1]
    rcases hend with h | ⟨k, p, h⟩ <;> rw [h] <;> rfl
  · rw [c2, hheard, e2]
    rcases hend with h | ⟨k, p, h⟩ <;> rw [h] <;> rfl
  · rw [progress_feed_cons, hheard, feed_single_progress]
    rcases hend with h | ⟨k, p, h⟩ <;> rw [h] <;> rfl

theorem feed_three (v : Vt) (s : Scan) (a b c : Bytes) :
    (feed v s (a ++ b ++ c)).scan =
        (feed (feed (feed v s a).vt (feed v s a).scan b).vt
            (feed (feed v s a).vt (feed v s a).scan b).scan c).scan ∧
      (feed v s (a ++ b ++ c)).asks =
        ((feed v s a).asks || (feed (feed v s a).vt (feed v s a).scan b).asks ||
          (feed (feed (feed v s a).vt (feed v s a).scan b).vt
              (feed (feed v s a).vt (feed v s a).scan b).scan c).asks) ∧
      (feed v s (a ++ b ++ c)).notice =
        ((feed (feed (feed v s a).vt (feed v s a).scan b).vt
              (feed (feed v s a).vt (feed v s a).scan b).scan c).notice.or
          ((feed (feed v s a).vt (feed v s a).scan b).notice.or (feed v s a).notice)) ∧
      (feed v s (a ++ b ++ c)).progress =
        ((feed (feed (feed v s a).vt (feed v s a).scan b).vt
              (feed (feed v s a).vt (feed v s a).scan b).scan c).progress.or
          ((feed (feed v s a).vt (feed v s a).scan b).progress.or (feed v s a).progress)) := by
  rw [List.append_assoc]
  obtain ⟨a1, a2, a3⟩ := feed_append_heard v s a (b ++ c)
  obtain ⟨b1, b2, b3⟩ := feed_append_heard (feed v s a).vt (feed v s a).scan b c
  have a4 := feed_append_progress v s a (b ++ c)
  have b4 := feed_append_progress (feed v s a).vt (feed v s a).scan b c
  rw [a1, a2, a3, a4, b1, b2, b3, b4, Bool.or_assoc, Option.or_assoc, Option.or_assoc]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem token_heard (v : Vt) (t : Stream.Token) (ht : t.Ok) :
    (feed v .ground t.bytes).scan = .ground ∧
      (feed v .ground t.bytes).asks = t.asks ∧
      (feed v .ground t.bytes).notice = t.notice ∧
      (feed v .ground t.bytes).progress = t.progress := by
  cases t with
  | text c =>
    obtain ⟨h1, h2⟩ := ht
    have hb' : (UInt8.ofNat c.toNat).toNat = c.toNat := by
      simp [UInt8.toNat_ofNat']; omega
    have hne : UInt8.ofNat c.toNat ≠ ESC := by
      intro h; have := congrArg UInt8.toNat h; rw [hb'] at this; simp [ESC] at this; omega
    have hbel : UInt8.ofNat c.toNat ≠ BEL := by
      intro h; have := congrArg UInt8.toNat h; rw [hb'] at this; simp [BEL] at this; omega
    obtain ⟨e1, e2, e3⟩ := feed_single v .ground (UInt8.ofNat c.toNat)
    rw [Stream.Token.bytes]
    exact
      ⟨by
        rw [e3]; simp [Scan.step, hne], by
        rw [e1]; simp [Scan.hears, hbel, Stream.Token.asks, Stream.Token.notice], by
        rw [e2]; rfl, by
        rw [feed_single_progress]; simp [Scan.hears, Stream.Token.progress]⟩
  | control b =>
    obtain ⟨_, h2⟩ := ht
    obtain ⟨e1, e2, e3⟩ := feed_single v .ground b
    rw [Stream.Token.bytes]
    exact
      ⟨by
        rw [e3]; simp [Scan.step, h2, ESC], by
        rw [e1]; simp [Scan.hears, Stream.Token.asks, BEL], by
        rw [e2]; rfl, by
        rw [feed_single_progress]; simp [Scan.hears, Stream.Token.progress]⟩
  | csi priv ps f =>
    obtain ⟨_, _, h1, h2⟩ := ht
    have hbody : Body ((if priv then [0x3F] else []) ++ Vt.Ref.params ps) := by
      intro b hb
      simp only [List.mem_append] at hb
      rcases hb with hb | hb
      · split at hb
        · simp at hb; subst hb; decide
        · simp at hb
      · rw [Vt.Conform.params_eq_joinSemi] at hb
        have := paramBytes_joinSemi ps b hb
        exact
          ⟨this.1, by
            have := UInt8.le_iff_toNat_le.mp this.2
            exact
              UInt8.le_iff_toNat_le.mpr
                (by
                  simp at this ⊢; omega)⟩
    have hf : f ≠ ESC ∧ f ≠ BEL ∧ (0x40 ≤ f && f ≤ 0x7E) = true := by
      have := UInt8.le_iff_toNat_le.mp h1
      refine ⟨fun h => ?_, fun h => ?_, by simp [h1, h2]⟩ <;> rw [h] at this <;>
        simp [ESC, BEL] at this
    rw [Stream.Token.bytes,
      show
        [0x1B, 0x5B] ++ (if priv = true then [0x3F] else []) ++ Vt.Ref.params ps ++ [f] =
          [ESC, 0x5B] ++ ((if priv = true then [0x3F] else []) ++ Vt.Ref.params ps) ++ [f]
        from by simp [ESC]]
    obtain ⟨t1, t2, t3, t4⟩ :=
      feed_three v .ground [ESC, 0x5B] ((if priv = true then [0x3F] else []) ++ Vt.Ref.params ps)
        [f]
    have o :
      (feed v .ground [ESC, 0x5B]).scan = .csi [0x5B, ESC] ∧
        (feed v .ground [ESC, 0x5B]).asks = false ∧
        (feed v .ground [ESC, 0x5B]).notice = none ∧
        (feed v .ground [ESC, 0x5B]).progress = none := by
      simp [feed, Scan.step, Scan.hears, ESC, BEL]
    rw [t1, t2, t3, t4, o.1, o.2.1, o.2.2.1, o.2.2.2]
    obtain ⟨b1, b2, b3, b4⟩ :=
      csi_body _ (feed v .ground [ESC, 0x5B]).vt (.csi [0x5B, ESC]) hbody (.inl ⟨_, rfl⟩)
    rw [b2, b3, b4]
    generalize
      (feed (feed v .ground [ESC, 0x5B]).vt (Scan.csi [0x5B, ESC])
          ((if priv = true then [0x3F] else []) ++ Vt.Ref.params ps)).vt =
      u at b1 ⊢
    obtain ⟨e1, e2, e3⟩ := feed_single u _ f
    rw [e1, e2, e3, feed_single_progress]
    rcases b1 with ⟨rev, h⟩ | h <;> rw [h]
    · refine
        ⟨?_, by simp [Scan.hears, hf.2.1, Stream.Token.asks, Stream.Token.notice], by
          simp [Scan.hears, Stream.Token.notice], by simp [Scan.hears, Stream.Token.progress]⟩
      simp only [Scan.step, hf.1, beq_iff_eq, ite_false, hf.2.2, ite_true]
      exact complete_scan _ _
    · refine
        ⟨by simp [Scan.step, hf.1, hf.2.2], by
          simp [Scan.hears, hf.2.1, Stream.Token.asks, Stream.Token.notice], by
          simp [Scan.hears, Stream.Token.notice], by simp [Scan.hears, Stream.Token.progress]⟩
  | osc pl st =>
    obtain ⟨hp, hcap⟩ := ht
    have hplain : Plain pl := hp
    have hn :=
      feed_osc_notice v pl hplain hcap (if st then [ESC, STFinal] else [BEL]) (by cases st <;> simp)
    have hp :=
      feed_osc_progress v pl hplain hcap (if st then [ESC, STFinal] else [BEL])
        (by cases st <;> simp)
    rw [Stream.Token.bytes,
      show
        [0x1B, 0x5D] ++ pl ++ (if st = true then [0x1B, 0x5C] else [0x07]) =
          [ESC, 0x5D] ++ pl ++ (if st = true then [ESC, STFinal] else [BEL])
        from rfl]
    refine
      ⟨?_, by
        rw [hn.1]; rfl, by
        rw [hn.2]; rfl, by
        rw [hp]; rfl⟩
    obtain ⟨t1, -, -⟩ :=
      feed_three v .ground [ESC, 0x5D] pl (if st = true then [ESC, STFinal] else [BEL])
    rw [t1, (feed_osc_open v).1]
    generalize (feed v .ground [ESC, 0x5D]).vt = w
    rw [(feed_osc_plain w [0x5D, ESC] pl hplain
          (by
            simp [oscCap] at hcap ⊢; omega)).1]
    generalize (feed w (.osc [0x5D, ESC] false) pl).vt = u
    have hfit : pl.length + 2 < oscCap := by omega
    cases st with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [(feed_single u _ BEL).2.2]
      simp only [Scan.step, beq_self_eq_true, Bool.true_or, ↓reduceIte]
      exact complete_scan _ _
    | true =>
      simp only [↓reduceIte]
      show
        (feed (u.step ESC) ((Scan.osc (pl.reverse ++ [0x5D, ESC]) false).step (u.step ESC) ESC).scan
              [STFinal]).scan =
          _
      have hstep :
        ((Scan.osc (pl.reverse ++ [0x5D, ESC]) false).step (u.step ESC) ESC).scan =
          .osc (ESC :: (pl.reverse ++ [0x5D, ESC])) true := by
        simp [Scan.step, hfit, ESC, BEL]
      rw [hstep, (feed_single _ _ STFinal).2.2]
      simp only [Scan.step, beq_self_eq_true, Bool.and_self, Bool.or_true, ↓reduceIte]
      exact complete_scan _ _
  | str i d =>
    obtain ⟨hi, hd⟩ := ht
    rw [Stream.Token.bytes,
      show [0x1B, i] ++ d ++ [0x1B, 0x5C] = [ESC, i] ++ d ++ [ESC, STFinal] from rfl]
    obtain ⟨t1, t2, t3, t4⟩ := feed_three v .ground [ESC, i] d [ESC, STFinal]
    have o :
      InStr (feed v .ground [ESC, i]).scan ∧
        (feed v .ground [ESC, i]).asks = false ∧
        (feed v .ground [ESC, i]).notice = none ∧ (feed v .ground [ESC, i]).progress = none := by
      rcases hi with rfl | rfl | rfl | rfl <;> simp [feed, Scan.step, Scan.hears, ESC, BEL, InStr]
    obtain ⟨s1, s2, s3, s4⟩ := str_body d (feed v .ground [ESC, i]).vt _ hd o.1
    obtain ⟨f1, f2, f3, f4⟩ :=
      str_end (feed (feed v .ground [ESC, i]).vt (feed v .ground [ESC, i]).scan d).vt _ s1
    rw [t1, t2, t3, t4, o.2.1, o.2.2.1, o.2.2.2, s2, s3, s4, f1, f2, f3, f4]
    exact ⟨rfl, rfl, rfl, rfl⟩
  | esc f =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := ht
    rw [Stream.Token.bytes]
    have hf : f ≠ ESC ∧ f ≠ BEL := by
      have := UInt8.le_iff_toNat_le.mp h1
      refine ⟨fun h => ?_, fun h => ?_⟩ <;> rw [h] at this <;> simp [ESC, BEL] at this
    simp [feed, Scan.step, Scan.hears, Stream.Token.asks, Stream.Token.notice,
      Stream.Token.progress, ESC, BEL, hf.1, hf.2, h3, h4, h5, h6, h7, h8]

theorem notice_foldl (ts : List Stream.Token) (acc : Option Bytes) :
    ts.foldl (fun n t => t.notice.or n) acc =
      (ts.foldl (fun n t => t.notice.or n) none).or acc := by
  induction ts generalizing acc with
  | nil => simp
  | cons t ts
    ih =>
    rw [List.foldl_cons, List.foldl_cons, ih, ih (t.notice.or none), Option.or_assoc]
    simp

theorem heard_stream (v : Vt) (ts : List Stream.Token) (ok : ∀ t ∈ ts, t.Ok) :
    (feed v .ground (ts.flatMap Stream.Token.bytes)).vt = v.feed (ts.flatMap Stream.Token.bytes) ∧
      (feed v .ground (ts.flatMap Stream.Token.bytes)).asks = ts.any Stream.Token.asks ∧
      (feed v .ground (ts.flatMap Stream.Token.bytes)).notice = Stream.notice ts := by
  refine ⟨feed_vt _ _ _, ?_⟩
  induction ts generalizing v with
  | nil => exact ⟨rfl, rfl⟩
  | cons t ts
    ih =>
    obtain ⟨a1, a2, -⟩ := feed_append_heard v .ground t.bytes (ts.flatMap Stream.Token.bytes)
    obtain ⟨h1, h2, h3, -⟩ := token_heard v t (ok t (by simp))
    obtain ⟨r1, r2⟩ := ih (feed v .ground t.bytes).vt (fun t' ht' => ok t' (by simp [ht']))
    rw [List.flatMap_cons, a1, a2, h1, h2, h3, r1, r2]
    refine ⟨by simp, ?_⟩
    unfold Stream.notice
    rw [List.foldl_cons, notice_foldl ts (t.notice.or none)]
    simp

theorem progress_foldl (ts : List Stream.Token) (acc : Option (Option Progress)) :
    ts.foldl (fun p t => t.progress.or p) acc =
      (ts.foldl (fun p t => t.progress.or p) none).or acc := by
  induction ts generalizing acc with
  | nil => simp
  | cons t ts
    ih =>
    rw [List.foldl_cons, List.foldl_cons, ih, ih (t.progress.or none), Option.or_assoc]
    simp

/-- The progress a program has declared after a stream, from `p`: the last report's state, as
`Token.reprogress` folds it. -/
theorem reprogress_foldl (ts : List Stream.Token) (p : Option Progress) :
    ((ts.foldl (fun q t => t.progress.or q) none).getD p) = ts.foldl Stream.Token.reprogress p := by
  induction ts generalizing p with
  | nil => rfl
  | cons t ts ih =>
    rw [List.foldl_cons, List.foldl_cons, progress_foldl, ← ih]
    cases h : (ts.foldl (fun q t => t.progress.or q) none) <;> cases ht : t.progress <;>
      simp [Stream.Token.reprogress, ht]

/-- The progress a stream reports, fed from ground: the last report among its tokens. -/
theorem progress_stream (v : Vt) (ts : List Stream.Token) (ok : ∀ t ∈ ts, t.Ok) :
    (feed v .ground (ts.flatMap Stream.Token.bytes)).progress =
      ts.foldl (fun p t => t.progress.or p) none := by
  induction ts generalizing v with
  | nil => rfl
  | cons t ts
    ih =>
    obtain ⟨-, -, a3⟩ := feed_append_heard v .ground t.bytes (ts.flatMap Stream.Token.bytes)
    have a4 := feed_append_progress v .ground t.bytes (ts.flatMap Stream.Token.bytes)
    obtain ⟨h1, -, -, h4⟩ := token_heard v t (ok t (by simp))
    rw [List.flatMap_cons, a4, h1, h4,
      ih (feed v .ground t.bytes).vt (fun t' ht' => ok t' (by simp [ht'])), List.foldl_cons,
      progress_foldl ts (t.progress.or none), Option.or_none]

end Terminal.Mediation

namespace Terminal.Vt.Conform
end Terminal.Vt.Conform
