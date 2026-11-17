module

import all Terminal.CoreCode.Render
import all Terminal.CoreCode.Vt
import all Terminal.Proofs.Vt
import all Terminal.Proofs.Vt.State
import all Terminal.Proofs.Render.Pen
import all Terminal.Proofs.Render.Keeps
import all Terminal.Proofs.Render.Quiet
import all Terminal.Proofs.Render.Ends

-- Module-private by default: `Vt`'s fields are sealed (see `packages/terminal/Terminal/Proofs/Vt/State.lean`).

/-! # The reference's bytes, as the emulator parses them

Each sequence of `Vt.Ref.Seq`, fed between control sequences and characters, is one emulator
operation: the parser half of `vt_conforms`. -/

namespace Terminal.Vt.Conform

open Terminal.Vt Terminal.Render

theorem dec_unfold (n : Nat) :
    Ref.dec n =
      if n < 10 then [UInt8.ofNat (0x30 + n)]
      else Ref.dec (n / 10) ++ [UInt8.ofNat (0x30 + n % 10)] := by
  conv =>
    lhs; unfold Ref.dec; rw [WellFounded.Nat.fix_eq]
  conv =>
    rhs; unfold Ref.dec
  simp only [dite_eq_ite]

theorem dec_eq_digits (n : Nat) : Ref.dec n = digits n := by
  induction n using digits.induct with
  | case1 n h =>
    rw [dec_unfold, digits]; simp [h]
  | case2 n h ih =>
    rw [dec_unfold, digits]; simp [h, ih]

theorem params_eq_joinSemi : ∀ ps : List Nat, Ref.params ps = joinSemi ps
  | [] => rfl
  | [n] => by simp [Ref.params, joinSemi, dec_eq_digits]
  | n :: m :: ns => by simp only [Ref.params, joinSemi, params_eq_joinSemi (m :: ns), dec_eq_digits]

/-- A CSI with parameters, from a quiet ground state, is one dispatch of its parameters. -/
theorem csi_codes_feed {v : Vt} (codes : List Nat) (final : UInt8) (hne : codes ≠ [])
    (hcap : codes.length ≤ 16) (hle : ∀ n ∈ codes, n ≤ 65535) (h1 : 0x40 ≤ final)
    (h2 : final ≤ 0x7E) (hg : v.pstate = .ground) (hu : v.u8need = 0) :
    ∃ (t : CsiState) (p : PState),
      t.priv = 0 ∧
        t.ignore = false ∧
        t.params.toList = codes.map (fun n => (n, false)) ∧
        v.feed (Ref.csi codes final) =
          { Vt.csiDispatch { v with pstate := p } t final with pstate := .ground } := by
  rw [show Ref.csi codes final = 0x1B :: 0x5B :: (joinSemi codes ++ [final]) from by
      simp [Ref.csi, params_eq_joinSemi]]
  rw [feed_cons, feed_cons, csi_open_feed hg hu, feed_append]
  obtain ⟨s1, hframe⟩ :=
    csi_param_run_frame (joinSemi codes) (v := { v with pstate := .csi {} }) rfl hu
      (paramBytes_joinSemi codes)
  obtain ⟨s', hs', hhave, hsub, hpriv, hinter, hign, hsize, hpush⟩ :=
    csi_joinSemi_feed codes (v := { v with pstate := .csi {} }) rfl rfl rfl hne
      (by simpa using hcap)
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
  refine ⟨_, _, by simpa using hpriv, by simpa using hign, ?_, rfl⟩
  rw [hpush]
  simp only [List.nil_append]
  exact
    List.map_congr_left
      (fun n hn => by
        rw [show min n 65535 = n from by
            have := hle n hn; omega])

/-- `CSI final` with no parameter, from a quiet ground state, dispatches an empty collector. -/
theorem csi_bare_feed {v : Vt} (final : UInt8) (h1 : 0x40 ≤ final) (h2 : final ≤ 0x7E)
    (hg : v.pstate = .ground) (hu : v.u8need = 0) :
    v.feed (Ref.csi [] final) =
      { Vt.csiDispatch { v with pstate := .csi {} } {} final with pstate := .ground } := by
  rw [show Ref.csi [] final = [0x1B, 0x5B] ++ [final] from rfl, feed_append, keeps_csi_open hg hu,
    show ∀ (w : Vt), w.feed [final] = w.step final from fun _ => rfl,
    csi_final_step_eq (v := { v with pstate := .csi {} }) (s := {}) final rfl hu rfl h1 h2]
  rfl

/-- A private CSI with one parameter, from a quiet ground state, is one dispatch of it. -/
theorem csi_priv_feed {v : Vt} (n : Nat) (final : UInt8) (hn : n ≤ 65535) (h1 : 0x40 ≤ final)
    (h2 : final ≤ 0x7E) (hg : v.pstate = .ground) (hu : v.u8need = 0) :
    ∃ (t : CsiState) (p : PState),
      t.priv = 0x3F ∧
        t.ignore = false ∧
        t.params.toList = [(n, false)] ∧
        v.feed ([0x1B, 0x5B, 0x3F] ++ Ref.dec n ++ [final]) =
          { Vt.csiDispatch { v with pstate := p } t final with pstate := .ground } := by
  rw [dec_eq_digits, List.append_assoc, feed_append, csi_priv_open_eq hg hu,
    csi_digits_tail_eq n final h1 h2 (v := { v with pstate := .csi ({ priv := 0x3F } : CsiState) })
      (s := ({ priv := 0x3F } : CsiState)) rfl hu rfl rfl (by simp)]
  refine ⟨_, _, rfl, rfl, by simp [show min n 65535 = n from by omega], rfl⟩

/-- An ESC sequence with a final byte, from a quiet ground state, is one `stepEsc`. -/
theorem esc_feed {v : Vt} (b : UInt8) (hg : v.pstate = .ground) (hu : v.u8need = 0) :
    v.feed [0x1B, b] = Vt.stepEsc { v with pstate := .esc } b := by
  rw [feed_cons, esc_step_eq hg hu, feed_cons, feed_nil,
    step_of_esc_quiet (v := { v with pstate := .esc }) b rfl hu]

/-- A C0 control other than ESC, from a quiet ground state, is executed. -/
theorem ctl_feed {v : Vt} (b : UInt8) (hb : b < 0x20) (he : b ≠ 0x1B) (hg : v.pstate = .ground)
    (hu : v.u8need = 0) : v.feed [b] = v.ctl b := by
  rw [feed_cons, feed_nil, step_of_ground_quiet b hg hu]
  unfold Vt.stepGround
  rw [ite_eq_right (by simpa using he), ite_eq_left (by simpa using hb)]

/-- A printable ASCII byte, from a quiet ground state, prints. -/
theorem print_feed {v : Vt} (b : UInt8) (h1 : 0x20 ≤ b) (h2 : b < 0x7F) (hg : v.pstate = .ground)
    (hu : v.u8need = 0) : v.feed [b] = v.acceptChar b.toNat := by
  rw [feed_cons, feed_nil, step_of_ground_quiet b hg hu]
  unfold Vt.stepGround
  obtain ⟨e1, e2, e4, e3⟩ : (b == 0x1B) = false ∧ ¬b < 0x20 ∧ b < 0x80 ∧ (b == 0x7F) = false := by
    simp only [UInt8.le_iff_toNat_le, UInt8.lt_iff_toNat_lt, beq_eq_false_iff_ne, ne_eq,
      ← UInt8.toNat_inj] at *
    simp at *
    omega
  rw [ite_eq_right (by simp [e1]), ite_eq_right e2, ite_eq_right (by simp [e3]), ite_eq_left e4]

end Terminal.Vt.Conform
