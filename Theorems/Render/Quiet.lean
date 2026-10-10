module

import all Linger.Core.Render
import all Linger.Core.Vt
import all Theorems.Render.Ends

-- Module-private by default: `Vt`'s fields are sealed (see `Theorems/Vt/State.lean`).

/-! # §Replay stage 3c — the numbers survive the round trip

`Quiet` and the digit bridge: what the emitted decimal parameters mean by the time
the parser has accumulated them, and that DECOM stays off through every stage of a
restore stream. Split out of `Theorems/Render.lean`; see that façade for the ladder
as a whole. -/

namespace Linger.Core.Render

open Linger.Core.Vt

/-! ## §Replay stage 3c — the numbers survive the round trip

Everything numeric in a restore stream (cursor positions, the scroll
region, mode numbers, colour components) is emitted by `digits` and read
back by the CSI parameter accumulator. This section proves those two are
inverse, up to the parser's documented 65535 clamp — the foundation the
value-fidelity theorems stand on.
-/

/-- The parser's parameter accumulator, as a fold: one digit byte at a
time, clamped exactly where `stepCsi` clamps. -/
def accDigits (cur : Nat) (bs : Bytes) : Nat :=
  bs.foldl (fun c b => min (c * 10 + (b.toNat - 0x30)) 65535) cur

theorem accDigits_append (cur : Nat) (a b : Bytes) :
    accDigits cur (a ++ b) = accDigits (accDigits cur a) b := by simp [accDigits, List.foldl_append]

/-- A digit byte's numeric value is recovered by subtracting `'0'`. -/
theorem digitByte_toNat (d : Nat) (hd : d < 10) : (UInt8.ofNat (0x30 + d)).toNat - 0x30 = d := by
  have h : (0x30 + d) < 256 := by omega
  simp [UInt8.toNat_ofNat', Nat.mod_eq_of_lt h]

/-- **The digit round trip.** Feeding `digits n` into a fresh accumulator
yields `n`, clamped at 65535 exactly as the parser clamps. -/
theorem accDigits_digits (n : Nat) : accDigits 0 (digits n) = min n 65535 := by
  induction n using digits.induct with
  | case1 n h =>
    rw [digits]
    simp only [ite_eq_left h, accDigits, List.foldl_cons, List.foldl_nil]
    rw [digitByte_toNat n h]
    omega
  | case2 n h ih =>
    rw [digits]
    simp only [ite_eq_right h]
    rw [accDigits_append, ih]
    have hlt : n % 10 < 10 := Nat.mod_lt _ (by omega)
    simp only [accDigits, List.foldl_cons, List.foldl_nil]
    rw [digitByte_toNat _ hlt]
    -- both clamps agree: below the cap nothing clamps, above it both saturate
    have hd10 : n / 10 ≥ 6554 → n ≥ 65535 := by omega
    omega

/-! ### …and the accumulator is what the parser actually runs -/

/-- One digit byte steps the accumulator, keeping every other field. -/
theorem csi_digit_step {v : Vt} {s : CsiState} (b : UInt8) (hg : v.pstate = .csi s) (h1 : 0x30 ≤ b)
    (h2 : b ≤ 0x39) :
    (v.step b).pstate =
      .csi
        { s with
          cur := min (s.cur * 10 + (b.toNat - 0x30)) 65535, haveCur := true } := by
  rw [Linger.Core.Vt.step_of_csi b hg]
  unfold Vt.stepCsi
  have hd : (b ≥ 0x30 && b ≤ 0x39) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨h1, h2⟩
  rw [ite_eq_left hd]

/-- A whole digit run drives the accumulator to `accDigits`. -/
theorem csi_digits_feed :
    ∀ (bs : Bytes) {v : Vt} {s : CsiState},
      v.pstate = .csi s →
        (∀ b ∈ bs, 0x30 ≤ b ∧ b ≤ 0x39) →
        bs ≠ [] →
        (v.feed bs).pstate =
          .csi
            { s with
              cur := accDigits s.cur bs, haveCur := true }
  | [], _, _, _, _, hne => absurd rfl hne
  | [x], v, s, hg, h, _ => by
    rw [show ([x] : Bytes) = x :: [] from rfl, feed_cons]
    have hx := csi_digit_step x hg (h x (by simp)).1 (h x (by simp)).2
    show ((v.step x).feed []).pstate = _
    simpa [Vt.feed, accDigits] using hx
  | x :: y :: rest, v, s, hg, h, _ => by
    rw [feed_cons]
    have hx := csi_digit_step x hg (h x (by simp)).1 (h x (by simp)).2
    have hrest := csi_digits_feed (y :: rest) hx (fun b hb => h b (by simp [hb])) (by simp)
    rw [hrest]
    simp [accDigits]

/-- §Replay 3c: the parameter the parser accumulates from `digits n` is
`n` (clamped) — the emitter and the parser are inverse on numbers. The
`inter`/`ignore`/`priv` facts come along because `csi_digits_feed` returns
a record *update*: a digit run touches nothing else. -/
theorem csi_digits_value (n : Nat) {v : Vt} {s : CsiState} (hg : v.pstate = .csi s)
    (hcur : s.cur = 0) :
    ∃ s',
      (v.feed (digits n)).pstate = .csi s' ∧
        s'.cur = min n 65535 ∧
        s'.haveCur = true ∧
        s'.params = s.params ∧
        s'.inter = s.inter ∧ s'.ignore = s.ignore ∧ s'.curSub = s.curSub ∧ s'.priv = s.priv := by
  have hne : digits n ≠ [] := by
    rw [digits]
    split <;> simp
  refine ⟨_, csi_digits_feed (digits n) hg (digits_range n) hne, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  show accDigits s.cur (digits n) = min n 65535
  rw [hcur]
  exact accDigits_digits n

/-! ### The parameter separator

`csi_group_step` (`Pen.lean`) composes `csi_digits_value` with the step below for each
`<digits>;` group of a `;`-joined run; `cup_feed_eq` reads `CUP`'s address and
`sgrOf_feed` an SGR's codes through that walk.
-/

/-- `;` closes the current parameter and starts the next. -/
theorem csi_semi_step {v : Vt} {s : CsiState} (hg : v.pstate = .csi s) :
    (v.step 0x3B).pstate = .csi (csiPush s false) := by
  rw [Linger.Core.Vt.step_of_csi 0x3B hg]
  unfold Vt.stepCsi
  rw [ite_eq_right (by decide), ite_eq_left (by decide)]

/-! ### DECOM, reset on purpose

The `≠ 6` family in `Theorems/Vt.lean` says a private mode replay cannot *turn
origin on*. The repaint's prologue needs the complement: `CSI ? 6 l` turns it
**off**, whatever it was. That is a claim about a value rather than a frame, so it
is proved at the one dispatch it belongs to. -/

theorem org_csiDispatch_decom_off (v : Vt) (s : CsiState) (hi : s.ignore = false)
    (hpriv : (s.priv == 0x3F) = true) (h6 : s.params.toList.any (fun p => p.1 == 6) = true) :
    (v.csiDispatch s 0x6C).modes.origin = false := by
  rw [csiDispatch_rm _ _ hi, org_setModes_eq, ite_eq_left ⟨hpriv, h6⟩]

theorem org_csiFinish_decom_off (v : Vt) (s : CsiState) (hi : s.ignore = false)
    (hpriv : (s.priv == 0x3F) = true) (hparams : s.params = #[]) (hhave : s.haveCur = true)
    (hcur : min s.cur 65535 = 6) : (v.csiFinish s 0x6C).modes.origin = false := by
  have hsize : ¬(s.params.size ≥ 16) := by
    rw [hparams]; simp
  unfold Vt.csiFinish
  dsimp only
  rw [ite_eq_left hhave, ite_eq_right hsize]
  refine org_csiDispatch_decom_off _ _ hi hpriv ?_
  rw [show
      ({ s with params := s.params.push (min s.cur 65535, s.curSub) } : CsiState) =
        { s with params := #[(6, s.curSub)] }
      from by
      rw [hparams, hcur]; rfl]
  rfl

theorem org_step_of_csi_decom_off {v : Vt} {s : CsiState} (hg : v.pstate = .csi s)
    (hi : s.ignore = false) (hpriv : (s.priv == 0x3F) = true) (hparams : s.params = #[])
    (hhave : s.haveCur = true) (hint : s.inter = 0) (hcur : min s.cur 65535 = 6) :
    (v.step 0x6C).modes.origin = false := by
  rw [Linger.Core.Vt.step_of_csi 0x6C hg]
  unfold Vt.stepCsi
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
    ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left (by decide),
    ite_eq_right
      (by
        rw [hint]; simp)]
  exact org_csiFinish_decom_off _ _ hi hpriv hparams hhave hcur

/-! ### A digit run leaves the frame alone

A CSI digit byte is a single `pstate` record update, so it cannot touch the fields a
dispatch reads off the state it acts on: the grid size and the mode flags. `frame`
bundles the three so one lemma per step covers them, and `quiet_csiPriv` carries
`origin` across a private sequence's digit run with it. -/

/-- The fields a CSI dispatch reads. -/
def frame (v : Vt) : Nat × Nat × Modes := (v.cols, v.rows, v.modes)

theorem frame_abortUtf8 (v : Vt) (b : UInt8) : frame (v.abortUtf8 b) = frame v := by
  unfold Vt.abortUtf8 frame; split <;> rfl

theorem frame_csi_digit_step {v : Vt} {s : CsiState} (b : UInt8) (hg : v.pstate = .csi s)
    (h1 : 0x30 ≤ b) (h2 : b ≤ 0x39) : frame (v.step b) = frame v := by
  have hd : (b ≥ 0x30 && b ≤ 0x39) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨h1, h2⟩
  rw [Linger.Core.Vt.step_of_csi b hg]
  unfold Vt.stepCsi
  rw [ite_eq_left hd]
  exact frame_abortUtf8 v b

/-- A digit run leaves the frame alone (and stays inside the CSI). -/
theorem frame_csi_digits_feed :
    ∀ (bs : Bytes) {v : Vt} {s : CsiState},
      v.pstate = .csi s → (∀ b ∈ bs, 0x30 ≤ b ∧ b ≤ 0x39) → frame (v.feed bs) = frame v
  | [], _, _, _, _ => rfl
  | x :: xs, v, s, hg, h => by
    rw [feed_cons]
    have hx := csi_digit_step x hg (h x (by simp)).1 (h x (by simp)).2
    exact
      (frame_csi_digits_feed xs hx (fun b hb => h b (by simp [hb]))).trans
        (frame_csi_digit_step x hg (h x (by simp)).1 (h x (by simp)).2)

/-! ### §Replay: DECOM stays off through a whole restore stream

The rung the restore-level cursor claim needs: a session with DECOM off
must replay with DECOM off, or the final `CUP` would be read
region-relative and land somewhere else entirely. `restoreBody_origin`
(`Sticky.lean`) composes the stage lemmas below over the body, after a
lead-in that clears DECOM in any receiver.

"`origin` stays off" is **not** composable on its own, and the reason is
worth recording, because it is what dictates the shape below. Fed in the
middle of a CSI, a bare `h` byte completes `CSI ? 6 h` and turns DECOM
*on* — so a predicate quantified over all emulator states is false even
for a run of plain text. The composable statement bundles the parser
state with the flag, which is exactly `Ends` and origin-off together:
-/

/-- From a ground parser with DECOM off, `bs` leaves both that way. -/
def Quiet (bs : Bytes) : Prop :=
  ∀ v : Vt,
    v.pstate = .ground →
      v.modes.origin = false → ((v.feed bs).pstate = .ground ∧ (v.feed bs).modes.origin = false)

theorem Quiet.nil : Quiet [] := fun _ hg ho => ⟨hg, ho⟩

/-- The composition law — the whole point of bundling. -/
theorem Quiet.append {a b : Bytes} (ha : Quiet a) (hb : Quiet b) : Quiet (a ++ b) := by
  intro v hg ho
  rw [show v.feed (a ++ b) = (v.feed a).feed b from by simp [Vt.feed, List.foldl_append]]
  obtain ⟨h1, h2⟩ := ha v hg ho
  exact hb _ h1 h2

theorem Quiet.streamPred : StreamPred Quiet := ⟨Quiet.nil, fun ha hb => Quiet.append ha hb⟩

/-- Both branches, with the condition available: the mode replays need it
(a guarded emit is what proves the mode number is not 6). -/
theorem Quiet.ite {c : Prop} [Decidable c] {a b : Bytes}
    (ha : c → Quiet a) (hb : ¬c → Quiet b) : Quiet (if c then a else b) :=
  Quiet.streamPred.ite ha hb

theorem Quiet.flatMap {α : Type} {f : α → Bytes} {l : List α}
    (h : ∀ a, Quiet (f a)) : Quiet (l.flatMap f) := Quiet.streamPred.flatMap h

/-- Text (no ESC): the grid repaint, and the one shift-out byte. -/
theorem quiet_ground_feed : ∀ (bs : Bytes) (v : Vt), v.pstate = .ground →
    v.modes.origin = false → (∀ b ∈ bs, b ≠ 0x1B) →
    ((v.feed bs).pstate = .ground ∧ (v.feed bs).modes.origin = false)
  | [], _, hg, ho, _ => ⟨hg, ho⟩
  | x :: xs, v, hg, ho, h => by
    rw [feed_cons]
    exact quiet_ground_feed xs _ (ground_step x hg (h x (by simp)))
      (by rw [org_step_of_ground x hg]; exact ho) (fun b hb => h b (by simp [hb]))

theorem Quiet.text {bs : Bytes} (h : ∀ b ∈ bs, b ≠ 0x1B) : Quiet bs :=
  fun v hg ho => quiet_ground_feed bs v hg ho h

/-! #### The CSI cases

`org_stepCsi` in `Theorems/Vt.lean` needs the private marker to be absent,
so the marker-free constructs are one lemma, and the private ones — which
are exactly what a mode replay *is* — go through the pending-parameter
escape hatch: a private sequence whose accumulated number is not 6 cannot
be DECOM. -/

/-- A parameter byte keeps the CSI open with the same private marker
(`ParamBytes` excludes markers, which is what makes this true) and cannot
touch `origin`, since no parameter byte dispatches. -/
theorem csi_plain_step {v : Vt} {s : CsiState} (b : UInt8) (hg : v.pstate = .csi s)
    (h1 : 0x30 ≤ b) (h2 : b ≤ 0x3B) :
    ∃ s', (v.step b).pstate = .csi s' ∧ s'.priv = s.priv := by
  obtain ⟨hn1, hn2⟩ := u8_bounds h1 h2
  simp only [UInt8.reduceToNat] at hn1 hn2
  rw [Linger.Core.Vt.step_of_csi b hg]
  unfold Vt.stepCsi
  by_cases hd : (b ≥ 0x30 && b ≤ 0x39) = true
  · rw [ite_eq_left hd]; exact ⟨_, rfl, rfl⟩
  by_cases hsemi : (b == 0x3B) = true
  · rw [ite_eq_right (by simp [hd]), ite_eq_left hsemi]
    exact ⟨_, rfl, Linger.Core.Vt.priv_csiPush _ _⟩
  by_cases hcolon : (b == 0x3A) = true
  · rw [ite_eq_right (by simp [hd]), ite_eq_right (by simp [hsemi]), ite_eq_left hcolon]
    exact ⟨_, rfl, Linger.Core.Vt.priv_csiPush _ _⟩
  · -- 0x30…0x3B minus digits, `;` and `:` is empty
    exfalso
    have hb39 : ¬ (b.toNat ≤ 57) := by
      intro hle
      exact hd (by
        simp only [Bool.and_eq_true, decide_eq_true_eq, UInt8.le_iff_toNat_le, UInt8.reduceToNat]
        omega)
    have hne3B : b.toNat ≠ 59 := by
      intro he
      exact hsemi (by
        simp only [beq_iff_eq]
        apply UInt8.toNat_inj.mp
        simpa using he)
    have hne3A : b.toNat ≠ 58 := by
      intro he
      exact hcolon (by
        simp only [beq_iff_eq]
        apply UInt8.toNat_inj.mp
        simpa using he)
    omega

/-- A whole parameter run: the marker is still absent at the end (so the
final byte cannot dispatch a private mode), and `origin` is untouched. -/
theorem csi_plain_feed : ∀ (bs : Bytes) {v : Vt} {s : CsiState}, v.pstate = .csi s →
    (s.priv == 0x3F) = false → ParamBytes bs →
    ∃ s', (v.feed bs).pstate = .csi s' ∧ (s'.priv == 0x3F) = false
      ∧ (v.feed bs).modes.origin = v.modes.origin
  | [], _, s, hg, hp, _ => ⟨s, hg, hp, rfl⟩
  | x :: xs, v, s, hg, hp, h => by
    obtain ⟨s1, hs1, hpv1⟩ := csi_plain_step x hg (h x (by simp)).1 (h x (by simp)).2
    have hp1 : (s1.priv == 0x3F) = false := by rw [hpv1]; exact hp
    have horg := org_step_of_csi x hg hp
    rw [feed_cons]
    obtain ⟨s2, hs2, hp2, ho2⟩ :=
      csi_plain_feed xs hs1 hp1 (fun b hb => h b (by simp [hb]))
    exact ⟨s2, hs2, hp2, ho2.trans horg⟩

/-- **The `Quiet` CSI lemma.** A marker-free `CSI <params> <final>` cannot
be DECOM whatever its final byte, because DECOM is a *private* mode and
`ParamBytes` excludes the marker. Cursor addressing, SGR pens, the scroll
region, the tab ruler and IRM are all instances. -/
theorem quiet_csi_seq (params : Bytes) (final : UInt8) (hp : ParamBytes params)
    (h1 : 0x40 ≤ final) (h2 : final ≤ 0x7E) : Quiet (csiB ++ params ++ [final]) := by
  intro v hg ho
  refine ⟨ends_csi_seq params final hp h1 h2 v hg, ?_⟩
  rw [show (csiB ++ params ++ [final] : Bytes) = 0x1B :: 0x5B :: (params ++ [final]) from by
    simp [csiB]]
  rw [feed_cons, feed_cons]
  have he := esc_step hg
  have hb := csi_open_step he
  have hob : ((v.step 0x1B).step 0x5B).modes.origin = false :=
    org_step_of_esc 0x5B he (by rw [org_step_of_ground 0x1B hg]; exact ho)
  rw [show ∀ (w : Vt), w.feed (params ++ [final]) = (w.feed params).feed [final] from
    fun w => by simp [Vt.feed, List.foldl_append]]
  obtain ⟨s', hs', hpv', hor'⟩ := csi_plain_feed params hb (by decide) hp
  rw [show ∀ (w : Vt), w.feed [final] = w.step final from fun _ => rfl]
  rw [org_step_of_csi final hs' hpv', hor']
  exact hob

theorem quiet_csiNum (n : Nat) (final : UInt8) (h1 : 0x40 ≤ final) (h2 : final ≤ 0x7E) :
    Quiet (csiNum n final) :=
  quiet_csi_seq _ final (paramBytes_digits n) h1 h2

theorem quiet_csiNum2 (a b : Nat) (final : UInt8) (h1 : 0x40 ≤ final)
    (h2 : final ≤ 0x7E) : Quiet (csiNum2 a b final) := by
  rw [show csiNum2 a b final = csiB ++ (digits a ++ [0x3B] ++ digits b) ++ [final] from by
    simp [csiNum2, List.append_assoc]]
  exact quiet_csi_seq _ final
    (((paramBytes_digits a).append
      (ParamBytes.cons (by decide) (by decide) ParamBytes.nil)).append
      (paramBytes_digits b)) h1 h2

theorem quiet_sgrOf (codes : List Nat) : Quiet (sgrOf codes) :=
  quiet_csi_seq _ 0x6D (paramBytes_joinSemi codes) (by decide) (by decide)

theorem quiet_sgrColorSeq (c : Color) (isFg : Bool) : Quiet (sgrColorSeq c isFg) := by
  unfold sgrColorSeq
  split
  · exact Quiet.nil
  · exact quiet_sgrOf _

theorem quiet_penSgr (p : Pen) : Quiet (penSgr p) := by
  unfold penSgr
  exact ((quiet_sgrOf _).append (quiet_sgrColorSeq _ _)).append (quiet_sgrColorSeq _ _)

/-- The private marker records itself and nothing else. -/
theorem csi_marker_step {v : Vt} {s : CsiState} (hg : v.pstate = .csi s)
    (hp : (s.priv == 0x3F) = false) :
    (v.step 0x3F).pstate = .csi { s with priv := 0x3F }
      ∧ (v.step 0x3F).modes.origin = v.modes.origin := by
  refine ⟨?_, org_step_of_csi 0x3F hg hp⟩
  rw [Linger.Core.Vt.step_of_csi 0x3F hg]
  unfold Vt.stepCsi
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left (by decide)]

/-- **A private mode replay is `Quiet` iff it is not DECOM.** The number
is accumulated before the guard exists, so the digit run's innocence comes
from the frame layer (`frame_csi_digits_feed`: a digit byte writes nothing
but the accumulator), and the final byte is discharged by the
pending-parameter hatch with `min n 65535 ≠ 6`. -/
theorem quiet_csiPriv (n : Nat) (final : UInt8) (hn : n ≠ 6) (h1 : 0x40 ≤ final)
    (h2 : final ≤ 0x7E) : Quiet (csiPriv n final) := by
  intro v hg ho
  refine ⟨ends_csiPriv n final h1 h2 v hg, ?_⟩
  rw [show csiPriv n final = 0x1B :: 0x5B :: 0x3F :: (digits n ++ [final]) from by
    simp [csiPriv, csiB]]
  rw [feed_cons, feed_cons, feed_cons]
  have he := esc_step hg
  have hb := csi_open_step he
  obtain ⟨hm, hmo⟩ := csi_marker_step hb (by decide)
  have hom : (((v.step 0x1B).step 0x5B).step 0x3F).modes.origin = false := by
    rw [hmo]
    exact org_step_of_esc 0x5B he (by rw [org_step_of_ground 0x1B hg]; exact ho)
  rw [show ∀ (w : Vt), w.feed (digits n ++ [final]) = (w.feed (digits n)).feed [final] from
    fun w => by simp [Vt.feed, List.foldl_append]]
  obtain ⟨s', hs', hcur', hhave', hpar', -⟩ := csi_digits_value n hm rfl
  -- the digit run writes only the accumulator, so `origin` is carried by the frame
  have hmodes : ((((v.step 0x1B).step 0x5B).step 0x3F).feed (digits n)).modes
      = (((v.step 0x1B).step 0x5B).step 0x3F).modes :=
    congrArg (·.2.2) (frame_csi_digits_feed (digits n) hm (digits_range n))
  rw [show ∀ (w : Vt), w.feed [final] = w.step final from fun _ => rfl]
  rw [org_step_of_csi_pending final hs' (by rw [hpar']) hhave'
    (by rw [hcur']; omega)]
  rw [show ((((v.step 0x1B).step 0x5B).step 0x3F).feed (digits n)).modes.origin
      = (((v.step 0x1B).step 0x5B).step 0x3F).modes.origin from congrArg (·.origin) hmodes]
  exact hom

/-! #### `ESC`-single, charset, and the OSC title -/

theorem quiet_escSeq (b : UInt8) (hb : b = 0x37 ∨ b = 0x3D ∨ b = 0x48 ∨ b = 0x3E ∨ b = 0x5C) :
    Quiet (escSeq b) := by
  intro v hg ho
  refine ⟨ends_escSeq b hb v hg, ?_⟩
  rw [show escSeq b = 0x1B :: [b] from by simp [escSeq, escB]]
  rw [feed_cons, show ∀ (w : Vt), w.feed [b] = w.step b from fun _ => rfl]
  exact org_step_of_esc b (esc_step hg) (by rw [org_step_of_ground 0x1B hg]; exact ho)

theorem quiet_escCharset (i x : UInt8) (hi : i = 0x28 ∨ i = 0x29)
    (hlo : 0x30 ≤ x) (hhi : x ≤ 0x7E) :
    Quiet (escCharset i x) := by
  intro v hg ho
  refine ⟨ends_escCharset i x hi hlo hhi v hg, ?_⟩
  rw [show escCharset i x = 0x1B :: i :: [x] from by simp [escCharset, escB]]
  rw [feed_cons, feed_cons, show ∀ (w : Vt), w.feed [x] = w.step x from fun _ => rfl]
  rw [org_step_of_escInter x (esc_inter_step i (esc_step hg) hi)]
  exact org_step_of_esc i (esc_step hg) (by rw [org_step_of_ground 0x1B hg]; exact ho)

/-- An OSC payload byte cannot dispatch anything: the accumulator is not
the mode machine. -/
theorem org_feed_osc : ∀ (bs : Bytes) {v : Vt} {acc : Array UInt8},
    v.pstate = .osc acc false → (∀ b ∈ bs, b ≠ 0x1B ∧ b ≠ 0x07) →
    (v.feed bs).modes.origin = v.modes.origin
  | [], _, _, _, _ => rfl
  | x :: xs, v, acc, hg, h => by
    obtain ⟨acc', hs⟩ := osc_accum_step x hg (h x (by simp)).1 (h x (by simp)).2
    rw [feed_cons]
    exact (org_feed_osc xs hs (fun b hb => h b (by simp [hb]))).trans
      (org_step_of_osc x hg)

theorem quiet_osc (payload : List Char) :
    Quiet (escB ++ [0x5D, 0x32, 0x3B] ++ utf8s payload ++ [0x07]) := by
  intro v hg ho
  refine ⟨ends_osc payload v hg, ?_⟩
  rw [show (escB ++ [0x5D, 0x32, 0x3B] ++ utf8s payload ++ [0x07] : Bytes)
      = 0x1B :: 0x5D :: 0x32 :: 0x3B :: (utf8s payload ++ [0x07]) from by simp [escB]]
  rw [feed_cons, feed_cons, feed_cons, feed_cons]
  have he := esc_step hg
  have h1 := osc_open_step he
  obtain ⟨a2, h2⟩ := osc_accum_step 0x32 h1 (by decide) (by decide)
  obtain ⟨a3, h3⟩ := osc_accum_step 0x3B h2 (by decide) (by decide)
  have hoo : ((v.step 0x1B).step 0x5D).modes.origin = false :=
    org_step_of_esc 0x5D he (by rw [org_step_of_ground 0x1B hg]; exact ho)
  rw [show ∀ (w : Vt), w.feed (utf8s payload ++ [0x07])
      = (w.feed (utf8s payload)).feed [0x07] from
    fun w => by simp [Vt.feed, List.foldl_append]]
  obtain ⟨a4, h4⟩ := osc_accum_feed (utf8s payload) h3 (utf8s_no_esc_bel payload)
  rw [show ∀ (w : Vt), w.feed [(0x07 : UInt8)] = w.step 0x07 from fun _ => rfl]
  rw [org_step_of_osc 0x07 h4, org_feed_osc (utf8s payload) h3 (utf8s_no_esc_bel payload),
    org_step_of_osc 0x3B h2, org_step_of_osc 0x32 h1]
  exact hoo

/-! #### The grid repaint, and the stages of a restore stream -/

theorem quiet_utf8s (cs : List Char) : Quiet (utf8s cs) :=
  Quiet.text (utf8s_no_esc cs)

theorem quiet_utf8_safe (ch : Char) : Quiet (utf8 (safeChar ch)) :=
  Quiet.text (fun b hb => by
    obtain ⟨hge, -⟩ := utf8_no_ctl (safeChar ch) (safeChar_ge ch).1 (safeChar_ge ch).2 b hb
    intro he; rw [he] at hge; exact absurd hge (by decide))

theorem quiet_cellText (c : Cell) : Quiet (cellText c) := by
  unfold cellText
  exact (quiet_utf8_safe c.base).append (quiet_utf8s c.marks)

theorem quiet_rowAnsi (row : Row) (p : Pen) : Quiet (rowAnsi row p).1 :=
  Quiet.streamPred.rowAnsi quiet_penSgr quiet_utf8_safe quiet_utf8s
    (fun n => quiet_csiNum n 0x47 (by decide) (by decide)) row p

theorem quiet_gridAnsi (grid : Array Row) : Quiet (gridAnsi grid) := by
  refine Quiet.streamPred.gridAnsi (quiet_csiNum 0 0x6D (by decide) (by decide))
    ?_ (Quiet.text (by decide)) quiet_rowAnsi grid
  exact quiet_csi_seq [] 0x48 ParamBytes.nil (by decide) (by decide)

theorem quiet_modeSet (n : Nat) (on : Bool) (hn : n ≠ 6) : Quiet (modeSet n on) := by
  unfold modeSet
  cases on
  · exact quiet_csiPriv n 0x6C hn (by decide) (by decide)
  · exact quiet_csiPriv n 0x68 hn (by decide) (by decide)

/-- **DECOM reset is `Quiet` because it makes the conclusion true outright.** The
`≠ 6` family says a mode replay cannot turn origin *on*; this says `?6l` turns it
*off*, which is what the repaint's prologue needs. -/
theorem quiet_modeSet_decom_off : Quiet (modeSet 6 false) := by
  intro v hg ho
  refine ⟨ends_modeSet 6 false v hg, ?_⟩
  rw [show modeSet 6 false = 0x1B :: 0x5B :: 0x3F :: (digits 6 ++ [(0x6C : UInt8)]) from by
    simp [modeSet, csiPriv, csiB]]
  rw [feed_cons, feed_cons, feed_cons]
  have hb := csi_open_step (esc_step hg)
  obtain ⟨hm, -⟩ := csi_marker_step hb (by decide)
  rw [show ∀ (w : Vt), w.feed (digits 6 ++ [(0x6C : UInt8)])
      = (w.feed (digits 6)).feed [(0x6C : UInt8)] from
    fun w => by simp [Vt.feed, List.foldl_append]]
  obtain ⟨s', hs', hcur', hhave', hpar', hint', hign', -, hpriv'⟩ :=
    csi_digits_value 6 hm rfl
  rw [show ∀ (w : Vt), w.feed [(0x6C : UInt8)] = w.step 0x6C from fun _ => rfl]
  exact org_step_of_csi_decom_off hs' (by simp [hign']) (by simp [hpriv']) (by simp [hpar'])
    hhave' (by simp [hint']) (by rw [hcur']; decide)

/-- The flush run keeps DECOM off: it is ESC-free, so `Quiet.text` carries it. -/
theorem quiet_crlfRun (n : Nat) : Quiet ((List.replicate n crlfB).flatten) :=
  Quiet.text (crlfRun_no_1B n)

/-- The history stage keeps DECOM off: the guarded `ED 3`, ring paint and flush run are
`Quiet`, and the trailing `4l ?6l ?7h` leave DECOM off. -/
theorem quiet_scrollbackAnsi (v : Vt) : Quiet (scrollbackAnsi v) := by
  unfold scrollbackAnsi
  -- `Quiet (modeSet 6 false)` cannot come from `quiet_modeSet`, which carries `n ≠ 6`
  -- because mode 6 *is* DECOM: it is the one mode emit whose `Quiet` is about its value
  -- rather than its number
  refine Quiet.append (Quiet.append (Quiet.append ?_
    (quiet_csiNum 4 0x6C (by decide) (by decide))) quiet_modeSet_decom_off)
    (quiet_modeSet 7 true (by decide))
  exact Quiet.ite (fun _ => Quiet.nil)
    (fun _ => (((quiet_csiNum 3 0x4A (by decide) (by decide)).append
      (quiet_gridAnsi (sbRows v))).append (quiet_crlfRun v.rows)))

theorem quiet_pendingAnsi (cols : Nat) (grid : Array Row) (cur : Cursor)
    (row : Nat) (pen : Pen) : Quiet (pendingAnsi cols grid cur row pen) := by
  unfold pendingAnsi
  dsimp only
  apply Quiet.ite
  · intro _
    exact (((quiet_csiNum2 _ _ 0x48 (by decide) (by decide)).append
      (quiet_penSgr _)).append (quiet_cellText _)).append (quiet_penSgr _)
  · intro _; exact Quiet.nil

theorem quiet_screensAnsi (v : Vt) : Quiet (screensAnsi v) := by
  unfold screensAnsi
  refine (quiet_scrollbackAnsi v).append ?_
  split
  · exact quiet_gridAnsi _
  · exact (((((quiet_gridAnsi _).append (quiet_penSgr _)).append
      (quiet_csiNum2 _ _ 0x48 (by decide) (by decide))).append
      (quiet_pendingAnsi _ _ _ _ _)).append
      (quiet_csiPriv 1049 0x68 (by decide) (by decide) (by decide))).append
      (quiet_gridAnsi _)

theorem quiet_regionAnsi (v : Vt) : Quiet (regionAnsi v) := by
  unfold regionAnsi
  exact Quiet.ite (fun _ => Quiet.nil)
    (fun _ => quiet_csiNum2 _ _ 0x72 (by decide) (by decide))

theorem quiet_tabsAnsi (v : Vt) : Quiet (tabsAnsi v) := by
  unfold tabsAnsi
  refine (quiet_csiNum 3 0x67 (by decide) (by decide)).append ?_
  refine Quiet.flatMap (fun i => ?_)
  exact (quiet_csiNum (i + 1) 0x47 (by decide) (by decide)).append
    (quiet_escSeq 0x48 (by decide))

theorem quiet_savedAnsi (v : Vt) : Quiet (savedAnsi v) := by
  unfold savedAnsi
  exact ((quiet_penSgr _).append (quiet_csiNum2 _ _ 0x48 (by decide) (by decide))).append
    (quiet_escSeq 0x37 (by decide))

theorem quiet_savedPendingAnsi (v : Vt) : Quiet (savedPendingAnsi v) := by
  unfold savedPendingAnsi
  exact Quiet.ite
    (fun _ => (quiet_pendingAnsi _ _ _ _ _).append (quiet_escSeq 0x37 (by decide)))
    (fun _ => Quiet.nil)

theorem quiet_charsetAnsi (v : Vt) : Quiet (charsetAnsi v) := by
  unfold charsetAnsi
  refine ((Quiet.ite (fun _ => quiet_escCharset 0x28 0x30 (by decide) (by decide) (by decide))
    (fun _ => quiet_escCharset 0x28 0x42 (by decide) (by decide) (by decide))).append
    (Quiet.ite (fun _ => quiet_escCharset 0x29 0x30 (by decide) (by decide) (by decide))
      (fun _ => quiet_escCharset 0x29 0x42 (by decide) (by decide) (by decide)))).append ?_
  exact Quiet.ite (fun _ => Quiet.text (by decide)) (fun _ => Quiet.nil)

theorem quiet_titleAnsi (v : Vt) : Quiet (titleAnsi v) := by
  unfold titleAnsi
  exact quiet_osc _

theorem quiet_irm (on : Bool) : Quiet (csiNum 4 (if on then 0x68 else 0x6C)) := by
  cases on
  · exact quiet_csiNum 4 0x6C (by decide) (by decide)
  · exact quiet_csiNum 4 0x68 (by decide) (by decide)

/-- The mode replay is where the DECOM hypothesis lands: with the session's origin
off the emit at mode 6 is a *reset*, discharged outright by
`quiet_modeSet_decom_off`. Every other private mode the emitter names is a literal
≠ 6, or the guarded mouse mode, whose allowlist contains no 6. -/
theorem quiet_modesAnsi (v : Vt) (ho : v.modes.origin = false) : Quiet (modesAnsi v) := by
  unfold modesAnsi
  rw [ho]
  refine Quiet.append ?_ (quiet_irm v.modes.insert)
  refine Quiet.append ?_ quiet_modeSet_decom_off
  refine Quiet.append ?_ (quiet_modeSet 1004 _ (by decide))
  refine Quiet.append ?_ (quiet_modeSet 1006 _ (by decide))
  refine Quiet.append ?_ (Quiet.ite (c := (v.modes.mouse == 1000 || v.modes.mouse == 1002
    || v.modes.mouse == 1003) = true)
    (fun h => quiet_modeSet v.modes.mouse true (by
      simp only [Bool.or_eq_true, beq_iff_eq] at h
      omega)) (fun _ => Quiet.nil))
  refine Quiet.append ?_ (quiet_modeSet 1003 false (by decide))
  refine Quiet.append ?_ (quiet_modeSet 1002 false (by decide))
  refine Quiet.append ?_ (quiet_modeSet 1000 false (by decide))
  refine Quiet.append ?_ (quiet_modeSet 2004 _ (by decide))
  refine Quiet.append ?_ (quiet_modeSet 25 _ (by decide))
  refine Quiet.append ?_ (Quiet.ite (fun _ => quiet_escSeq 0x3D (by decide))
    (fun _ => quiet_escSeq 0x3E (by decide)))
  exact (quiet_modeSet 7 _ (by decide)).append (quiet_modeSet 1 _ (by decide))

end Linger.Core.Render
