import Theorems.Render.Ends
/-! # §Replay stage 3c — the numbers survive the round trip

`Quiet` and the digit/cursor bridges: what the emitted decimal parameters mean by
the time the parser has accumulated them, that the cursor lands where the session
had it, and that DECOM stays off through a whole restore stream. Split out of
`Theorems/Render.lean`; see that façade for the ladder as a whole. -/

namespace Zmx.Core.Render

open Zmx.Core.Vt

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
    accDigits cur (a ++ b) = accDigits (accDigits cur a) b := by
  simp [accDigits, List.foldl_append]

/-- A digit byte's numeric value is recovered by subtracting `'0'`. -/
theorem digitByte_toNat (d : Nat) (hd : d < 10) :
    (UInt8.ofNat (0x30 + d)).toNat - 0x30 = d := by
  have h : (0x30 + d) < 256 := by omega
  simp [UInt8.toNat_ofNat', Nat.mod_eq_of_lt h]

/-- **The digit round trip.** Feeding `digits n` into a fresh accumulator
yields `n`, clamped at 65535 exactly as the parser clamps. -/
theorem accDigits_digits (n : Nat) : accDigits 0 (digits n) = min n 65535 := by
  induction n using digits.induct with
  | case1 n h =>
    rw [digits]
    simp only [if_pos h, accDigits, List.foldl_cons, List.foldl_nil]
    rw [digitByte_toNat n h]
    omega
  | case2 n h ih =>
    rw [digits]
    simp only [if_neg h]
    rw [accDigits_append, ih]
    have hlt : n % 10 < 10 := Nat.mod_lt _ (by omega)
    have hdiv : n / 10 * 10 + n % 10 = n := Nat.div_add_mod' n 10
    simp only [accDigits, List.foldl_cons, List.foldl_nil]
    rw [digitByte_toNat _ hlt]
    -- both clamps agree: below the cap nothing clamps, above it both saturate
    have hd10 : n / 10 ≥ 6554 → n ≥ 65535 := by omega
    omega

/-! ### …and the accumulator is what the parser actually runs -/

/-- One digit byte steps the accumulator, keeping every other field. -/
theorem csi_digit_step {v : Vt} {s : CsiState} (b : UInt8) (hg : v.pstate = .csi s)
    (h1 : 0x30 ≤ b) (h2 : b ≤ 0x39) :
    (v.step b).pstate
      = .csi { s with cur := min (s.cur * 10 + (b.toNat - 0x30)) 65535, haveCur := true } := by
  have hw : (v.abortUtf8 b).pstate = PState.csi s := by
    rw [Zmx.Core.Vt.ps_abortUtf8]; exact hg
  unfold Vt.step
  dsimp only
  rw [hw]
  unfold Vt.stepCsi
  dsimp only
  have hd : (b ≥ 0x30 && b ≤ 0x39) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨h1, h2⟩
  rw [if_pos hd]

/-- A whole digit run drives the accumulator to `accDigits`. -/
theorem csi_digits_feed : ∀ (bs : Bytes) {v : Vt} {s : CsiState}, v.pstate = .csi s →
    (∀ b ∈ bs, 0x30 ≤ b ∧ b ≤ 0x39) → bs ≠ [] →
    (v.feed bs).pstate = .csi { s with cur := accDigits s.cur bs, haveCur := true }
  | [], _, _, _, _, hne => absurd rfl hne
  | [x], v, s, hg, h, _ => by
    rw [show ([x] : Bytes) = x :: [] from rfl, feed_cons]
    have hx := csi_digit_step x hg (h x (by simp)).1 (h x (by simp)).2
    show ((v.step x).feed []).pstate = _
    simpa [Vt.feed, accDigits] using hx
  | x :: y :: rest, v, s, hg, h, _ => by
    rw [feed_cons]
    have hx := csi_digit_step x hg (h x (by simp)).1 (h x (by simp)).2
    have hrest := csi_digits_feed (y :: rest) hx
      (fun b hb => h b (by simp [hb])) (by simp)
    rw [hrest]
    simp [accDigits]

/-- Every byte `digits` emits is a digit byte. -/
theorem digits_are_digits (n : Nat) : ∀ b ∈ digits n, 0x30 ≤ b ∧ b ≤ 0x39 :=
  digits_range n

/-- §Replay 3c: the parameter the parser accumulates from `digits n` is
`n` (clamped) — the emitter and the parser are inverse on numbers. The
`inter`/`ignore`/`priv` facts come along because `csi_digits_feed` returns
a record *update*: a digit run touches nothing else. -/
theorem csi_digits_value (n : Nat) {v : Vt} {s : CsiState} (hg : v.pstate = .csi s)
    (hcur : s.cur = 0) :
    ∃ s', (v.feed (digits n)).pstate = .csi s' ∧ s'.cur = min n 65535
      ∧ s'.haveCur = true ∧ s'.params = s.params ∧ s'.inter = s.inter
      ∧ s'.ignore = s.ignore ∧ s'.curSub = s.curSub ∧ s'.priv = s.priv := by
  have hne : digits n ≠ [] := by
    rw [digits]
    split <;> simp
  refine ⟨_, csi_digits_feed (digits n) hg (digits_are_digits n) hne, ?_, rfl, rfl, rfl,
    rfl, rfl, rfl⟩
  show accDigits s.cur (digits n) = min n 65535
  rw [hcur]
  exact accDigits_digits n

/-! ### Cursor fidelity

`CUP` sets the cursor outright, so the interesting content is entirely in
the final byte of `cursorAnsi`: the two accumulated parameters must come
back out as the cursor position. That is what this proves, stated about
the state just before that byte (which `csi_digits_value` and
`csi_semi_step` above are what produce).
-/

/-- `;` closes the current parameter and starts the next. -/
theorem csi_semi_step {v : Vt} {s : CsiState} (hg : v.pstate = .csi s) :
    (v.step 0x3B).pstate = .csi (csiPush s false) := by
  have hw : (v.abortUtf8 0x3B).pstate = PState.csi s := by
    rw [Zmx.Core.Vt.ps_abortUtf8]; exact hg
  unfold Vt.step
  dsimp only
  rw [hw]
  unfold Vt.stepCsi
  dsimp only
  rw [if_neg (by decide), if_pos (by decide)]

/-- `CsiState.arg` over a literal two-parameter list, computed. -/
theorem arg_of_one (s : CsiState) (a : Nat) (f : Bool) (d : Nat) :
    CsiState.arg { s with params := #[(a, f)] } 0 d = if a = 0 then d else a := by
  unfold CsiState.arg
  cases a <;> simp

/-! ### DECOM, reset on purpose

The `≠ 6` family in `Theorems/Vt.lean` says a private mode replay cannot *turn
origin on*. The repaint's prologue needs the complement: `CSI ? 6 l` turns it
**off**, whatever it was. That is a claim about a value rather than a frame, so it
is proved at the one dispatch it belongs to. -/

theorem org_setMode_decom_off (v : Vt) : (v.setMode true 6 false).modes.origin = false := by
  show (({ v with modes := { v.modes with origin := false } } : Vt).moveTo 0 0).modes.origin
      = false
  rw [Zmx.Core.Vt.org_moveTo]

theorem org_csiDispatch_decom_off (v : Vt) (s : CsiState) (hi : s.ignore = false)
    (hpriv : (s.priv == 0x3F) = true) (h6 : s.arg 0 0 = 6) :
    (v.csiDispatch s 0x6C).modes.origin = false := by
  unfold Vt.csiDispatch
  rw [if_neg (by rw [hi]; simp)]
  show (v.setMode (s.priv == 0x3F) (s.arg 0 0) false).modes.origin = false
  rw [hpriv, h6]
  exact org_setMode_decom_off v

theorem org_csiFinish_decom_off (v : Vt) (s : CsiState) (hi : s.ignore = false)
    (hpriv : (s.priv == 0x3F) = true) (hparams : s.params = #[]) (hhave : s.haveCur = true)
    (hcur : min s.cur 65535 = 6) :
    (v.csiFinish s 0x6C).modes.origin = false := by
  have hsize : ¬ (s.params.size ≥ 16) := by rw [hparams]; simp
  unfold Vt.csiFinish
  dsimp only
  rw [if_pos hhave, if_neg hsize]
  refine org_csiDispatch_decom_off _ _ hi hpriv ?_
  rw [show ({ s with params := s.params.push (min s.cur 65535, s.curSub) } : CsiState)
      = { s with params := #[(6, s.curSub)] } from by rw [hparams, hcur]; rfl]
  rw [arg_of_one, if_neg (by decide)]

theorem org_step_of_csi_decom_off {v : Vt} {s : CsiState} (hg : v.pstate = .csi s)
    (hi : s.ignore = false) (hpriv : (s.priv == 0x3F) = true) (hparams : s.params = #[])
    (hhave : s.haveCur = true) (hint : s.inter = 0) (hcur : min s.cur 65535 = 6) :
    (v.step 0x6C).modes.origin = false := by
  have hw : (v.abortUtf8 0x6C).pstate = PState.csi s := by
    rw [Zmx.Core.Vt.ps_abortUtf8]; exact hg
  unfold Vt.step
  dsimp only
  rw [hw]
  unfold Vt.stepCsi
  dsimp only
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_pos (by decide), if_neg (by rw [hint]; simp)]
  exact org_csiFinish_decom_off _ _ hi hpriv hparams hhave hcur

theorem arg_of_two (s : CsiState) (a b : Nat) (fa fb : Bool) (d : Nat) :
    (CsiState.arg { s with params := #[(a, fa), (b, fb)] } 0 d = if a = 0 then d else a)
      ∧ (CsiState.arg { s with params := #[(a, fa), (b, fb)] } 1 d
          = if b = 0 then d else b) := by
  unfold CsiState.arg
  refine ⟨?_, ?_⟩
  · cases a <;> simp
  · cases b <;> simp

/-- **CUP delivers the parameters to the cursor.** With a row parameter
already pushed and a column parameter in the accumulator, the `H` byte
moves the cursor to exactly (`col-1`, `row-1`). The bounds hypotheses are
what make `moveTo`'s clamps identities (`Good` supplies them at every
call site); `origin = false` is required because under DECOM the address
is region-relative — see the note in specs/archive/bigger-theorems.md. -/
theorem cup_step_cursor {w : Vt} {s : CsiState} (row col : Nat)
    (hs : w.pstate = .csi s) (hinter : s.inter = 0) (hignore : s.ignore = false)
    (hhave : s.haveCur = true) (hcur : s.cur = min col 65535)
    (hparams : s.params = #[(min row 65535, false)])
    (hrow : 1 ≤ row) (hcol : 1 ≤ col) (hr : row ≤ 65535) (hc : col ≤ 65535)
    (hry : row - 1 < w.rows) (hcx : col - 1 < w.cols) (ho : w.modes.origin = false) :
    ((w.step 0x48).cursor.x = col - 1) ∧ ((w.step 0x48).cursor.y = row - 1) := by
  have hw : (w.abortUtf8 0x48).pstate = PState.csi s := by
    rw [Zmx.Core.Vt.ps_abortUtf8]; exact hs
  -- the aborted state agrees with `w` on everything the dispatch reads
  have hac : (w.abortUtf8 0x48).cols = w.cols := by
    unfold Vt.abortUtf8; split <;> rfl
  have har : (w.abortUtf8 0x48).rows = w.rows := by
    unfold Vt.abortUtf8; split <;> rfl
  have ham : (w.abortUtf8 0x48).modes = w.modes := by
    unfold Vt.abortUtf8; split <;> rfl
  have hminr : min row 65535 = row := by omega
  have hminc : min (min col 65535) 65535 = col := by omega
  -- the parameter list `csiFinish` closes, as a literal
  have hs4 : ({ s with params := s.params.push (min s.cur 65535, s.curSub) } : CsiState)
      = { s with params := #[(row, false), (col, s.curSub)] } := by
    rw [hparams, hcur, hminc, hminr]
    rfl
  obtain ⟨ha0, ha1⟩ := arg_of_two s row col false s.curSub 1
  rw [if_neg (by omega : ¬ row = 0)] at ha0
  rw [if_neg (by omega : ¬ col = 0)] at ha1
  unfold Vt.step
  dsimp only
  rw [hw]
  unfold Vt.stepCsi
  dsimp only
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
      if_neg (by decide), if_pos (by decide), if_neg (by simp [hinter])]
  unfold Vt.csiFinish
  dsimp only
  rw [if_pos hhave, if_neg (by simp [hparams]), hs4]
  unfold Vt.csiDispatch
  dsimp only
  rw [if_neg (by simp [hignore])]
  unfold Vt.moveTo
  simp only [ha0, ha1, ham, ho, hac, har, Bool.false_eq_true, if_false]
  exact ⟨by omega, by omega⟩

/-! ### From the final byte to the whole sequence

`cup_step_cursor` reads the grid size and the mode flags off the state it
acts on, so lifting it to the whole `CSI row ; col H` needs one fact: the
sequence's *prefix* (`ESC [ digits ; digits`) leaves those fields alone.
It does — every one of those steps is a single `pstate` record update —
and `Frame` bundles the three fields so one lemma per step covers them. -/

/-- The fields the CUP dispatch reads. -/
def Frame (v : Vt) : Nat × Nat × Modes := (v.cols, v.rows, v.modes)

theorem frame_abortUtf8 (v : Vt) (b : UInt8) : Frame (v.abortUtf8 b) = Frame v := by
  unfold Vt.abortUtf8 Frame; split <;> rfl

theorem frame_esc_step {v : Vt} (hg : v.pstate = .ground) :
    Frame (v.step 0x1B) = Frame v := by
  have hw : (v.abortUtf8 0x1B).pstate = PState.ground := by
    rw [Zmx.Core.Vt.ps_abortUtf8]; exact hg
  unfold Vt.step
  dsimp only
  rw [hw]
  unfold Vt.stepGround
  rw [if_pos (by decide)]
  exact frame_abortUtf8 v 0x1B

theorem frame_csi_open_step {v : Vt} (hg : v.pstate = .esc) :
    Frame (v.step 0x5B) = Frame v := by
  have hw : (v.abortUtf8 0x5B).pstate = PState.esc := by
    rw [Zmx.Core.Vt.ps_abortUtf8]; exact hg
  unfold Vt.step
  dsimp only
  rw [hw]
  exact frame_abortUtf8 v 0x5B

theorem frame_csi_digit_step {v : Vt} {s : CsiState} (b : UInt8) (hg : v.pstate = .csi s)
    (h1 : 0x30 ≤ b) (h2 : b ≤ 0x39) : Frame (v.step b) = Frame v := by
  have hw : (v.abortUtf8 b).pstate = PState.csi s := by
    rw [Zmx.Core.Vt.ps_abortUtf8]; exact hg
  have hd : (b ≥ 0x30 && b ≤ 0x39) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨h1, h2⟩
  unfold Vt.step
  dsimp only
  rw [hw]
  unfold Vt.stepCsi
  dsimp only
  rw [if_pos hd]
  exact frame_abortUtf8 v b

theorem frame_csi_semi_step {v : Vt} {s : CsiState} (hg : v.pstate = .csi s) :
    Frame (v.step 0x3B) = Frame v := by
  have hw : (v.abortUtf8 0x3B).pstate = PState.csi s := by
    rw [Zmx.Core.Vt.ps_abortUtf8]; exact hg
  unfold Vt.step
  dsimp only
  rw [hw]
  unfold Vt.stepCsi
  dsimp only
  rw [if_neg (by decide), if_pos (by decide)]
  exact frame_abortUtf8 v 0x3B

/-- A digit run leaves the frame alone (and stays inside the CSI). -/
theorem frame_csi_digits_feed : ∀ (bs : Bytes) {v : Vt} {s : CsiState},
    v.pstate = .csi s → (∀ b ∈ bs, 0x30 ≤ b ∧ b ≤ 0x39) → Frame (v.feed bs) = Frame v
  | [], _, _, _, _ => rfl
  | x :: xs, v, s, hg, h => by
    rw [feed_cons]
    have hx := csi_digit_step x hg (h x (by simp)).1 (h x (by simp)).2
    exact (frame_csi_digits_feed xs hx (fun b hb => h b (by simp [hb]))).trans
      (frame_csi_digit_step x hg (h x (by simp)).1 (h x (by simp)).2)

/-- **Cursor fidelity for a whole `CSI row ; col H`.** Feeding the
sequence `cursorAnsi` emits places the cursor at exactly (`col-1`,
`row-1`) — the parser's parameter accumulator, `csiFinish`, `arg` and
`moveTo` all composed. Hypotheses as in `cup_step_cursor`: the bounds are
what `Good` supplies, and `origin = false` because under DECOM the
address is region-relative. -/
theorem cup_places_cursor {v : Vt} (row col : Nat) (hg : v.pstate = .ground)
    (hrow : 1 ≤ row) (hcol : 1 ≤ col) (hr : row ≤ 65535) (hc : col ≤ 65535)
    (hry : row - 1 < v.rows) (hcx : col - 1 < v.cols) (ho : v.modes.origin = false) :
    ((v.feed (csiNum2 row col 0x48)).cursor.x = col - 1)
      ∧ ((v.feed (csiNum2 row col 0x48)).cursor.y = row - 1) := by
  -- the stream as a chain of stages
  have hchain : v.feed (csiNum2 row col 0x48)
      = (((((v.step 0x1B).step 0x5B).feed (digits row)).step 0x3B).feed
          (digits col)).step 0x48 := by
    simp [csiNum2, csiB, Vt.feed, List.foldl_append]
  rw [hchain]
  -- parser states: ESC [ opens an empty CSI, the row accumulates, `;`
  -- pushes it, the column accumulates
  have he := esc_step hg
  have hb := csi_open_step he
  obtain ⟨s1, hs1, hcur1, hhave1, hpar1, hint1, hign1, hsub1, hpv1⟩ := csi_digits_value row hb rfl
  have hs2 := csi_semi_step hs1
  have hpush : csiPush s1 false
      = { s1 with params := s1.params.push (min s1.cur 65535, s1.curSub),
                  cur := 0, curSub := false, haveCur := false } := by
    unfold csiPush
    rw [if_pos (by simp [hhave1]), if_neg (by simp [hpar1])]
  rw [hpush] at hs2
  obtain ⟨s3, hs3, hcur3, hhave3, hpar3, hint3, hign3, hsub3, hpv3⟩ := csi_digits_value col hs2 rfl
  -- the frame survives the prefix, so `v`'s bounds transport to it
  have hfr : Frame ((((v.step 0x1B).step 0x5B).feed (digits row)).step 0x3B |>.feed
      (digits col)) = Frame v :=
    ((frame_csi_digits_feed (digits col) hs2 (digits_are_digits col)).trans
      ((frame_csi_semi_step hs1).trans
        ((frame_csi_digits_feed (digits row) hb (digits_are_digits row)).trans
          ((frame_csi_open_step he).trans (frame_esc_step hg)))))
  have hcols : ((((v.step 0x1B).step 0x5B).feed (digits row)).step 0x3B |>.feed
      (digits col)).cols = v.cols := congrArg (·.1) hfr
  have hrows : ((((v.step 0x1B).step 0x5B).feed (digits row)).step 0x3B |>.feed
      (digits col)).rows = v.rows := congrArg (·.2.1) hfr
  have hmod : ((((v.step 0x1B).step 0x5B).feed (digits row)).step 0x3B |>.feed
      (digits col)).modes = v.modes := congrArg (·.2.2) hfr
  -- the row parameter, as `cup_step_cursor` wants it
  have hmm : min (min row 65535) 65535 = min row 65535 := by omega
  have hp : s3.params = #[(min row 65535, false)] := by
    rw [hpar3, hcur1, hpar1, hsub1, hmm]
    rfl
  exact cup_step_cursor row col hs3 (by rw [hint3, hint1])
    (by rw [hign3, hign1]) hhave3 hcur3 hp hrow hcol hr hc
    (by rw [hrows]; exact hry) (by rw [hcols]; exact hcx)
    (by rw [hmod]; exact ho)

/-! ### §Replay: DECOM stays off through a whole restore stream

The rung the restore-level cursor claim needs: a session with DECOM off
must replay with DECOM off, or the final `CUP` would be read
region-relative and land somewhere else entirely.

"`origin` stays off" is **not** composable on its own, and the reason is
worth recording, because it is what dictates the shape below. Fed in the
middle of a CSI, a bare `h` byte completes `CSI ? 6 h` and turns DECOM
*on* — so a predicate quantified over all emulator states is false even
for a run of plain text. The composable statement bundles the parser
state with the flag, which is exactly `Ends` and origin-off together:
-/

/-- From a ground parser with DECOM off, `bs` leaves both that way. -/
def Quiet (bs : Bytes) : Prop :=
  ∀ v : Vt, v.pstate = .ground → v.modes.origin = false →
    ((v.feed bs).pstate = .ground ∧ (v.feed bs).modes.origin = false)

theorem Quiet.nil : Quiet [] := fun _ hg ho => ⟨hg, ho⟩

/-- The composition law — the whole point of bundling. -/
theorem Quiet.append {a b : Bytes} (ha : Quiet a) (hb : Quiet b) : Quiet (a ++ b) := by
  intro v hg ho
  rw [show v.feed (a ++ b) = (v.feed a).feed b from by simp [Vt.feed, List.foldl_append]]
  obtain ⟨h1, h2⟩ := ha v hg ho
  exact hb _ h1 h2

theorem Quiet.streamPred : StreamPred Quiet := ⟨Quiet.nil, fun ha hb => Quiet.append ha hb⟩

theorem Quiet.append3 {a b c : Bytes} (ha : Quiet a) (hb : Quiet b) (hc : Quiet c) :
    Quiet (a ++ b ++ c) := Quiet.streamPred.append3 ha hb hc

/-- Both branches, with the condition available: the mode replays need it
(a guarded emit is what proves the mode number is not 6). -/
theorem Quiet.ite {c : Prop} [Decidable c] {a b : Bytes}
    (ha : c → Quiet a) (hb : ¬c → Quiet b) : Quiet (if c then a else b) :=
  Quiet.streamPred.ite ha hb

theorem Quiet.flatten {l : List Bytes} (h : ∀ bs ∈ l, Quiet bs) : Quiet l.flatten :=
  Quiet.streamPred.flatten h

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
  simp only [show ((0x30 : UInt8)).toNat = 48 from rfl,
    show ((0x3B : UInt8)).toNat = 59 from rfl] at hn1 hn2
  have hw : (v.abortUtf8 b).pstate = PState.csi s := by
    rw [Zmx.Core.Vt.ps_abortUtf8]; exact hg
  unfold Vt.step
  dsimp only
  rw [hw]
  unfold Vt.stepCsi
  dsimp only
  by_cases hd : (b ≥ 0x30 && b ≤ 0x39) = true
  · rw [if_pos hd]; exact ⟨_, rfl, rfl⟩
  by_cases hsemi : (b == 0x3B) = true
  · rw [if_neg (by simp [hd]), if_pos hsemi]
    exact ⟨_, rfl, Zmx.Core.Vt.priv_csiPush _ _⟩
  by_cases hcolon : (b == 0x3A) = true
  · rw [if_neg (by simp [hd]), if_neg (by simp [hsemi]), if_pos hcolon]
    exact ⟨_, rfl, Zmx.Core.Vt.priv_csiPush _ _⟩
  · -- 0x30…0x3B minus digits, `;` and `:` is empty
    exfalso
    have hb39 : ¬ (b.toNat ≤ 57) := by
      intro hle
      exact hd (by
        simp only [Bool.and_eq_true, decide_eq_true_eq, UInt8.le_iff_toNat_le,
          show ((0x30 : UInt8)).toNat = 48 from rfl,
          show ((0x39 : UInt8)).toNat = 57 from rfl]
        omega)
    have hne3B : b.toNat ≠ 59 := by
      intro he
      exact hsemi (by
        simp only [beq_iff_eq]
        apply UInt8.toNat_inj.mp
        simpa [show ((0x3B : UInt8)).toNat = 59 from rfl] using he)
    have hne3A : b.toNat ≠ 58 := by
      intro he
      exact hcolon (by
        simp only [beq_iff_eq]
        apply UInt8.toNat_inj.mp
        simpa [show ((0x3A : UInt8)).toNat = 58 from rfl] using he)
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
  have hw : (v.abortUtf8 0x3F).pstate = PState.csi s := by
    rw [Zmx.Core.Vt.ps_abortUtf8]; exact hg
  refine ⟨?_, org_step_of_csi 0x3F hg hp⟩
  unfold Vt.step
  dsimp only
  rw [hw]
  unfold Vt.stepCsi
  dsimp only
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos (by decide)]

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
    congrArg (·.2.2) (frame_csi_digits_feed (digits n) hm (digits_are_digits n))
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

theorem quiet_escCharset (i x : UInt8) (hi : i = 0x28 ∨ i = 0x29) :
    Quiet (escCharset i x) := by
  intro v hg ho
  refine ⟨ends_escCharset i x hi v hg, ?_⟩
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
  exact (Quiet.text (fun b hb => by
    obtain ⟨hge, -⟩ := utf8_no_ctl (safeChar c.base) (safeChar_ge c.base).1
      (safeChar_ge c.base).2 b hb
    intro he; rw [he] at hge; exact absurd hge (by decide))).append (quiet_utf8s c.marks)

theorem quiet_rowAnsi (row : Row) (p : Pen) : Quiet (rowAnsi row p).1 := by
  unfold rowAnsi
  rw [← Array.foldl_toList]
  refine invariant_foldl (fun acc => Quiet acc.1) _ ?_ row.toList ([], p, 0) Quiet.nil
  intro acc c hacc
  unfold rowSlot
  dsimp only
  repeat' split
  all_goals first
    | exact hacc.append (quiet_utf8s c.marks)
    | exact hacc.append (quiet_cellText c)
    | exact (hacc.append (quiet_penSgr c.pen)).append (quiet_cellText c)
    | exact hacc.append ((((quiet_utf8_safe c.base).append
        (quiet_csiNum _ 0x47 (by decide) (by decide))).append
        (quiet_utf8s c.marks)).append (quiet_csiNum _ 0x47 (by decide) (by decide)))
    | exact (hacc.append (quiet_penSgr c.pen)).append ((((quiet_utf8_safe c.base).append
        (quiet_csiNum _ 0x47 (by decide) (by decide))).append
        (quiet_utf8s c.marks)).append (quiet_csiNum _ 0x47 (by decide) (by decide)))

theorem quiet_joinCRLF : ∀ (l : List Bytes), (∀ bs ∈ l, Quiet bs) → Quiet (joinCRLF l)
  | [], _ => Quiet.nil
  | [b], h => by
    unfold joinCRLF
    exact h b (by simp)
  | b :: c :: bs, h => by
    unfold joinCRLF
    refine ((h b (by simp)).append (Quiet.text (by decide))).append ?_
    exact quiet_joinCRLF (c :: bs) (fun x hx => h x (by simp [hx]))

theorem quiet_gridAnsi (grid : Array Row) : Quiet (gridAnsi grid) := by
  unfold gridAnsi
  dsimp only
  have hrows : ∀ bs ∈ (grid.foldl
      (fun (acc : List Bytes × Pen) row =>
        (acc.1 ++ [(rowAnsi row acc.2).1], (rowAnsi row acc.2).2))
      (([], ({} : Pen)))).1, Quiet bs := by
    rw [← Array.foldl_toList]
    refine invariant_foldl (fun acc => ∀ bs ∈ acc.1, Quiet bs) _ ?_ grid.toList
      (([], ({} : Pen))) (by intro bs hbs; simp at hbs)
    intro acc row hacc bs hbs
    dsimp only at hbs
    rcases List.mem_append.mp hbs with h | h
    · exact hacc bs h
    · simp only [List.mem_singleton] at h
      subst h
      exact quiet_rowAnsi row acc.2
  have hhome : Quiet (csiB ++ [0x48] : Bytes) := by
    rw [show (csiB ++ [0x48] : Bytes) = csiB ++ [] ++ [0x48] from by simp]
    exact quiet_csi_seq [] 0x48 ParamBytes.nil (by decide) (by decide)
  exact (quiet_csiNum 0 0x6D (by decide) (by decide)).append
    (hhome.append (quiet_joinCRLF _ hrows))

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

/-- `Quiet (modeSet 6 false)` cannot come from `quiet_modeSet` — that carries
`n ≠ 6`, for the good reason that mode 6 *is* DECOM. It is the one mode emit whose
`Quiet` is about its value rather than its number. -/
theorem quiet_scrollbackAnsi (v : Vt) : Quiet (scrollbackAnsi v) := by
  unfold scrollbackAnsi
  refine Quiet.append (Quiet.append (Quiet.append ?_
    (quiet_csiNum 4 0x6C (by decide) (by decide))) quiet_modeSet_decom_off)
    (quiet_modeSet 7 true (by decide))
  exact Quiet.ite (fun _ => Quiet.nil)
    (fun _ => (((quiet_csiNum 3 0x4A (by decide) (by decide)).append
      (quiet_gridAnsi (sbRows v))).append (quiet_crlfRun v.rows)))

theorem quiet_screensAnsi (v : Vt) : Quiet (screensAnsi v) := by
  unfold screensAnsi
  refine (quiet_scrollbackAnsi v).append ?_
  split
  · exact quiet_gridAnsi _
  · exact ((((quiet_gridAnsi _).append (quiet_penSgr _)).append
      (quiet_csiNum2 _ _ 0x48 (by decide) (by decide))).append
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

theorem quiet_charsetAnsi (v : Vt) : Quiet (charsetAnsi v) := by
  unfold charsetAnsi
  refine ((Quiet.ite (fun _ => quiet_escCharset 0x28 0x30 (by decide))
    (fun _ => quiet_escCharset 0x28 0x42 (by decide))).append
    (Quiet.ite (fun _ => quiet_escCharset 0x29 0x30 (by decide))
      (fun _ => quiet_escCharset 0x29 0x42 (by decide)))).append ?_
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

theorem quiet_prologueAnsi (v : Vt) : Quiet (prologueAnsi v) := by
  unfold prologueAnsi
  refine Quiet.append ?_ (Quiet.text (bs := [0x0F]) (by decide))
  refine Quiet.append ?_ (quiet_escCharset 0x29 0x42 (by decide))
  refine Quiet.append ?_ (quiet_escCharset 0x28 0x42 (by decide))
  refine Quiet.append ?_ (quiet_csiNum2 1 v.rows 0x72 (by decide) (by decide))
  refine Quiet.append ?_ (quiet_modeSet 7 true (by decide))
  refine Quiet.append ?_ quiet_modeSet_decom_off
  refine Quiet.append ?_ (quiet_csiNum 4 0x6C (by decide) (by decide))
  exact (quiet_escSeq 0x5C (by decide)).append (quiet_modeSet 1049 false (by decide))

theorem quiet_restoreBody (v : Vt) (ho : v.modes.origin = false) : Quiet (restoreBody v) := by
  unfold restoreBody
  refine Quiet.append ?_ (quiet_penSgr v.pen)
  refine Quiet.append ?_ (quiet_charsetAnsi v)
  refine Quiet.append ?_ (quiet_modesAnsi v ho)
  refine Quiet.append ?_ (quiet_titleAnsi v)
  refine Quiet.append ?_ (quiet_savedAnsi v)
  refine Quiet.append ?_ (quiet_tabsAnsi v)
  refine Quiet.append ?_ (quiet_regionAnsi v)
  refine Quiet.append ?_ (quiet_screensAnsi v)
  refine Quiet.append ?_ (quiet_csiNum 2 0x4A (by decide) (by decide))
  exact (quiet_prologueAnsi v).append (quiet_csiNum 0 0x6D (by decide) (by decide))


end Zmx.Core.Render
