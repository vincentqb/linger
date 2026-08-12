import Zmx.Core.Render
import Theorems.Vt
/-! # §Replay, stage 3b — a restore stream leaves the parser in ground

The §Replay target (specs/bigger-theorems.md step 3) is
`(Vt.init v.cols v.rows).feed (restore v) ≃ v`. This file proves the
*parser* half of that `≃`, for ANY `Vt` and with no hypotheses: after
feeding a whole restore stream, the emulator is back in `.ground` with
no half-decoded UTF-8 — i.e. `restore` never leaves a client's parser
wedged mid-sequence, and a checkpoint taken right after a restore is
`quiesce`-clean.

The ladder is compositional, which is the point:

* `Ends bs` — "from ground, `bs` returns to ground with no pending
  UTF-8". `Ends.append` makes it closed under `++`, and `restore` is a
  concatenation, so the top theorem is assembled from one lemma per
  emitted construct (`Ends.csiNum`, `Ends.penSgr`, `Ends.osc`, …).
* Each construct's lemma is proved from the byte facts of the emitters
  (`digits_range`, `utf8_no_ctl`) — which only exist because `Render`
  builds `List UInt8` rather than `String`s (see that module's header).

What this does *not* say: nothing about the screen contents, cursor, or
pen — that is stages 3c/3d, pinned meanwhile by the round-trip fixtures
in `Tests/Render.lean`.
-/

namespace Zmx.Core.Render

open Zmx.Core.Vt

/-! ## Byte facts about the emitters -/

/-- Every digit byte is an ASCII digit — so it is a CSI *parameter*
byte, never a final or a control. -/
theorem digits_range (n : Nat) : ∀ b ∈ digits n, 0x30 ≤ b ∧ b ≤ 0x39 := by
  induction n using digits.induct with
  | case1 n h =>
    intro b hb
    rw [digits] at hb
    simp only [if_pos h, List.mem_singleton] at hb
    subst hb
    have h8 : (0x30 + n) < 256 := by omega
    refine ⟨UInt8.le_iff_toNat_le.mpr ?_, UInt8.le_iff_toNat_le.mpr ?_⟩
    · simp [UInt8.toNat_ofNat', Nat.mod_eq_of_lt h8]
    · simp [UInt8.toNat_ofNat', Nat.mod_eq_of_lt h8]
      omega
  | case2 n h ih =>
    intro b hb
    rw [digits] at hb
    simp only [if_neg h, List.mem_append, List.mem_singleton] at hb
    rcases hb with hb | hb
    · exact ih b hb
    · subst hb
      have hlt : n % 10 < 10 := Nat.mod_lt _ (by omega)
      have h8 : (0x30 + n % 10) < 256 := by omega
      refine ⟨UInt8.le_iff_toNat_le.mpr ?_, UInt8.le_iff_toNat_le.mpr ?_⟩
      · simp [UInt8.toNat_ofNat', Nat.mod_eq_of_lt h8]
      · simp [UInt8.toNat_ofNat', Nat.mod_eq_of_lt h8]
        omega

/-- A digit byte is not ESC. -/
theorem digits_no_esc (n : Nat) : ∀ b ∈ digits n, b ≠ 0x1B := by
  intro b hb he
  obtain ⟨h1, -⟩ := digits_range n b hb
  rw [he] at h1
  exact absurd h1 (by decide)

/-- `safeChar` never yields a C0 control or DEL. -/
theorem safeChar_ge (c : Char) : (safeChar c).toNat ≥ 0x20 ∧ (safeChar c).toNat ≠ 0x7F := by
  unfold safeChar
  by_cases h : (c.toNat < 0x20 || c.toNat == 0x7F) = true
  · simp only [h, if_true]
    exact ⟨by decide, by decide⟩
  · simp only [h, Bool.false_eq_true, if_false]
    simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, not_or, Nat.not_lt] at h
    exact ⟨h.1, h.2⟩

/-- A byte built by `UInt8.ofNat` from an in-range non-control number is
a non-control byte. The bridge from the emitters' arithmetic to byte
facts. -/
theorem ofNat_no_ctl (m : Nat) (h20 : 0x20 ≤ m) (hlt : m < 256) (h7 : m ≠ 0x7F) :
    (UInt8.ofNat m) ≥ 0x20 ∧ (UInt8.ofNat m) ≠ 0x7F := by
  have htn : (UInt8.ofNat m).toNat = m := by
    simp [UInt8.toNat_ofNat', Nat.mod_eq_of_lt hlt]
  refine ⟨UInt8.le_iff_toNat_le.mpr (by rw [htn]; simpa using h20), ?_⟩
  intro hcon
  have := congrArg UInt8.toNat hcon
  rw [htn] at this
  simp at this
  exact h7 this

/-- Every byte of a UTF-8 encoding of a non-control codepoint is itself
non-control: ASCII ≥ 0x20 stays put, and every lead/continuation byte of
a multi-byte sequence is ≥ 0x80. So printable text can never smuggle an
ESC (or any C0) into the stream. -/
theorem utf8_no_ctl (c : Char) (h : c.toNat ≥ 0x20) (h7 : c.toNat ≠ 0x7F) :
    ∀ b ∈ utf8 c, b ≥ 0x20 ∧ b ≠ 0x7F := by
  intro b hb
  unfold utf8 at hb
  dsimp only at hb
  -- the clamp makes every branch's arithmetic omega-visible; the branch
  -- conditions land as inaccessible hypotheses, which omega still reads
  have hm1 : min c.toNat 0x10FFFF % 64 < 64 := Nat.mod_lt _ (by omega)
  have hm2 : min c.toNat 0x10FFFF / 64 % 64 < 64 := Nat.mod_lt _ (by omega)
  have hm3 : min c.toNat 0x10FFFF / 4096 % 64 < 64 := Nat.mod_lt _ (by omega)
  repeat' split at hb
  all_goals simp only [List.mem_cons] at hb
  -- rcases substitutes `b` itself in the multi-byte cases; the 1-byte
  -- case is a bare equality, so the subst there is the `try`
  all_goals repeat' rcases hb with hb | hb
  all_goals try subst hb
  all_goals exact ofNat_no_ctl _ (by omega) (by omega) (by omega)

/-- …and therefore of a whole scrubbed char list. -/
theorem utf8s_no_ctl (cs : List Char) : ∀ b ∈ utf8s cs, b ≥ 0x20 ∧ b ≠ 0x7F := by
  intro b hb
  unfold utf8s at hb
  obtain ⟨c, -, hmem⟩ := List.mem_flatMap.mp hb
  obtain ⟨hge, hne⟩ := safeChar_ge c
  exact utf8_no_ctl (safeChar c) hge hne b hmem

theorem utf8s_no_esc (cs : List Char) : ∀ b ∈ utf8s cs, b ≠ 0x1B := by
  intro b hb he
  obtain ⟨hge, -⟩ := utf8s_no_ctl cs b hb
  rw [he] at hge
  exact absurd hge (by decide)

/-! ## `Ends`: the compositional core

`Ends bs` is exactly the property that composes over `++`, which is what
lets the top theorem be assembled construct by construct instead of by
tracing a whole restore stream.
-/

/-- From a ground parser, feeding `bs` returns to a ground parser: no
restore stream can leave a client wedged mid-sequence, eating the
application's next output.

Scoped deliberately to `pstate`. The companion claim `u8need = 0` needs
per-operation `u8need` lemmas through `csiDispatch` (~25, the same shape
as the `cols`/`rows` gap in the step-4 notes) and buys much less: a
trailing partial UTF-8 sequence can only mis-render the *next* glyph,
whereas a stuck `.csi` state swallows everything. `restore` emits only
complete encodings, and it is pinned by the `Tests/Render.lean` fixtures
(`replayEq` checks `u8need == 0`); the theorem is listed as open in
specs/bigger-theorems.md. -/
def Ends (bs : Bytes) : Prop :=
  ∀ v : Vt, v.pstate = .ground → (v.feed bs).pstate = .ground

theorem feed_cons (v : Vt) (x : UInt8) (xs : Bytes) :
    v.feed (x :: xs) = (v.step x).feed xs := by simp [Vt.feed]

theorem Ends.nil : Ends [] := fun _ h => h

/-- The composition law. `Vt.feed` is a `foldl`, so this is
`List.foldl_append` plus transitivity. -/
theorem Ends.append {a b : Bytes} (ha : Ends a) (hb : Ends b) : Ends (a ++ b) := by
  intro v h
  have : v.feed (a ++ b) = (v.feed a).feed b := by simp [Vt.feed, List.foldl_append]
  rw [this]
  exact hb (v.feed a) (ha v h)

theorem Ends.append3 {a b c : Bytes} (ha : Ends a) (hb : Ends b) (hc : Ends c) :
    Ends (a ++ b ++ c) := (ha.append hb).append hc

theorem Ends.append4 {a b c d : Bytes} (ha : Ends a) (hb : Ends b) (hc : Ends c)
    (hd : Ends d) : Ends (a ++ b ++ c ++ d) := ((ha.append hb).append hc).append hd

/-- An `if` over two `Ends` pieces is `Ends` (restore is full of
conditional fragments). -/
theorem Ends.ite {c : Prop} [Decidable c] {a b : Bytes}
    (ha : Ends a) (hb : Ends b) : Ends (if c then a else b) := by
  by_cases h : c <;> simp only [h, if_true, if_false] <;> assumption

theorem Ends.flatten {l : List Bytes} (h : ∀ bs ∈ l, Ends bs) : Ends l.flatten := by
  induction l with
  | nil => exact Ends.nil
  | cons a as ih =>
    rw [List.flatten_cons]
    exact (h a (by simp)).append (ih (fun bs hbs => h bs (by simp [hbs])))

theorem Ends.flatMap {α : Type} {f : α → Bytes} {l : List α}
    (h : ∀ a, Ends (f a)) : Ends (l.flatMap f) := by
  induction l with
  | nil => exact Ends.nil
  | cons a as ih =>
    rw [List.flatMap_cons]
    exact (h a).append ih

/-! ### One lemma per emitted construct

These are the only places that reason about `Vt.step`. Everything above
is plumbing; the top theorem is their composition.
-/

/-- A single non-ESC byte from a ground parser leaves it ground. -/
theorem ground_step {v : Vt} (b : UInt8) (hg : v.pstate = .ground) (hb : b ≠ 0x1B) :
    (v.step b).pstate = .ground := by
  -- `abortUtf8` touches only u8need/u8acc, so the match scrutinee is
  -- still ground; rewriting it is what lets the match reduce
  have hw : (v.abortUtf8 b).pstate = PState.ground := by
    rw [Zmx.Core.Vt.ps_abortUtf8]; exact hg
  unfold Vt.step
  dsimp only
  rw [hw, Zmx.Core.Vt.ps_stepGround _ b hb]
  exact hw

/-- Printable/control text (anything with no ESC in it) is `Ends`: the
grid repaint, which is most of a restore stream, lands here. -/
theorem ground_feed : ∀ (bs : Bytes) (v : Vt), v.pstate = .ground →
    (∀ b ∈ bs, b ≠ 0x1B) → (v.feed bs).pstate = .ground
  | [], _, hg, _ => hg
  | x :: xs, v, hg, h => by
    rw [feed_cons]
    exact ground_feed xs _ (ground_step x hg (h x (by simp)))
      (fun b hb => h b (by simp [hb]))

theorem Ends.text {bs : Bytes} (h : ∀ b ∈ bs, b ≠ 0x1B) : Ends bs :=
  fun v hg => ground_feed bs v hg h

/-- ESC from ground opens `.esc`. -/
theorem esc_step {v : Vt} (hg : v.pstate = .ground) : (v.step 0x1B).pstate = .esc := by
  have hw : (v.abortUtf8 0x1B).pstate = PState.ground := by
    rw [Zmx.Core.Vt.ps_abortUtf8]; exact hg
  unfold Vt.step
  dsimp only
  rw [hw]
  rfl

/-- `ESC [` opens a CSI with an empty parameter set. -/
theorem csi_open_step {v : Vt} (hg : v.pstate = .esc) :
    (v.step 0x5B).pstate = .csi {} := by
  have hw : (v.abortUtf8 0x5B).pstate = PState.esc := by
    rw [Zmx.Core.Vt.ps_abortUtf8]; exact hg
  unfold Vt.step
  dsimp only
  rw [hw]
  rfl

/-- `UInt8` comparisons, in `Nat` where `omega` can see them. The whole
ladder's guard reasoning goes through this. -/
private theorem u8_bounds {b : UInt8} {lo hi : UInt8} (h1 : lo ≤ b) (h2 : b ≤ hi) :
    lo.toNat ≤ b.toNat ∧ b.toNat ≤ hi.toNat :=
  ⟨UInt8.le_iff_toNat_le.mp h1, UInt8.le_iff_toNat_le.mp h2⟩

/-- A parameter byte (digit, `:`, `;`, or a `<=>?` private marker) keeps
us inside `.csi` — with some other accumulator, which is all the ladder
needs to know. -/
theorem csi_param_step {v : Vt} {s : CsiState} (b : UInt8) (hg : v.pstate = .csi s)
    (h1 : 0x30 ≤ b) (h2 : b ≤ 0x3F) : ∃ s', (v.step b).pstate = .csi s' := by
  obtain ⟨hn1, hn2⟩ := u8_bounds h1 h2
  simp only [show ((0x30 : UInt8)).toNat = 48 from rfl,
    show ((0x3F : UInt8)).toNat = 63 from rfl] at hn1 hn2
  have hw : (v.abortUtf8 b).pstate = PState.csi s := by
    rw [Zmx.Core.Vt.ps_abortUtf8]; exact hg
  unfold Vt.step
  dsimp only
  rw [hw]
  unfold Vt.stepCsi
  dsimp only
  -- digit? separator? private marker? — every case stays in `.csi`
  by_cases hd : (b ≥ 0x30 && b ≤ 0x39) = true
  · rw [if_pos hd]; exact ⟨_, rfl⟩
  by_cases hsemi : (b == 0x3B) = true
  · rw [if_neg (by simp [hd]), if_pos hsemi]; exact ⟨_, rfl⟩
  by_cases hcolon : (b == 0x3A) = true
  · rw [if_neg (by simp [hd]), if_neg (by simp [hsemi]), if_pos hcolon]
    exact ⟨_, rfl⟩
  · -- what remains is 0x3C…0x3F
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
    have hpriv : (b ≥ 0x3C && b ≤ 0x3F) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq, UInt8.le_iff_toNat_le,
        show ((0x3C : UInt8)).toNat = 60 from rfl,
        show ((0x3F : UInt8)).toNat = 63 from rfl]
      omega
    rw [if_neg (by simp [hd]), if_neg (by simp [hsemi]), if_neg (by simp [hcolon]),
        if_pos hpriv]
    exact ⟨_, rfl⟩

/-- A run of parameter bytes keeps us inside `.csi`. -/
theorem csi_param_feed : ∀ (bs : Bytes) {v : Vt} {s : CsiState}, v.pstate = .csi s →
    (∀ b ∈ bs, 0x30 ≤ b ∧ b ≤ 0x3F) → ∃ s', (v.feed bs).pstate = .csi s'
  | [], _, s, hg, _ => ⟨s, hg⟩
  | x :: xs, v, s, hg, h => by
    obtain ⟨s', hs'⟩ := csi_param_step x hg (h x (by simp)).1 (h x (by simp)).2
    rw [feed_cons]
    exact csi_param_feed xs hs' (fun b hb => h b (by simp [hb]))

/-- A final byte in 0x40…0x7E dispatches the sequence and returns to
ground: `csiFinish` assigns `.ground` unconditionally, and so does the
intermediate-ignore branch. -/
theorem csi_final_step {v : Vt} {s : CsiState} (b : UInt8) (hg : v.pstate = .csi s)
    (h1 : 0x40 ≤ b) (h2 : b ≤ 0x7E) : (v.step b).pstate = .ground := by
  obtain ⟨hn1, hn2⟩ := u8_bounds h1 h2
  simp only [show ((0x40 : UInt8)).toNat = 64 from rfl,
    show ((0x7E : UInt8)).toNat = 126 from rfl] at hn1 hn2
  have hw : (v.abortUtf8 b).pstate = PState.csi s := by
    rw [Zmx.Core.Vt.ps_abortUtf8]; exact hg
  -- every pre-final guard is below 0x40, so all are false
  have g1 : (b ≥ 0x30 && b ≤ 0x39) = false := by
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, UInt8.le_iff_toNat_le,
      show ((0x39 : UInt8)).toNat = 57 from rfl]
    right; omega
  have g2 : (b == 0x3B) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro he
    rw [he] at hn1
    simp only [show ((0x3B : UInt8)).toNat = 59 from rfl] at hn1
    omega
  have g3 : (b == 0x3A) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro he
    rw [he] at hn1
    simp only [show ((0x3A : UInt8)).toNat = 58 from rfl] at hn1
    omega
  have g4 : (b ≥ 0x3C && b ≤ 0x3F) = false := by
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, UInt8.le_iff_toNat_le,
      show ((0x3F : UInt8)).toNat = 63 from rfl]
    right; omega
  have g5 : (b ≥ 0x20 && b ≤ 0x2F) = false := by
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, UInt8.le_iff_toNat_le,
      show ((0x2F : UInt8)).toNat = 47 from rfl]
    right; omega
  have g6 : (b ≥ 0x40 && b ≤ 0x7E) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨h1, h2⟩
  unfold Vt.step
  dsimp only
  rw [hw]
  unfold Vt.stepCsi
  dsimp only
  rw [if_neg (by simp [g1]), if_neg (by simp [g2]), if_neg (by simp [g3]),
      if_neg (by simp [g4]), if_neg (by simp [g5]), if_pos g6]
  -- both remaining branches assign `.ground`
  split
  · rfl
  · unfold Vt.csiFinish
    rfl

/-- Bytes legal inside a CSI parameter string: digits, `:`/`;`, and the
`<=>?` private markers — everything `Render` puts between `CSI` and the
final byte. -/
def ParamBytes (bs : Bytes) : Prop := ∀ b ∈ bs, 0x30 ≤ b ∧ b ≤ 0x3F

theorem ParamBytes.nil : ParamBytes [] := by intro b hb; simp at hb

theorem ParamBytes.append {a b : Bytes} (ha : ParamBytes a) (hb : ParamBytes b) :
    ParamBytes (a ++ b) := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact ha x h
  · exact hb x h

theorem ParamBytes.cons {x : UInt8} {bs : Bytes} (h1 : 0x30 ≤ x) (h2 : x ≤ 0x3F)
    (hb : ParamBytes bs) : ParamBytes (x :: bs) := by
  intro y hy
  rcases List.mem_cons.mp hy with h | h
  · subst h; exact ⟨h1, h2⟩
  · exact hb y h

theorem paramBytes_digits (n : Nat) : ParamBytes (digits n) := by
  intro b hb
  obtain ⟨hd1, hd2⟩ := digits_range n b hb
  refine ⟨hd1, ?_⟩
  simp only [UInt8.le_iff_toNat_le, show ((0x39 : UInt8)).toNat = 57 from rfl,
    show ((0x3F : UInt8)).toNat = 63 from rfl] at hd2 ⊢
  omega

/-- `;<number>` — the shape every SGR sub-parameter takes. -/
theorem paramBytes_semiDigits (n : Nat) : ParamBytes (0x3B :: digits n) := by
  refine ParamBytes.cons ?_ ?_ (paramBytes_digits n) <;> decide

/-- **The CSI lemma.** `CSI <params> <final>` returns the parser to
ground. Every CSI-shaped construct in `restore` — cursor addressing, SGR
pens, mode set/reset, scroll region, tab ruler — is an instance, so this
is where the ladder pays for itself. -/
theorem ends_csi_seq (params : Bytes) (final : UInt8) (hp : ParamBytes params)
    (h1 : 0x40 ≤ final) (h2 : final ≤ 0x7E) : Ends (csiB ++ params ++ [final]) := by
  intro v hg
  show (v.feed ([0x1B, 0x5B] ++ params ++ [final])).pstate = .ground
  rw [show ([0x1B, 0x5B] ++ params ++ [final] : Bytes)
        = 0x1B :: 0x5B :: (params ++ [final]) from rfl]
  rw [feed_cons, feed_cons]
  have hb := csi_open_step (esc_step hg)
  have hsplit : ((v.step 0x1B).step 0x5B).feed (params ++ [final])
      = (((v.step 0x1B).step 0x5B).feed params).feed [final] := by
    simp [Vt.feed, List.foldl_append]
  rw [hsplit]
  obtain ⟨s', hs'⟩ := csi_param_feed params hb hp
  rw [show (((v.step 0x1B).step 0x5B).feed params).feed [final]
        = ((((v.step 0x1B).step 0x5B).feed params).step final) from rfl]
  exact csi_final_step final hs' h1 h2

theorem ends_csiNum (n : Nat) (final : UInt8) (h1 : 0x40 ≤ final) (h2 : final ≤ 0x7E) :
    Ends (csiNum n final) :=
  ends_csi_seq _ final (paramBytes_digits n) h1 h2

theorem ends_csiNum2 (a b : Nat) (final : UInt8) (h1 : 0x40 ≤ final)
    (h2 : final ≤ 0x7E) : Ends (csiNum2 a b final) := by
  have : csiNum2 a b final = csiB ++ (digits a ++ [0x3B] ++ digits b) ++ [final] := by
    simp [csiNum2, List.append_assoc]
  rw [this]
  exact ends_csi_seq _ final
    (((paramBytes_digits a).append
      (ParamBytes.cons (by decide) (by decide) ParamBytes.nil)).append
      (paramBytes_digits b)) h1 h2

theorem ends_csiPriv (n : Nat) (final : UInt8) (h1 : 0x40 ≤ final)
    (h2 : final ≤ 0x7E) : Ends (csiPriv n final) := by
  have : csiPriv n final = csiB ++ (0x3F :: digits n) ++ [final] := by
    simp [csiPriv]
  rw [this]
  exact ends_csi_seq _ final
    (ParamBytes.cons (by decide) (by decide) (paramBytes_digits n)) h1 h2

/-- Not yet proved: the composition. See below. -/
theorem paramBytes_sgr_subparam (n : Nat) : ParamBytes (0x3B :: digits n) :=
  paramBytes_semiDigits n

/-! ### SGR pens -/

theorem paramBytes_sgrAttr (on : Bool) (code : Nat) : ParamBytes (sgrAttr on code) := by
  unfold sgrAttr
  by_cases h : on <;> simp only [h, if_true]
  · exact paramBytes_semiDigits _
  · exact ParamBytes.nil

theorem paramBytes_sgrColor (c : Color) (isFg : Bool) : ParamBytes (sgrColor c isFg) := by
  unfold sgrColor
  cases c with
  | default => exact ParamBytes.nil
  | idx i =>
    dsimp only
    repeat' split
    all_goals first
      | exact paramBytes_semiDigits _
      | exact (((paramBytes_semiDigits _).append (paramBytes_semiDigits _)).append
          (paramBytes_semiDigits _))
  | rgb r g b =>
    exact ((((((paramBytes_semiDigits _).append (paramBytes_semiDigits _)).append
      (paramBytes_semiDigits _)).append (paramBytes_semiDigits _)).append
      (paramBytes_semiDigits _)))

theorem paramBytes_penSgrBody (p : Pen) : ParamBytes (penSgrBody p) := by
  unfold penSgrBody
  exact (((((((((paramBytes_digits 0).append (paramBytes_sgrAttr _ 1)).append
    (paramBytes_sgrAttr _ 2)).append (paramBytes_sgrAttr _ 3)).append
    (paramBytes_sgrAttr _ 4)).append (paramBytes_sgrAttr _ 5)).append
    (paramBytes_sgrAttr _ 7)).append (paramBytes_sgrAttr _ 9)).append
    (paramBytes_sgrColor _ true)).append (paramBytes_sgrColor _ false)

/-- An SGR pen is one CSI sequence: `Ends`, for any pen (16-colour,
256-colour, truecolour). -/
theorem ends_penSgr (p : Pen) : Ends (penSgr p) :=
  ends_csi_seq _ 0x6D (paramBytes_penSgrBody p) (by decide) (by decide)

/-! ### `ESC`-single and charset sequences

`stepEsc` assigns `.ground` for every final it honours; `ESC (`/`ESC )`
go to `.escInter`, whose every branch is `.ground`. -/

/-- An `ESC <final>` whose final is one of the single-byte sequences
`restore` emits — `7` (DECSC), `=` (app keypad), `H` (HTS) — lands back
in ground. -/
theorem esc_single_step {v : Vt} (b : UInt8) (hg : v.pstate = .esc)
    (hb : b = 0x37 ∨ b = 0x3D ∨ b = 0x48) : (v.step b).pstate = .ground := by
  have hw : (v.abortUtf8 b).pstate = PState.esc := by
    rw [Zmx.Core.Vt.ps_abortUtf8]; exact hg
  unfold Vt.step
  dsimp only
  rw [hw]
  unfold Vt.stepEsc
  rcases hb with h | h | h <;> subst h <;> rfl

/-- `ESC (` / `ESC )` enter the charset-designation state. -/
theorem esc_inter_step {v : Vt} (b : UInt8) (hg : v.pstate = .esc)
    (hb : b = 0x28 ∨ b = 0x29) : (v.step b).pstate = .escInter b := by
  have hw : (v.abortUtf8 b).pstate = PState.esc := by
    rw [Zmx.Core.Vt.ps_abortUtf8]; exact hg
  unfold Vt.step
  dsimp only
  rw [hw]
  unfold Vt.stepEsc
  rcases hb with h | h <;> subst h <;> rfl

/-- …and the byte after it always returns to ground. -/
theorem esc_inter_finish {v : Vt} {i : UInt8} (b : UInt8) (hg : v.pstate = .escInter i) :
    (v.step b).pstate = .ground := by
  have hw : (v.abortUtf8 b).pstate = PState.escInter i := by
    rw [Zmx.Core.Vt.ps_abortUtf8]; exact hg
  unfold Vt.step
  dsimp only
  rw [hw]
  unfold Vt.stepEscInter
  dsimp only
  repeat' split
  all_goals rfl

/-- `ESC 7` (DECSC), `ESC =` and `ESC H` (HTS) are `Ends`. -/
theorem ends_escSeq (b : UInt8) (hb : b = 0x37 ∨ b = 0x3D ∨ b = 0x48) :
    Ends (escSeq b) := by
  intro v hg
  show (v.feed ([0x1B] ++ [b])).pstate = .ground
  rw [show ([0x1B] ++ [b] : Bytes) = 0x1B :: [b] from rfl, feed_cons]
  show ((v.step 0x1B).step b).pstate = .ground
  exact esc_single_step b (esc_step hg) hb

/-- `ESC ( x` / `ESC ) x` (charset designation) are `Ends`. -/
theorem ends_escCharset (i x : UInt8) (hi : i = 0x28 ∨ i = 0x29) :
    Ends (escCharset i x) := by
  intro v hg
  show (v.feed ([0x1B] ++ [i, x])).pstate = .ground
  rw [show ([0x1B] ++ [i, x] : Bytes) = 0x1B :: i :: [x] from rfl, feed_cons, feed_cons]
  show (((v.step 0x1B).step i).step x).pstate = .ground
  exact esc_inter_finish x (esc_inter_step i (esc_step hg) hi)

/-! ### OSC (the window title)

`ESC ] 2 ; <payload> BEL`. The payload is `utf8s`-scrubbed, so it holds
neither ESC nor BEL: it cannot terminate its own sequence early, and
cannot start a nested one. -/

/-- `ESC ]` opens an OSC accumulator. -/
theorem osc_open_step {v : Vt} (hg : v.pstate = .esc) :
    (v.step 0x5D).pstate = .osc #[] false := by
  have hw : (v.abortUtf8 0x5D).pstate = PState.esc := by
    rw [Zmx.Core.Vt.ps_abortUtf8]; exact hg
  unfold Vt.step
  dsimp only
  rw [hw]
  rfl

/-- A payload byte that is neither ESC nor BEL keeps accumulating. The
`esc`-flag stays `false`, which matters: with the flag set, a `\` byte
would close the sequence as an ST — so the flag has to be carried, not
existentially quantified. -/
theorem osc_accum_step {v : Vt} {acc : Array UInt8} (b : UInt8)
    (hg : v.pstate = .osc acc false) (h1 : b ≠ 0x1B) (h2 : b ≠ 0x07) :
    ∃ acc', (v.step b).pstate = .osc acc' false := by
  have hw : (v.abortUtf8 b).pstate = PState.osc acc false := by
    rw [Zmx.Core.Vt.ps_abortUtf8]; exact hg
  unfold Vt.step
  dsimp only
  rw [hw]
  unfold Vt.stepOsc
  dsimp only
  -- ST needs the esc flag (false here); BEL and ESC are excluded; both
  -- the cap branch and the accumulate branch stay `.osc … false`
  rw [if_neg (by simp), if_neg (by simp [h2]), if_neg (by simp [h1])]
  split
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

theorem osc_accum_feed : ∀ (bs : Bytes) {v : Vt} {acc : Array UInt8},
    v.pstate = .osc acc false → (∀ b ∈ bs, b ≠ 0x1B ∧ b ≠ 0x07) →
    ∃ acc', (v.feed bs).pstate = .osc acc' false
  | [], _, acc, hg, _ => ⟨acc, hg⟩
  | x :: xs, v, acc, hg, h => by
    obtain ⟨acc', hs⟩ := osc_accum_step x hg (h x (by simp)).1 (h x (by simp)).2
    rw [feed_cons]
    exact osc_accum_feed xs hs (fun b hb => h b (by simp [hb]))

/-- BEL closes the OSC: `oscFinish` assigns `.ground` before it decides
whether the payload was a title. -/
theorem osc_bel_step {v : Vt} {acc : Array UInt8} {e : Bool}
    (hg : v.pstate = .osc acc e) : (v.step 0x07).pstate = .ground := by
  have hw : (v.abortUtf8 0x07).pstate = PState.osc acc e := by
    rw [Zmx.Core.Vt.ps_abortUtf8]; exact hg
  unfold Vt.step
  dsimp only
  rw [hw]
  unfold Vt.stepOsc
  dsimp only
  rw [if_neg (by simp), if_pos (by decide)]
  unfold Vt.oscFinish
  dsimp only
  repeat' split
  all_goals rfl

/-- The scrubbed title payload carries neither ESC nor BEL. -/
theorem utf8s_no_esc_bel (cs : List Char) : ∀ b ∈ utf8s cs, b ≠ 0x1B ∧ b ≠ 0x07 := by
  intro b hb
  obtain ⟨hge, -⟩ := utf8s_no_ctl cs b hb
  refine ⟨fun he => ?_, fun he => ?_⟩
  · rw [he] at hge; exact absurd hge (by decide)
  · rw [he] at hge; exact absurd hge (by decide)

/-- §Replay: an OSC 2 title sequence is `Ends`. -/
theorem ends_osc (payload : List Char) :
    Ends (escB ++ [0x5D, 0x32, 0x3B] ++ utf8s payload ++ [0x07]) := by
  have hshape : (escB ++ [0x5D, 0x32, 0x3B] ++ utf8s payload ++ [0x07] : Bytes)
      = 0x1B :: 0x5D :: 0x32 :: 0x3B :: (utf8s payload ++ [0x07]) := by
    simp [escB]
  intro v hg
  rw [hshape, feed_cons, feed_cons, feed_cons, feed_cons]
  have h1 := osc_open_step (esc_step hg)
  obtain ⟨a2, h2⟩ := osc_accum_step 0x32 h1 (by decide) (by decide)
  obtain ⟨a3, h3⟩ := osc_accum_step 0x3B h2 (by decide) (by decide)
  have hsplit : ∀ (w : Vt), w.feed (utf8s payload ++ [0x07])
      = (w.feed (utf8s payload)).feed [0x07] := by
    intro w; simp [Vt.feed, List.foldl_append]
  rw [hsplit]
  obtain ⟨a4, h4⟩ := osc_accum_feed (utf8s payload) h3 (utf8s_no_esc_bel payload)
  exact osc_bel_step h4

/-! ### The grid repaint

Cells contribute scrubbed text (`Ends.text`) and, when the pen changes,
an SGR sequence (`ends_penSgr`). Both are `Ends`, so the fold that
assembles a row preserves "everything so far is `Ends`" — the generic
fold-invariant lemma below is what carries that, and it is reused for the
grid's list of painted rows. -/

theorem invariant_foldl {α β : Type} (P : β → Prop) (f : β → α → β)
    (hf : ∀ acc a, P acc → P (f acc a)) :
    ∀ (l : List α) (acc : β), P acc → P (l.foldl f acc)
  | [], _, h => h
  | a :: as, acc, h => invariant_foldl P f hf as (f acc a) (hf acc a h)

theorem ends_utf8s (cs : List Char) : Ends (utf8s cs) :=
  Ends.text (utf8s_no_esc cs)

theorem ends_cellText (c : Cell) : Ends (cellText c) := by
  unfold cellText
  exact (Ends.text (fun b hb => by
    obtain ⟨hge, -⟩ := utf8_no_ctl (safeChar c.base) (safeChar_ge c.base).1
      (safeChar_ge c.base).2 b hb
    intro he; rw [he] at hge; exact absurd hge (by decide))).append (ends_utf8s c.marks)

theorem ends_rowAnsi (row : Row) (p : Pen) : Ends (rowAnsi row p).1 := by
  unfold rowAnsi
  rw [← Array.foldl_toList]
  refine invariant_foldl (fun acc => Ends acc.1) _ ?_ row.toList ([], p) Ends.nil
  intro acc c hacc
  dsimp only
  split
  · exact hacc.append (ends_utf8s c.marks)
  · dsimp only
    split
    · exact hacc.append (ends_cellText c)
    · exact (hacc.append (ends_penSgr c.pen)).append (ends_cellText c)

theorem ends_crlf : Ends [0x0D, 0x0A] := Ends.text (by decide)

theorem ends_joinCRLF : ∀ (l : List Bytes), (∀ bs ∈ l, Ends bs) → Ends (joinCRLF l)
  | [], _ => Ends.nil
  | [b], h => by
    unfold joinCRLF
    exact h b (by simp)
  | b :: c :: bs, h => by
    unfold joinCRLF
    refine ((h b (by simp)).append ends_crlf).append ?_
    exact ends_joinCRLF (c :: bs) (fun x hx => h x (by simp [hx]))

theorem ends_gridAnsi (grid : Array Row) : Ends (gridAnsi grid) := by
  unfold gridAnsi
  dsimp only
  have hrows : ∀ bs ∈ (grid.foldl
      (fun (acc : List Bytes × Pen) row =>
        (acc.1 ++ [(rowAnsi row acc.2).1], (rowAnsi row acc.2).2))
      (([], ({} : Pen)))).1, Ends bs := by
    rw [← Array.foldl_toList]
    refine invariant_foldl (fun acc => ∀ bs ∈ acc.1, Ends bs) _ ?_ grid.toList
      (([], ({} : Pen))) (by intro bs hbs; simp at hbs)
    intro acc row hacc bs hbs
    dsimp only at hbs
    rcases List.mem_append.mp hbs with h | h
    · exact hacc bs h
    · simp only [List.mem_singleton] at h
      subst h
      exact ends_rowAnsi row acc.2
  -- `ESC [ H` is a CSI sequence with no parameters
  have hhome : Ends (csiB ++ [0x48] : Bytes) := by
    have : (csiB ++ [0x48] : Bytes) = csiB ++ [] ++ [0x48] := by simp
    rw [this]
    exact ends_csi_seq [] 0x48 ParamBytes.nil (by decide) (by decide)
  exact hhome.append (ends_joinCRLF _ hrows)

/-! ### The composition: a whole restore stream

Every stage of `restore` is `Ends`, so the stream is. This is §Replay's
parser half, for ANY `Vt` and with no hypotheses.
-/

theorem ends_screensAnsi (v : Vt) : Ends (screensAnsi v) := by
  unfold screensAnsi
  split
  · exact ends_gridAnsi _
  · exact ((((ends_gridAnsi _).append (ends_penSgr _)).append
      (ends_csiNum2 _ _ 0x48 (by decide) (by decide))).append
      (ends_csiPriv 1049 0x68 (by decide) (by decide))).append (ends_gridAnsi _)

theorem ends_regionAnsi (v : Vt) : Ends (regionAnsi v) := by
  unfold regionAnsi
  exact Ends.ite Ends.nil (ends_csiNum2 _ _ 0x72 (by decide) (by decide))

theorem ends_tabsAnsi (v : Vt) : Ends (tabsAnsi v) := by
  unfold tabsAnsi
  refine Ends.ite Ends.nil ?_
  refine (ends_csiNum 3 0x67 (by decide) (by decide)).append ?_
  refine Ends.flatMap (fun i => ?_)
  exact (ends_csiNum (i + 1) 0x47 (by decide) (by decide)).append
    (ends_escSeq 0x48 (by decide))

theorem ends_savedAnsi (v : Vt) : Ends (savedAnsi v) := by
  unfold savedAnsi
  exact ((ends_penSgr _).append (ends_csiNum2 _ _ 0x48 (by decide) (by decide))).append
    (ends_escSeq 0x37 (by decide))

theorem ends_charsetAnsi (v : Vt) : Ends (charsetAnsi v) := by
  unfold charsetAnsi
  refine ((Ends.ite (ends_escCharset 0x28 0x30 (by decide))
    (ends_escCharset 0x28 0x42 (by decide))).append
    (Ends.ite (ends_escCharset 0x29 0x30 (by decide))
      (ends_escCharset 0x29 0x42 (by decide)))).append ?_
  exact Ends.ite (Ends.text (by decide)) Ends.nil

theorem ends_titleAnsi (v : Vt) : Ends (titleAnsi v) := by
  unfold titleAnsi
  exact Ends.ite Ends.nil (ends_osc _)

theorem ends_modesAnsi (v : Vt) : Ends (modesAnsi v) := by
  unfold modesAnsi
  dsimp only
  have hset : ∀ (n : Nat) (on : Bool), Ends (csiPriv n (if on then 0x68 else 0x6C)) := by
    intro n on
    by_cases h : on <;> simp only [h, if_true]
    · exact ends_csiPriv n 0x68 (by decide) (by decide)
    · exact ends_csiPriv n 0x6C (by decide) (by decide)
  have e1 : Ends (if v.modes.wrap then [] else csiPriv 7 (if false then 0x68 else 0x6C)) :=
    Ends.ite Ends.nil (hset 7 false)
  have e2 := Ends.ite (c := v.modes.appCursor = true) (hset 1 true) Ends.nil
  have e3 := Ends.ite (c := v.modes.appKeypad = true) (ends_escSeq 0x3D (by decide)) Ends.nil
  have e4 := Ends.ite (c := v.modes.cursorVisible = true) Ends.nil (hset 25 false)
  have e5 := Ends.ite (c := v.modes.bracketedPaste = true) (hset 2004 true) Ends.nil
  have e6 := Ends.ite (c := (v.modes.mouse != 0) = true) (hset v.modes.mouse true) Ends.nil
  have e7 := Ends.ite (c := v.modes.mouseSgr = true) (hset 1006 true) Ends.nil
  have e8 := Ends.ite (c := v.modes.focusEvents = true) (hset 1004 true) Ends.nil
  have e9 := Ends.ite (c := v.modes.origin = true) (hset 6 true) Ends.nil
  have e10 := Ends.ite (c := v.modes.insert = true)
    (ends_csiNum 4 0x68 (by decide) (by decide)) Ends.nil
  exact ((((((((e1.append e2).append e3).append e4).append e5).append e6).append
    e7).append e8).append e9).append e10

theorem ends_cursorAnsi (v : Vt) : Ends (cursorAnsi v) := by
  unfold cursorAnsi
  exact Ends.ite (ends_csiNum2 _ _ 0x48 (by decide) (by decide))
    (ends_csiNum2 _ _ 0x48 (by decide) (by decide))

theorem ends_restoreBody (v : Vt) : Ends (restoreBody v) := by
  unfold restoreBody
  exact ((((((((
    (ends_csiNum 0 0x6D (by decide) (by decide)).append
    (ends_csiNum 2 0x4A (by decide) (by decide))).append
    (ends_screensAnsi v)).append
    (ends_regionAnsi v)).append
    (ends_tabsAnsi v)).append
    (ends_savedAnsi v)).append
    (ends_titleAnsi v)).append
    (ends_modesAnsi v)).append
    (ends_charsetAnsi v)).append
    (ends_penSgr v.pen)

/-- **§Replay (parser half).** Feeding a whole restore stream to a fresh
terminal emulator leaves its parser in `ground`: no reattach can wedge a
client mid-sequence, whatever the session's screen, pen, modes, title or
charset state. Proved for every `Vt`, with no hypotheses. -/
theorem ends_restore (v : Vt) : Ends (restore v) := by
  unfold restore
  exact (ends_restoreBody v).append (ends_cursorAnsi v)

/-- The operational form: a fresh emulator fed `restore v` is ready for
the application's next byte. -/
theorem restore_leaves_ground (v : Vt) (cols rows : Nat) :
    (((Vt.init cols rows).feed (restore v)).pstate = .ground) :=
  ends_restore v (Vt.init cols rows) rfl

/-! ### No half-decoded character either

`restore` ends with the cursor's `CSI … H`. Its leading ESC clears any
pending UTF-8 sequence whatever came before, and every byte after it is
below 0xC0 — so none can re-arm one. That is why this needs no reasoning
about the grid repaint's multi-byte encodings: the tail sequence
re-establishes the property regardless of the prefix.
-/

theorem paramBytes_lt_C0 {bs : Bytes} (h : ParamBytes bs) : ∀ b ∈ bs, b < 0xC0 := by
  intro b hb
  obtain ⟨-, h2⟩ := h b hb
  simp only [UInt8.le_iff_toNat_le, show ((0x3F : UInt8)).toNat = 63 from rfl] at h2
  simp only [UInt8.lt_iff_toNat_lt, show ((0xC0 : UInt8)).toNat = 192 from rfl]
  omega

/-- Any complete CSI sequence leaves no pending UTF-8, from any state. -/
theorem u8_zero_after_csi (params : Bytes) (final : UInt8) (hp : ParamBytes params)
    (hf : final ≤ 0x7E) (v : Vt) :
    ((v.feed (csiB ++ params ++ [final])).u8need = 0) := by
  have hshape : (csiB ++ params ++ [final] : Bytes)
      = 0x1B :: 0x5B :: (params ++ [final]) := by simp [csiB]
  rw [hshape, feed_cons, feed_cons]
  refine Zmx.Core.Vt.uz_feed _ _ ?_
    (Zmx.Core.Vt.uz_step 0x5B (by decide) (Zmx.Core.Vt.uz_step_esc v))
  intro b hb
  rcases List.mem_append.mp hb with h | h
  · exact paramBytes_lt_C0 hp b h
  · simp only [List.mem_singleton] at h
    subst h
    simp only [UInt8.le_iff_toNat_le, show ((0x7E : UInt8)).toNat = 126 from rfl] at hf
    simp only [UInt8.lt_iff_toNat_lt, show ((0xC0 : UInt8)).toNat = 192 from rfl]
    omega

/-- **§Replay (parser half, complete).** A fresh emulator fed a whole
restore stream is *quiesced*: parser in `ground`, no half-decoded
character. So a reattaching client is left ready for the application's
next byte, and a checkpoint taken straight after a restore is exact. -/
theorem restore_quiesced (v : Vt) (cols rows : Nat) :
    (((Vt.init cols rows).feed (restore v)).pstate = .ground)
      ∧ (((Vt.init cols rows).feed (restore v)).u8need = 0) := by
  refine ⟨restore_leaves_ground v cols rows, ?_⟩
  -- `restore = restoreBody ++ cursorAnsi`, and `cursorAnsi` is one CSI
  unfold restore
  rw [show ∀ (w : Vt), w.feed (restoreBody v ++ cursorAnsi v)
        = (w.feed (restoreBody v)).feed (cursorAnsi v) from
      fun w => by simp [Vt.feed, List.foldl_append]]
  unfold cursorAnsi
  split
  all_goals
    (unfold csiNum2
     refine u8_zero_after_csi _ 0x48 ?_ (by decide) _
     exact ((paramBytes_digits _).append
       (ParamBytes.cons (by decide) (by decide) ParamBytes.nil)).append
       (paramBytes_digits _))

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
`n` (clamped) — the emitter and the parser are inverse on numbers. -/
theorem csi_digits_value (n : Nat) {v : Vt} {s : CsiState} (hg : v.pstate = .csi s)
    (hcur : s.cur = 0) :
    ∃ s', (v.feed (digits n)).pstate = .csi s' ∧ s'.cur = min n 65535
      ∧ s'.haveCur = true ∧ s'.params = s.params := by
  have hne : digits n ≠ [] := by
    rw [digits]
    split <;> simp
  refine ⟨_, csi_digits_feed (digits n) hg (digits_are_digits n) hne, ?_, rfl, rfl⟩
  show accDigits s.cur (digits n) = min n 65535
  rw [hcur]
  exact accDigits_digits n

end Zmx.Core.Render
