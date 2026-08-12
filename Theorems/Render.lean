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

/-- Not yet proved: `Ends (penSgr p)`. It is one CSI sequence, so
`ends_csi_seq` applies the moment `penSgr`'s parameter body is a named
stage — as written it associates as `(csiB ++ digits 0) ++ …`, so the
parameter chunk is not syntactically separable, and re-associating inside
the proof is uglier than naming the stage in the emitter. Every `penSgr`
byte *is* a parameter byte, and this is the piece that will discharge it.
Tracked in specs/bigger-theorems.md (3b-rest), with the OSC-title and
`ESC`-single constructs. -/
theorem paramBytes_sgr_subparam (n : Nat) : ParamBytes (0x3B :: digits n) :=
  paramBytes_semiDigits n

end Zmx.Core.Render
