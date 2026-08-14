import Zmx.Core.Render
import Theorems.Vt
/-! # §Replay, stage 3b — a restore stream leaves the parser in ground

The §Replay target (specs/grid-fidelity.md; the parser half was closed
in specs/archive/bigger-theorems.md) is
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
specs/archive/bigger-theorems.md. -/
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

/-- **The shape all three stream layers share.**

`Ends`, `Quiet` and `Keeps` are three predicates on a byte string, each closed
under concatenation, and each needing the same five derived combinators. Written
out per layer that is fifteen proofs of five facts.

Everything derived follows from `nil` and `append` alone, so those two are the
bundle and the rest are generic: a fourth layer costs one instance instead of five
proofs. That is the reason to do it now — the decision recorded in SCRATCHPAD was
to leave the duplication alone "unless a third layer wants the same skeleton", and
`Keeps` is that third layer.

The boundary is deliberate: only the *combinators* generalize, and `Keeps` is what
shows why. `Ends.text` and `Quiet.text` both say an ESC-free run is harmless, but
the same statement for `Keeps` is **false** — printable bytes are exactly what
writes cells. A shared instance ladder would have had to weaken to accommodate
that, which is the trap the earlier sketch hit from the other direction
(`modesAnsi`'s DECOM branch is hypothesis-free for `Ends` and hypothesis-bearing
for `Quiet`). -/
structure StreamPred (P : Bytes → Prop) : Prop where
  nil : P []
  append : ∀ {a b : Bytes}, P a → P b → P (a ++ b)

namespace StreamPred

theorem append3 {P : Bytes → Prop} (hP : StreamPred P) {a b c : Bytes}
    (ha : P a) (hb : P b) (hc : P c) : P (a ++ b ++ c) :=
  hP.append (hP.append ha hb) hc

theorem append4 {P : Bytes → Prop} (hP : StreamPred P) {a b c d : Bytes}
    (ha : P a) (hb : P b) (hc : P c) (hd : P d) : P (a ++ b ++ c ++ d) :=
  hP.append (hP.append3 ha hb hc) hd

/-- Both branches, with the condition available — a guarded emit is what proves a
mode number is not the one that would break the claim, so the branch hypotheses
have to be able to use it (`Quiet`'s DECOM branch, `Keeps`'s screen-switch
branch). -/
theorem ite {P : Bytes → Prop} (_hP : StreamPred P) {c : Prop} [Decidable c]
    {a b : Bytes} (ha : c → P a) (hb : ¬c → P b) : P (if c then a else b) := by
  by_cases h : c
  · rw [if_pos h]; exact ha h
  · rw [if_neg h]; exact hb h

theorem flatten {P : Bytes → Prop} (hP : StreamPred P) {l : List Bytes}
    (h : ∀ bs ∈ l, P bs) : P l.flatten := by
  induction l with
  | nil => exact hP.nil
  | cons a as ih =>
    rw [List.flatten_cons]
    exact hP.append (h a (by simp)) (ih (fun bs hbs => h bs (by simp [hbs])))

theorem flatMap {P : Bytes → Prop} (hP : StreamPred P) {α : Type} {f : α → Bytes}
    {l : List α} (h : ∀ a, P (f a)) : P (l.flatMap f) := by
  induction l with
  | nil => exact hP.nil
  | cons a as ih =>
    rw [List.flatMap_cons]
    exact hP.append (h a) ih

end StreamPred

theorem Ends.streamPred : StreamPred Ends := ⟨Ends.nil, fun ha hb => Ends.append ha hb⟩

/-! The five derived combinators keep their own names, so no downstream proof
changes — the conversion rule from the frames pass. -/

theorem Ends.append3 {a b c : Bytes} (ha : Ends a) (hb : Ends b) (hc : Ends c) :
    Ends (a ++ b ++ c) := Ends.streamPred.append3 ha hb hc

theorem Ends.append4 {a b c d : Bytes} (ha : Ends a) (hb : Ends b) (hc : Ends c)
    (hd : Ends d) : Ends (a ++ b ++ c ++ d) := Ends.streamPred.append4 ha hb hc hd

/-- An `if` over two `Ends` pieces is `Ends` (restore is full of conditional
fragments). Unconditional in both branches, unlike the `Quiet`/`Keeps` forms. -/
theorem Ends.ite {c : Prop} [Decidable c] {a b : Bytes}
    (ha : Ends a) (hb : Ends b) : Ends (if c then a else b) :=
  Ends.streamPred.ite (fun _ => ha) (fun _ => hb)

theorem Ends.flatten {l : List Bytes} (h : ∀ bs ∈ l, Ends bs) : Ends l.flatten :=
  Ends.streamPred.flatten h

theorem Ends.flatMap {α : Type} {f : α → Bytes} {l : List α}
    (h : ∀ a, Ends (f a)) : Ends (l.flatMap f) := Ends.streamPred.flatMap h

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

/-- The six pre-final guards in `stepCsi`, all false below `0x40`. Factored out
because two layers need them: the parser claim (`csi_final_step`, just below) and
the state claim (`csi_final_step_eq`, which needs `step_of_csi_quiet` and so lives
with the grid layer at the end of this file). Re-deriving UInt8 comparisons at
each use is what made a first attempt at the grid layer unpleasant. -/
theorem csi_final_guards (b : UInt8) (h1 : 0x40 ≤ b) (h2 : b ≤ 0x7E) :
    (b ≥ 0x30 && b ≤ 0x39) = false ∧ (b == 0x3B) = false ∧ (b == 0x3A) = false
      ∧ (b ≥ 0x3C && b ≤ 0x3F) = false ∧ (b ≥ 0x20 && b ≤ 0x2F) = false
      ∧ (b ≥ 0x40 && b ≤ 0x7E) = true := by
  obtain ⟨hn1, hn2⟩ := u8_bounds h1 h2
  simp only [show ((0x40 : UInt8)).toNat = 64 from rfl,
    show ((0x7E : UInt8)).toNat = 126 from rfl] at hn1 hn2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, UInt8.le_iff_toNat_le,
      show ((0x39 : UInt8)).toNat = 57 from rfl]
    right; omega
  · simp only [beq_eq_false_iff_ne, ne_eq]
    intro he
    rw [he] at hn1
    simp only [show ((0x3B : UInt8)).toNat = 59 from rfl] at hn1
    omega
  · simp only [beq_eq_false_iff_ne, ne_eq]
    intro he
    rw [he] at hn1
    simp only [show ((0x3A : UInt8)).toNat = 58 from rfl] at hn1
    omega
  · simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, UInt8.le_iff_toNat_le,
      show ((0x3F : UInt8)).toNat = 63 from rfl]
    right; omega
  · simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, UInt8.le_iff_toNat_le,
      show ((0x2F : UInt8)).toNat = 47 from rfl]
    right; omega
  · simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨h1, h2⟩

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
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := csi_final_guards b h1 h2
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

/-- Bytes legal inside a CSI *parameter* string: digits and the `:`/`;`
separators. The `<=>?` private markers are deliberately **excluded** — a
marker is what decides whether a sequence can be DECOM, so it is
structure, not a parameter (`ends_csi_priv_seq` and `Quiet` below both
turn on that distinction). -/
def ParamBytes (bs : Bytes) : Prop := ∀ b ∈ bs, 0x30 ≤ b ∧ b ≤ 0x3B

/-- The parser's own bound is the looser one (it accepts markers mid-run),
so the walk lemmas are fed through this. -/
theorem paramBytes_le_3F {bs : Bytes} (h : ParamBytes bs) :
    ∀ b ∈ bs, 0x30 ≤ b ∧ b ≤ 0x3F := by
  intro b hb
  obtain ⟨h1, h2⟩ := h b hb
  refine ⟨h1, ?_⟩
  simp only [UInt8.le_iff_toNat_le, show ((0x3B : UInt8)).toNat = 59 from rfl,
    show ((0x3F : UInt8)).toNat = 63 from rfl] at h2 ⊢
  omega

theorem ParamBytes.nil : ParamBytes [] := by intro b hb; simp at hb

theorem ParamBytes.append {a b : Bytes} (ha : ParamBytes a) (hb : ParamBytes b) :
    ParamBytes (a ++ b) := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact ha x h
  · exact hb x h

theorem ParamBytes.cons {x : UInt8} {bs : Bytes} (h1 : 0x30 ≤ x) (h2 : x ≤ 0x3B)
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
    show ((0x3B : UInt8)).toNat = 59 from rfl] at hd2 ⊢
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
  obtain ⟨s', hs'⟩ := csi_param_feed params hb (paramBytes_le_3F hp)
  rw [show (((v.step 0x1B).step 0x5B).feed params).feed [final]
        = ((((v.step 0x1B).step 0x5B).feed params).step final) from rfl]
  exact csi_final_step final hs' h1 h2

/-- `CSI ? <params> <final>` — the private-mode shape, the one construct
with a marker. Split out from `ends_csi_seq` because `ParamBytes` excludes
the marker byte: here it is consumed as its own step, which is also what
lets `Quiet` reason about *which* private mode a sequence sets. -/
theorem ends_csi_priv_seq (params : Bytes) (final : UInt8) (hp : ParamBytes params)
    (h1 : 0x40 ≤ final) (h2 : final ≤ 0x7E) :
    Ends (csiB ++ (0x3F :: params) ++ [final]) := by
  intro v hg
  show (v.feed ([0x1B, 0x5B] ++ (0x3F :: params) ++ [final])).pstate = .ground
  rw [show ([0x1B, 0x5B] ++ (0x3F :: params) ++ [final] : Bytes)
        = 0x1B :: 0x5B :: 0x3F :: (params ++ [final]) from rfl]
  rw [feed_cons, feed_cons, feed_cons]
  obtain ⟨sm, hsm⟩ :=
    csi_param_step 0x3F (csi_open_step (esc_step hg)) (by decide) (by decide)
  rw [show ∀ (w : Vt), w.feed (params ++ [final]) = (w.feed params).feed [final] from
    fun w => by simp [Vt.feed, List.foldl_append]]
  obtain ⟨s', hs'⟩ := csi_param_feed params hsm (paramBytes_le_3F hp)
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
  exact ends_csi_priv_seq _ final (paramBytes_digits n) h1 h2

/-- Not yet proved: the composition. See below. -/
theorem paramBytes_sgr_subparam (n : Nat) : ParamBytes (0x3B :: digits n) :=
  paramBytes_semiDigits n

/-! ### SGR pens

A pen is up to three sequences (attributes, foreground, background) — see
`penSgr`'s note on the parameter cap. Each is a plain CSI, so the `Ends`
and `Quiet` facts are one `ends_csi_seq` each; what needs proving is that
`joinSemi` emits only parameter bytes. -/

theorem paramBytes_joinSemi : ∀ (ns : List Nat), ParamBytes (joinSemi ns)
  | [] => ParamBytes.nil
  | [n] => paramBytes_digits n
  | n :: m :: ns => by
    rw [show joinSemi (n :: m :: ns) = digits n ++ [0x3B] ++ joinSemi (m :: ns) from rfl]
    exact ((paramBytes_digits n).append
      (ParamBytes.cons (by decide) (by decide) ParamBytes.nil)).append
      (paramBytes_joinSemi (m :: ns))

/-! ### The parameter cap

The parser honours 16 parameters and silently drops any sequence carrying
more (`csiPush` sets `ignore`, `csiDispatch` returns early). A pen used to
be emitted as one 18-parameter sequence and came back blank; these bounds
are the invariant that replaced the bug, and what a future attribute or
colour form has to keep true. -/

private theorem ite_len (c : Prop) [Decidable c] (n : Nat) :
    (if c then [n] else []).length ≤ 1 := by
  by_cases h : c <;> simp [h]

theorem penAttrCodes_length (p : Pen) : (penAttrCodes p).length ≤ 8 := by
  unfold penAttrCodes
  simp only [List.length_cons, List.length_append]
  have h1 := ite_len (p.bold = true) 1
  have h2 := ite_len (p.dim = true) 2
  have h3 := ite_len (p.italic = true) 3
  have h4 := ite_len (p.underline = true) 4
  have h5 := ite_len (p.blink = true) 5
  have h6 := ite_len (p.reverse = true) 7
  have h7 := ite_len (p.strike = true) 9
  omega

theorem colorCodes_length (c : Color) (isFg : Bool) : (colorCodes c isFg).length ≤ 5 := by
  unfold colorCodes
  cases c <;> dsimp only
  · simp
  · repeat' split
    all_goals simp
  · simp

/-- **Every SGR a restore emits stays under the parser's cap**, with room to
spare: attributes ≤ 8, each colour ≤ 5, where the old single sequence
reached 18. Stated as a theorem rather than trusted to the fixtures,
because the failure is silent — an over-long SGR is not mis-applied, it is
dropped whole. -/
theorem penSgr_under_cap (p : Pen) :
    (penAttrCodes p).length ≤ 16 ∧ (colorCodes p.fg true).length ≤ 16
      ∧ (colorCodes p.bg false).length ≤ 16 :=
  ⟨by have := penAttrCodes_length p; omega,
   by have := colorCodes_length p.fg true; omega,
   by have := colorCodes_length p.bg false; omega⟩

theorem ends_sgrOf (codes : List Nat) : Ends (sgrOf codes) :=
  ends_csi_seq _ 0x6D (paramBytes_joinSemi codes) (by decide) (by decide)

theorem ends_sgrColorSeq (c : Color) (isFg : Bool) : Ends (sgrColorSeq c isFg) := by
  unfold sgrColorSeq
  split
  · exact Ends.nil
  · exact ends_sgrOf _

/-- An SGR pen is `Ends`, for any pen (16-colour, 256-colour, truecolour). -/
theorem ends_penSgr (p : Pen) : Ends (penSgr p) := by
  unfold penSgr
  exact ((ends_sgrOf _).append (ends_sgrColorSeq _ _)).append (ends_sgrColorSeq _ _)

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

-- `invariant_foldl` now lives in `Theorems/Vt.lean`, shared with the four
-- specializations there; this file's uses resolve to it through `open`.

theorem ends_utf8s (cs : List Char) : Ends (utf8s cs) :=
  Ends.text (utf8s_no_esc cs)

theorem ends_utf8_safe (ch : Char) : Ends (utf8 (safeChar ch)) :=
  Ends.text (fun b hb => by
    obtain ⟨hge, -⟩ := utf8_no_ctl (safeChar ch) (safeChar_ge ch).1 (safeChar_ge ch).2 b hb
    intro he; rw [he] at hge; exact absurd hge (by decide))

theorem ends_cellText (c : Cell) : Ends (cellText c) := by
  unfold cellText
  exact (Ends.text (fun b hb => by
    obtain ⟨hge, -⟩ := utf8_no_ctl (safeChar c.base) (safeChar_ge c.base).1
      (safeChar_ge c.base).2 b hb
    intro he; rw [he] at hge; exact absurd hge (by decide))).append (ends_utf8s c.marks)

theorem ends_rowAnsi (row : Row) (p : Pen) : Ends (rowAnsi row p).1 := by
  unfold rowAnsi
  rw [← Array.foldl_toList]
  refine invariant_foldl (fun acc => Ends acc.1) _ ?_ row.toList ([], p, 0) Ends.nil
  intro acc c hacc
  dsimp only
  -- the marked-wide branch is `glyph CHA marks CHA`, four pieces
  repeat' split
  all_goals first
    | exact hacc.append (ends_utf8s c.marks)
    | exact hacc.append (ends_cellText c)
    | exact (hacc.append (ends_penSgr c.pen)).append (ends_cellText c)
    | exact hacc.append ((((ends_utf8_safe c.base).append
        (ends_csiNum _ 0x47 (by decide) (by decide))).append
        (ends_utf8s c.marks)).append (ends_csiNum _ 0x47 (by decide) (by decide)))
    | exact (hacc.append (ends_penSgr c.pen)).append ((((ends_utf8_safe c.base).append
        (ends_csiNum _ 0x47 (by decide) (by decide))).append
        (ends_utf8s c.marks)).append (ends_csiNum _ 0x47 (by decide) (by decide)))

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
  exact (ends_csiNum 0 0x6D (by decide) (by decide)).append
    (hhome.append (ends_joinCRLF _ hrows))

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
  have e1 : Ends (csiPriv 7 (if v.modes.wrap then 0x68 else 0x6C)) := hset 7 v.modes.wrap
  have e2 := Ends.ite (c := v.modes.appCursor = true) (hset 1 true) Ends.nil
  have e3 := Ends.ite (c := v.modes.appKeypad = true) (ends_escSeq 0x3D (by decide)) Ends.nil
  have e4 := Ends.ite (c := v.modes.cursorVisible = true) Ends.nil (hset 25 false)
  have e5 := Ends.ite (c := v.modes.bracketedPaste = true) (hset 2004 true) Ends.nil
  have e6 := Ends.ite (c := (v.modes.mouse == 1000 || v.modes.mouse == 1002
      || v.modes.mouse == 1003) = true) (hset v.modes.mouse true) Ends.nil
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
  simp only [UInt8.le_iff_toNat_le, show ((0x3B : UInt8)).toNat = 59 from rfl] at h2
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

theorem quiet_escSeq (b : UInt8) (hb : b = 0x37 ∨ b = 0x3D ∨ b = 0x48) :
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

theorem quiet_screensAnsi (v : Vt) : Quiet (screensAnsi v) := by
  unfold screensAnsi
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
  refine Quiet.ite (fun _ => Quiet.nil) (fun _ => ?_)
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
  exact Quiet.ite (fun _ => Quiet.nil) (fun _ => quiet_osc _)

/-- The mode replay is where the hypothesis lands. Every private mode the
emitter names is a literal ≠ 6 except two: the mouse mode, which the
emitter *guards* (mode 6 is not a mouse mode — see `modesAnsi`), and DECOM
itself, which is emitted only when the session had it on. So a session
with DECOM off replays with DECOM off. -/
theorem quiet_modesAnsi (v : Vt) (ho : v.modes.origin = false) : Quiet (modesAnsi v) := by
  unfold modesAnsi
  dsimp only
  have hset : ∀ (n : Nat) (on : Bool), n ≠ 6 →
      Quiet (csiPriv n (if on then 0x68 else 0x6C)) := by
    intro n on hn
    by_cases h : on <;> simp only [h, if_true]
    · exact quiet_csiPriv n 0x68 hn (by decide) (by decide)
    · exact quiet_csiPriv n 0x6C hn (by decide) (by decide)
  have e1 : Quiet (csiPriv 7 (if v.modes.wrap then 0x68 else 0x6C)) :=
    hset 7 v.modes.wrap (by decide)
  have e2 := Quiet.ite (c := v.modes.appCursor = true)
    (fun _ => hset 1 true (by decide)) (fun _ => Quiet.nil)
  have e3 := Quiet.ite (c := v.modes.appKeypad = true)
    (fun _ => quiet_escSeq 0x3D (by decide)) (fun _ => Quiet.nil)
  have e4 := Quiet.ite (c := v.modes.cursorVisible = true)
    (fun _ => Quiet.nil) (fun _ => hset 25 false (by decide))
  have e5 := Quiet.ite (c := v.modes.bracketedPaste = true)
    (fun _ => hset 2004 true (by decide)) (fun _ => Quiet.nil)
  -- the guarded emit: the allowlist names three modes, none of them DECOM
  have e6 := Quiet.ite (c := (v.modes.mouse == 1000 || v.modes.mouse == 1002
      || v.modes.mouse == 1003) = true)
    (fun h => hset v.modes.mouse true (by
      simp only [Bool.or_eq_true, beq_iff_eq] at h
      omega)) (fun _ => Quiet.nil)
  have e7 := Quiet.ite (c := v.modes.mouseSgr = true)
    (fun _ => hset 1006 true (by decide)) (fun _ => Quiet.nil)
  have e8 := Quiet.ite (c := v.modes.focusEvents = true)
    (fun _ => hset 1004 true (by decide)) (fun _ => Quiet.nil)
  -- DECOM itself: the hypothesis is consumed exactly here, at the one emit
  -- that would turn it on
  have e9 : Quiet (if v.modes.origin = true then csiPriv 6 (if true = true then 0x68 else 0x6C)
      else []) :=
    Quiet.ite (fun h => absurd (ho.symm.trans h) (by simp)) (fun _ => Quiet.nil)
  have e10 := Quiet.ite (c := v.modes.insert = true)
    (fun _ => quiet_csiNum 4 0x68 (by decide) (by decide)) (fun _ => Quiet.nil)
  exact ((((((((e1.append e2).append e3).append e4).append e5).append e6).append
    e7).append e8).append e9).append e10

/-- **§Replay: DECOM survives a restore.** Every stage of a restore body
leaves the parser ground and DECOM off, given the session had DECOM off —
which is what lets the final `CUP` be read as an absolute address. -/
theorem quiet_restoreBody (v : Vt) (ho : v.modes.origin = false) : Quiet (restoreBody v) := by
  unfold restoreBody
  exact ((((((((
    (quiet_csiNum 0 0x6D (by decide) (by decide)).append
    (quiet_csiNum 2 0x4A (by decide) (by decide))).append
    (quiet_screensAnsi v)).append
    (quiet_regionAnsi v)).append
    (quiet_tabsAnsi v)).append
    (quiet_savedAnsi v)).append
    (quiet_titleAnsi v)).append
    (quiet_modesAnsi v ho)).append
    (quiet_charsetAnsi v)).append
    (quiet_penSgr v.pen)

/-! ## §Replay stage 3d — the painted cells come back

The strategy that makes this tractable: reduce the byte stream to *emulator
operations* first — one lemma per emitted construct saying "feeding these
bytes **is** this `Vt` function" — and only then argue about fidelity, with
no bytes left in the argument. `utf8_feed` below is the load-bearing one: it
turns a repaint into a chain of `Vt.print`s.
-/

private theorem u8_ofNat_toNat (m : Nat) (h : m < 256) : (UInt8.ofNat m).toNat = m := by
  simp [UInt8.toNat_ofNat', Nat.mod_eq_of_lt h]

/-- Every `Char` is at most the largest scalar value, so `utf8`'s clamp is
the identity — the reason that clamp costs nothing. -/
theorem char_le (c : Char) : c.toNat ≤ 0x10FFFF := by
  have h := c.valid
  unfold UInt32.isValidChar Nat.isValidChar at h
  simp only [Char.toNat]
  omega

/-- A codepoint that came from a `Char` is always valid, so `acceptChar`
never falls back to U+FFFD. -/
theorem acceptChar_toNat (v : Vt) (c : Char) : v.acceptChar c.toNat = v.print c := by
  unfold Vt.acceptChar
  rw [if_pos (show c.toNat.isValidChar from c.valid), Char.ofNat_toNat]

/-- With nothing pending, `step` is `stepGround`: `abortUtf8` is the
identity. -/
theorem step_of_ground_quiet {v : Vt} (b : UInt8) (hg : v.pstate = .ground)
    (hu : v.u8need = 0) : v.step b = v.stepGround b := by
  have ha : v.abortUtf8 b = v := by
    unfold Vt.abortUtf8
    rw [if_neg (by simp [hu])]
  unfold Vt.step
  dsimp only
  rw [ha, hg]

/-! #### Byte comparisons, once

`stepGround` is an eight-way ladder of byte comparisons. Rather than repeat
the `UInt8`-to-`Nat` conversion at each rung of each case below, these two
lemmas do it once; every guard then reduces to arithmetic `omega` can see.
-/

private theorem lt_lit {m : Nat} (k : Nat) (hm : m < 256) (hk : (UInt8.ofNat k).toNat = k) :
    ((UInt8.ofNat m) < (UInt8.ofNat k)) ↔ m < k := by
  simp only [UInt8.lt_iff_toNat_lt, u8_ofNat_toNat m hm, hk]

private theorem ne_lit {m : Nat} (k : Nat) (hm : m < 256) (hk : (UInt8.ofNat k).toNat = k)
    (h : m ≠ k) : ¬((UInt8.ofNat m == (UInt8.ofNat k)) = true) := by
  simp only [beq_iff_eq]
  intro he
  have := congrArg UInt8.toNat he
  rw [u8_ofNat_toNat m hm, hk] at this
  exact h this

/-- An ASCII byte ≥ 0x20 prints. -/
theorem step_ascii {v : Vt} {m : Nat} (hg : v.pstate = .ground) (hu : v.u8need = 0)
    (h20 : 0x20 ≤ m) (hlt : m < 0x80) :
    v.step (UInt8.ofNat m) = v.acceptChar m := by
  have hb : (UInt8.ofNat m).toNat = m := u8_ofNat_toNat m (by omega)
  have c1 : ¬((UInt8.ofNat m == (0x1B : UInt8)) = true) :=
    ne_lit 0x1B (by omega) rfl (by omega)
  have c2 : ¬((UInt8.ofNat m) < (0x20 : UInt8)) := by
    rw [show ((0x20 : UInt8)) = UInt8.ofNat 0x20 from rfl, lt_lit 0x20 (by omega) rfl]
    omega
  have c3 : (UInt8.ofNat m) < (0x80 : UInt8) := by
    rw [show ((0x80 : UInt8)) = UInt8.ofNat 0x80 from rfl, lt_lit 0x80 (by omega) rfl]
    omega
  rw [step_of_ground_quiet _ hg hu]
  unfold Vt.stepGround
  rw [if_neg c1, if_neg c2, if_pos c3, hb]

/-- The three lead bytes, each announcing how many continuations follow.
Stated separately rather than parameterised: they take different rungs of
`stepGround`'s ladder, so a shared statement would only move the case
split somewhere less readable. -/
theorem step_lead2 {v : Vt} {m : Nat} (hg : v.pstate = .ground) (hu : v.u8need = 0)
    (hm : m < 32) :
    v.step (UInt8.ofNat (0xC0 + m)) = { v with u8need := 1, u8acc := m } := by
  have hb : (UInt8.ofNat (0xC0 + m)).toNat = 0xC0 + m := u8_ofNat_toNat _ (by omega)
  have c1 : ¬((UInt8.ofNat (0xC0 + m) == (0x1B : UInt8)) = true) :=
    ne_lit 0x1B (by omega) rfl (by omega)
  have c2 : ¬((UInt8.ofNat (0xC0 + m)) < (0x20 : UInt8)) := by
    rw [show ((0x20 : UInt8)) = UInt8.ofNat 0x20 from rfl, lt_lit 0x20 (by omega) rfl]
    omega
  have c3 : ¬((UInt8.ofNat (0xC0 + m)) < (0x80 : UInt8)) := by
    rw [show ((0x80 : UInt8)) = UInt8.ofNat 0x80 from rfl, lt_lit 0x80 (by omega) rfl]
    omega
  have c4 : ¬((UInt8.ofNat (0xC0 + m)) < (0xC0 : UInt8)) := by
    rw [show ((0xC0 : UInt8)) = UInt8.ofNat 0xC0 from rfl, lt_lit 0xC0 (by omega) rfl]
    omega
  have c5 : (UInt8.ofNat (0xC0 + m)) < (0xE0 : UInt8) := by
    rw [show ((0xE0 : UInt8)) = UInt8.ofNat 0xE0 from rfl, lt_lit 0xE0 (by omega) rfl]
    omega
  have hval : 0xC0 + m - 0xC0 = m := by omega
  rw [step_of_ground_quiet _ hg hu]
  unfold Vt.stepGround
  rw [if_neg c1, if_neg c2, if_neg c3, if_neg c4, if_pos c5, hb, hval]

theorem step_lead3 {v : Vt} {m : Nat} (hg : v.pstate = .ground) (hu : v.u8need = 0)
    (hm : m < 16) :
    v.step (UInt8.ofNat (0xE0 + m)) = { v with u8need := 2, u8acc := m } := by
  have hb : (UInt8.ofNat (0xE0 + m)).toNat = 0xE0 + m := u8_ofNat_toNat _ (by omega)
  have c1 : ¬((UInt8.ofNat (0xE0 + m) == (0x1B : UInt8)) = true) :=
    ne_lit 0x1B (by omega) rfl (by omega)
  have c2 : ¬((UInt8.ofNat (0xE0 + m)) < (0x20 : UInt8)) := by
    rw [show ((0x20 : UInt8)) = UInt8.ofNat 0x20 from rfl, lt_lit 0x20 (by omega) rfl]
    omega
  have c3 : ¬((UInt8.ofNat (0xE0 + m)) < (0x80 : UInt8)) := by
    rw [show ((0x80 : UInt8)) = UInt8.ofNat 0x80 from rfl, lt_lit 0x80 (by omega) rfl]
    omega
  have c4 : ¬((UInt8.ofNat (0xE0 + m)) < (0xC0 : UInt8)) := by
    rw [show ((0xC0 : UInt8)) = UInt8.ofNat 0xC0 from rfl, lt_lit 0xC0 (by omega) rfl]
    omega
  have c5 : ¬((UInt8.ofNat (0xE0 + m)) < (0xE0 : UInt8)) := by
    rw [show ((0xE0 : UInt8)) = UInt8.ofNat 0xE0 from rfl, lt_lit 0xE0 (by omega) rfl]
    omega
  have c6 : (UInt8.ofNat (0xE0 + m)) < (0xF0 : UInt8) := by
    rw [show ((0xF0 : UInt8)) = UInt8.ofNat 0xF0 from rfl, lt_lit 0xF0 (by omega) rfl]
    omega
  have hval : 0xE0 + m - 0xE0 = m := by omega
  rw [step_of_ground_quiet _ hg hu]
  unfold Vt.stepGround
  rw [if_neg c1, if_neg c2, if_neg c3, if_neg c4, if_neg c5, if_pos c6, hb, hval]

theorem step_lead4 {v : Vt} {m : Nat} (hg : v.pstate = .ground) (hu : v.u8need = 0)
    (hm : m < 8) :
    v.step (UInt8.ofNat (0xF0 + m)) = { v with u8need := 3, u8acc := m } := by
  have hb : (UInt8.ofNat (0xF0 + m)).toNat = 0xF0 + m := u8_ofNat_toNat _ (by omega)
  have c1 : ¬((UInt8.ofNat (0xF0 + m) == (0x1B : UInt8)) = true) :=
    ne_lit 0x1B (by omega) rfl (by omega)
  have c2 : ¬((UInt8.ofNat (0xF0 + m)) < (0x20 : UInt8)) := by
    rw [show ((0x20 : UInt8)) = UInt8.ofNat 0x20 from rfl, lt_lit 0x20 (by omega) rfl]
    omega
  have c3 : ¬((UInt8.ofNat (0xF0 + m)) < (0x80 : UInt8)) := by
    rw [show ((0x80 : UInt8)) = UInt8.ofNat 0x80 from rfl, lt_lit 0x80 (by omega) rfl]
    omega
  have c4 : ¬((UInt8.ofNat (0xF0 + m)) < (0xC0 : UInt8)) := by
    rw [show ((0xC0 : UInt8)) = UInt8.ofNat 0xC0 from rfl, lt_lit 0xC0 (by omega) rfl]
    omega
  have c5 : ¬((UInt8.ofNat (0xF0 + m)) < (0xE0 : UInt8)) := by
    rw [show ((0xE0 : UInt8)) = UInt8.ofNat 0xE0 from rfl, lt_lit 0xE0 (by omega) rfl]
    omega
  have c6 : ¬((UInt8.ofNat (0xF0 + m)) < (0xF0 : UInt8)) := by
    rw [show ((0xF0 : UInt8)) = UInt8.ofNat 0xF0 from rfl, lt_lit 0xF0 (by omega) rfl]
    omega
  have c7 : (UInt8.ofNat (0xF0 + m)) < (0xF8 : UInt8) := by
    rw [show ((0xF8 : UInt8)) = UInt8.ofNat 0xF8 from rfl, lt_lit 0xF8 (by omega) rfl]
    omega
  have hval : 0xF0 + m - 0xF0 = m := by omega
  rw [step_of_ground_quiet _ hg hu]
  unfold Vt.stepGround
  rw [if_neg c1, if_neg c2, if_neg c3, if_neg c4, if_neg c5, if_neg c6, if_pos c7, hb, hval]

/-- A continuation byte never aborts a sequence — that is what makes the
`abortUtf8` guard invisible to a well-formed encoding. -/
private theorem abortUtf8_cont (v : Vt) {m : Nat} (hm : m < 64) :
    v.abortUtf8 (UInt8.ofNat (0x80 + m)) = v := by
  have h1 : ¬((UInt8.ofNat (0x80 + m)) < (0x80 : UInt8)) := by
    rw [show ((0x80 : UInt8)) = UInt8.ofNat 0x80 from rfl, lt_lit 0x80 (by omega) rfl]
    omega
  have h2 : ¬((0xC0 : UInt8) ≤ (UInt8.ofNat (0x80 + m))) := by
    simp only [UInt8.le_iff_toNat_le, u8_ofNat_toNat _ (show 0x80 + m < 256 by omega),
      show ((0xC0 : UInt8)).toNat = 192 from rfl]
    omega
  unfold Vt.abortUtf8
  split
  · rename_i hc
    exfalso
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hc
    rcases hc.2 with h | h
    · exact h1 h
    · exact h2 h
  · rfl

/-- A continuation byte reaches \`stepGround\` whatever is pending: unlike
\`step_of_ground_quiet\` this needs no \`u8need = 0\`, because a continuation
byte is exactly the byte \`abortUtf8\` lets through. Stated as its own lemma
so the \`pstate\` rewrite cannot touch the callers' right-hand sides. -/
private theorem step_cont_bridge {v : Vt} {m : Nat} (hg : v.pstate = .ground) (hm : m < 64) :
    v.step (UInt8.ofNat (0x80 + m)) = v.stepGround (UInt8.ofNat (0x80 + m)) := by
  unfold Vt.step
  dsimp only
  rw [abortUtf8_cont v hm, hg]

/-- The four guards a continuation byte passes on its way to the
accumulator branch, proved once for both continuation cases. -/
private theorem cont_guards {m : Nat} (hm : m < 64) :
    ¬((UInt8.ofNat (0x80 + m) == (0x1B : UInt8)) = true)
      ∧ ¬((UInt8.ofNat (0x80 + m)) < (0x20 : UInt8))
      ∧ ¬((UInt8.ofNat (0x80 + m)) < (0x80 : UInt8))
      ∧ ((UInt8.ofNat (0x80 + m)) < (0xC0 : UInt8))
      ∧ (UInt8.ofNat (0x80 + m)).toNat = 0x80 + m := by
  refine ⟨ne_lit 0x1B (by omega) rfl (by omega), ?_, ?_, ?_,
    u8_ofNat_toNat _ (by omega)⟩
  · rw [show ((0x20 : UInt8)) = UInt8.ofNat 0x20 from rfl, lt_lit 0x20 (by omega) rfl]
    omega
  · rw [show ((0x80 : UInt8)) = UInt8.ofNat 0x80 from rfl, lt_lit 0x80 (by omega) rfl]
    omega
  · rw [show ((0xC0 : UInt8)) = UInt8.ofNat 0xC0 from rfl, lt_lit 0xC0 (by omega) rfl]
    omega

/-- A continuation byte with more to come: folds six bits in. -/
theorem step_cont_more {v : Vt} {k acc m : Nat} (hg : v.pstate = .ground)
    (hu : v.u8need = k + 2) (hacc : v.u8acc = acc) (hm : m < 64)
    (hb2 : acc * 64 + m ≤ 2097151) :
    v.step (UInt8.ofNat (0x80 + m)) = { v with u8need := k + 1, u8acc := acc * 64 + m } := by
  obtain ⟨c1, c2, c3, c4, hb⟩ := cont_guards hm
  have e0 : ¬((v.u8need == 0) = true) := by simp only [hu, beq_iff_eq]; omega
  have e1 : ¬((v.u8need == 1) = true) := by simp only [hu, beq_iff_eq]; omega
  have hval : 0x80 + m - 0x80 = m := by omega
  have hmin : min (acc * 64 + m) 2097151 = acc * 64 + m := by omega
  have hneed : v.u8need - 1 = k + 1 := by omega
  rw [step_cont_bridge hg hm]
  unfold Vt.stepGround
  rw [if_neg c1, if_neg c2, if_neg c3, if_pos c4, if_neg e0]
  dsimp only
  rw [hb, hval, hacc, hmin, if_neg e1, hneed]

/-- The last continuation byte: the codepoint is complete, so it prints. -/
theorem step_cont_last {v : Vt} {acc m : Nat} (hg : v.pstate = .ground)
    (hu : v.u8need = 1) (hacc : v.u8acc = acc) (hm : m < 64)
    (hb2 : acc * 64 + m ≤ 2097151) :
    v.step (UInt8.ofNat (0x80 + m))
      = ({ v with u8need := 0, u8acc := 0 }).acceptChar (acc * 64 + m) := by
  obtain ⟨c1, c2, c3, c4, hb⟩ := cont_guards hm
  have e0 : ¬((v.u8need == 0) = true) := by simp only [hu, beq_iff_eq]; omega
  have e1 : ((v.u8need == 1) = true) := by simp only [hu, beq_iff_eq]
  have hval : 0x80 + m - 0x80 = m := by omega
  have hmin : min (acc * 64 + m) 2097151 = acc * 64 + m := by omega
  rw [step_cont_bridge hg hm]
  unfold Vt.stepGround
  rw [if_neg c1, if_neg c2, if_neg c3, if_pos c4, if_neg e0]
  dsimp only
  rw [hb, hval, hacc, hmin, if_pos e1]

/-- Collapsing the nested `u8need`/`u8acc` writes that a completed sequence
leaves behind: from a quiet start, decoding one codepoint returns the
accumulator to exactly where it was. -/
private theorem reset_u8 {v : Vt} (hu : v.u8need = 0) (ha : v.u8acc = 0) (x y : Nat) :
    ({ { v with u8need := x, u8acc := y } with u8need := 0, u8acc := 0 } : Vt) = v := by
  cases v
  simp_all

private theorem feed1 (w : Vt) (a : UInt8) : w.feed [a] = w.step a := by
  simp [Vt.feed]
private theorem feed2 (w : Vt) (a b : UInt8) : w.feed [a, b] = (w.step a).step b := by
  simp [Vt.feed]
private theorem feed3 (w : Vt) (a b c : UInt8) :
    w.feed [a, b, c] = ((w.step a).step b).step c := by
  simp [Vt.feed]
private theorem feed4 (w : Vt) (a b c d : UInt8) :
    w.feed [a, b, c, d] = (((w.step a).step b).step c).step d := by
  simp [Vt.feed]

/-- **The UTF-8 round trip.** The bytes `utf8` emits for a printable
codepoint decode back to exactly that codepoint: feeding them *is*
printing it. This is the lemma that turns a repaint's byte stream into a
chain of `Vt.print`s, after which the fidelity argument has no bytes left
in it. -/
theorem utf8_feed {v : Vt} (c : Char) (h20 : 0x20 ≤ c.toNat)
    (hg : v.pstate = .ground) (hu : v.u8need = 0) (ha : v.u8acc = 0) :
    v.feed (utf8 c) = v.print c := by
  have hle := char_le c
  have hn : min c.toNat 0x10FFFF = c.toNat := by omega
  -- the two nested-division facts `omega` cannot see on its own
  have e2 : c.toNat / 64 / 64 = c.toNat / 4096 := by
    simp [Nat.div_div_eq_div_mul]
  have e1 : c.toNat / 4096 / 64 = c.toNat / 262144 := by
    simp [Nat.div_div_eq_div_mul]
  unfold utf8
  dsimp only
  rw [hn]
  by_cases h1 : c.toNat < 0x80
  · -- one byte: an ASCII glyph
    rw [if_pos h1, feed1, step_ascii hg hu h20 h1, acceptChar_toNat]
  rw [if_neg h1]
  by_cases h2 : c.toNat < 0x800
  · -- two bytes: lead + final continuation
    rw [if_pos h2, feed2,
      step_lead2 hg hu (by omega),
      step_cont_last (acc := c.toNat / 64) (m := c.toNat % 64) (by rw [← hg]) rfl rfl (by omega) (by omega),
      reset_u8 hu ha,
      show c.toNat / 64 * 64 + c.toNat % 64 = c.toNat from by omega,
      acceptChar_toNat]
  rw [if_neg h2]
  by_cases h3 : c.toNat < 0x10000
  · -- three bytes
    rw [if_pos h3, feed3,
      step_lead3 hg hu (by omega),
      step_cont_more (k := 0) (acc := c.toNat / 4096) (m := c.toNat / 64 % 64) (by rw [← hg]) rfl rfl
        (by omega) (by omega),
      show c.toNat / 4096 * 64 + c.toNat / 64 % 64 = c.toNat / 64 from by omega,
      step_cont_last (acc := c.toNat / 64) (m := c.toNat % 64) (by rw [← hg]) rfl rfl (by omega) (by omega),
      reset_u8 hu ha,
      show c.toNat / 64 * 64 + c.toNat % 64 = c.toNat from by omega,
      acceptChar_toNat]
  -- four bytes
  rw [if_neg h3, feed4,
    step_lead4 hg hu (by omega),
    step_cont_more (k := 1) (acc := c.toNat / 262144) (m := c.toNat / 4096 % 64) (by rw [← hg]) rfl rfl
      (by omega) (by omega),
    show c.toNat / 262144 * 64 + c.toNat / 4096 % 64 = c.toNat / 4096 from by omega,
    step_cont_more (k := 0) (acc := c.toNat / 4096) (m := c.toNat / 64 % 64) (by rw [← hg]) rfl rfl
      (by omega) (by omega),
    show c.toNat / 4096 * 64 + c.toNat / 64 % 64 = c.toNat / 64 from by omega,
    step_cont_last (acc := c.toNat / 64) (m := c.toNat % 64) (by rw [← hg]) rfl rfl (by omega) (by omega),
    reset_u8 hu ha,
    show c.toNat / 64 * 64 + c.toNat % 64 = c.toNat from by omega,
    acceptChar_toNat]

theorem feed_append (v : Vt) (a b : Bytes) : v.feed (a ++ b) = (v.feed a).feed b := by
  simp [Vt.feed, List.foldl_append]

/-- "Quiet" in the decoder's sense: ground parser, nothing half-decoded.
Printing preserves it, which is what makes the run below an induction. -/
private theorem print_quiet {v : Vt} (c : Char) (hg : v.pstate = .ground) (hu : v.u8need = 0)
    (ha : v.u8acc = 0) :
    (v.print c).pstate = .ground ∧ (v.print c).u8need = 0 ∧ (v.print c).u8acc = 0 :=
  ⟨by rw [Zmx.Core.Vt.ps_print]; exact hg,
   by rw [Zmx.Core.Vt.un_print]; exact hu,
   by rw [Zmx.Core.Vt.ua_print]; exact ha⟩

/-- **A glyph run is a chain of prints.** The emitted bytes of a scrubbed
char list feed back as exactly those characters printed, in order. -/
theorem utf8s_feed : ∀ (cs : List Char) {v : Vt}, v.pstate = .ground → v.u8need = 0 →
    v.u8acc = 0 → v.feed (utf8s cs) = cs.foldl (fun w c => w.print (safeChar c)) v
  | [], _, _, _, _ => rfl
  | c :: cs, v, hg, hu, ha => by
    have hb := safeChar_ge c
    rw [show utf8s (c :: cs) = utf8 (safeChar c) ++ utf8s cs from by
      simp [utf8s, List.flatMap_cons]]
    rw [feed_append, utf8_feed (safeChar c) hb.1 hg hu ha]
    obtain ⟨h1, h2, h3⟩ := print_quiet (safeChar c) hg hu ha
    rw [utf8s_feed cs h1 h2 h3]
    rfl

/-- **A painted cell is a chain of prints**: its base glyph, then each of
its combining marks. Where those land is `Vt.print`'s business — and
§Replay fix 1 (a mark parked on a wide char's shadow cell) is exactly why
the marks have to be replayed at all. -/
theorem cellText_feed {v : Vt} (c : Cell) (hg : v.pstate = .ground) (hu : v.u8need = 0)
    (ha : v.u8acc = 0) :
    v.feed (cellText c)
      = c.marks.foldl (fun w m => w.print (safeChar m)) (v.print (safeChar c.base)) := by
  have hb := safeChar_ge c.base
  unfold cellText
  rw [feed_append, utf8_feed (safeChar c.base) hb.1 hg hu ha]
  obtain ⟨h1, h2, h3⟩ := print_quiet (safeChar c.base) hg hu ha
  exact utf8s_feed c.marks h1 h2 h3

/-- The row separator is a carriage return and a line feed, nothing more.
`joinCRLF` emits no trailing one, which is what keeps the last row from
scrolling the screen away. -/
theorem crlf_feed {v : Vt} (hg : v.pstate = .ground) (hu : v.u8need = 0) :
    v.feed [0x0D, 0x0A] = v.carriageReturn.lineFeed := by
  have hcr : v.step 0x0D = v.carriageReturn := by
    rw [step_of_ground_quiet _ hg hu]
    unfold Vt.stepGround
    rw [if_neg (by decide), if_pos (by decide)]
    rfl
  have hg2 : v.carriageReturn.pstate = .ground := by
    rw [Zmx.Core.Vt.ps_carriageReturn]; exact hg
  have hu2 : v.carriageReturn.u8need = 0 := by
    rw [Zmx.Core.Vt.un_carriageReturn]; exact hu
  rw [feed2, hcr, step_of_ground_quiet _ hg2 hu2]
  unfold Vt.stepGround
  rw [if_neg (by decide), if_pos (by decide)]
  rfl

/-! ### The pen round trip, semantic half — `applySgr` inverts the encoding

`penSgr` emits parameter *numbers* (`penAttrCodes`, `colorCodes`) and the
parser folds them back into a `Pen` with `Vt.applySgr`. This section proves
that fold recovers exactly the pen that was encoded, from **any** starting
pen — the attribute sequence leads with `0`, so it resets first.

Two shapes of proof, both driven by the guards in `applySgr`'s fold:

* the attributes are seven independent `Bool`s, so 128 concrete branches
  settle it outright — cheaper than seven step lemmas plus a composition;
* a colour lands in one of four forms, and the 16-colour ones are 8
  concrete codes each, which lets the fold's long `if`-chain decide by
  computation instead of needing a disequality per rung.

What is *not* here: that the parser's CSI accumulator delivers these
numbers in the first place (step 1 of specs/grid-fidelity.md). This half is
about `Vt.applySgr` alone.
-/

private theorem u8_lt256 (x : UInt8) : x.toNat < 256 := x.toNat_lt_size

/-- Parameters as the accumulator delivers them: no sub-parameter flags,
since `joinSemi` separates with `;` and never `:`. -/
def sgrParamsOf (ns : List Nat) : List (Nat × Bool) := ns.map (fun n => (n, false))

/-- The pen after one emitted SGR, at the fuel `applySgr` supplies. -/
def penAfter (q : Pen) (ns : List Nat) : Pen :=
  Vt.applySgr.go q (sgrParamsOf ns) (ns.length + 1)

/-- **The attribute sequence resets, then re-establishes `p`'s attributes.**
Both colours come out default because the leading `0` resets them and no
attribute code touches a colour. -/
theorem penAfter_attrCodes (q : Pen) (p : Pen) :
    penAfter q (penAttrCodes p)
      = { bold := p.bold, dim := p.dim, italic := p.italic,
          underline := p.underline, blink := p.blink, reverse := p.reverse,
          strike := p.strike } := by
  obtain ⟨fg, bg, b, d, i, u, bl, r, s⟩ := p
  cases b <;> cases d <;> cases i <;> cases u <;> cases bl <;> cases r <;> cases s <;>
    simp [penAfter, sgrParamsOf, penAttrCodes, Vt.applySgr.go]

/-- **A colour sequence writes exactly that colour**, in all four emitted
forms (16-colour, bright, 256-colour, truecolour). -/
theorem penAfter_colorCodes (q : Pen) (c : Color) (isFg : Bool)
    (hne : colorCodes c isFg ≠ []) :
    penAfter q (colorCodes c isFg)
      = (if isFg then { q with fg := c } else { q with bg := c }) := by
  cases c with
  | default => simp [colorCodes] at hne
  | idx i =>
    have key : UInt8.ofNat i.toNat = i := UInt8.ofNat_toNat
    have hi := u8_lt256 i
    by_cases h8 : i.toNat < 8
    · rcases (show i.toNat = 0 ∨ i.toNat = 1 ∨ i.toNat = 2 ∨ i.toNat = 3 ∨ i.toNat = 4
          ∨ i.toNat = 5 ∨ i.toNat = 6 ∨ i.toNat = 7 from by omega) with
        h'|h'|h'|h'|h'|h'|h'|h' <;>
        rw [h'] at key <;> cases isFg <;>
        simp [penAfter, sgrParamsOf, colorCodes, Vt.applySgr.go, ← key]
    by_cases h16 : i.toNat < 16
    · rcases (show i.toNat = 8 ∨ i.toNat = 9 ∨ i.toNat = 10 ∨ i.toNat = 11
          ∨ i.toNat = 12 ∨ i.toNat = 13 ∨ i.toNat = 14 ∨ i.toNat = 15 from by omega) with
        h'|h'|h'|h'|h'|h'|h'|h' <;>
        rw [h'] at key <;> cases isFg <;>
        simp [penAfter, sgrParamsOf, colorCodes, Vt.applySgr.go, ← key]
    · cases isFg <;>
        simp [penAfter, sgrParamsOf, colorCodes, h8, h16, Vt.applySgr.go, color256,
          show min i.toNat 255 = i.toNat from by omega, key]
  | rgb r g b =>
    have hr := u8_lt256 r; have hg := u8_lt256 g; have hb := u8_lt256 b
    cases isFg <;>
      simp [penAfter, sgrParamsOf, colorCodes, Vt.applySgr.go, UInt8.ofNat_toNat,
        show min r.toNat 255 = r.toNat from by omega,
        show min g.toNat 255 = g.toNat from by omega,
        show min b.toNat 255 = b.toNat from by omega]

/-- `colorCodes` is empty exactly for the default colour — which is why
`sgrColorSeq` can use emptiness as its "send nothing" test. -/
theorem colorCodes_eq_nil (c : Color) (isFg : Bool) :
    colorCodes c isFg = [] ↔ c = .default := by
  cases c with
  | default => simp [colorCodes]
  | idx i =>
    -- resolve the range guards first: with a literal list as the scrutinee
    -- the outer match reduces by iota
    unfold colorCodes
    dsimp only
    by_cases h8 : i.toNat < 8
    · rw [if_pos h8]; simp
    rw [if_neg h8]
    by_cases h16 : i.toNat < 16
    · rw [if_pos h16]; simp
    · rw [if_neg h16]; simp
  | rgb r g b => simp [colorCodes]

/-- The pen after a colour sequence *as the emitter decides whether to send
one* — mirroring `sgrColorSeq`, which sends nothing for a default colour. -/
def penAfterColor (q : Pen) (c : Color) (isFg : Bool) : Pen :=
  if c = .default then q else penAfter q (colorCodes c isFg)

theorem penAfterColor_eq (q : Pen) (c : Color) (isFg : Bool)
    (hdef : (if isFg then q.fg else q.bg) = .default) :
    penAfterColor q c isFg = (if isFg then { q with fg := c } else { q with bg := c }) := by
  unfold penAfterColor
  by_cases hc : c = .default
  · -- nothing emitted, and the attribute reset already left it default
    subst hc
    rw [if_pos rfl]
    cases isFg <;>
      simp only [Bool.false_eq_true, if_false, if_true] at hdef ⊢ <;> rw [← hdef]
  · rw [if_neg hc]
    exact penAfter_colorCodes q c isFg
      (fun h => hc ((colorCodes_eq_nil c isFg).mp h))

/-- **The pen encoding is invertible.** Feeding the three sequences
`penSgr` emits — attributes, then foreground, then background — to *any*
starting pen recovers exactly `p`. The semantic half of the pen round trip:
what remains is that the parser hands these numbers to `applySgr`, which is
step 1 of specs/grid-fidelity.md. -/
theorem pen_codes_recover (q : Pen) (p : Pen) :
    penAfterColor (penAfterColor (penAfter q (penAttrCodes p)) p.fg true) p.bg false = p := by
  rw [penAfter_attrCodes]
  rw [penAfterColor_eq _ _ true rfl]
  rw [penAfterColor_eq _ _ false rfl]
  simp

/-! ### The pen round trip, parser half — the accumulator delivers the numbers

`joinSemi` emits `<n1>;<n2>;…`, and the CSI accumulator turns that into the
parameter array `applySgr` folds over. Two lemmas, deliberately separate:
`csi_param_run_frame` says a parameter run changes *nothing but the parser
state*, and `csi_joinSemi_feed` says what that state contains. The second is
stated in terms of the array *after* the final push, because that push is
exactly what `csiFinish` performs — carrying `dropLast`/`getLast` through the
induction instead would fight `joinSemi`'s three-arm recursion for no gain.
-/

/-- Inside a CSI with nothing half-decoded, `step` is `stepCsi`. -/
theorem step_of_csi_quiet {v : Vt} {s : CsiState} (b : UInt8) (hg : v.pstate = .csi s)
    (hu : v.u8need = 0) : v.step b = v.stepCsi s b := by
  have ha : v.abortUtf8 b = v := by
    unfold Vt.abortUtf8
    rw [if_neg (by simp [hu])]
  unfold Vt.step
  dsimp only
  rw [ha, hg]

/-- `ESC [` from a quiet ground state opens an empty CSI and touches nothing
else. -/
theorem csi_open_feed {v : Vt} (hg : v.pstate = .ground) (hu : v.u8need = 0) :
    ((v.step 0x1B).step 0x5B) = { v with pstate := .csi {} } := by
  have h1 : v.step 0x1B = { v with pstate := .esc } := by
    rw [step_of_ground_quiet _ hg hu]
    unfold Vt.stepGround
    rw [if_pos (by decide)]
  rw [h1]
  have ha : ({ v with pstate := .esc } : Vt).abortUtf8 0x5B = { v with pstate := .esc } := by
    unfold Vt.abortUtf8
    rw [if_neg (by simp [hu])]
  unfold Vt.step
  dsimp only
  rw [ha]
  rfl

/-- A parameter byte moves the accumulator and nothing else. -/
theorem csi_param_step_frame {v : Vt} {s : CsiState} (b : UInt8) (hg : v.pstate = .csi s)
    (hu : v.u8need = 0) (h1 : 0x30 ≤ b) (h2 : b ≤ 0x3B) :
    ∃ s', v.step b = { v with pstate := .csi s' } := by
  obtain ⟨hn1, hn2⟩ := u8_bounds h1 h2
  simp only [show ((0x30 : UInt8)).toNat = 48 from rfl,
    show ((0x3B : UInt8)).toNat = 59 from rfl] at hn1 hn2
  rw [step_of_csi_quiet b hg hu]
  unfold Vt.stepCsi
  by_cases hd : (b ≥ 0x30 && b ≤ 0x39) = true
  · rw [if_pos hd]; exact ⟨_, rfl⟩
  by_cases hsemi : (b == 0x3B) = true
  · rw [if_neg (by simp [hd]), if_pos hsemi]; exact ⟨_, rfl⟩
  by_cases hcolon : (b == 0x3A) = true
  · rw [if_neg (by simp [hd]), if_neg (by simp [hsemi]), if_pos hcolon]; exact ⟨_, rfl⟩
  · exfalso
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

/-- …and so does a whole run of them: only `pstate` differs at the end. -/
theorem csi_param_run_frame : ∀ (bs : Bytes) {v : Vt} {s : CsiState}, v.pstate = .csi s →
    v.u8need = 0 → ParamBytes bs → ∃ s', v.feed bs = { v with pstate := .csi s' }
  | [], v, s, hg, _, _ => ⟨s, by rw [show v.feed [] = v from rfl, ← hg]⟩
  | x :: xs, v, s, hg, hu, hp => by
    obtain ⟨s1, hs1⟩ := csi_param_step_frame x hg hu (hp x (by simp)).1 (hp x (by simp)).2
    rw [feed_cons, hs1]
    obtain ⟨s2, hs2⟩ :=
      csi_param_run_frame xs (v := { v with pstate := .csi s1 }) rfl hu
        (fun b hb => hp b (by simp [hb]))
    exact ⟨s2, by rw [hs2]⟩

/-- One `<digits>;` group: the number closes into the array and the
accumulator is clear for the next. -/
theorem csi_group_step {v : Vt} {s : CsiState} (n : Nat) (hg : v.pstate = .csi s)
    (hcur : s.cur = 0) (hsize : s.params.size < 16) :
    (v.feed (digits n ++ [0x3B])).pstate
      = .csi { s with params := s.params.push (min n 65535, s.curSub),
                      cur := 0, curSub := false, haveCur := false } := by
  rw [feed_append]
  obtain ⟨s1, hs1, hcur1, hhave1, hpar1, hint1, hign1, hsub1, hpv1⟩ :=
    csi_digits_value n hg hcur
  rw [show ∀ (w : Vt), w.feed [(0x3B : UInt8)] = w.step 0x3B from fun _ => rfl]
  rw [csi_semi_step hs1]
  unfold csiPush
  rw [if_pos (by simp [hhave1]), if_neg (by rw [hpar1]; omega)]
  obtain ⟨p, ps, c, cs, hc, it, ig⟩ := s1
  simp_all

/-- **The parameter run.** Feeding a `;`-joined list of numbers leaves the
last one pending; pushing it — which is what `csiFinish` does — yields
exactly those numbers as the parameter array. -/
theorem csi_joinSemi_feed : ∀ (codes : List Nat) {v : Vt} {s : CsiState},
    v.pstate = .csi s → s.cur = 0 → s.curSub = false → codes ≠ [] →
    s.params.size + codes.length ≤ 16 →
    ∃ s', (v.feed (joinSemi codes)).pstate = .csi s'
      ∧ s'.haveCur = true ∧ s'.curSub = false ∧ s'.priv = s.priv
      ∧ s'.inter = s.inter ∧ s'.ignore = s.ignore ∧ s'.params.size < 16
      ∧ (s'.params.push (min s'.cur 65535, s'.curSub)).toList
          = s.params.toList ++ codes.map (fun n => (min n 65535, false))
  | [], _, _, _, _, _, hne, _ => absurd rfl hne
  | [n], v, s, hg, hcur, hsub, _, hcap => by
    obtain ⟨s1, hs1, hcur1, hhave1, hpar1, hint1, hign1, hsub1, hpv1⟩ :=
      csi_digits_value n hg hcur
    refine ⟨s1, hs1, hhave1, by rw [hsub1, hsub], hpv1, hint1, hign1, ?_, ?_⟩
    · rw [hpar1]; simp at hcap; omega
    · rw [hcur1, hpar1, hsub1, hsub,
        show min (min n 65535) 65535 = min n 65535 from by omega]
      simp
  | n :: m :: ns, v, s, hg, hcur, hsub, _, hcap => by
    rw [show joinSemi (n :: m :: ns) = (digits n ++ [0x3B]) ++ joinSemi (m :: ns) from by
      simp [joinSemi, List.append_assoc]]
    rw [feed_append]
    have hsz : s.params.size < 16 := by simp at hcap; omega
    obtain ⟨s', hs', h1, h2, h3, h4, h5, h6, h7⟩ :=
      csi_joinSemi_feed (m :: ns) (csi_group_step n hg hcur hsz) rfl rfl (by simp)
        (by simp only [Array.size_push]; simp at hcap ⊢; omega)
    refine ⟨s', hs', h1, h2, by rw [h3], by rw [h4], by rw [h5], h6, ?_⟩
    rw [h7, hsub]
    simp

/-- **The pen round trip.** Feeding one emitted SGR sets the pen to exactly
what its parameter numbers encode, and touches nothing else. With
`pen_codes_recover`, this is what makes a pen replay. -/
theorem sgrOf_feed {v : Vt} (codes : List Nat) (hne : codes ≠ [])
    (hcap : codes.length ≤ 16) (hle : ∀ n ∈ codes, n ≤ 65535)
    (hg : v.pstate = .ground) (hu : v.u8need = 0) :
    v.feed (sgrOf codes) = { v with pen := penAfter v.pen codes } := by
  rw [show sgrOf codes = 0x1B :: 0x5B :: (joinSemi codes ++ [0x6D]) from by
    simp [sgrOf, csiB]]
  rw [feed_cons, feed_cons, csi_open_feed hg hu, feed_append]
  -- the run: only the parser state moves, and we know what it holds
  obtain ⟨s1, hframe⟩ :=
    csi_param_run_frame (joinSemi codes) (v := { v with pstate := .csi {} }) rfl hu
      (paramBytes_joinSemi codes)
  obtain ⟨s', hs', hhave, hsub, hpriv, hinter, hign, hsize, hpush⟩ :=
    csi_joinSemi_feed codes (v := { v with pstate := .csi {} }) rfl rfl rfl hne
      (by simpa using hcap)
  -- the two views agree, so the run's result is a record we can compute with
  have hid : s1 = s' := by
    rw [hframe] at hs'
    exact PState.csi.inj hs'
  rw [hid] at hframe
  rw [hframe, show ∀ (w : Vt), w.feed [(0x6D : UInt8)] = w.step 0x6D from fun _ => rfl]
  rw [step_of_csi_quiet (v := { v with pstate := .csi s' }) (s := s') 0x6D rfl hu]
  -- 0x6D is a final byte, with no intermediate, so it dispatches
  unfold Vt.stepCsi
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_pos (by decide), if_neg (by simp [hinter])]
  unfold Vt.csiFinish
  dsimp only
  rw [if_pos hhave, if_neg (by simp; omega)]
  unfold Vt.csiDispatch
  dsimp only
  rw [if_neg (by simp [hign])]
  -- SGR: the parameters are the numbers the emitter chose
  -- stated over any record with that array, since `priv` gets normalised to
  -- its default on the way here and a fixed shape would stop matching
  have hparams : ∀ (t : CsiState),
      t.params = s'.params.push (min s'.cur 65535, s'.curSub) →
      t.sgrParams = sgrParamsOf codes := by
    intro t ht
    unfold CsiState.sgrParams
    rw [ht, hpush]
    simp only [List.nil_append]
    unfold sgrParamsOf
    exact List.map_congr_left (fun n hn => by
      rw [show min n 65535 = n from by have := hle n hn; omega])
  have hne' : ¬ (sgrParamsOf codes).isEmpty = true := by
    cases codes with
    | nil => exact absurd rfl hne
    | cons a as => simp [sgrParamsOf]
  simp only [hpriv, beq_self_eq_true, if_pos]
  unfold Vt.applySgr
  dsimp only
  rw [hparams _ rfl, if_neg hne']
  -- everything above the pen is untouched, and the parser is back in ground
  unfold penAfter
  simp only [sgrParamsOf, List.length_map]
  rw [← hg]

/-! ### Step 2 complete — a pen replays exactly -/

theorem penAttrCodes_ne_nil (p : Pen) : penAttrCodes p ≠ [] := by
  unfold penAttrCodes; simp

theorem penAttrCodes_le (p : Pen) : ∀ n ∈ penAttrCodes p, n ≤ 65535 := by
  obtain ⟨fg, bg, b, d, i, u, bl, r, s⟩ := p
  cases b <;> cases d <;> cases i <;> cases u <;> cases bl <;> cases r <;> cases s <;>
    simp [penAttrCodes]

theorem colorCodes_le (c : Color) (isFg : Bool) : ∀ n ∈ colorCodes c isFg, n ≤ 65535 := by
  intro n hn
  cases c with
  | default => simp [colorCodes] at hn
  | idx i =>
    have hi := u8_lt256 i
    cases isFg <;> unfold colorCodes at hn <;> dsimp only at hn <;> repeat' split at hn
    all_goals (simp at hn; omega)
  | rgb r g b =>
    have hr := u8_lt256 r; have hg := u8_lt256 g; have hb := u8_lt256 b
    cases isFg <;> (simp [colorCodes] at hn; omega)

/-- `sgrColorSeq` as an `if`, which is what the proofs want: rewriting a
`match` scrutinee runs into "motive is not type correct". -/
theorem sgrColorSeq_eq (c : Color) (isFg : Bool) :
    sgrColorSeq c isFg = if c = .default then [] else sgrOf (colorCodes c isFg) := by
  unfold sgrColorSeq
  cases c with
  | default => simp [colorCodes]
  | idx i =>
    -- resolve the range guards first: with a literal list as the scrutinee
    -- the outer match reduces by iota
    unfold colorCodes
    dsimp only
    by_cases h8 : i.toNat < 8
    · rw [if_pos h8]; simp
    rw [if_neg h8]
    by_cases h16 : i.toNat < 16
    · rw [if_pos h16]; simp
    · rw [if_neg h16]; simp
  | rgb r g b => simp [colorCodes]

theorem sgrColorSeq_feed {v : Vt} (c : Color) (isFg : Bool) (hg : v.pstate = .ground)
    (hu : v.u8need = 0) :
    v.feed (sgrColorSeq c isFg) = { v with pen := penAfterColor v.pen c isFg } := by
  rw [sgrColorSeq_eq]
  unfold penAfterColor
  by_cases hc : c = .default
  · rw [if_pos hc, if_pos hc, show v.feed [] = v from rfl]
  · rw [if_neg hc, if_neg hc]
    exact sgrOf_feed _ (fun h => hc ((colorCodes_eq_nil c isFg).mp h))
      (by have := colorCodes_length c isFg; omega) (colorCodes_le c isFg) hg hu

/-- **A pen replays exactly.** Feeding the sequences `penSgr` emits to a
quiet emulator sets its pen to `p` and changes nothing else — the parser
half (`sgrOf_feed`) composed with the semantic half
(`pen_codes_recover`). §Replay's pen fidelity, closed. -/
theorem penSgr_feed {v : Vt} (p : Pen) (hg : v.pstate = .ground) (hu : v.u8need = 0) :
    v.feed (penSgr p) = { v with pen := p } := by
  -- each stage's starting state is the previous stage's result, so they are
  -- pinned explicitly rather than left to unification
  have h1 := sgrOf_feed (v := v) (penAttrCodes p) (penAttrCodes_ne_nil p)
    (by have := penAttrCodes_length p; omega) (penAttrCodes_le p) hg hu
  have h2 := sgrColorSeq_feed (v := { v with pen := penAfter v.pen (penAttrCodes p) })
    p.fg true hg hu
  have h3 := sgrColorSeq_feed
    (v := { v with pen := penAfterColor (penAfter v.pen (penAttrCodes p)) p.fg true })
    p.bg false hg hu
  unfold penSgr
  rw [feed_append, feed_append, h1, h2, h3]
  exact congrArg (fun q => { v with pen := q }) (pen_codes_recover v.pen p)

/-! ### Step 3 — one glyph, placed

`print` is five stages; under the conditions a repaint actually runs in
(insert mode off, no charset translation, no pending wrap) four of them are
the identity and the fifth writes one cell. That is the rung a row induction
steps by.

Note the **grid-shape hypotheses**. `putCell` writes through
`setIfInBounds`, so a row shorter than `cols` would swallow the write
silently. Every reachable state satisfies `row.size = cols` and
`grid.size = rows` — `Vt.init` builds them that way and `resize` re-fits —
but `Good` does not say so, which is a gap in §Bound rather than in this
proof. `Renderable` (step 1 of specs/grid-fidelity.md) is where it belongs.
-/

/-- **One narrow glyph writes one cell.** `hpc` says the glyph is stored as
itself: no charset translation is in effect — true of a fresh emulator, and the
reason `charsetAnsi` is emitted *after* the repaint, since with `ESC ( 0` in
force every ASCII glyph would be re-drawn as a box character — and it is not a
control codepoint, which `Vt.printableChar` would otherwise replace. -/
theorem print_narrow {v : Vt} (ch : Char)
    (hpc : v.printChar ch = ch)
    (hw : charWidth ch = 1) (hins : v.modes.insert = false)
    (hpend : v.cursor.pending = false)
    (hrow : (v.getRow v.cursor.y).size = v.cols) (hgrid : v.grid.size = v.rows)
    (hx : v.cursor.x < v.cols) (hy : v.cursor.y < v.rows) :
    (v.print ch).getCell v.cursor.x v.cursor.y
        = { base := ch, marks := [], width := 1, pen := v.pen } := by
  rw [print_narrow_eq hpc hw hins hpend, getCell_printAdvance]
  refine getCell_write_mendRow_narrow _ _ _ _ rfl ?_ ?_
  · show v.cursor.y < v.grid.size
    rw [hgrid]; exact hy
  · show v.cursor.x < (v.getRow v.cursor.y).size
    rw [hrow]; exact hx

/-- **…and touches no other row.** The frame a grid induction needs: a glyph
paints inside one row. *Within* that row the claim is deliberately absent — the
print ends in a whole-row repair (`Row.mend`), which may rewrite any column of a
row that was not already pair-consistent — so the one-cell form is stated where
the row is known pair-consistent (`Renderable`), not here. -/
theorem print_narrow_frame {v : Vt} (ch : Char)
    (hpc : v.printChar ch = ch)
    (hw : charWidth ch = 1) (hins : v.modes.insert = false)
    (hpend : v.cursor.pending = false) (x' y' : Nat)
    (hne : y' ≠ v.cursor.y) :
    (v.print ch).getCell x' y' = v.getCell x' y' := by
  rw [print_narrow_eq hpc hw hins hpend, getCell_printAdvance]
  rw [getCell_write_mendRow_other _ _ _ _ _ _ (show y' ≠ v.cursor.y from hne)]
  rfl

/-- **A wide glyph writes two cells**: the glyph at the cursor with width 2, and
a width-0 *shadow* to its right, which carries nothing of its own — a repaint of
the base re-creates it, which is why marks are stored on the base
(`Vt.printMark`) and why a half pair is repaired rather than emitted. -/
theorem print_wide {v : Vt} (ch : Char)
    (hpc : v.printChar ch = ch)
    (hw : charWidth ch = 2) (hins : v.modes.insert = false)
    (hpend : v.cursor.pending = false) (hfit : v.cursor.x + 1 < v.cols)
    (hrow : (v.getRow v.cursor.y).size = v.cols) (hgrid : v.grid.size = v.rows)
    (hy : v.cursor.y < v.rows) :
    (v.print ch).getCell v.cursor.x v.cursor.y
        = { base := ch, marks := [], width := 2, pen := v.pen }
      ∧ (v.print ch).getCell (v.cursor.x + 1) v.cursor.y
        = { base := ' ', marks := [], width := 0, pen := v.pen } := by
  rw [print_wide_eq hpc hw hins hpend hfit, getCell_printAdvance, getCell_printAdvance]
  refine getCell_write_mendRow_wide _ _ _ _ rfl ?_ ?_
  · show v.cursor.y < v.grid.size
    rw [hgrid]; exact hy
  · show v.cursor.x + 1 < (v.getRow v.cursor.y).size
    rw [hrow]; exact hfit

/-- **A combining mark attaches to the cell before the cursor** — provided that
cell is not a wide glyph's shadow, in which case `Vt.printMark` redirects to its
base instead. The `< 8` cap is §Bound's: an adversarial mark stream must not
grow a cell without limit, so past eight the mark is dropped.

`hnarrow` is what the repair sweep needs to leave the marked cell alone. Marks
on a *wide* base survive too — its shadow is untouched by the write — but that
case reads the row's pair fact, so it is stated with `Renderable`. -/
theorem print_mark {v : Vt} (m : Char)
    (hpc : v.printChar m = m)
    (hw : charWidth m = 0) (hpend : v.cursor.pending = false) (hx0 : v.cursor.x ≠ 0)
    (hnw : (v.getCell (v.cursor.x - 1) v.cursor.y).width ≠ 0)
    (hnarrow : (v.getCell (v.cursor.x - 1) v.cursor.y).width = 1)
    (hcap : (v.getCell (v.cursor.x - 1) v.cursor.y).marks.length < 8)
    (hrow : (v.getRow v.cursor.y).size = v.cols) (hgrid : v.grid.size = v.rows)
    (hx : v.cursor.x - 1 < v.cols) (hy : v.cursor.y < v.rows) :
    (v.print m).getCell (v.cursor.x - 1) v.cursor.y
      = { v.getCell (v.cursor.x - 1) v.cursor.y with
          marks := (v.getCell (v.cursor.x - 1) v.cursor.y).marks ++ [m] } := by
  rw [print_mark_eq hpc hw hpend hx0 hnw hcap]
  exact getCell_write_mendRow_narrow _ _ _ _ hnarrow (by rw [hgrid]; exact hy)
    (by rw [hrow]; exact hx)

/-! ### §Replay stage 3c — the cursor lands where the session had it

The composition. `cup_places_cursor` says the final `CUP` delivers its two
parameters to the cursor; `quiet_restoreBody` says the ~kilobyte of repaint
in front of it leaves the parser ground with DECOM off, so those parameters
are read as an absolute address; the `dims` layer says the repaint cannot
have resized the emulator out from under the bounds. -/

/-- A fresh emulator of the session's own size is `Good`, so `clampDim` is
the identity on its dimensions. -/
theorem init_dims (v : Vt) (h : Good v) :
    (Vt.init v.cols v.rows).cols = v.cols ∧ (Vt.init v.cols v.rows).rows = v.rows := by
  have hc := h.colsPos; have hcl := h.colsLe
  have hr := h.rowsPos; have hrl := h.rowsLe
  refine ⟨?_, ?_⟩ <;> simp only [Vt.init, clampDim] <;> omega

/-- **§Replay (cursor).** Feeding a whole restore stream to a fresh
emulator of the session's size leaves the cursor exactly where the session
had it. `Good v` supplies the bounds (a real session always satisfies it —
`good_init` plus §Bound's induction); `origin = false` is the documented
gap, since under DECOM a region-relative address cannot reproduce a cursor
parked outside the scroll region. -/
theorem restore_cursor (v : Vt) (hgood : Good v) (ho : v.modes.origin = false) :
    (((Vt.init v.cols v.rows).feed (restore v)).cursor.x = v.cursor.x)
      ∧ (((Vt.init v.cols v.rows).feed (restore v)).cursor.y = v.cursor.y) := by
  obtain ⟨hic, hir⟩ := init_dims v hgood
  -- the stream splits at the final cursor address
  rw [show restore v = restoreBody v ++ cursorAnsi v from rfl]
  rw [show ∀ (w : Vt), w.feed (restoreBody v ++ cursorAnsi v)
      = (w.feed (restoreBody v)).feed (cursorAnsi v) from
    fun w => by simp [Vt.feed, List.foldl_append]]
  rw [show cursorAnsi v = csiNum2 (v.cursor.y + 1) (v.cursor.x + 1) 0x48 from by
    simp only [cursorAnsi, ho]; rfl]
  -- the body leaves the parser ground with DECOM still off
  obtain ⟨hpg, hpo⟩ := quiet_restoreBody v ho (Vt.init v.cols v.rows) rfl rfl
  -- …and cannot have resized the emulator
  have hd := dims_feed (restoreBody v) (good_init v.cols v.rows)
  have hdc : ((Vt.init v.cols v.rows).feed (restoreBody v)).cols = v.cols := by
    rw [show ((Vt.init v.cols v.rows).feed (restoreBody v)).cols
        = (dims ((Vt.init v.cols v.rows).feed (restoreBody v))).1 from rfl, hd]
    exact hic
  have hdr : ((Vt.init v.cols v.rows).feed (restoreBody v)).rows = v.rows := by
    rw [show ((Vt.init v.cols v.rows).feed (restoreBody v)).rows
        = (dims ((Vt.init v.cols v.rows).feed (restoreBody v))).2 from rfl, hd]
    exact hir
  obtain ⟨hx, hy⟩ := cup_places_cursor (v.cursor.y + 1) (v.cursor.x + 1) hpg
    (by omega) (by omega)
    (by have := hgood.curY; have := hgood.rowsLe; omega)
    (by have := hgood.curX; have := hgood.colsLe; omega)
    (by rw [hdr]; simpa using hgood.curY)
    (by rw [hdc]; simpa using hgood.curX) hpo
  exact ⟨by simpa using hx, by simpa using hy⟩

end Zmx.Core.Render



namespace Zmx.Core.Render

open Zmx.Core.Vt
/-! ## §Replay stage 3d — everything after the repaint leaves the screen alone

`restore` paints the grid and then tells the terminal the rest: scroll region,
tab ruler, DECSC slot, title, modes, charset, pen, and the final cursor address.
For the grid claim to be about the *repaint*, none of that tail may write a cell —
and that is not obvious from reading it, because `CSI r` moves the cursor, a
private mode set can home it, and `ESC H` edits the tab ruler.

`Keeps` is the third stream predicate, after `Ends` (the parser ends in ground)
and `Quiet` (DECOM stays off), and it is bundled for the same reason: the grid
claim needs the parser-state claim at every step, so carrying them separately
would mean re-establishing one in order to use the other. `u8need` rides along
because a stream must not leave a half-decoded character armed for the next one.
-/

/-- **The final byte, as a state equation.** `csi_final_step` gives only the
parser state; the grid layer needs the whole result. Stated here rather than
beside `csi_final_step` because it needs `step_of_csi_quiet`. The `s.inter = 0`
hypothesis is what separates a dispatched sequence from an ignored one
(`DECSCUSR` and friends take the intermediate branch). -/
theorem csi_final_step_eq {v : Vt} {s : CsiState} (b : UInt8) (hg : v.pstate = .csi s)
    (hu : v.u8need = 0) (hi : s.inter = 0) (h1 : 0x40 ≤ b) (h2 : b ≤ 0x7E) :
    v.step b = v.csiFinish s b := by
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := csi_final_guards b h1 h2
  rw [step_of_csi_quiet b hg hu]
  unfold Vt.stepCsi
  rw [if_neg (by simp [g1]), if_neg (by simp [g2]), if_neg (by simp [g3]),
      if_neg (by simp [g4]), if_neg (by simp [g5]), if_pos g6]
  rw [if_neg (by simp [hi])]

def Keeps (bs : Bytes) : Prop :=
  ∀ v : Vt, v.pstate = .ground → v.u8need = 0 →
    ((v.feed bs).pstate = .ground ∧ (v.feed bs).u8need = 0
      ∧ (v.feed bs).grid = v.grid)

theorem Keeps.nil : Keeps [] := fun _ hg hu => ⟨hg, hu, rfl⟩

theorem Keeps.append {a b : Bytes} (ha : Keeps a) (hb : Keeps b) : Keeps (a ++ b) := by
  intro v hg hu
  rw [show v.feed (a ++ b) = (v.feed a).feed b from by simp [Vt.feed, List.foldl_append]]
  obtain ⟨h1, h2, h3⟩ := ha v hg hu
  obtain ⟨h4, h5, h6⟩ := hb _ h1 h2
  exact ⟨h4, h5, h6.trans h3⟩

theorem Keeps.streamPred : StreamPred Keeps := ⟨Keeps.nil, fun ha hb => Keeps.append ha hb⟩

theorem Keeps.append3 {a b c : Bytes} (ha : Keeps a) (hb : Keeps b) (hc : Keeps c) :
    Keeps (a ++ b ++ c) := Keeps.streamPred.append3 ha hb hc

theorem Keeps.append4 {a b c d : Bytes} (ha : Keeps a) (hb : Keeps b) (hc : Keeps c)
    (hd : Keeps d) : Keeps (a ++ b ++ c ++ d) := Keeps.streamPred.append4 ha hb hc hd

/-- Both branches, with the condition available — `modesAnsi`'s screen-switch
guard is what will discharge `grid_setMode`'s hypotheses. -/
theorem Keeps.ite {c : Prop} [Decidable c] {a b : Bytes}
    (ha : c → Keeps a) (hb : ¬c → Keeps b) : Keeps (if c then a else b) :=
  Keeps.streamPred.ite ha hb

theorem Keeps.flatten {l : List Bytes} (h : ∀ bs ∈ l, Keeps bs) : Keeps l.flatten :=
  Keeps.streamPred.flatten h

theorem Keeps.flatMap {α : Type} {f : α → Bytes} {l : List α}
    (h : ∀ a, Keeps (f a)) : Keeps (l.flatMap f) := Keeps.streamPred.flatMap h

/-! ### The CSI workhorse

A `CSI … <final>` sequence can change the grid only through
`csiDispatch s final`: the walk to the final byte is a chain of `pstate` record
updates, which `csi_param_run_frame` already says. So the walk is done once here,
and each construct supplies only the one fact about its own final byte. -/

/-- `csiPush` closes a parameter; it never touches the intermediate slot. -/
theorem inter_csiPush (s : CsiState) (sub : Bool) : (csiPush s sub).inter = s.inter := by
  unfold csiPush
  repeat' split
  all_goals rfl

/-- A parameter run leaves the intermediate slot alone, which is what
`csi_final_step_eq` needs of it. -/
theorem csi_param_run_inter : ∀ (bs : Bytes) {v : Vt} {s : CsiState}, v.pstate = .csi s →
    v.u8need = 0 → ParamBytes bs →
    ∃ s', v.feed bs = { v with pstate := .csi s' } ∧ s'.inter = s.inter
  | [], v, s, hg, _, _ => ⟨s, by rw [show v.feed [] = v from rfl, ← hg], rfl⟩
  | x :: xs, v, s, hg, hu, hp => by
    obtain ⟨hx1, hx2⟩ := hp x (by simp)
    -- one parameter byte: a digit accumulates, `;`/`:` closes — both keep `inter`
    have hstep : ∃ t, v.step x = { v with pstate := .csi t } ∧ t.inter = s.inter := by
      rw [step_of_csi_quiet x hg hu]
      unfold Vt.stepCsi
      by_cases hd : (x ≥ 0x30 && x ≤ 0x39) = true
      · rw [if_pos hd]
        exact ⟨_, rfl, rfl⟩
      · rw [if_neg hd]
        by_cases hsemi : (x == 0x3B) = true
        · rw [if_pos hsemi]
          exact ⟨_, rfl, inter_csiPush s false⟩
        · rw [if_neg hsemi]
          by_cases hcolon : (x == 0x3A) = true
          · rw [if_pos hcolon]
            exact ⟨_, rfl, inter_csiPush s true⟩
          · -- 0x30…0x3B with none of the above is impossible
            exfalso
            simp only [Bool.and_eq_true, decide_eq_true_eq, UInt8.le_iff_toNat_le,
              show ((0x30 : UInt8)).toNat = 48 from rfl,
              show ((0x39 : UInt8)).toNat = 57 from rfl] at hd
            simp only [beq_iff_eq] at hsemi hcolon
            obtain ⟨hb1, hb2⟩ := u8_bounds hx1 hx2
            simp only [show ((0x30 : UInt8)).toNat = 48 from rfl,
              show ((0x3B : UInt8)).toNat = 59 from rfl] at hb1 hb2
            have h3A : x ≠ 0x3A := hcolon
            have h3B : x ≠ 0x3B := hsemi
            have hn3A : x.toNat ≠ 58 := fun he => h3A (UInt8.toNat_inj.mp
              (by simpa [show ((0x3A : UInt8)).toNat = 58 from rfl] using he))
            have hn3B : x.toNat ≠ 59 := fun he => h3B (UInt8.toNat_inj.mp
              (by simpa [show ((0x3B : UInt8)).toNat = 59 from rfl] using he))
            have hgt : 57 < x.toNat := by
              rcases Nat.lt_or_ge 57 x.toNat with h | h
              · exact h
              · exact absurd ⟨hb1, h⟩ hd
            omega
    obtain ⟨t, hxs, hti⟩ := hstep
    rw [feed_cons, hxs]
    obtain ⟨s', hs', hsi⟩ := csi_param_run_inter xs (v := { v with pstate := .csi t })
      (s := t) rfl hu (fun b hb => hp b (by simp [hb]))
    exact ⟨s', by rw [hs'], hsi.trans hti⟩

/-- From ground, `ESC [` lands in a fresh collector with nothing else touched. -/
theorem keeps_csi_open {v : Vt} (hg : v.pstate = .ground) (hu : v.u8need = 0) :
    v.feed [0x1B, 0x5B] = { v with pstate := .csi {} } := by
  rw [show v.feed [0x1B, 0x5B] = (v.step 0x1B).step 0x5B from by simp [Vt.feed]]
  have hesc : v.step 0x1B = { v with pstate := .esc } := by
    unfold Vt.step Vt.abortUtf8
    dsimp only
    rw [if_neg (by simp [hu]), hg]
    dsimp only
    unfold Vt.stepGround
    rw [if_pos (by decide)]
  rw [hesc]
  unfold Vt.step Vt.abortUtf8
  dsimp only
  rw [if_neg (by simp [hu])]
  unfold Vt.stepEsc
  rfl

/-- The shared tail: from a collector with no intermediate, a parameter run and a
final byte return to ground and touch the grid only as the dispatch does. -/
theorem keeps_csi_tail (params : Bytes) (final : UInt8) (hp : ParamBytes params)
    (h1 : 0x40 ≤ final) (h2 : final ≤ 0x7E)
    (hgrid : ∀ (w : Vt) (t : CsiState), (w.csiDispatch t final).grid = w.grid)
    {v : Vt} {s : CsiState} (hg : v.pstate = .csi s) (hu : v.u8need = 0)
    (hi : s.inter = 0) :
    ((v.feed (params ++ [final])).pstate = .ground
      ∧ (v.feed (params ++ [final])).u8need = 0
      ∧ (v.feed (params ++ [final])).grid = v.grid) := by
  obtain ⟨s', hs', hsi⟩ := csi_param_run_inter params hg hu hp
  rw [show ∀ (w : Vt), w.feed (params ++ [final]) = (w.feed params).feed [final] from
    fun w => by simp [Vt.feed, List.foldl_append]]
  rw [hs', show ∀ (w : Vt), w.feed [final] = w.step final from fun _ => rfl]
  rw [csi_final_step_eq final (v := { v with pstate := .csi s' }) (s := s') rfl
    (by simpa using hu) (by rw [hsi]; exact hi) h1 h2]
  unfold Vt.csiFinish
  dsimp only
  refine ⟨rfl, ?_, ?_⟩
  · rw [un_csiDispatch]
    simpa using hu
  · rw [hgrid]

theorem keeps_csi_seq (params : Bytes) (final : UInt8) (hp : ParamBytes params)
    (h1 : 0x40 ≤ final) (h2 : final ≤ 0x7E)
    (hgrid : ∀ (w : Vt) (t : CsiState), (w.csiDispatch t final).grid = w.grid) :
    Keeps (csiB ++ params ++ [final]) := by
  intro v hg hu
  rw [show (csiB ++ params ++ [final] : Bytes) = [0x1B, 0x5B] ++ (params ++ [final]) from by
    unfold csiB; simp]
  rw [show ∀ (w : Vt), w.feed ([0x1B, 0x5B] ++ (params ++ [final]))
      = (w.feed [0x1B, 0x5B]).feed (params ++ [final]) from
    fun w => by simp [Vt.feed, List.foldl_append]]
  rw [keeps_csi_open hg hu]
  exact keeps_csi_tail params final hp h1 h2 hgrid rfl (by simpa using hu) rfl

/-- The private form (`CSI ? n h/l`), which is what a mode replay is made of. The
marker byte sits outside `ParamBytes` — deliberately, since a marker is what
decides whether a sequence can be DECOM — so it takes one explicit step. -/
theorem keeps_csi_priv_seq (params : Bytes) (final : UInt8) (hp : ParamBytes params)
    (h1 : 0x40 ≤ final) (h2 : final ≤ 0x7E)
    (hgrid : ∀ (w : Vt) (t : CsiState), (w.csiDispatch t final).grid = w.grid) :
    Keeps (csiB ++ ([0x3F] ++ params) ++ [final]) := by
  intro v hg hu
  rw [show (csiB ++ ([0x3F] ++ params) ++ [final] : Bytes)
      = [0x1B, 0x5B] ++ ([(0x3F : UInt8)] ++ (params ++ [final])) from by unfold csiB; simp]
  rw [show ∀ (w : Vt), w.feed ([0x1B, 0x5B] ++ ([(0x3F : UInt8)] ++ (params ++ [final])))
      = ((w.feed [0x1B, 0x5B]).feed [(0x3F : UInt8)]).feed (params ++ [final]) from
    fun w => by simp [Vt.feed, List.foldl_append]]
  rw [keeps_csi_open hg hu]
  rw [show ∀ (w : Vt), w.feed [(0x3F : UInt8)] = w.step 0x3F from fun _ => rfl]
  rw [step_of_csi_quiet (0x3F : UInt8) (v := { v with pstate := .csi {} }) (s := {}) rfl
    (by simpa using hu)]
  unfold Vt.stepCsi
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos (by decide)]
  exact keeps_csi_tail params final hp h1 h2 hgrid rfl (by simpa using hu) rfl

/-! ### One fact per final byte the tail uses -/

theorem grid_csiDispatch_cup (v : Vt) (s : CsiState) :
    (v.csiDispatch s 0x48).grid = v.grid := by
  by_cases hi : s.ignore = true
  · simp [Vt.csiDispatch, hi]
  · unfold Vt.csiDispatch
    rw [if_neg hi]
    show (v.moveTo (s.arg 1 1 - 1) (s.arg 0 1 - 1)).grid = v.grid
    rw [frame_moveTo]

theorem grid_csiDispatch_cha (v : Vt) (s : CsiState) :
    (v.csiDispatch s 0x47).grid = v.grid := by
  by_cases hi : s.ignore = true
  · simp [Vt.csiDispatch, hi]
  · unfold Vt.csiDispatch
    rw [if_neg hi]
    show (v.setCol (s.arg 0 1 - 1)).grid = v.grid
    rw [frame_setCol]

theorem grid_csiDispatch_sgr (v : Vt) (s : CsiState) :
    (v.csiDispatch s 0x6D).grid = v.grid := by
  by_cases hi : s.ignore = true
  · simp [Vt.csiDispatch, hi]
  · unfold Vt.csiDispatch
    rw [if_neg hi]
    show (if s.priv == 0 then v.applySgr s.sgrParams else v).grid = v.grid
    split
    · rw [frame_applySgr]
    · rfl

theorem grid_csiDispatch_tbc (v : Vt) (s : CsiState) :
    (v.csiDispatch s 0x67).grid = v.grid := by
  by_cases hi : s.ignore = true
  · simp [Vt.csiDispatch, hi]
  · unfold Vt.csiDispatch
    rw [if_neg hi]
    show (match s.arg 0 0 with
      | 0 => { v with tabs := v.tabs.setIfInBounds v.cursor.x false }
      | 3 => { v with tabs := Array.replicate v.cols false }
      | _ => v).grid = v.grid
    repeat' split
    all_goals rfl

theorem grid_csiDispatch_stbm (v : Vt) (s : CsiState) :
    (v.csiDispatch s 0x72).grid = v.grid := by
  by_cases hi : s.ignore = true
  · simp [Vt.csiDispatch, hi]
  · unfold Vt.csiDispatch
    rw [if_neg hi]
    show (if s.priv != 0 then v else
            if s.arg 0 1 - 1 < s.arg 1 v.rows - 1 && s.arg 1 v.rows - 1 < v.rows then
              ({ v with top := s.arg 0 1 - 1, bot := s.arg 1 v.rows - 1 }).moveTo 0 0
            else v).grid = v.grid
    repeat' split
    all_goals first
      | rfl
      | rw [frame_moveTo]

/-! ### The CSI-shaped constructs in the tail -/

theorem keeps_csiNum (n : Nat) (final : UInt8) (h1 : 0x40 ≤ final) (h2 : final ≤ 0x7E)
    (hgrid : ∀ (w : Vt) (t : CsiState), (w.csiDispatch t final).grid = w.grid) :
    Keeps (csiNum n final) :=
  keeps_csi_seq _ _ (paramBytes_digits n) h1 h2 hgrid

theorem keeps_csiNum2 (a b : Nat) (final : UInt8) (h1 : 0x40 ≤ final) (h2 : final ≤ 0x7E)
    (hgrid : ∀ (w : Vt) (t : CsiState), (w.csiDispatch t final).grid = w.grid) :
    Keeps (csiNum2 a b final) := by
  rw [show csiNum2 a b final = csiB ++ (digits a ++ [0x3B] ++ digits b) ++ [final] from by
    unfold csiNum2; simp]
  refine keeps_csi_seq _ _ (fun x hx => ?_) h1 h2 hgrid
  rcases List.mem_append.mp hx with hx' | hx'
  · rcases List.mem_append.mp hx' with hx'' | hx''
    · exact paramBytes_digits a x hx''
    · rw [show x = 0x3B from by simpa using hx'']
      exact ⟨by decide, by decide⟩
  · exact paramBytes_digits b x hx'

theorem keeps_csiPriv (n : Nat) (final : UInt8) (h1 : 0x40 ≤ final) (h2 : final ≤ 0x7E)
    (hgrid : ∀ (w : Vt) (t : CsiState), (w.csiDispatch t final).grid = w.grid) :
    Keeps (csiPriv n final) := by
  rw [show csiPriv n final = csiB ++ ([0x3F] ++ digits n) ++ [final] from by
    unfold csiPriv; simp]
  exact keeps_csi_priv_seq _ _ (paramBytes_digits n) h1 h2 hgrid

end Zmx.Core.Render



namespace Zmx.Core.Render

open Zmx.Core.Vt
/-! ### The SGR pen, and the one mode fact the replay turns on -/

theorem keeps_sgrOf (codes : List Nat) : Keeps (sgrOf codes) := by
  unfold sgrOf
  exact keeps_csi_seq _ _ (paramBytes_joinSemi codes) (by decide) (by decide)
    grid_csiDispatch_sgr

theorem keeps_sgrColorSeq (c : Color) (isFg : Bool) : Keeps (sgrColorSeq c isFg) := by
  unfold sgrColorSeq
  split
  · exact Keeps.nil
  · exact keeps_sgrOf _

/-- **An SGR pen writes no cell**, for any pen — 16-colour, 256-colour or
truecolour, and however `penSgr` splits it across sequences. This is the piece
`savedAnsi` and `restoreBody`'s trailing pen both rest on. -/
theorem keeps_penSgr (p : Pen) : Keeps (penSgr p) := by
  unfold penSgr
  exact ((keeps_sgrOf _).append (keeps_sgrColorSeq _ _)).append (keeps_sgrColorSeq _ _)

/-- **A mode set writes no cell — unless it switches screens.** `47`, `1047` and
`1049` swap the grid for the alternate one, and nothing else in `setMode` touches
a cell. `modesAnsi` never emits those three, which is the same guarded-emit
argument `quiet_modesAnsi` makes for DECOM (mode 6): the emitter is what keeps the
claim true, so the hypothesis is discharged where the bytes are chosen rather than
assumed about the parser.

Turning this into `Keeps (modesAnsi v)` needs one more bridge — that the digits
the emitter writes are the number the parser accumulates (`csi_digits_value`) — so
that `s.arg 0 0` can be identified with the emitted mode. That bridge exists for
the pen and cursor rungs and is the next step here. -/
theorem grid_setMode (v : Vt) (priv : Bool) (n : Nat) (on : Bool)
    (h47 : n ≠ 47) (h1047 : n ≠ 1047) (h1049 : n ≠ 1049) :
    (v.setMode priv n on).grid = v.grid := by
  unfold Vt.setMode
  split
  · split
    all_goals first
      | rfl
      | rw [frame_moveTo]
      | exact absurd rfl h47
      | exact absurd rfl h1047
      | exact absurd rfl h1049
      | (split <;> rfl)
  · split
    all_goals rfl

end Zmx.Core.Render



namespace Zmx.Core.Render

open Zmx.Core.Vt
/-! ### The non-CSI tail

`ESC`-singles (DECSC, HTS, app-keypad), charset designations and the shift-out
byte. Each is a two- or three-byte walk, and at each step the grid is untouched
because every branch `stepEsc`/`stepEscInter`/`ctl` takes for these bytes is a
record update on some *other* field — the saved slot, the tab ruler, a mode flag,
the charset flags, `shiftOut`. -/

theorem step_of_esc_quiet {v : Vt} (b : UInt8) (hg : v.pstate = .esc) (hu : v.u8need = 0) :
    v.step b = v.stepEsc b := by
  have ha : v.abortUtf8 b = v := by
    unfold Vt.abortUtf8
    rw [if_neg (by simp [hu])]
  unfold Vt.step
  dsimp only
  rw [ha, hg]

theorem step_of_escInter_quiet {v : Vt} {i : UInt8} (b : UInt8) (hg : v.pstate = .escInter i)
    (hu : v.u8need = 0) : v.step b = v.stepEscInter i b := by
  have ha : v.abortUtf8 b = v := by
    unfold Vt.abortUtf8
    rw [if_neg (by simp [hu])]
  unfold Vt.step
  dsimp only
  rw [ha, hg]

/-- From ground, `ESC` only arms the parser. Stated as an equation (not just a
`pstate` fact) so the layers that care about other fields can use it. -/
theorem esc_step_eq {v : Vt} (hg : v.pstate = .ground) (hu : v.u8need = 0) :
    v.step 0x1B = { v with pstate := .esc } := by
  unfold Vt.step Vt.abortUtf8
  dsimp only
  rw [if_neg (by simp [hu]), hg]
  dsimp only
  unfold Vt.stepGround
  rw [if_pos (by decide)]

/-- `ESC 7` (DECSC), `ESC H` (HTS) and `ESC =` (app keypad) write the saved slot,
the tab ruler and a mode flag respectively — never a cell. -/
theorem keeps_escSeq (b : UInt8) (hb : b = 0x37 ∨ b = 0x3D ∨ b = 0x48) :
    Keeps (escSeq b) := by
  intro v hg hu
  rw [show escSeq b = [0x1B] ++ [b] from rfl]
  rw [show ∀ (w : Vt), w.feed ([0x1B] ++ [b]) = (w.step 0x1B).step b from
    fun w => by simp [Vt.feed]]
  rw [esc_step_eq hg hu, step_of_esc_quiet b rfl (by simpa using hu)]
  rcases hb with h | h | h
  · subst h
    show _ ∧ _ ∧ _
    unfold Vt.stepEsc
    exact ⟨rfl, by simpa using hu, rfl⟩
  · subst h
    show _ ∧ _ ∧ _
    unfold Vt.stepEsc
    exact ⟨rfl, by simpa using hu, rfl⟩
  · subst h
    show _ ∧ _ ∧ _
    unfold Vt.stepEsc
    exact ⟨rfl, by simpa using hu, rfl⟩

/-- `ESC ( x` / `ESC ) x` set a charset flag. -/
theorem keeps_escCharset (i x : UInt8) (hi : i = 0x28 ∨ i = 0x29) :
    Keeps (escCharset i x) := by
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

/-- `SO` selects G1. A C0 byte from ground goes through `ctl`, which for `0x0E`
sets one flag. -/
theorem keeps_shiftOut : Keeps [0x0E] := by
  intro v hg hu
  rw [show ∀ (w : Vt), w.feed [(0x0E : UInt8)] = w.step 0x0E from fun _ => rfl]
  rw [step_of_ground_quiet (0x0E : UInt8) hg hu]
  show _ ∧ _ ∧ _
  unfold Vt.stepGround
  rw [if_neg (by decide), if_pos (by decide)]
  unfold Vt.ctl
  -- `SO` leaves the parser exactly where it was, so the ground fact is `hg`
  exact ⟨hg, by simpa using hu, rfl⟩

/-! ### The stages that need no digit bridge

Everything except `modesAnsi`, which needs the emitted mode number identified with
the parsed one before `grid_setMode` applies. -/

theorem keeps_regionAnsi (v : Vt) : Keeps (regionAnsi v) := by
  unfold regionAnsi
  exact Keeps.ite (fun _ => Keeps.nil)
    (fun _ => keeps_csiNum2 _ _ 0x72 (by decide) (by decide) grid_csiDispatch_stbm)

theorem keeps_cursorAnsi (v : Vt) : Keeps (cursorAnsi v) := by
  unfold cursorAnsi
  exact Keeps.ite
    (fun _ => keeps_csiNum2 _ _ 0x48 (by decide) (by decide) grid_csiDispatch_cup)
    (fun _ => keeps_csiNum2 _ _ 0x48 (by decide) (by decide) grid_csiDispatch_cup)

theorem keeps_savedAnsi (v : Vt) : Keeps (savedAnsi v) := by
  unfold savedAnsi
  exact ((keeps_penSgr _).append
    (keeps_csiNum2 _ _ 0x48 (by decide) (by decide) grid_csiDispatch_cup)).append
    (keeps_escSeq 0x37 (by decide))

theorem keeps_tabsAnsi (v : Vt) : Keeps (tabsAnsi v) := by
  unfold tabsAnsi
  refine Keeps.ite (fun _ => Keeps.nil) (fun _ => ?_)
  refine (keeps_csiNum 3 0x67 (by decide) (by decide) grid_csiDispatch_tbc).append ?_
  refine Keeps.flatMap (fun i => ?_)
  exact (keeps_csiNum (i + 1) 0x47 (by decide) (by decide) grid_csiDispatch_cha).append
    (keeps_escSeq 0x48 (by decide))

theorem keeps_charsetAnsi (v : Vt) : Keeps (charsetAnsi v) := by
  unfold charsetAnsi
  refine ((Keeps.ite (fun _ => keeps_escCharset 0x28 0x30 (by decide))
    (fun _ => keeps_escCharset 0x28 0x42 (by decide))).append
    (Keeps.ite (fun _ => keeps_escCharset 0x29 0x30 (by decide))
      (fun _ => keeps_escCharset 0x29 0x42 (by decide)))).append ?_
  exact Keeps.ite (fun _ => keeps_shiftOut) (fun _ => Keeps.nil)

end Zmx.Core.Render



namespace Zmx.Core.Render

open Zmx.Core.Vt
/-! ### The window title

An OSC is the one tail construct with an unbounded payload, so it is the one that
needs an induction. Every step is still a `pstate` record update — the accumulator
lives inside the parser state — and `oscFinish` writes the title and nothing else. -/

theorem step_of_osc_quiet {v : Vt} {acc : Array UInt8} {e : Bool} (b : UInt8)
    (hg : v.pstate = .osc acc e) (hu : v.u8need = 0) : v.step b = v.stepOsc acc e b := by
  have ha : v.abortUtf8 b = v := by
    unfold Vt.abortUtf8
    rw [if_neg (by simp [hu])]
  unfold Vt.step
  dsimp only
  rw [ha, hg]

theorem grid_oscFinish (v : Vt) (acc : Array UInt8) : (v.oscFinish acc).grid = v.grid := by
  unfold Vt.oscFinish
  dsimp only
  repeat' split
  all_goals rfl

theorem un_oscFinish' (v : Vt) (acc : Array UInt8) : (v.oscFinish acc).u8need = v.u8need := by
  unfold Vt.oscFinish
  dsimp only
  repeat' split
  all_goals rfl

theorem ps_oscFinish' (v : Vt) (acc : Array UInt8) : (v.oscFinish acc).pstate = .ground := by
  unfold Vt.oscFinish
  dsimp only
  repeat' split
  all_goals rfl

/-- A payload byte only grows the accumulator, which lives in the parser state. -/
theorem osc_accum_eq {v : Vt} {acc : Array UInt8} (b : UInt8)
    (hg : v.pstate = .osc acc false) (hu : v.u8need = 0) (h1 : b ≠ 0x1B) (h2 : b ≠ 0x07) :
    ∃ acc', v.step b = { v with pstate := .osc acc' false } := by
  rw [step_of_osc_quiet b hg hu]
  unfold Vt.stepOsc
  -- the guards in order: ST (impossible, no pending ESC), BEL, ESC, then the cap
  rw [if_neg (by simp), if_neg (by simp [h2]), if_neg (by simp [h1])]
  split
  · exact ⟨acc, rfl⟩
  · exact ⟨acc.push b, rfl⟩

theorem osc_accum_run : ∀ (bs : Bytes) {v : Vt} {acc : Array UInt8},
    v.pstate = .osc acc false → v.u8need = 0 → (∀ b ∈ bs, b ≠ 0x1B ∧ b ≠ 0x07) →
    ∃ acc', v.feed bs = { v with pstate := .osc acc' false }
  | [], v, acc, hg, _, _ => ⟨acc, by rw [show v.feed [] = v from rfl, ← hg]⟩
  | x :: xs, v, acc, hg, hu, h => by
    obtain ⟨acc1, hx⟩ := osc_accum_eq x hg hu (h x (by simp)).1 (h x (by simp)).2
    rw [feed_cons, hx]
    obtain ⟨acc2, hrest⟩ := osc_accum_run xs (v := { v with pstate := .osc acc1 false })
      (acc := acc1) rfl (by simpa using hu) (fun b hb => h b (by simp [hb]))
    exact ⟨acc2, by rw [hrest]⟩

/-- **The title writes no cell.** The payload cannot terminate its own sequence:
`utf8s` puts every byte at or above `0x20`, so neither `ESC` nor `BEL` can appear
in it — the same fact that makes `ends_osc` work. -/
theorem keeps_osc (payload : List Char) :
    Keeps (escB ++ [0x5D, 0x32, 0x3B] ++ utf8s payload ++ [0x07]) := by
  intro v hg hu
  rw [show (escB ++ [0x5D, 0x32, 0x3B] ++ utf8s payload ++ [0x07] : Bytes)
      = [0x1B] ++ ([0x5D] ++ ([0x32, 0x3B] ++ (utf8s payload ++ [0x07]))) from by
    simp [escB]]
  rw [show ∀ (w : Vt), w.feed ([0x1B] ++ ([0x5D] ++ ([0x32, 0x3B]
        ++ (utf8s payload ++ [0x07]))))
      = ((((w.step 0x1B).step 0x5D).feed [0x32, 0x3B]).feed (utf8s payload)).step 0x07 from
    fun w => by simp [Vt.feed, List.foldl_append]]
  rw [esc_step_eq hg hu]
  -- `ESC ]` opens the string
  rw [show ({ v with pstate := .esc } : Vt).step 0x5D
      = { v with pstate := .osc #[] false } from by
    rw [step_of_esc_quiet 0x5D rfl (by simpa using hu)]
    unfold Vt.stepEsc
    rfl]
  -- the code and its separator, then the payload
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
  -- BEL finishes it
  rw [step_of_osc_quiet (0x07 : UInt8) rfl (by simpa using hu)]
  unfold Vt.stepOsc
  rw [if_neg (by decide), if_pos (by decide)]
  exact ⟨ps_oscFinish' _ _, by rw [un_oscFinish']; simpa using hu,
    by rw [grid_oscFinish]⟩

theorem keeps_titleAnsi (v : Vt) : Keeps (titleAnsi v) := by
  unfold titleAnsi
  exact Keeps.ite (fun _ => Keeps.nil) (fun _ => keeps_osc _)

end Zmx.Core.Render
