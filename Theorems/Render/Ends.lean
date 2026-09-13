module

public import Linger.Core.Render
public import Theorems.Vt
import all Linger.Core.Render
import all Linger.Core.Vt
import all Theorems.Vt

-- No `public section`: a **public** declaration's type may not mention a private
-- field, and `Vt`'s are private now (the seal, `specs/vt-toolkit.md` Step 1).
-- Module-private is the default, so consumers reach in with `import all`. See the
-- longer note in `Theorems/Vt.lean`.

/-! # §Replay, stage 3b — a restore stream leaves the parser in ground

The §Replay target (specs/archive/grid-fidelity.md; the parser half was closed
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

namespace Linger.Core.Render

open Linger.Core.Vt

/-! ## Byte facts about the emitters -/

/-- Every digit byte is an ASCII digit — so it is a CSI *parameter*
byte, never a final or a control. -/
theorem digits_range (n : Nat) : ∀ b ∈ digits n, 0x30 ≤ b ∧ b ≤ 0x39 := by
  induction n using digits.induct with
  | case1 n h =>
    intro b hb
    rw [digits] at hb
    simp only [ite_eq_left h, List.mem_singleton] at hb
    subst hb
    have h8 : (0x30 + n) < 256 := by omega
    refine ⟨UInt8.le_iff_toNat_le.mpr ?_, UInt8.le_iff_toNat_le.mpr ?_⟩
    · simp [UInt8.toNat_ofNat', Nat.mod_eq_of_lt h8]
    · simp [UInt8.toNat_ofNat', Nat.mod_eq_of_lt h8]
      omega
  | case2 n h ih =>
    intro b hb
    rw [digits] at hb
    simp only [ite_eq_right h, List.mem_append, List.mem_singleton] at hb
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
  · simp only [h, ite_true]
    exact ⟨by decide, by decide⟩
  · simp only [h, Bool.false_eq_true, ite_false]
    simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, not_or, Nat.not_lt] at h
    exact ⟨h.1, h.2⟩

/-- A byte built by `UInt8.ofNat` from an in-range non-control number is
a non-control byte. The bridge from the emitters' arithmetic to byte
facts. -/
theorem ofNat_no_ctl (m : Nat) (h20 : 0x20 ≤ m) (hlt : m < 256) (h7 : m ≠ 0x7F) :
    (UInt8.ofNat m) ≥ 0x20 ∧ (UInt8.ofNat m) ≠ 0x7F := by
  have htn : (UInt8.ofNat m).toNat = m := by simp [UInt8.toNat_ofNat', Nat.mod_eq_of_lt hlt]
  refine
    ⟨UInt8.le_iff_toNat_le.mpr
        (by
          rw [htn]; simpa using h20),
      ?_⟩
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
def Ends (bs : Bytes) : Prop := ∀ v : Vt, v.pstate = .ground → (v.feed bs).pstate = .ground

theorem feed_cons (v : Vt) (x : UInt8) (xs : Bytes) : v.feed (x :: xs) = (v.step x).feed xs := by
  simp [Vt.feed]

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

theorem append3 {P : Bytes → Prop} (hP : StreamPred P) {a b c : Bytes} (ha : P a) (hb : P b)
    (hc : P c) : P (a ++ b ++ c) := hP.append (hP.append ha hb) hc

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
  · rw [ite_eq_left h]; exact ha h
  · rw [ite_eq_right h]; exact hb h

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
    rw [Linger.Core.Vt.ps_abortUtf8]; exact hg
  unfold Vt.step
  dsimp only
  rw [hw, Linger.Core.Vt.ps_stepGround _ b hb]
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
    rw [Linger.Core.Vt.ps_abortUtf8]; exact hg
  unfold Vt.step
  dsimp only
  rw [hw]
  rfl

/-- `ESC [` opens a CSI with an empty parameter set. -/
theorem csi_open_step {v : Vt} (hg : v.pstate = .esc) :
    (v.step 0x5B).pstate = .csi {} := by
  have hw : (v.abortUtf8 0x5B).pstate = PState.esc := by
    rw [Linger.Core.Vt.ps_abortUtf8]; exact hg
  unfold Vt.step
  dsimp only
  rw [hw]
  rfl

/-- `UInt8` comparisons, in `Nat` where `omega` can see them. The whole
ladder's guard reasoning goes through this. -/
-- not `private`: used by the Quiet, Pen and Keeps rungs too (it was private
-- only because they all used to live in one file).
theorem u8_bounds {b : UInt8} {lo hi : UInt8} (h1 : lo ≤ b) (h2 : b ≤ hi) :
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
    rw [Linger.Core.Vt.ps_abortUtf8]; exact hg
  unfold Vt.step
  dsimp only
  rw [hw]
  unfold Vt.stepCsi
  dsimp only
  -- digit? separator? private marker? — every case stays in `.csi`
  by_cases hd : (b ≥ 0x30 && b ≤ 0x39) = true
  · rw [ite_eq_left hd]; exact ⟨_, rfl⟩
  by_cases hsemi : (b == 0x3B) = true
  · rw [ite_eq_right (by simp [hd]), ite_eq_left hsemi]; exact ⟨_, rfl⟩
  by_cases hcolon : (b == 0x3A) = true
  · rw [ite_eq_right (by simp [hd]), ite_eq_right (by simp [hsemi]), ite_eq_left hcolon]
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
    rw [ite_eq_right (by simp [hd]), ite_eq_right (by simp [hsemi]), ite_eq_right (by simp [hcolon]),
        ite_eq_left hpriv]
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
    rw [Linger.Core.Vt.ps_abortUtf8]; exact hg
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := csi_final_guards b h1 h2
  unfold Vt.step
  dsimp only
  rw [hw]
  unfold Vt.stepCsi
  dsimp only
  rw [ite_eq_right (by simp [g1]), ite_eq_right (by simp [g2]), ite_eq_right (by simp [g3]),
      ite_eq_right (by simp [g4]), ite_eq_right (by simp [g5]), ite_eq_left g6]
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
    (hb : b = 0x37 ∨ b = 0x3D ∨ b = 0x48 ∨ b = 0x3E ∨ b = 0x5C) :
    (v.step b).pstate = .ground := by
  have hw : (v.abortUtf8 b).pstate = PState.esc := by
    rw [Linger.Core.Vt.ps_abortUtf8]; exact hg
  unfold Vt.step
  dsimp only
  rw [hw]
  unfold Vt.stepEsc
  rcases hb with h | h | h | h | h <;> subst h <;> rfl

/-- `ESC (` / `ESC )` enter the charset-designation state. -/
theorem esc_inter_step {v : Vt} (b : UInt8) (hg : v.pstate = .esc)
    (hb : b = 0x28 ∨ b = 0x29) : (v.step b).pstate = .escInter b := by
  have hw : (v.abortUtf8 b).pstate = PState.esc := by
    rw [Linger.Core.Vt.ps_abortUtf8]; exact hg
  unfold Vt.step
  dsimp only
  rw [hw]
  unfold Vt.stepEsc
  rcases hb with h | h <;> subst h <;> rfl

/-- …and the byte after it always returns to ground. -/
theorem esc_inter_finish {v : Vt} {i : UInt8} (b : UInt8) (hg : v.pstate = .escInter i) :
    (v.step b).pstate = .ground := by
  have hw : (v.abortUtf8 b).pstate = PState.escInter i := by
    rw [Linger.Core.Vt.ps_abortUtf8]; exact hg
  unfold Vt.step
  dsimp only
  rw [hw]
  unfold Vt.stepEscInter
  dsimp only
  repeat' split
  all_goals rfl

/-- `ESC 7` (DECSC), `ESC =` and `ESC H` (HTS) are `Ends`. -/
theorem ends_escSeq (b : UInt8) (hb : b = 0x37 ∨ b = 0x3D ∨ b = 0x48 ∨ b = 0x3E ∨ b = 0x5C) :
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
    rw [Linger.Core.Vt.ps_abortUtf8]; exact hg
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
    rw [Linger.Core.Vt.ps_abortUtf8]; exact hg
  unfold Vt.step
  dsimp only
  rw [hw]
  unfold Vt.stepOsc
  dsimp only
  -- ST needs the esc flag (false here); BEL and ESC are excluded; both
  -- the cap branch and the accumulate branch stay `.osc … false`
  rw [ite_eq_right (by simp), ite_eq_right (by simp [h2]), ite_eq_right (by simp [h1])]
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
    rw [Linger.Core.Vt.ps_abortUtf8]; exact hg
  unfold Vt.step
  dsimp only
  rw [hw]
  unfold Vt.stepOsc
  dsimp only
  rw [ite_eq_right (by simp), ite_eq_left (by decide)]
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
  unfold rowSlot
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

/-- One both-ways mode emit. `modeSet` is a definition rather than a local lambda
precisely so this matches structurally. -/
theorem ends_modeSet (n : Nat) (on : Bool) : Ends (modeSet n on) := by
  unfold modeSet
  cases on
  · exact ends_csiPriv n 0x6C (by decide) (by decide)
  · exact ends_csiPriv n 0x68 (by decide) (by decide)

/-! ### The scrollback stage

The history push is a paint plus a run of CR+LF, and the run is what the three
stream layers each need one new ingredient for: a `crlfB` carries no ESC, no SI
and no SO, so it is `text` to all of them. That single fact plus the fact that
`ends_gridAnsi`/`quiet_gridAnsi`/`smap_id_gridAnsi` are already generic in the
array is what makes the whole stage cost a handful of lines per layer. -/

/-- The flush carries no ESC, no SO and no SI — the three bytes every stream layer
cares about. Stated for all three at once so `Quiet` and `SMap` reuse it. -/
theorem crlfRun_no_esc (n : Nat) :
    ∀ b ∈ (List.replicate n crlfB).flatten, b ≠ 0x1B ∧ b ≠ 0x0E ∧ b ≠ 0x0F := by
  intro b hb
  rw [List.mem_flatten] at hb
  obtain ⟨l, hl, hbl⟩ := hb
  rw [List.eq_of_mem_replicate hl] at hbl
  simp only [crlfB, List.mem_cons, List.not_mem_nil, or_false] at hbl
  rcases hbl with h | h
  all_goals (subst h; exact ⟨by decide, by decide, by decide⟩)

theorem crlfRun_no_1B (n : Nat) :
    ∀ b ∈ (List.replicate n crlfB).flatten, b ≠ (0x1B : UInt8) :=
  fun b hb => (crlfRun_no_esc n b hb).1

/-- The flush run returns the parser to ground: it is `text`, whatever its
length. -/
theorem ends_crlfRun (n : Nat) : Ends ((List.replicate n crlfB).flatten) :=
  Ends.text (crlfRun_no_1B n)

theorem ends_scrollbackAnsi (v : Vt) : Ends (scrollbackAnsi v) := by
  unfold scrollbackAnsi
  refine Ends.append (Ends.append (Ends.append ?_
    (ends_csiNum 4 0x6C (by decide) (by decide))) (ends_modeSet 6 false))
    (ends_modeSet 7 true)
  exact Ends.ite Ends.nil
    (((ends_csiNum 3 0x4A (by decide) (by decide)).append (ends_gridAnsi (sbRows v))).append
      (ends_crlfRun v.rows))

/-! ### The composition: a whole restore stream

Every stage of `restore` is `Ends`, so the stream is. This is §Replay's
parser half, for ANY `Vt` and with no hypotheses.
-/

theorem ends_screensAnsi (v : Vt) : Ends (screensAnsi v) := by
  unfold screensAnsi
  refine (ends_scrollbackAnsi v).append ?_
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
  exact ends_osc _

theorem ends_irm (on : Bool) : Ends (csiNum 4 (if on then 0x68 else 0x6C)) := by
  cases on
  · exact ends_csiNum 4 0x6C (by decide) (by decide)
  · exact ends_csiNum 4 0x68 (by decide) (by decide)

/-- The chains below are **right**-associated to match `++`. Left-associating them
makes the elaborator reconcile the two shapes by unfolding `List.append`, which at a
dozen chunks exhausts the heartbeat budget. -/
theorem ends_modesAnsi (v : Vt) : Ends (modesAnsi v) := by
  unfold modesAnsi
  refine Ends.append ?_ (ends_irm v.modes.insert)
  refine Ends.append ?_ (ends_modeSet 6 _)
  refine Ends.append ?_ (ends_modeSet 1004 _)
  refine Ends.append ?_ (ends_modeSet 1006 _)
  refine Ends.append ?_ (Ends.ite (ends_modeSet v.modes.mouse true) Ends.nil)
  refine Ends.append ?_ (ends_modeSet 1003 false)
  refine Ends.append ?_ (ends_modeSet 1002 false)
  refine Ends.append ?_ (ends_modeSet 1000 false)
  refine Ends.append ?_ (ends_modeSet 2004 _)
  refine Ends.append ?_ (ends_modeSet 25 _)
  refine Ends.append ?_
    (Ends.ite (ends_escSeq 0x3D (by decide)) (ends_escSeq 0x3E (by decide)))
  exact (ends_modeSet 7 _).append (ends_modeSet 1 _)

theorem ends_prologueAnsi (v : Vt) : Ends (prologueAnsi v) := by
  unfold prologueAnsi
  refine Ends.append ?_ (Ends.text (bs := [0x0F]) (by decide))
  refine Ends.append ?_ (ends_escCharset 0x29 0x42 (by decide))
  refine Ends.append ?_ (ends_escCharset 0x28 0x42 (by decide))
  refine Ends.append ?_ (ends_csiNum2 1 v.rows 0x72 (by decide) (by decide))
  refine Ends.append ?_ (ends_modeSet 7 true)
  refine Ends.append ?_ (ends_modeSet 6 false)
  refine Ends.append ?_ (ends_csiNum 4 0x6C (by decide) (by decide))
  exact (ends_escSeq 0x5C (by decide)).append (ends_modeSet 1049 false)

theorem ends_cursorAnsi (v : Vt) : Ends (cursorAnsi v) := by
  unfold cursorAnsi
  exact Ends.ite (ends_csiNum2 _ _ 0x48 (by decide) (by decide))
    (ends_csiNum2 _ _ 0x48 (by decide) (by decide))

theorem ends_restoreBody (v : Vt) : Ends (restoreBody v) := by
  unfold restoreBody
  refine Ends.append ?_ (ends_penSgr v.pen)
  refine Ends.append ?_ (ends_charsetAnsi v)
  refine Ends.append ?_ (ends_modesAnsi v)
  refine Ends.append ?_ (ends_titleAnsi v)
  refine Ends.append ?_ (ends_savedAnsi v)
  refine Ends.append ?_ (ends_tabsAnsi v)
  refine Ends.append ?_ (ends_regionAnsi v)
  refine Ends.append ?_ (ends_screensAnsi v)
  refine Ends.append ?_ (ends_csiNum 2 0x4A (by decide) (by decide))
  exact (ends_prologueAnsi v).append (ends_csiNum 0 0x6D (by decide) (by decide))

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
  refine Linger.Core.Vt.uz_feed _ _ ?_
    (Linger.Core.Vt.uz_step 0x5B (by decide) (Linger.Core.Vt.uz_step_esc v))
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

end Linger.Core.Render
