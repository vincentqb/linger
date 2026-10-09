module

public import Linger.Core.Render
public import Theorems.Vt
import all Linger.Core.Render
import all Linger.Core.Vt
import all Theorems.Vt

-- Module-private by default: `Vt`'s fields are sealed (see `Theorems/Vt/State.lean`).

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

* `Ends bs` — "from ground, `bs` returns to ground". `Ends.append` makes
  it closed under `++`, and `restore` is a concatenation, so the top
  theorem is assembled from one lemma per emitted construct
  (`ends_csiNum`, `ends_penSgr`, `ends_osc`, …).
* Each construct's lemma is proved from the byte facts of the emitters
  (`digits_range`, `utf8_no_ctl`) — which only exist because `Render`
  builds `List UInt8` rather than `String`s (see that module's header).

Screen contents, cursor and pen are later rungs (`restore_cursor_any`,
`restore_grid_any`).
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
  intro b hb; have := utf8s_no_ctl cs b hb; grind

theorem utf8s_cons (c : Char) (cs : List Char) :
    utf8s (c :: cs) = utf8 (safeChar c) ++ utf8s cs := by simp only [utf8s, List.flatMap_cons]

/-- Each scrubbed Unicode scalar occupies at most four bytes. -/
theorem utf8s_length_le (cs : List Char) : (utf8s cs).length ≤ 4 * cs.length := by
  induction cs with
  | nil => simp [utf8s]
  | cons c cs
    ih =>
    have scalar : (utf8 (safeChar c)).length ≤ 4 := by
      unfold utf8
      dsimp only
      split <;> (try split) <;> (try split) <;> simp
    simp only [utf8s, List.flatMap_cons, List.length_append, List.length_cons] at *
    omega

/-! ## `Ends`: the compositional core

`Ends bs` is exactly the property that composes over `++`, which is what
lets the top theorem be assembled construct by construct instead of by
tracing a whole restore stream.
-/

/-- From a ground parser, feeding `bs` returns to a ground parser: no
restore stream can leave a client wedged mid-sequence, eating the
application's next output.

Scoped to `pstate`, which composes over `++`; the whole-stream decoder claim is
`restore_quiesced`. -/
def Ends (bs : Bytes) : Prop := ∀ v : Vt, v.pstate = .ground → (v.feed bs).pstate = .ground

theorem feed_nil (v : Vt) : v.feed [] = v := rfl

theorem feed_cons (v : Vt) (x : UInt8) (xs : Bytes) : v.feed (x :: xs) = (v.step x).feed xs := rfl

theorem feed_append (v : Vt) (a b : Bytes) : v.feed (a ++ b) = (v.feed a).feed b :=
  Good.feed_append v a b

theorem Ends.nil : Ends [] := fun _ h => h

/-- The composition law. `Vt.feed` is a `foldl`, so this is
`List.foldl_append` plus transitivity. -/
theorem Ends.append {a b : Bytes} (ha : Ends a) (hb : Ends b) : Ends (a ++ b) := by
  intro v h
  rw [feed_append]
  exact hb (v.feed a) (ha v h)

/-- **The shape all three stream layers share.**

`Ends`, `Quiet` and `Keeps` are predicates on a byte string, each closed under
concatenation. Everything derived follows from `nil` and `append` alone, so those
two are the bundle and the combinators are generic.

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

theorem flatMap {P : Bytes → Prop} (hP : StreamPred P) {α : Type} {f : α → Bytes}
    {l : List α} (h : ∀ a, P (f a)) : P (l.flatMap f) := by
  induction l with
  | nil => exact hP.nil
  | cons a as ih =>
    rw [List.flatMap_cons]
    exact hP.append (h a) ih

/-- The painter's traversal preserves any stream predicate supported by its
primitive emissions. Text safety stays a premise: preserving the grid, for
example, cannot supply it. The pen and column accumulators remain unrestricted. -/
theorem rowAnsi {P : Bytes → Prop} (hP : StreamPred P)
    (hpen : ∀ p, P (penSgr p)) (hbase : ∀ ch, P (utf8 (safeChar ch)))
    (hmarks : ∀ cs, P (utf8s cs)) (hcha : ∀ n, P (csiNum n 0x47))
    (row : Row) (p : Pen) : P (Linger.Core.Render.rowAnsi row p).1 := by
  unfold Linger.Core.Render.rowAnsi
  rw [← Array.foldl_toList]
  refine invariant_foldl (fun acc => P acc.1) _ ?_ row.toList ([], p, 0) hP.nil
  intro acc c hacc
  unfold rowSlot
  dsimp only
  split
  · exact hP.append hacc (hmarks c.marks)
  · apply hP.append
    · split
      · exact hacc
      · exact hP.append hacc (hpen c.pen)
    · split
      · exact hP.append4 (hbase c.base) (hcha _) (hmarks c.marks) (hcha _)
      · exact hP.append (hbase c.base) (hmarks c.marks)

theorem joinCRLF {P : Bytes → Prop} (hP : StreamPred P) (hcrlf : P [0x0D, 0x0A]) :
    ∀ (l : List Bytes), (∀ bs ∈ l, P bs) → P (Linger.Core.Render.joinCRLF l)
  | [], _ => hP.nil
  | [b], h => by
    unfold Linger.Core.Render.joinCRLF
    exact h b (by simp)
  | b :: c :: bs, h => by
    unfold Linger.Core.Render.joinCRLF
    exact hP.append (hP.append (h b (by simp)) hcrlf)
      (hP.joinCRLF hcrlf (c :: bs) (fun x hx => h x (by simp [hx])))

/-- Row predicates lift through the grid painter, including its reset, home and
separators. No receiver invariant or bound on the source grid is introduced. -/
theorem gridAnsi {P : Bytes → Prop} (hP : StreamPred P)
    (hreset : P (csiNum 0 0x6D)) (hhome : P (csiB ++ [0x48]))
    (hcrlf : P [0x0D, 0x0A]) (hrow : ∀ row p, P (Linger.Core.Render.rowAnsi row p).1)
    (grid : Array Row) : P (Linger.Core.Render.gridAnsi grid) := by
  unfold Linger.Core.Render.gridAnsi
  dsimp only
  apply hP.append hreset
  apply hP.append hhome
  apply hP.joinCRLF hcrlf
  simp only [List.mem_reverse]
  rw [← Array.foldl_toList]
  refine invariant_foldl (fun acc => ∀ bs ∈ acc.1, P bs) _ ?_ grid.toList
    (([], ({} : Pen))) (by intro bs hbs; simp at hbs)
  intro acc row hacc bs hbs
  dsimp only at hbs
  rcases List.mem_cons.mp hbs with h | h
  · subst h
    exact hrow row acc.2
  · exact hacc bs h

end StreamPred

theorem Ends.streamPred : StreamPred Ends := ⟨Ends.nil, fun ha hb => Ends.append ha hb⟩

/-- An `if` over two `Ends` pieces is `Ends` (restore is full of conditional
fragments). Unconditional in both branches, unlike the `Quiet`/`Keeps` forms. -/
theorem Ends.ite {c : Prop} [Decidable c] {a b : Bytes}
    (ha : Ends a) (hb : Ends b) : Ends (if c then a else b) :=
  Ends.streamPred.ite (fun _ => ha) (fun _ => hb)

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

/-- `UInt8` comparisons, in `Nat` where `omega` can see them. -/
-- not `private`: the Quiet rung uses it too (it was private only because the rungs
-- used to live in one file).
theorem u8_bounds {b : UInt8} {lo hi : UInt8} (h1 : lo ≤ b) (h2 : b ≤ hi) :
    lo.toNat ≤ b.toNat ∧ b.toNat ≤ hi.toNat :=
  ⟨UInt8.le_iff_toNat_le.mp h1, UInt8.le_iff_toNat_le.mp h2⟩

/-- A parameter byte (digit, `:`, `;`, or a `<=>?` private marker) keeps
us inside `.csi` — with some other accumulator, which is all the ladder
needs to know. -/
theorem csi_param_step {v : Vt} {s : CsiState} (b : UInt8) (hg : v.pstate = .csi s)
    (h1 : 0x30 ≤ b) (h2 : b ≤ 0x3F) : ∃ s', (v.step b).pstate = .csi s' := by
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
    rw [ite_eq_right (by simp [hd]), ite_eq_right (by simp [hsemi]), ite_eq_right (by simp [hcolon]),
        ite_eq_left (by grind)]
    exact ⟨_, rfl⟩

/-- A run of parameter bytes keeps us inside `.csi`. -/
theorem csi_param_feed : ∀ (bs : Bytes) {v : Vt} {s : CsiState}, v.pstate = .csi s →
    (∀ b ∈ bs, 0x30 ≤ b ∧ b ≤ 0x3F) → ∃ s', (v.feed bs).pstate = .csi s'
  | [], _, s, hg, _ => ⟨s, hg⟩
  | x :: xs, v, s, hg, h => by
    obtain ⟨s', hs'⟩ := csi_param_step x hg (h x (by simp)).1 (h x (by simp)).2
    rw [feed_cons]
    exact csi_param_feed xs hs' (fun b hb => h b (by simp [hb]))

/-- The six pre-final guards in `stepCsi`, all false below `0x40`, shared by
`csi_final_step` and `csi_final_step_eq` (`Keeps.lean`). -/
theorem csi_final_guards (b : UInt8) (h1 : 0x40 ≤ b) (h2 : b ≤ 0x7E) :
    (b ≥ 0x30 && b ≤ 0x39) = false ∧ (b == 0x3B) = false ∧ (b == 0x3A) = false
      ∧ (b ≥ 0x3C && b ≤ 0x3F) = false ∧ (b ≥ 0x20 && b ≤ 0x2F) = false
      ∧ (b ≥ 0x40 && b ≤ 0x7E) = true := by
  grind

/-- A final byte in 0x40…0x7E dispatches the sequence and returns to
ground: `csiFinish` assigns `.ground` unconditionally, and so does the
intermediate-ignore branch. -/
theorem csi_final_step {v : Vt} {s : CsiState} (b : UInt8) (hg : v.pstate = .csi s)
    (h1 : 0x40 ≤ b) (h2 : b ≤ 0x7E) : (v.step b).pstate = .ground := by
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
  intro b hb; have := h b hb; grind

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
  intro b hb; have := digits_range n b hb; grind

/-- `;<number>` — the shape every SGR sub-parameter takes. -/
theorem paramBytes_semiDigits (n : Nat) : ParamBytes (0x3B :: digits n) := by
  refine ParamBytes.cons ?_ ?_ (paramBytes_digits n) <;> decide

/-- `<a>;<b>` — the two-parameter shape of `CUP` and `DECSTBM`. -/
theorem paramBytes_digits2 (a b : Nat) : ParamBytes (digits a ++ [0x3B] ++ digits b) := by
  rw [List.append_assoc, List.singleton_append]
  exact (paramBytes_digits a).append (paramBytes_semiDigits b)

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
  rw [feed_append]
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
  rw [feed_append]
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
  exact ends_csi_seq _ final (paramBytes_digits2 a b) h1 h2

theorem ends_csiPriv (n : Nat) (final : UInt8) (h1 : 0x40 ≤ final)
    (h2 : final ≤ 0x7E) : Ends (csiPriv n final) := by
  have : csiPriv n final = csiB ++ (0x3F :: digits n) ++ [final] := by
    simp [csiPriv]
  rw [this]
  exact ends_csi_priv_seq _ final (paramBytes_digits n) h1 h2

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
go to `.escInter`, which waits for a final in `0x30..0x7E`. -/

/-- An `ESC <final>` whose final is one of the single-byte sequences
`restore` emits — `7` (DECSC), `=`/`>` (keypad modes), `H` (HTS), `\` (ST) —
lands back in ground. -/
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

/-- A final byte returns the intermediate sequence to ground. -/
theorem esc_inter_finish {v : Vt} {i : UInt8} (b : UInt8) (hg : v.pstate = .escInter i)
    (hlo : 0x30 ≤ b) (hhi : b ≤ 0x7E) :
    (v.step b).pstate = .ground := by
  have hw : (v.abortUtf8 b).pstate = PState.escInter i := by
    rw [Linger.Core.Vt.ps_abortUtf8]; exact hg
  unfold Vt.step
  dsimp only
  rw [hw]
  dsimp only
  rw [Linger.Core.Vt.stepEscInter_final _ i b hlo hhi]
  repeat' split
  all_goals rfl

/-- The single-byte `ESC` sequences `restore` emits are `Ends`. -/
theorem ends_escSeq (b : UInt8) (hb : b = 0x37 ∨ b = 0x3D ∨ b = 0x48 ∨ b = 0x3E ∨ b = 0x5C) :
    Ends (escSeq b) := by
  intro v hg
  show (v.feed ([0x1B] ++ [b])).pstate = .ground
  rw [show ([0x1B] ++ [b] : Bytes) = 0x1B :: [b] from rfl, feed_cons]
  show ((v.step 0x1B).step b).pstate = .ground
  exact esc_single_step b (esc_step hg) hb

/-- `ESC ( x` / `ESC ) x` (charset designation) are `Ends`. -/
theorem ends_escCharset (i x : UInt8) (hi : i = 0x28 ∨ i = 0x29)
    (hlo : 0x30 ≤ x) (hhi : x ≤ 0x7E) :
    Ends (escCharset i x) := by
  intro v hg
  show (v.feed ([0x1B] ++ [i, x])).pstate = .ground
  rw [show ([0x1B] ++ [i, x] : Bytes) = 0x1B :: i :: [x] from rfl, feed_cons, feed_cons]
  show (((v.step 0x1B).step i).step x).pstate = .ground
  exact esc_inter_finish x (esc_inter_step i (esc_step hg) hi) hlo hhi

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
  intro b hb; have := utf8s_no_ctl cs b hb; grind

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
  rw [feed_append]
  obtain ⟨a4, h4⟩ := osc_accum_feed (utf8s payload) h3 (utf8s_no_esc_bel payload)
  exact osc_bel_step h4

/-! ### The grid repaint

Cells contribute scrubbed text (`Ends.text`) and, when the pen changes,
an SGR sequence (`ends_penSgr`). Both are `Ends`, so the fold that
assembles a row preserves "everything so far is `Ends`" — `invariant_foldl`
(`Theorems/Vt/State.lean`) carries that in `StreamPred.rowAnsi`, and again over
the grid's list of painted rows in `StreamPred.gridAnsi`. -/

theorem ends_utf8s (cs : List Char) : Ends (utf8s cs) :=
  Ends.text (utf8s_no_esc cs)

theorem ends_utf8_safe (ch : Char) : Ends (utf8 (safeChar ch)) :=
  Ends.text (fun b hb => by
    have := utf8_no_ctl (safeChar ch) (safeChar_ge ch).1 (safeChar_ge ch).2 b hb; grind)

theorem ends_cellText (c : Cell) : Ends (cellText c) := by
  unfold cellText
  exact (ends_utf8_safe c.base).append (ends_utf8s c.marks)

theorem ends_pendingAnsi (cols : Nat) (grid : Array Row) (cur : Cursor)
    (row : Nat) (pen : Pen) : Ends (Linger.Core.Render.pendingAnsi cols grid cur row pen) := by
  unfold pendingAnsi
  dsimp only
  apply Ends.ite
  · exact (((ends_csiNum2 _ _ 0x48 (by decide) (by decide)).append
      (ends_penSgr _)).append (ends_cellText _)).append (ends_penSgr _)
  · exact Ends.nil

theorem ends_rowAnsi (row : Row) (p : Pen) : Ends (rowAnsi row p).1 :=
  Ends.streamPred.rowAnsi ends_penSgr ends_utf8_safe ends_utf8s
    (fun n => ends_csiNum n 0x47 (by decide) (by decide)) row p

theorem ends_crlf : Ends [0x0D, 0x0A] := Ends.text (by decide)

theorem ends_gridAnsi (grid : Array Row) : Ends (gridAnsi grid) := by
  refine Ends.streamPred.gridAnsi (ends_csiNum 0 0x6D (by decide) (by decide))
    ?_ ends_crlf ends_rowAnsi grid
  exact ends_csi_seq [] 0x48 ParamBytes.nil (by decide) (by decide)

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
  obtain ⟨l, hl, hbl⟩ := List.mem_flatten.mp hb
  rw [List.eq_of_mem_replicate hl] at hbl
  simp only [crlfB] at hbl
  grind

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
  · exact (((((ends_gridAnsi _).append (ends_penSgr _)).append
      (ends_csiNum2 _ _ 0x48 (by decide) (by decide))).append
      (ends_pendingAnsi _ _ _ _ _)).append
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

theorem ends_savedPendingAnsi (v : Vt) : Ends (Linger.Core.Render.savedPendingAnsi v) := by
  unfold savedPendingAnsi
  exact Ends.ite ((ends_pendingAnsi _ _ _ _ _).append (ends_escSeq 0x37 (by decide))) Ends.nil

theorem ends_charsetAnsi (v : Vt) : Ends (charsetAnsi v) := by
  unfold charsetAnsi
  refine ((Ends.ite (ends_escCharset 0x28 0x30 (by decide) (by decide) (by decide))
    (ends_escCharset 0x28 0x42 (by decide) (by decide) (by decide))).append
    (Ends.ite (ends_escCharset 0x29 0x30 (by decide) (by decide) (by decide))
      (ends_escCharset 0x29 0x42 (by decide) (by decide) (by decide)))).append ?_
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
  refine Ends.append ?_ (ends_escCharset 0x29 0x42 (by decide) (by decide) (by decide))
  refine Ends.append ?_ (ends_escCharset 0x28 0x42 (by decide) (by decide) (by decide))
  refine Ends.append ?_ (ends_csiNum2 1 v.rows 0x72 (by decide) (by decide))
  refine Ends.append ?_ (ends_modeSet 7 true)
  refine Ends.append ?_ (ends_modeSet 6 false)
  refine Ends.append ?_ (ends_csiNum 4 0x6C (by decide) (by decide))
  exact (ends_escSeq 0x5C (by decide)).append (ends_modeSet 1049 false)

theorem ends_cursorAnsi (v : Vt) : Ends (cursorAnsi v) := by
  unfold cursorAnsi
  exact Ends.ite (ends_csiNum2 _ _ 0x48 (by decide) (by decide))
    (ends_csiNum2 _ _ 0x48 (by decide) (by decide))

theorem ends_cursorPendingAnsi (v : Vt) : Ends (Linger.Core.Render.cursorPendingAnsi v) := by
  unfold cursorPendingAnsi
  apply Ends.ite
  · refine Ends.append ?_ (ends_penSgr _)
    refine Ends.append ?_ (ends_charsetAnsi _)
    refine Ends.append ?_ (ends_irm _)
    refine Ends.append ?_ (ends_modeSet 7 _)
    refine Ends.append ?_ (ends_pendingAnsi _ _ _ _ _)
    refine Ends.append ?_ (Ends.text (bs := [0x0F]) (by decide))
    refine Ends.append ?_ (ends_escCharset 0x29 0x42 (by decide) (by decide) (by decide))
    refine Ends.append ?_ (ends_escCharset 0x28 0x42 (by decide) (by decide) (by decide))
    exact (ends_modeSet 7 true).append (ends_irm false)
  · exact Ends.nil

theorem ends_restoreBody (v : Vt) : Ends (restoreBody v) := by
  unfold restoreBody
  refine Ends.append ?_ (ends_penSgr v.pen)
  refine Ends.append ?_ (ends_charsetAnsi v)
  refine Ends.append ?_ (ends_modesAnsi v)
  refine Ends.append ?_ (ends_titleAnsi v)
  refine Ends.append ?_ (ends_savedPendingAnsi v)
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
  exact ((ends_restoreBody v).append (ends_cursorAnsi v)).append (ends_cursorPendingAnsi v)

/-- The operational form: a fresh emulator fed `restore v` is ready for
the application's next byte. -/
theorem restore_leaves_ground (v : Vt) (cols rows : Nat) :
    (((Vt.init cols rows).feed (restore v)).pstate = .ground) :=
  ends_restore v (Vt.init cols rows) rfl

/-! ### No half-decoded character either

The cursor's `CSI … H` clears any pending UTF-8 sequence. If the optional
deferred-wrap stage runs afterward, its final `penSgr` clears the decoder
again after reprinting the margin cell and marks. Both complete CSI tails
start with ESC and contain no UTF-8 lead bytes, so the result is independent
of the preceding repaint's encodings.
-/

theorem paramBytes_lt_C0 {bs : Bytes} (h : ParamBytes bs) : ∀ b ∈ bs, b < 0xC0 := by
  intro b hb; have := h b hb; grind

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
    grind

theorem u8_zero_after_penSgr (p : Pen) (w : Vt) : (w.feed (penSgr p)).u8need = 0 := by
  have hs (codes : List Nat) (w : Vt) : (w.feed (sgrOf codes)).u8need = 0 :=
    u8_zero_after_csi _ _ (paramBytes_joinSemi codes) (by decide) w
  have hc (c : Color) (fg : Bool) (w : Vt) (hu : w.u8need = 0) :
      (w.feed (sgrColorSeq c fg)).u8need = 0 := by
    unfold sgrColorSeq
    split
    · exact hu
    · exact hs _ _
  unfold penSgr
  rw [Good.feed_append, Good.feed_append]
  exact hc _ _ _ (hc _ _ _ (hs _ _))

theorem u8_zero_after_cursorPendingAnsi (v w : Vt) (hu : w.u8need = 0) :
    (w.feed (cursorPendingAnsi v)).u8need = 0 := by
  unfold cursorPendingAnsi
  split
  · rw [Good.feed_append]
    exact u8_zero_after_penSgr _ _
  · exact hu

/-- **§Replay (parser half, complete).** A fresh emulator fed a whole
restore stream is *quiesced*: parser in `ground`, no half-decoded
character. So a reattaching client is left ready for the application's
next byte, and a checkpoint taken straight after a restore is exact. -/
theorem restore_quiesced (v : Vt) (cols rows : Nat) :
    (((Vt.init cols rows).feed (restore v)).pstate = .ground)
      ∧ (((Vt.init cols rows).feed (restore v)).u8need = 0) := by
  refine ⟨restore_leaves_ground v cols rows, ?_⟩
  unfold restore
  rw [Good.feed_append]
  apply u8_zero_after_cursorPendingAnsi
  rw [Good.feed_append]
  unfold cursorAnsi
  split
  all_goals
    (unfold csiNum2
     exact u8_zero_after_csi _ 0x48 (paramBytes_digits2 _ _) (by decide) _)

end Linger.Core.Render
