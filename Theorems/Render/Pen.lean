import Theorems.Render.Quiet
/-! # §Replay stage 3d — the pen round trip, and one glyph placed

The value half begins here: `applySgr` inverts `penSgr`'s encoding (semantic half),
the accumulator delivers the numbers the encoder wrote (parser half), and one glyph
lands in one cell. Split out of `Theorems/Render.lean`. -/

namespace Linger.Core.Render

open Linger.Core.Vt

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
-- not `private`: the Row rung uses it too (it was private only because they
-- both used to live in one file).
theorem print_quiet {v : Vt} (c : Char) (hg : v.pstate = .ground) (hu : v.u8need = 0)
    (ha : v.u8acc = 0) :
    (v.print c).pstate = .ground ∧ (v.print c).u8need = 0 ∧ (v.print c).u8acc = 0 :=
  ⟨by rw [Linger.Core.Vt.ps_print]; exact hg,
   by rw [Linger.Core.Vt.un_print]; exact hu,
   by rw [Linger.Core.Vt.ua_print]; exact ha⟩

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
    rw [Linger.Core.Vt.ps_carriageReturn]; exact hg
  have hu2 : v.carriageReturn.u8need = 0 := by
    rw [Linger.Core.Vt.un_carriageReturn]; exact hu
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
numbers in the first place (step 1 of specs/archive/grid-fidelity.md). This half is
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
step 1 of specs/archive/grid-fidelity.md. -/
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
proof. `Renderable` (step 1 of specs/archive/grid-fidelity.md) is where it belongs.
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

/-- Projecting `dims`, proved on a variable so that no call site has to reduce the
state it is applied to. -/
theorem dims_fst (w : Vt) : (dims w).1 = w.cols := rfl

theorem dims_snd (w : Vt) : (dims w).2 = w.rows := rfl

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
  -- `dims` is a pair, and projecting it with `rfl` at this type forces the whole
  -- `feed` to whnf; the two accessor lemmas above are the same fact proved once on a
  -- variable, which is why they exist
  have hdc : ((Vt.init v.cols v.rows).feed (restoreBody v)).cols = v.cols := by
    rw [← dims_fst ((Vt.init v.cols v.rows).feed (restoreBody v)), hd]
    exact hic
  have hdr : ((Vt.init v.cols v.rows).feed (restoreBody v)).rows = v.rows := by
    rw [← dims_snd ((Vt.init v.cols v.rows).feed (restoreBody v)), hd]
    exact hir
  obtain ⟨hx, hy⟩ := cup_places_cursor (v.cursor.y + 1) (v.cursor.x + 1) hpg
    (by omega) (by omega)
    (by have := hgood.curY; have := hgood.rowsLe; omega)
    (by have := hgood.curX; have := hgood.colsLe; omega)
    (by rw [hdr]; simpa using hgood.curY)
    (by rw [hdc]; simpa using hgood.curX) hpo
  exact ⟨by simpa using hx, by simpa using hy⟩

end Linger.Core.Render
