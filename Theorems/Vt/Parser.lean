module

public import Theorems.Vt.State
import all Theorems.Vt.State

namespace Linger.Core.Vt

/-! ## No half-decoded character (`u8need`) survives an operation

The companion of the `pstate` layer above. Same staged shape, same
reason: §Replay needs to know that a restore stream leaves the emulator
holding no partial UTF-8 sequence, so a checkpoint taken right after a
reattach is exact and the next byte from the application is read as
itself.

Stated as *preservation* equations (`… .u8need = v.u8need`) rather than
as implications, so they can be used as guided `simp` rewrites — an
`exact` against the wrong branch whnf's the print chain to death.
`stepEsc` is the one exception: its `RIS` branch rebuilds through
`Vt.init`, where `u8need` is zero by construction, so that one is stated
in "stays zero" form.
-/

/-- A fold of `u8need`-preserving steps preserves it. One lemma for every
`List.range` fold in the erase/scroll/insert operations. -/
theorem un_foldl {α : Type} (f : Vt → α → Vt) (hf : ∀ v a, (f v a).u8need = v.u8need) :
    ∀ (l : List α) (v : Vt), (l.foldl f v).u8need = v.u8need := fun l v =>
  invariant_foldl (fun w => w.u8need = v.u8need) f (fun w a hw => (hf w a).trans hw) l v rfl

theorem un_clearPending (v : Vt) : v.clearPending.u8need = v.u8need := by rfl

theorem un_carriageReturn (v : Vt) : v.carriageReturn.u8need = v.u8need := by rfl

theorem un_moveTo (v : Vt) (x y : Nat) : (v.moveTo x y).u8need = v.u8need := by rfl

theorem un_moveRel (v : Vt) (dx dy : Int) : (v.moveRel dx dy).u8need = v.u8need := by rfl

theorem un_setCol (v : Vt) (x : Nat) : (v.setCol x).u8need = v.u8need := by rfl

theorem un_eraseRowSpan (v : Vt) (y a b : Nat) : (v.eraseRowSpan y a b).u8need = v.u8need := by rfl

theorem un_scrollDownIn (v : Vt) (t b : Nat) : (v.scrollDownIn t b).u8need = v.u8need := by rfl

theorem un_deleteChars (v : Vt) (n : Nat) : (v.deleteChars n).u8need = v.u8need := by rfl

theorem un_insertChars (v : Vt) (n : Nat) : (v.insertChars n).u8need = v.u8need := by rfl

theorem un_applySgr (v : Vt) (ps : List (Nat × Bool)) : (v.applySgr ps).u8need = v.u8need := by rfl

theorem un_backTab (v : Vt) : v.backTab.u8need = v.u8need := by rfl

theorem un_scrollUpIn (v : Vt) (t b : Nat) (a : Bool) : (v.scrollUpIn t b a).u8need = v.u8need := by
  unfold Vt.scrollUpIn; dsimp only; split <;> rfl

theorem un_scrollUp (v : Vt) : v.scrollUp.u8need = v.u8need := un_scrollUpIn _ _ _ _

theorem un_scrollDown (v : Vt) : v.scrollDown.u8need = v.u8need := un_scrollDownIn _ _ _

theorem un_lineFeed (v : Vt) : v.lineFeed.u8need = v.u8need := by rw [frame_lineFeed]

theorem un_reverseIndex (v : Vt) : v.reverseIndex.u8need = v.u8need := by rw [frame_reverseIndex]

theorem un_backspace (v : Vt) : v.backspace.u8need = v.u8need := by
  unfold Vt.backspace; split <;> rfl

theorem un_tab (v : Vt) : v.tab.u8need = v.u8need := by
  unfold Vt.tab; dsimp only; exact un_clearPending v

theorem un_eraseChars (v : Vt) (n : Nat) : (v.eraseChars n).u8need = v.u8need :=
  un_eraseRowSpan _ _ _ _

theorem un_eraseLine (v : Vt) (m : Nat) : (v.eraseLine m).u8need = v.u8need := by
  rw [frame_eraseLine]

theorem un_eraseScreen (v : Vt) (m : Nat) : (v.eraseScreen m).u8need = v.u8need := by
  rw [frame_eraseScreen]

theorem modes_eraseScreen (v : Vt) (m : Nat) : (v.eraseScreen m).modes = v.modes := by
  rw [frame_eraseScreen]

theorem un_insertLines (v : Vt) (n : Nat) : (v.insertLines n).u8need = v.u8need := by
  rw [frame_insertLines]

theorem un_deleteLines (v : Vt) (n : Nat) : (v.deleteLines n).u8need = v.u8need := by
  rw [frame_deleteLines]

theorem un_enterAlt (v : Vt) (s : Bool) : (v.enterAlt s).u8need = v.u8need := by
  unfold Vt.enterAlt; dsimp only; split <;> rfl

theorem un_leaveAlt (v : Vt) (s : Bool) : (v.leaveAlt s).u8need = v.u8need := by
  unfold Vt.leaveAlt; split <;> rfl

/-- **`setMode` commutes with a parser-state change.** `csiFinish` dispatches on a receiver
whose `pstate` it has already moved to `.csi s`, then forces `.ground`; the mode operation
itself reads no parser state, so the two can be separated — which is what turns the CSI walk
into a *state* equation rather than a field-by-field one. -/
theorem setMode_pstate (v : Vt) (p : PState) (priv : Bool) (n : Nat) (on : Bool) :
    ({ v with pstate := p }).setMode priv n on = { v.setMode priv n on with pstate := p } := by
  unfold Vt.setMode Vt.enterAlt Vt.leaveAlt Vt.moveTo
  dsimp only
  repeat' split
  all_goals rfl

theorem un_setMode (v : Vt) (priv : Bool) (n : Nat) (on : Bool) :
    (v.setMode priv n on).u8need = v.u8need := by
  unfold Vt.setMode
  repeat' split
  all_goals try simp only [un_moveTo, un_enterAlt, un_leaveAlt]
  all_goals rfl

theorem un_setModes (v : Vt) (priv : Bool) (ps : List (Nat × Bool)) (on : Bool) :
    (v.setModes priv ps on).u8need = v.u8need :=
  un_foldl (fun w (p : Nat × Bool) => w.setMode priv p.1 on) (fun w p => un_setMode w priv p.1 on)
    ps v

theorem un_print (v : Vt) (c : Char) : (v.print c).u8need = v.u8need :=
  congrArg OffScreen.u8need (off_print v c)

theorem un_acceptChar (v : Vt) (n : Nat) : (v.acceptChar n).u8need = v.u8need := by
  unfold Vt.acceptChar; split <;> exact un_print _ _

theorem un_ctl (v : Vt) (b : UInt8) : (v.ctl b).u8need = v.u8need := by
  unfold Vt.ctl
  repeat' split
  all_goals
    with_reducible
      first
      | exact un_backspace v
      | exact un_tab v
      | exact un_lineFeed v
      | exact un_carriageReturn v
      | rfl

theorem un_csiDispatch (v : Vt) (s : CsiState) (final : UInt8) :
    (v.csiDispatch s final).u8need = v.u8need := by
  fun_cases Vt.csiDispatch v s final
  all_goals
    try
      simp only [un_insertChars, un_moveRel, un_carriageReturn, un_setCol, un_moveTo,
        un_eraseScreen, un_eraseLine, un_insertLines, un_deleteLines, un_deleteChars, un_eraseChars,
        un_setModes, un_applySgr]
  all_goals
    with_reducible
      first
      | rfl
      | exact un_foldl _ (fun w _ => un_tab w) _ _
      | exact un_foldl _ (fun w _ => un_scrollUp w) _ _
      | exact un_foldl _ (fun w _ => un_scrollDown w) _ _
      | exact un_foldl _ (fun w _ => un_backTab w) _ _

theorem un_csiFinish (v : Vt) (s : CsiState) (final : UInt8) :
    (v.csiFinish s final).u8need = v.u8need := by
  unfold Vt.csiFinish
  dsimp only
  split <;> exact un_csiDispatch _ _ _

theorem un_stepCsi (v : Vt) (s : CsiState) (b : UInt8) : (v.stepCsi s b).u8need = v.u8need := by
  unfold Vt.stepCsi
  simp only [apply_ite Vt.u8need, un_csiFinish, un_ctl, ite_self]

theorem un_stepEscInter (v : Vt) (i b : UInt8) : (v.stepEscInter i b).u8need = v.u8need := by
  rw [frame_stepEscInter]

theorem un_oscFinish (v : Vt) (acc : Array UInt8) : (v.oscFinish acc).u8need = v.u8need := by
  rw [frame_oscFinish]

theorem un_stepOsc (v : Vt) (acc : Array UInt8) (e : Bool) (b : UInt8) :
    (v.stepOsc acc e b).u8need = v.u8need := by
  unfold Vt.stepOsc
  repeat' split
  all_goals
    with_reducible
      first
      | rfl
      | exact un_oscFinish _ _

theorem un_stepStr (v : Vt) (e : Bool) (b : UInt8) : (v.stepStr e b).u8need = v.u8need := by
  rw [frame_stepStr]

/-- `stepEsc` in "stays zero" form: `RIS` rebuilds through `Vt.init`,
which has no pending sequence by construction. -/
theorem uz_stepEsc {v : Vt} (b : UInt8) (h : v.u8need = 0) : (v.stepEsc b).u8need = 0 := by
  unfold Vt.stepEsc
  dsimp only
  repeat' split
  all_goals try simp only [un_lineFeed, un_carriageReturn, un_reverseIndex]
  all_goals
    first
    | exact h
    | rfl

/-- `stepGround` keeps `u8need` at zero for any byte that is not a
multi-byte UTF-8 lead (≥ 0xC0): a lead byte is exactly what *starts* a
pending sequence. -/
theorem uz_stepGround {v : Vt} (b : UInt8) (hb : b < 0xC0) (h : v.u8need = 0) :
    (v.stepGround b).u8need = 0 := by
  unfold Vt.stepGround
  repeat' split
  all_goals try simp only [un_ctl, un_acceptChar]
  all_goals
    with_reducible
      first
      | exact h
      | rfl
      | (simp [h])
      | ( exfalso
          simp only [UInt8.lt_iff_toNat_lt, Bool.not_eq_true, decide_eq_false_iff_not,
            decide_eq_true_eq, Nat.not_lt, show ((0x20 : UInt8)).toNat = 32 from rfl,
            show ((0x80 : UInt8)).toNat = 128 from rfl, show ((0xC0 : UInt8)).toNat = 192 from rfl,
            show ((0xE0 : UInt8)).toNat = 224 from rfl, show ((0xF0 : UInt8)).toNat = 240 from rfl,
            show ((0xF8 : UInt8)).toNat = 248 from rfl] at *
          omega)

/-! ### The `u8acc` twin of the layer above

`Matches`/`Walking` carry `u8acc = 0`, because `utf8_feed` needs it to decode a *multi-byte*
glyph (`reset_u8`). A CSI's final byte forces `u8need = 0` but says nothing about `u8acc`:
`abortUtf8` zeroes the accumulator only when a sequence was actually pending. So the paint's
entry state needs its own argument, and this is it — the same shape as the `u8need` family,
`rfl` for everything that is a record update and "stays zero" where `RIS` rebuilds. -/

theorem ua_foldl {α : Type} (f : Vt → α → Vt) (hf : ∀ v a, (f v a).u8acc = v.u8acc) :
    ∀ (l : List α) (v : Vt), (l.foldl f v).u8acc = v.u8acc := fun l v =>
  invariant_foldl (fun w => w.u8acc = v.u8acc) f (fun w a hw => (hf w a).trans hw) l v rfl

theorem ua_clearPending (v : Vt) : v.clearPending.u8acc = v.u8acc := by rfl

theorem ua_carriageReturn (v : Vt) : v.carriageReturn.u8acc = v.u8acc := by rfl

theorem ua_moveTo (v : Vt) (x y : Nat) : (v.moveTo x y).u8acc = v.u8acc := by rfl

theorem ua_moveRel (v : Vt) (dx dy : Int) : (v.moveRel dx dy).u8acc = v.u8acc := by rfl

theorem ua_setCol (v : Vt) (x : Nat) : (v.setCol x).u8acc = v.u8acc := by rfl

theorem ua_eraseRowSpan (v : Vt) (y a b : Nat) : (v.eraseRowSpan y a b).u8acc = v.u8acc := by rfl

theorem ua_scrollDownIn (v : Vt) (t b : Nat) : (v.scrollDownIn t b).u8acc = v.u8acc := by rfl

theorem ua_deleteChars (v : Vt) (n : Nat) : (v.deleteChars n).u8acc = v.u8acc := by rfl

theorem ua_insertChars (v : Vt) (n : Nat) : (v.insertChars n).u8acc = v.u8acc := by rfl

theorem ua_applySgr (v : Vt) (ps : List (Nat × Bool)) : (v.applySgr ps).u8acc = v.u8acc := by rfl

theorem ua_backTab (v : Vt) : v.backTab.u8acc = v.u8acc := by rfl

theorem ua_scrollUpIn (v : Vt) (t b : Nat) (a : Bool) : (v.scrollUpIn t b a).u8acc = v.u8acc := by
  unfold Vt.scrollUpIn; dsimp only; split <;> rfl

theorem ua_scrollUp (v : Vt) : v.scrollUp.u8acc = v.u8acc := ua_scrollUpIn _ _ _ _

theorem ua_scrollDown (v : Vt) : v.scrollDown.u8acc = v.u8acc := ua_scrollDownIn _ _ _

theorem ua_lineFeed (v : Vt) : v.lineFeed.u8acc = v.u8acc := by rw [frame_lineFeed]

theorem ua_reverseIndex (v : Vt) : v.reverseIndex.u8acc = v.u8acc := by rw [frame_reverseIndex]

theorem ua_backspace (v : Vt) : v.backspace.u8acc = v.u8acc := by
  unfold Vt.backspace; split <;> rfl

theorem ua_tab (v : Vt) : v.tab.u8acc = v.u8acc := by
  unfold Vt.tab; dsimp only; exact ua_clearPending v

theorem ua_eraseChars (v : Vt) (n : Nat) : (v.eraseChars n).u8acc = v.u8acc :=
  ua_eraseRowSpan _ _ _ _

theorem ua_eraseLine (v : Vt) (m : Nat) : (v.eraseLine m).u8acc = v.u8acc := by rw [frame_eraseLine]

theorem ua_eraseScreen (v : Vt) (m : Nat) : (v.eraseScreen m).u8acc = v.u8acc := by
  rw [frame_eraseScreen]

theorem ua_insertLines (v : Vt) (n : Nat) : (v.insertLines n).u8acc = v.u8acc := by
  rw [frame_insertLines]

theorem ua_deleteLines (v : Vt) (n : Nat) : (v.deleteLines n).u8acc = v.u8acc := by
  rw [frame_deleteLines]

theorem ua_enterAlt (v : Vt) (s : Bool) : (v.enterAlt s).u8acc = v.u8acc := by
  unfold Vt.enterAlt; dsimp only; split <;> rfl

theorem ua_leaveAlt (v : Vt) (s : Bool) : (v.leaveAlt s).u8acc = v.u8acc := by
  unfold Vt.leaveAlt; split <;> rfl

theorem ua_setMode (v : Vt) (priv : Bool) (n : Nat) (on : Bool) :
    (v.setMode priv n on).u8acc = v.u8acc := by
  unfold Vt.setMode
  repeat' split
  all_goals try simp only [ua_moveTo, ua_enterAlt, ua_leaveAlt]
  all_goals rfl

theorem ua_setModes (v : Vt) (priv : Bool) (ps : List (Nat × Bool)) (on : Bool) :
    (v.setModes priv ps on).u8acc = v.u8acc :=
  ua_foldl (fun w (p : Nat × Bool) => w.setMode priv p.1 on) (fun w p => ua_setMode w priv p.1 on)
    ps v

theorem ua_ctl (v : Vt) (b : UInt8) : (v.ctl b).u8acc = v.u8acc := by
  unfold Vt.ctl
  repeat' split
  all_goals
    with_reducible
      first
      | exact ua_backspace v
      | exact ua_tab v
      | exact ua_lineFeed v
      | exact ua_carriageReturn v
      | rfl

theorem ua_csiDispatch (v : Vt) (s : CsiState) (final : UInt8) :
    (v.csiDispatch s final).u8acc = v.u8acc := by
  fun_cases Vt.csiDispatch v s final
  all_goals
    try
      simp only [ua_insertChars, ua_moveRel, ua_carriageReturn, ua_setCol, ua_moveTo,
        ua_eraseScreen, ua_eraseLine, ua_insertLines, ua_deleteLines, ua_deleteChars, ua_eraseChars,
        ua_setModes, ua_applySgr]
  all_goals
    with_reducible
      first
      | rfl
      | exact ua_foldl _ (fun w _ => ua_tab w) _ _
      | exact ua_foldl _ (fun w _ => ua_scrollUp w) _ _
      | exact ua_foldl _ (fun w _ => ua_scrollDown w) _ _
      | exact ua_foldl _ (fun w _ => ua_backTab w) _ _

theorem ua_csiFinish (v : Vt) (s : CsiState) (final : UInt8) :
    (v.csiFinish s final).u8acc = v.u8acc := by
  unfold Vt.csiFinish
  dsimp only
  split <;> exact ua_csiDispatch _ _ _

theorem ua_stepCsi (v : Vt) (s : CsiState) (b : UInt8) : (v.stepCsi s b).u8acc = v.u8acc := by
  unfold Vt.stepCsi
  simp only [apply_ite Vt.u8acc, ua_csiFinish, ua_ctl, ite_self]

theorem ua_stepEscInter (v : Vt) (i b : UInt8) : (v.stepEscInter i b).u8acc = v.u8acc := by
  rw [frame_stepEscInter]

theorem ua_oscFinish (v : Vt) (acc : Array UInt8) : (v.oscFinish acc).u8acc = v.u8acc := by
  rw [frame_oscFinish]

theorem ua_stepOsc (v : Vt) (acc : Array UInt8) (e : Bool) (b : UInt8) :
    (v.stepOsc acc e b).u8acc = v.u8acc := by
  unfold Vt.stepOsc
  repeat' split
  all_goals
    with_reducible
      first
      | rfl
      | exact ua_oscFinish _ _

theorem ua_stepStr (v : Vt) (e : Bool) (b : UInt8) : (v.stepStr e b).u8acc = v.u8acc := by
  rw [frame_stepStr]

/-- `stepEsc` in "stays zero" form: `RIS` rebuilds through `Vt.init`,
which has no pending sequence by construction. -/
theorem uaz_stepEsc {v : Vt} (b : UInt8) (h : v.u8acc = 0) : (v.stepEsc b).u8acc = 0 := by
  unfold Vt.stepEsc
  dsimp only
  repeat' split
  all_goals try simp only [ua_lineFeed, ua_carriageReturn, ua_reverseIndex]
  all_goals
    first
    | exact h
    | rfl

/-- **`stepEsc` on the decoder pair: unchanged, or both cleared.** The honest statement — the
backwards direction is *false*, because `RIS` rebuilds through `Vt.init` and so reports zero
whatever the receiver held. This is what `U8Ok` needs, and stating it as one disjunction is
what lets every branch fall to a uniform script. -/
theorem u8pair_stepEsc (v : Vt) (b : UInt8) :
    ((v.stepEsc b).u8need = v.u8need ∧ (v.stepEsc b).u8acc = v.u8acc) ∨
      ((v.stepEsc b).u8need = 0 ∧ (v.stepEsc b).u8acc = 0) := by
  unfold Vt.stepEsc
  dsimp only
  repeat' split
  all_goals
    with_reducible
      first
      | exact Or.inl ⟨rfl, rfl⟩
      | exact Or.inr ⟨rfl, rfl⟩
      | exact Or.inl ⟨un_lineFeed _, ua_lineFeed _⟩
      |
        exact
          Or.inl
            ⟨(un_lineFeed _).trans (un_carriageReturn _),
              (ua_lineFeed _).trans (ua_carriageReturn _)⟩
      | exact Or.inl ⟨un_reverseIndex _, ua_reverseIndex _⟩

/-- `stepGround` keeps `u8acc` at zero for any byte that is not a
multi-byte UTF-8 lead (≥ 0xC0): a lead byte is exactly what *starts* a
pending sequence. -/
theorem uaz_stepGround {v : Vt} (b : UInt8) (hb : b < 0x80) (h : v.u8acc = 0) :
    (v.stepGround b).u8acc = 0 := by
  unfold Vt.stepGround
  repeat' split
  all_goals try simp only [ua_ctl, ua_acceptChar]
  all_goals
    with_reducible
      first
      | exact h
      | rfl
      | (simp [h])
      | ( exfalso
          simp only [UInt8.lt_iff_toNat_lt, Bool.not_eq_true, decide_eq_false_iff_not,
            decide_eq_true_eq, Nat.not_lt, show ((0x20 : UInt8)).toNat = 32 from rfl,
            show ((0x80 : UInt8)).toNat = 128 from rfl, show ((0xC0 : UInt8)).toNat = 192 from rfl,
            show ((0xE0 : UInt8)).toNat = 224 from rfl, show ((0xF0 : UInt8)).toNat = 240 from rfl,
            show ((0xF8 : UInt8)).toNat = 248 from rfl] at *
          omega)

/-- **One step keeps `u8acc` at zero**, in any parser state, for any byte that is not a
UTF-8 lead byte. `abortUtf8` either zeroes the accumulator (a sequence was pending) or is
the identity (none was, and it was already zero) — so either way it stays zero. -/
theorem uaz_step {v : Vt} (b : UInt8) (hb : b < 0x80) (h : v.u8acc = 0) : (v.step b).u8acc = 0 := by
  have hab : (v.abortUtf8 b).u8acc = 0 := by
    unfold Vt.abortUtf8
    split
    · rfl
    · exact h
  unfold Vt.step
  dsimp only
  split
  all_goals try simp only [ua_stepEscInter, ua_stepCsi, ua_stepOsc, ua_stepStr]
  all_goals
    with_reducible
      first
      | exact hab
      | exact uaz_stepGround _ hb hab
      | exact uaz_stepEsc _ hab

/-- One step keeps `u8need` at zero, in any parser state, for any byte
that is not a UTF-8 lead byte. -/
theorem uz_step {v : Vt} (b : UInt8) (hb : b < 0xC0) (h : v.u8need = 0) :
    (v.step b).u8need = 0 := by
  have hab : (v.abortUtf8 b).u8need = 0 := by
    unfold Vt.abortUtf8
    split
    · rfl
    · exact h
  unfold Vt.step
  dsimp only
  split
  all_goals try simp only [un_stepEscInter, un_stepCsi, un_stepOsc, un_stepStr]
  all_goals
    with_reducible
      first
      | exact hab
      | exact uz_stepGround _ hb hab
      | exact uz_stepEsc _ hab

theorem ascii_lt_c0 {b : UInt8} (h : b < 0x80) : b < 0xC0 := by
  rw [UInt8.lt_iff_toNat_lt] at h ⊢
  rw [show ((0x80 : UInt8)).toNat = 128 from rfl] at h
  rw [show ((0xC0 : UInt8)).toNat = 192 from rfl]
  omega

/-- **An all-ASCII stream leaves the decoder quiesced.** Every byte the restore
emits is ASCII except the glyphs themselves, so this is what carries `u8need = 0 ∧ u8acc = 0`
across the prologue, the SGR reset and the clear — the entry state the paint assumes. -/
theorem uaz_feed :
    ∀ (bs : List UInt8) {v : Vt},
      (∀ b ∈ bs, b < 0x80) →
        v.u8need = 0 → v.u8acc = 0 → (v.feed bs).u8need = 0 ∧ (v.feed bs).u8acc = 0
  | [], _, _, hn, ha => ⟨hn, ha⟩
  | b :: bs, v, hb, hn, ha => by
    rw [feed_cons]
    exact
      uaz_feed bs (fun x hx => hb x (List.mem_cons_of_mem b hx))
        (uz_step b (ascii_lt_c0 (hb b (List.mem_cons_self))) hn)
        (uaz_step b (hb b (List.mem_cons_self)) ha)

/-- Feeding ESC from ANY state (pending UTF-8 or not) leaves none: the
abort fires, and no ESC branch of any parser state re-arms it. -/
theorem uz_step_esc (v : Vt) : (v.step 0x1B).u8need = 0 := by
  have hab : (v.abortUtf8 0x1B).u8need = 0 := by
    rcases Nat.eq_zero_or_pos v.u8need with hz | hpos
    · unfold Vt.abortUtf8
      split
      · rfl
      · exact hz
    · have hg : (v.u8need > 0 && ((0x1B : UInt8) < 0x80 || (0x1B : UInt8) ≥ 0xC0)) = true := by
        simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
        exact ⟨hpos, Or.inl (by decide)⟩
      unfold Vt.abortUtf8
      rw [ite_eq_left hg]
  unfold Vt.step
  dsimp only
  split
  all_goals try simp only [un_stepEscInter, un_stepCsi, un_stepOsc, un_stepStr]
  all_goals
    with_reducible
      first
      | exact hab
      | exact uz_stepGround _ (by decide) hab
      | exact uz_stepEsc _ hab

/-- A run of non-lead bytes keeps `u8need` at zero. -/
theorem uz_feed :
    ∀ (bs : List UInt8) (v : Vt), (∀ b ∈ bs, b < 0xC0) → v.u8need = 0 → (v.feed bs).u8need = 0
  | [], _, _, h => h
  | x :: xs, v, hb, h => by
    rw [feed_cons]
    exact uz_feed xs _ (fun b hm => hb b (by simp [hm])) (uz_step x (hb x (by simp)) h)

/-! ## The grid keeps its dimensions

The third invariance layer, and the one the step-4 notes recorded as
open: "every operation preserves `cols`/`rows` syntactically except RIS
(which re-derives them via `clampDim`, identity under `Good`), but
stating it needs per-op lemmas". Here they are — the same staged,
equation-form shape as the `pstate` and `u8need` layers, over the pair
`dims v = (v.cols, v.rows)` so one lemma covers both fields.

Needed because §Replay's cursor claim goes through `moveTo`, which clamps
against the *replayed* state's dimensions: `w.cursor = v.cursor` is only
meaningful once `w.cols = v.cols`.

`RIS` is the one conditional case (hence `dims_step` takes `Good v`):
`Vt.init` re-clamps, and `Good` is exactly what makes that the identity.
-/

/-- Grid dimensions as a pair, so one lemma per operation covers both. -/
def dims (v : Vt) : Nat × Nat := (v.cols, v.rows)

theorem dims_foldl {α : Type} (f : Vt → α → Vt) (hf : ∀ v a, dims (f v a) = dims v) :
    ∀ (l : List α) (v : Vt), dims (l.foldl f v) = dims v := fun l v =>
  invariant_foldl (fun w => dims w = dims v) f (fun w a hw => (hf w a).trans hw) l v rfl

theorem dims_clearPending (v : Vt) : dims v.clearPending = dims v := by rfl

theorem dims_carriageReturn (v : Vt) : dims v.carriageReturn = dims v := by rfl

theorem dims_moveTo (v : Vt) (x y : Nat) : dims (v.moveTo x y) = dims v := by rfl

theorem dims_moveRel (v : Vt) (dx dy : Int) : dims (v.moveRel dx dy) = dims v := by rfl

theorem dims_setCol (v : Vt) (x : Nat) : dims (v.setCol x) = dims v := by rfl

theorem dims_eraseRowSpan (v : Vt) (y a b : Nat) : dims (v.eraseRowSpan y a b) = dims v := by rfl

theorem dims_scrollDownIn (v : Vt) (t b : Nat) : dims (v.scrollDownIn t b) = dims v := by rfl

theorem dims_deleteChars (v : Vt) (n : Nat) : dims (v.deleteChars n) = dims v := by rfl

theorem dims_insertChars (v : Vt) (n : Nat) : dims (v.insertChars n) = dims v := by rfl

theorem dims_applySgr (v : Vt) (ps : List (Nat × Bool)) : dims (v.applySgr ps) = dims v := by rfl

theorem dims_backTab (v : Vt) : dims v.backTab = dims v := by rfl

theorem dims_scrollUpIn (v : Vt) (t b : Nat) (a : Bool) : dims (v.scrollUpIn t b a) = dims v := by
  unfold Vt.scrollUpIn; dsimp only; split <;> rfl

theorem dims_scrollUp (v : Vt) : dims v.scrollUp = dims v := dims_scrollUpIn _ _ _ _

theorem dims_scrollDown (v : Vt) : dims v.scrollDown = dims v := dims_scrollDownIn _ _ _

theorem dims_lineFeed (v : Vt) : dims v.lineFeed = dims v := by
  rw [frame_lineFeed]
  rfl

theorem dims_reverseIndex (v : Vt) : dims v.reverseIndex = dims v := by
  rw [frame_reverseIndex]
  rfl

theorem dims_backspace (v : Vt) : dims v.backspace = dims v := by
  unfold Vt.backspace; split <;> rfl

theorem dims_tab (v : Vt) : dims v.tab = dims v := by
  unfold Vt.tab; dsimp only; exact dims_clearPending v

theorem dims_eraseChars (v : Vt) (n : Nat) : dims (v.eraseChars n) = dims v :=
  dims_eraseRowSpan _ _ _ _

theorem dims_eraseLine (v : Vt) (m : Nat) : dims (v.eraseLine m) = dims v := by
  rw [frame_eraseLine]
  rfl

theorem dims_eraseScreen (v : Vt) (m : Nat) : dims (v.eraseScreen m) = dims v := by
  rw [frame_eraseScreen]
  rfl

theorem dims_insertLines (v : Vt) (n : Nat) : dims (v.insertLines n) = dims v := by
  rw [frame_insertLines]
  rfl

theorem dims_deleteLines (v : Vt) (n : Nat) : dims (v.deleteLines n) = dims v := by
  rw [frame_deleteLines]
  rfl

theorem dims_enterAlt (v : Vt) (s : Bool) : dims (v.enterAlt s) = dims v := by
  unfold Vt.enterAlt; dsimp only; split <;> rfl

theorem dims_leaveAlt (v : Vt) (s : Bool) : dims (v.leaveAlt s) = dims v := by
  unfold Vt.leaveAlt; split <;> rfl

theorem dims_setMode (v : Vt) (priv : Bool) (n : Nat) (on : Bool) :
    dims (v.setMode priv n on) = dims v := by
  unfold Vt.setMode
  repeat' split
  all_goals try simp only [dims_moveTo, dims_enterAlt, dims_leaveAlt]
  all_goals rfl

theorem dims_setModes (v : Vt) (priv : Bool) (ps : List (Nat × Bool)) (on : Bool) :
    dims (v.setModes priv ps on) = dims v :=
  dims_foldl (fun w (p : Nat × Bool) => w.setMode priv p.1 on)
    (fun w p => dims_setMode w priv p.1 on) ps v

theorem dims_print (v : Vt) (c : Char) : dims (v.print c) = dims v :=
  congrArg (fun s => (s.cols, s.rows)) (off_print v c)

theorem dims_acceptChar (v : Vt) (n : Nat) : dims (v.acceptChar n) = dims v := by
  unfold Vt.acceptChar; split <;> exact dims_print _ _

theorem dims_ctl (v : Vt) (b : UInt8) : dims (v.ctl b) = dims v := by
  unfold Vt.ctl
  repeat' split
  all_goals
    first
    | exact dims_backspace v
    | exact dims_tab v
    | exact dims_lineFeed v
    | exact dims_carriageReturn v
    | rfl

theorem dims_csiDispatch (v : Vt) (s : CsiState) (final : UInt8) :
    dims (v.csiDispatch s final) = dims v := by
  unfold Vt.csiDispatch
  dsimp only
  repeat' split
  all_goals
    try
      simp only [dims_insertChars, dims_moveRel, dims_carriageReturn, dims_setCol, dims_moveTo,
        dims_eraseScreen, dims_eraseLine, dims_insertLines, dims_deleteLines, dims_deleteChars,
        dims_eraseChars, dims_setModes, dims_applySgr]
  all_goals
    first
    | rfl
    | exact dims_foldl _ (fun w _ => dims_tab w) _ _
    | exact dims_foldl _ (fun w _ => dims_scrollUp w) _ _
    | exact dims_foldl _ (fun w _ => dims_scrollDown w) _ _
    | exact dims_foldl _ (fun w _ => dims_backTab w) _ _

theorem dims_csiFinish (v : Vt) (s : CsiState) (final : UInt8) :
    dims (v.csiFinish s final) = dims v := by
  unfold Vt.csiFinish
  dsimp only
  split <;> exact dims_csiDispatch _ _ _

theorem dims_stepCsi (v : Vt) (s : CsiState) (b : UInt8) : dims (v.stepCsi s b) = dims v := by
  unfold Vt.stepCsi
  simp only [apply_ite dims, dims_csiFinish, dims_ctl]
  simp only [dims, ite_self]

theorem dims_stepEscInter (v : Vt) (i b : UInt8) : dims (v.stepEscInter i b) = dims v := by
  rw [frame_stepEscInter]
  rfl

theorem dims_oscFinish (v : Vt) (acc : Array UInt8) : dims (v.oscFinish acc) = dims v := by
  rw [frame_oscFinish]
  rfl

theorem dims_stepOsc (v : Vt) (acc : Array UInt8) (e : Bool) (b : UInt8) :
    dims (v.stepOsc acc e b) = dims v := by
  unfold Vt.stepOsc
  repeat' split
  all_goals
    first
    | rfl
    | exact dims_oscFinish _ _

theorem dims_stepStr (v : Vt) (e : Bool) (b : UInt8) : dims (v.stepStr e b) = dims v := by
  rw [frame_stepStr]
  rfl

theorem dims_abortUtf8 (v : Vt) (b : UInt8) : dims (v.abortUtf8 b) = dims v := by
  unfold Vt.abortUtf8; split <;> rfl

/-- `RIS` rebuilds the state through `Vt.init`, which re-clamps the
dimensions — the identity exactly when they are already in range, which
is what `Good` says. This is the one place the dims layer needs a
hypothesis. -/
theorem dims_stepEsc {v : Vt} (b : UInt8) (h : Good v) : dims (v.stepEsc b) = dims v := by
  have hc : clampDim v.cols = v.cols := (clampDim_eq_self_iff _).2 ⟨h.colsPos, h.colsLe⟩
  have hr : clampDim v.rows = v.rows := (clampDim_eq_self_iff _).2 ⟨h.rowsPos, h.rowsLe⟩
  unfold Vt.stepEsc
  dsimp only
  repeat' split
  all_goals
    first
    | rfl
    | exact dims_lineFeed v
    | exact dims_reverseIndex v
    | exact (dims_lineFeed _).trans (dims_carriageReturn v)
    | (simp only [dims, Vt.init, hc, hr])

theorem dims_stepGround (v : Vt) (b : UInt8) : dims (v.stepGround b) = dims v := by
  fun_cases Vt.stepGround v b
  all_goals try simp only [dims_ctl, dims_acceptChar]
  all_goals rfl

/-- One step keeps the dimensions, for any byte. -/
theorem dims_step {v : Vt} (b : UInt8) (h : Good v) : dims (v.step b) = dims v := by
  have hg : Good (v.abortUtf8 b) := by
    unfold Vt.abortUtf8
    split
    · exact Good.set_u8 0 0 (by omega) h
    · exact h
  have hd : dims (v.abortUtf8 b) = dims v := dims_abortUtf8 v b
  unfold Vt.step
  dsimp only
  split
  all_goals
    try simp only [dims_stepGround, dims_stepEscInter, dims_stepCsi, dims_stepOsc, dims_stepStr]
  all_goals
    with_reducible
      first
      | exact hd
      | exact (dims_stepEsc _ hg).trans hd

/-- **The dims layer's payoff.** No byte stream changes the grid
dimensions: what a client's emulator is told to paint, it paints at the
size it already had. -/
theorem dims_feed : ∀ (bs : List UInt8) {v : Vt}, Good v → dims (v.feed bs) = dims v
  | [], _, _ => rfl
  | x :: xs, v, h => by
    rw [feed_cons]
    exact (dims_feed xs (Good.step x h)).trans (dims_step x h)

/-! ### …and without `Good`, for streams that do not emit `RIS`

`Good` is in the three lemmas above for `RIS` alone (`Vt.init` re-clamps, and
`Good` is what makes that the identity). No linger stream emits `ESC c`, so the
receiver-quantified restore claims can have the height fact for **any** receiver
rather than only a structurally sane one — which matters, because "any receiver"
is the whole point of `Render.SMap`. -/

theorem dims_stepEsc_ne_ris {v : Vt} (b : UInt8) (h : b ≠ 0x63) : dims (v.stepEsc b) = dims v := by
  unfold Vt.stepEsc
  dsimp only
  repeat' split
  all_goals
    first
    | rfl
    | exact dims_lineFeed v
    | exact dims_reverseIndex v
    | exact (dims_lineFeed _).trans (dims_carriageReturn v)
    | exact absurd rfl h

theorem dims_step_ne_ris {v : Vt} (b : UInt8) (h : b ≠ 0x63) : dims (v.step b) = dims v := by
  have hd : dims (v.abortUtf8 b) = dims v := dims_abortUtf8 v b
  unfold Vt.step
  dsimp only
  split
  all_goals
    try simp only [dims_stepGround, dims_stepEscInter, dims_stepCsi, dims_stepOsc, dims_stepStr]
  all_goals
    with_reducible
      first
      | exact hd
      | exact (dims_stepEsc_ne_ris _ h).trans hd

theorem dims_feed_ne_ris :
    ∀ (bs : List UInt8) {v : Vt}, (∀ b ∈ bs, b ≠ 0x63) → dims (v.feed bs) = dims v
  | [], _, _ => rfl
  | x :: xs, v, h => by
    rw [feed_cons]
    exact
      (dims_feed_ne_ris xs (fun b hb => h b (by simp [hb]))).trans
        (dims_step_ne_ris x (h x (by simp)))

/-! ## §Ruler — the tab stops keep pace with the width

Another instance of the invariance-layer recipe the `dims` section above set up, and
the one `Render.restore_tabs_any` needs: its premise `v.tabs.size = v.cols` holds of
every reachable state (`tabsOk_of_liveReachable`, `specs/archive/vt-toolkit.md` Step 3).

`tabs` is written in exactly five places in the whole emulator — `Vt.init` and
`Vt.resize` install `defaultTabs`, `TBC 0`/`HTS` poke one stop with
`setIfInBounds`, and `TBC 3` replaces the array with `Array.replicate v.cols` —
and `cols` in exactly two, `init` and `resize`. So `tsz` is invariant everywhere
except `TBC 3` and `RIS`, and at those two the new size is `cols` by
construction. That is why this layer needs **no `Good`**, unlike `dims`: `RIS`
re-clamps *both* sides through `Vt.init`, so the equation survives a clamp that
moves the value.
-/

/-- A fresh ruler is exactly `cols` long — the `hvtabs` witness for a live session,
and the reason the hypothesis is discharged rather than assumed at every call site
that starts from `Vt.init`. Stated here rather than in `Theorems/Render/Tabs.lean`,
where it used to live, because the invariant below is what generalises it and both
`Vt.init` and `Vt.resize` need it. -/
theorem size_defaultTabs (c : Nat) : (defaultTabs c).size = c := by
  unfold defaultTabs
  simp

/-- Ruler length, as its own projection so one lemma per operation covers it. -/
def tsz (v : Vt) : Nat := v.tabs.size

/-- Transfer along the two projections: an operation that moves neither the
ruler's length nor the width keeps them equal. Every arm of the sweep below is
this lemma plus the pair of equations for its operation. -/
theorem TabsOk.transfer {v w : Vt} (h : TabsOk v) (ht : tsz w = tsz v) (hc : dims w = dims v) :
    TabsOk w := by
  unfold TabsOk tsz at *
  rw [ht, show w.cols = v.cols from congrArg Prod.fst hc]
  exact h

theorem tsz_foldl {α : Type} (f : Vt → α → Vt) (hf : ∀ v a, tsz (f v a) = tsz v) :
    ∀ (l : List α) (v : Vt), tsz (l.foldl f v) = tsz v := fun l v =>
  invariant_foldl (fun w => tsz w = tsz v) f (fun w a hw => (hf w a).trans hw) l v rfl

theorem tsz_clearPending (v : Vt) : tsz v.clearPending = tsz v := by rfl

theorem tsz_carriageReturn (v : Vt) : tsz v.carriageReturn = tsz v := by rfl

theorem tsz_moveTo (v : Vt) (x y : Nat) : tsz (v.moveTo x y) = tsz v := by rfl

theorem tsz_moveRel (v : Vt) (dx dy : Int) : tsz (v.moveRel dx dy) = tsz v := by rfl

theorem tsz_setCol (v : Vt) (x : Nat) : tsz (v.setCol x) = tsz v := by rfl

theorem tsz_eraseRowSpan (v : Vt) (y a b : Nat) : tsz (v.eraseRowSpan y a b) = tsz v := by rfl

theorem tsz_scrollDownIn (v : Vt) (t b : Nat) : tsz (v.scrollDownIn t b) = tsz v := by rfl

theorem tsz_deleteChars (v : Vt) (n : Nat) : tsz (v.deleteChars n) = tsz v := by rfl

theorem tsz_insertChars (v : Vt) (n : Nat) : tsz (v.insertChars n) = tsz v := by rfl

theorem tsz_applySgr (v : Vt) (ps : List (Nat × Bool)) : tsz (v.applySgr ps) = tsz v := by rfl

theorem tsz_backTab (v : Vt) : tsz v.backTab = tsz v := by rfl

theorem tsz_scrollUpIn (v : Vt) (t b : Nat) (a : Bool) : tsz (v.scrollUpIn t b a) = tsz v := by
  unfold Vt.scrollUpIn; dsimp only; split <;> rfl

theorem tsz_scrollUp (v : Vt) : tsz v.scrollUp = tsz v := tsz_scrollUpIn _ _ _ _

theorem tsz_scrollDown (v : Vt) : tsz v.scrollDown = tsz v := tsz_scrollDownIn _ _ _

theorem tsz_lineFeed (v : Vt) : tsz v.lineFeed = tsz v := by
  rw [frame_lineFeed]
  rfl

theorem tsz_reverseIndex (v : Vt) : tsz v.reverseIndex = tsz v := by
  rw [frame_reverseIndex]
  rfl

theorem tsz_backspace (v : Vt) : tsz v.backspace = tsz v := by
  unfold Vt.backspace; split <;> rfl

theorem tsz_tab (v : Vt) : tsz v.tab = tsz v := by
  unfold Vt.tab; dsimp only; exact tsz_clearPending v

theorem tsz_eraseChars (v : Vt) (n : Nat) : tsz (v.eraseChars n) = tsz v := tsz_eraseRowSpan _ _ _ _

theorem tsz_eraseLine (v : Vt) (m : Nat) : tsz (v.eraseLine m) = tsz v := by
  rw [frame_eraseLine]
  rfl

theorem tsz_eraseScreen (v : Vt) (m : Nat) : tsz (v.eraseScreen m) = tsz v := by
  rw [frame_eraseScreen]
  rfl

theorem tsz_insertLines (v : Vt) (n : Nat) : tsz (v.insertLines n) = tsz v := by
  rw [frame_insertLines]
  rfl

theorem tsz_deleteLines (v : Vt) (n : Nat) : tsz (v.deleteLines n) = tsz v := by
  rw [frame_deleteLines]
  rfl

theorem tsz_enterAlt (v : Vt) (s : Bool) : tsz (v.enterAlt s) = tsz v := by
  unfold Vt.enterAlt; dsimp only; split <;> rfl

theorem tsz_leaveAlt (v : Vt) (s : Bool) : tsz (v.leaveAlt s) = tsz v := by
  unfold Vt.leaveAlt; split <;> rfl

theorem tsz_setMode (v : Vt) (priv : Bool) (n : Nat) (on : Bool) :
    tsz (v.setMode priv n on) = tsz v := by
  unfold Vt.setMode
  repeat' split
  all_goals try simp only [tsz_moveTo, tsz_enterAlt, tsz_leaveAlt]
  all_goals rfl

theorem tsz_setModes (v : Vt) (priv : Bool) (ps : List (Nat × Bool)) (on : Bool) :
    tsz (v.setModes priv ps on) = tsz v :=
  tsz_foldl (fun w (p : Nat × Bool) => w.setMode priv p.1 on) (fun w p => tsz_setMode w priv p.1 on)
    ps v

theorem tsz_print (v : Vt) (c : Char) : tsz (v.print c) = tsz v :=
  congrArg (fun s => s.tabs.size) (off_print v c)

theorem tsz_acceptChar (v : Vt) (n : Nat) : tsz (v.acceptChar n) = tsz v := by
  unfold Vt.acceptChar; split <;> exact tsz_print _ _

theorem tsz_ctl (v : Vt) (b : UInt8) : tsz (v.ctl b) = tsz v := by
  unfold Vt.ctl
  repeat' split
  all_goals
    first
    | exact tsz_backspace v
    | exact tsz_tab v
    | exact tsz_lineFeed v
    | exact tsz_carriageReturn v
    | rfl

theorem tsz_stepEscInter (v : Vt) (i b : UInt8) : tsz (v.stepEscInter i b) = tsz v := by
  rw [frame_stepEscInter]
  rfl

theorem tsz_oscFinish (v : Vt) (acc : Array UInt8) : tsz (v.oscFinish acc) = tsz v := by
  rw [frame_oscFinish]
  rfl

theorem tsz_stepOsc (v : Vt) (acc : Array UInt8) (e : Bool) (b : UInt8) :
    tsz (v.stepOsc acc e b) = tsz v := by
  unfold Vt.stepOsc
  repeat' split
  all_goals
    first
    | rfl
    | exact tsz_oscFinish _ _

theorem tsz_stepStr (v : Vt) (e : Bool) (b : UInt8) : tsz (v.stepStr e b) = tsz v := by
  rw [frame_stepStr]
  rfl

theorem tsz_abortUtf8 (v : Vt) (b : UInt8) : tsz (v.abortUtf8 b) = tsz v := by
  unfold Vt.abortUtf8; split <;> rfl

theorem tsz_stepGround (v : Vt) (b : UInt8) : tsz (v.stepGround b) = tsz v := by
  fun_cases Vt.stepGround v b
  all_goals try simp only [tsz_ctl, tsz_acceptChar]
  all_goals rfl

/-! ### The three writers

`TBC` and `HTS` are CSI `g` and **ESC** `H`; `RIS` is ESC `c`. Everything else is
the sweep above, so each of these gets the honest treatment and nothing else has
to. -/

theorem tsz_csiDispatch_ne_tbc {v : Vt} (s : CsiState) (final : UInt8) (h : final ≠ 0x67) :
    tsz (v.csiDispatch s final) = tsz v := by
  unfold Vt.csiDispatch
  dsimp only
  repeat' split
  all_goals
    try
      simp only [tsz_insertChars, tsz_moveRel, tsz_carriageReturn, tsz_setCol, tsz_moveTo,
        tsz_eraseScreen, tsz_eraseLine, tsz_insertLines, tsz_deleteLines, tsz_deleteChars,
        tsz_eraseChars, tsz_setModes, tsz_applySgr]
  all_goals
    first
    | rfl
    | exact tsz_foldl _ (fun w _ => tsz_tab w) _ _
    | exact tsz_foldl _ (fun w _ => tsz_scrollUp w) _ _
    | exact tsz_foldl _ (fun w _ => tsz_scrollDown w) _ _
    | exact tsz_foldl _ (fun w _ => tsz_backTab w) _ _
    | exact absurd rfl h

/-- **`TBC` keeps the ruler as wide as the screen.** `TBC 0` pokes one stop with
`setIfInBounds`, which cannot change a length; `TBC 3` installs
`Array.replicate v.cols`, which is the right length by construction — so this arm
*re-establishes* the invariant rather than preserving it, and is the reason the
layer is stated over `TabsOk` and not over `tsz` alone. -/
theorem tabsOk_csiDispatch {v : Vt} (s : CsiState) (final : UInt8) (h : TabsOk v) :
    TabsOk (v.csiDispatch s final) := by
  by_cases hg : final = 0x67
  · subst hg
    by_cases hi : s.ignore = true
    · simpa [Vt.csiDispatch, hi] using h
    · unfold Vt.csiDispatch
      rw [ite_eq_right hi]
      show
        TabsOk
          (match s.arg 0 0 with
          | 0 => { v with tabs := v.tabs.setIfInBounds v.cursor.x false }
          | 3 => { v with tabs := Array.replicate v.cols false }
          | _ => v)
      split
      · show (v.tabs.setIfInBounds v.cursor.x false).size = v.cols
        rw [Array.size_setIfInBounds]
        exact h
      · show (Array.replicate v.cols false).size = v.cols
        rw [Array.size_replicate]
      · exact h
  · exact h.transfer (tsz_csiDispatch_ne_tbc s final hg) (dims_csiDispatch v s final)

theorem tabsOk_csiFinish {v : Vt} (s : CsiState) (final : UInt8) (h : TabsOk v) :
    TabsOk (v.csiFinish s final) := by
  unfold Vt.csiFinish
  dsimp only
  split <;> exact tabsOk_csiDispatch _ _ h

theorem tabsOk_stepCsi {v : Vt} (s : CsiState) (b : UInt8) (h : TabsOk v) :
    TabsOk (v.stepCsi s b) := by
  fun_cases Vt.stepCsi v s b
  all_goals
    first
    | exact tabsOk_csiFinish _ _ h
    | exact h.transfer (tsz_ctl _ _) (dims_ctl _ _)
    | exact h

theorem tsz_stepEsc_ne {v : Vt} (b : UInt8) (h48 : b ≠ 0x48) (h63 : b ≠ 0x63) :
    tsz (v.stepEsc b) = tsz v := by
  unfold Vt.stepEsc
  dsimp only
  repeat' split
  all_goals
    first
    | rfl
    | exact tsz_lineFeed v
    | exact tsz_reverseIndex v
    | exact (tsz_lineFeed _).trans (tsz_carriageReturn v)
    | exact absurd rfl h48
    | exact absurd rfl h63

/-- **`HTS` and `RIS`, the two escapes that move the ruler.** `HTS` sets a stop
with `setIfInBounds`; `RIS` rebuilds through `Vt.init`, which installs
`defaultTabs (clampDim v.cols)` beside `cols := clampDim v.cols` — the same clamp
on both sides, which is why this needs no `Good` where `dims_stepEsc` does. -/
theorem tabsOk_stepEsc {v : Vt} (b : UInt8) (h : TabsOk v) : TabsOk (v.stepEsc b) := by
  by_cases h48 : b = 0x48
  · subst h48
    show (v.tabs.setIfInBounds v.cursor.x true).size = v.cols
    rw [Array.size_setIfInBounds]
    exact h
  by_cases h63 : b = 0x63
  · subst h63
    show (defaultTabs (clampDim v.cols)).size = clampDim v.cols
    exact size_defaultTabs _
  · exact h.transfer (tsz_stepEsc_ne b h48 h63) (dims_stepEsc_ne_ris b h63)

/-! ### …and the stream

`Vt.init` and `Vt.resize` both install `defaultTabs` beside the clamped width, so
the two doors into a `Vt` establish the invariant and every byte preserves it. -/

theorem tabsOk_init (cols rows : Nat) : TabsOk (Vt.init cols rows) := size_defaultTabs _

theorem tabsOk_resize (v : Vt) (cols rows : Nat) : TabsOk (v.resize cols rows) := size_defaultTabs _

theorem tabsOk_quiesce {v : Vt} (h : TabsOk v) : TabsOk v.quiesce := h

/-- **The ruler keeps pace with the width, for any byte.** -/
theorem tabsOk_step {v : Vt} (b : UInt8) (h : TabsOk v) : TabsOk (v.step b) := by
  have hab : TabsOk (v.abortUtf8 b) := h.transfer (tsz_abortUtf8 v b) (dims_abortUtf8 v b)
  unfold Vt.step
  dsimp only
  split
  · exact hab.transfer (tsz_stepGround _ _) (dims_stepGround _ _)
  · exact tabsOk_stepEsc _ hab
  · exact hab.transfer (tsz_stepEscInter _ _ _) (dims_stepEscInter _ _ _)
  · exact tabsOk_stepCsi _ _ hab
  · exact hab.transfer (tsz_stepOsc _ _ _ _) (dims_stepOsc _ _ _ _)
  · exact hab.transfer (tsz_stepStr _ _ _) (dims_stepStr _ _ _)

/-- The stream form. -/
theorem tabsOk_feed : ∀ (bs : List UInt8) {v : Vt}, TabsOk v → TabsOk (v.feed bs) := fun bs {v} h =>
  invariant_foldl TabsOk Vt.step (fun _ b hw => tabsOk_step b hw) bs v h

/-! ## Origin mode survives everything that is not a mode set

The rung §Replay's *restore-level* cursor claim stands on: a session with
DECOM off must replay with DECOM off, or the final `CUP` would be read
region-relative and land somewhere else.

The structural fact that makes this cheap: `modes` is only ever written
by `setMode`, which `csiDispatch` reaches only through the `h`/`l`
finals. So one conditional lemma (`org_setMode`: only *private* mode 6
touches `origin`) plus the usual arm sweep carries it. Fourth instance of
the invariance-layer recipe, and the one that will also serve pen,
region and mode fidelity.
-/

theorem org_foldl {α : Type} (f : Vt → α → Vt) (hf : ∀ v a, (f v a).modes.origin = v.modes.origin) :
    ∀ (l : List α) (v : Vt), (l.foldl f v).modes.origin = v.modes.origin := fun l v =>
  invariant_foldl (fun w => w.modes.origin = v.modes.origin) f (fun w a hw => (hf w a).trans hw) l v
    rfl

theorem org_clearPending (v : Vt) : v.clearPending.modes.origin = v.modes.origin := by rfl

theorem org_carriageReturn (v : Vt) : v.carriageReturn.modes.origin = v.modes.origin := by rfl

theorem org_moveTo (v : Vt) (x y : Nat) : (v.moveTo x y).modes.origin = v.modes.origin := by rfl

theorem org_moveRel (v : Vt) (dx dy : Int) : (v.moveRel dx dy).modes.origin = v.modes.origin := by
  rfl

theorem org_setCol (v : Vt) (x : Nat) : (v.setCol x).modes.origin = v.modes.origin := by rfl

theorem org_eraseRowSpan (v : Vt) (y a b : Nat) :
    (v.eraseRowSpan y a b).modes.origin = v.modes.origin := by rfl

theorem org_scrollDownIn (v : Vt) (t b : Nat) :
    (v.scrollDownIn t b).modes.origin = v.modes.origin := by rfl

theorem org_deleteChars (v : Vt) (n : Nat) : (v.deleteChars n).modes.origin = v.modes.origin := by
  rfl

theorem org_insertChars (v : Vt) (n : Nat) : (v.insertChars n).modes.origin = v.modes.origin := by
  rfl

theorem org_applySgr (v : Vt) (ps : List (Nat × Bool)) :
    (v.applySgr ps).modes.origin = v.modes.origin := by rfl

theorem org_backTab (v : Vt) : v.backTab.modes.origin = v.modes.origin := by rfl

theorem org_scrollUpIn (v : Vt) (t b : Nat) (a : Bool) :
    (v.scrollUpIn t b a).modes.origin = v.modes.origin := by
  unfold Vt.scrollUpIn; dsimp only; split <;> rfl

theorem org_scrollUp (v : Vt) : v.scrollUp.modes.origin = v.modes.origin := org_scrollUpIn _ _ _ _

theorem org_scrollDown (v : Vt) : v.scrollDown.modes.origin = v.modes.origin :=
  org_scrollDownIn _ _ _

theorem org_lineFeed (v : Vt) : v.lineFeed.modes.origin = v.modes.origin := by rw [frame_lineFeed]

theorem org_reverseIndex (v : Vt) : v.reverseIndex.modes.origin = v.modes.origin := by
  rw [frame_reverseIndex]

theorem org_backspace (v : Vt) : v.backspace.modes.origin = v.modes.origin := by
  unfold Vt.backspace; split <;> rfl

theorem org_tab (v : Vt) : v.tab.modes.origin = v.modes.origin := by
  unfold Vt.tab; dsimp only; exact org_clearPending v

theorem org_eraseChars (v : Vt) (n : Nat) :
    (v.eraseChars n).modes.origin = v.modes.origin := org_eraseRowSpan _ _ _ _

theorem org_eraseLine (v : Vt) (m : Nat) : (v.eraseLine m).modes.origin = v.modes.origin := by
  rw [frame_eraseLine]

theorem org_eraseScreen (v : Vt) (m : Nat) : (v.eraseScreen m).modes.origin = v.modes.origin := by
  rw [frame_eraseScreen]

theorem org_insertLines (v : Vt) (n : Nat) : (v.insertLines n).modes.origin = v.modes.origin := by
  rw [frame_insertLines]

theorem org_deleteLines (v : Vt) (n : Nat) : (v.deleteLines n).modes.origin = v.modes.origin := by
  rw [frame_deleteLines]

theorem org_enterAlt (v : Vt) (s : Bool) : (v.enterAlt s).modes.origin = v.modes.origin := by
  unfold Vt.enterAlt; dsimp only; split <;> rfl

theorem org_leaveAlt (v : Vt) (s : Bool) : (v.leaveAlt s).modes.origin = v.modes.origin := by
  unfold Vt.leaveAlt; split <;> rfl

/-- **The conditional rung.** Only *private* mode 6 (DECOM) writes
`origin`; every other mode number, private or not, leaves it alone. -/
theorem org_setMode (v : Vt) (priv : Bool) (n : Nat) (on : Bool) (h : ¬(priv = true ∧ n = 6)) :
    (v.setMode priv n on).modes.origin = v.modes.origin := by
  unfold Vt.setMode
  split
  · rename_i hp
    -- private modes: only 6 touches origin, and that case is excluded
    repeat' split
    all_goals
      first
      | rfl
      | exact org_enterAlt _ _
      | exact org_leaveAlt _ _
      | ( exfalso
          apply h
          refine ⟨hp, ?_⟩
          first
          | rfl
          | assumption
          | omega)
  · -- non-private: only IRM (4), which is a different flag
    repeat' split
    all_goals rfl

/-- A mode batch preserves origin when none of its requested modes is DECOM. -/
theorem org_setModes (v : Vt) (priv : Bool) (ps : List (Nat × Bool)) (on : Bool)
    (h : ∀ p ∈ ps, ¬(priv = true ∧ p.1 = 6)) :
    (v.setModes priv ps on).modes.origin = v.modes.origin :=
  setModes_invariant (fun w => w.modes.origin = v.modes.origin) priv on ps
    (fun w p hp hw => (org_setMode w priv p.1 on (h p hp)).trans hw) v rfl

theorem org_setMode_eq (v : Vt) (priv : Bool) (n : Nat) (on : Bool) :
    (v.setMode priv n on).modes.origin = if priv = true ∧ n = 6 then on else v.modes.origin := by
  by_cases h : priv = true ∧ n = 6
  · obtain ⟨hp, hn⟩ := h
    subst priv; subst n
    rw [ite_eq_left ⟨rfl, rfl⟩]
    exact org_moveTo _ _ _
  · rw [ite_eq_right h]
    exact org_setMode v priv n on h

/-- Any occurrence of private mode 6 sets origin to the batch's requested value.
This covers repeated DECOM and DECOM after other modes, without a frame premise. -/
theorem org_setModes_eq (v : Vt) (priv : Bool) (ps : List (Nat × Bool)) (on : Bool) :
    (v.setModes priv ps on).modes.origin =
      if priv = true ∧ ps.any (fun p => p.1 == 6) = true then on else v.modes.origin := by
  induction ps generalizing v with
  | nil => simp [setModes_nil]
  | cons p ps ih =>
    rw [setModes_cons, ih, org_setMode_eq, List.any_cons]
    simp only [Bool.or_eq_true, beq_iff_eq]
    by_cases hp : priv = true <;> by_cases hn : p.1 = 6 <;>
      by_cases ht : ps.any (fun p => p.1 == 6) = true <;>
      simp [hp, hn, ht]

/-- `csiDispatch` preserves `origin` unless a private sequence requests DECOM
somewhere in its parameters. The first parameter alone cannot establish this. -/
theorem org_csiDispatch (v : Vt) (s : CsiState) (final : UInt8)
    (h : ∀ p ∈ s.params.toList, ¬((s.priv == 0x3F) = true ∧ p.1 = 6)) :
    (v.csiDispatch s final).modes.origin = v.modes.origin := by
  unfold Vt.csiDispatch
  dsimp only
  repeat' split
  all_goals
    try
      simp only [org_insertChars, org_moveRel, org_carriageReturn, org_setCol, org_moveTo,
        org_eraseScreen, org_eraseLine, org_insertLines, org_deleteLines, org_deleteChars,
        org_eraseChars, org_applySgr]
  all_goals
    with_reducible
      first
      | rfl
      | exact org_setModes _ _ _ _ h
      | exact org_foldl _ (fun w _ => org_tab w) _ _
      | exact org_foldl _ (fun w _ => org_scrollUp w) _ _
      | exact org_foldl _ (fun w _ => org_scrollDown w) _ _
      | exact org_foldl _ (fun w _ => org_backTab w) _ _

theorem priv_csiPush (s : CsiState) (sub : Bool) : (csiPush s sub).priv = s.priv := by
  unfold csiPush
  repeat' split
  all_goals rfl

theorem org_csiFinish (v : Vt) (s : CsiState) (final : UInt8) (hp : (s.priv == 0x3F) = false) :
    (v.csiFinish s final).modes.origin = v.modes.origin := by
  -- every record `csiFinish` builds keeps `priv`, so one hypothesis covers
  -- every dispatch site
  have hnot :
    ∀ (t : CsiState),
      t.priv = s.priv → ∀ p ∈ t.params.toList, ¬((t.priv == 0x3F) = true ∧ p.1 = 6) := by
    intro t ht p _ hc
    rw [ht, hp] at hc
    exact absurd hc.1 (by simp)
  unfold Vt.csiFinish
  dsimp only
  split
  · split
    · exact org_csiDispatch _ _ _ (hnot _ rfl)
    · exact org_csiDispatch _ _ _ (hnot _ rfl)
  · split
    · exact org_csiDispatch _ _ _ (hnot _ rfl)
    · exact org_csiDispatch _ _ _ (hnot _ (priv_csiPush s false))

theorem org_ctl (v : Vt) (b : UInt8) : (v.ctl b).modes.origin = v.modes.origin := by
  unfold Vt.ctl
  repeat' split
  all_goals
    with_reducible
      first
      | exact org_backspace v
      | exact org_tab v
      | exact org_lineFeed v
      | exact org_carriageReturn v
      | rfl

/-- Inside a CSI, `origin` survives unless the sequence is a private
mode-6 set/reset — and a private-marker byte only *records* the marker. -/
theorem org_stepCsi (v : Vt) (s : CsiState) (b : UInt8) (hp : (s.priv == 0x3F) = false) :
    (v.stepCsi s b).modes.origin = v.modes.origin := by
  unfold Vt.stepCsi
  simp only [apply_ite (fun w : Vt => w.modes.origin), org_csiFinish _ _ _ hp, org_ctl, ite_self]

theorem org_print (v : Vt) (c : Char) : (v.print c).modes.origin = v.modes.origin :=
  congrArg (fun s => s.modes.origin) (off_print v c)

theorem org_acceptChar (v : Vt) (n : Nat) : (v.acceptChar n).modes.origin = v.modes.origin := by
  unfold Vt.acceptChar; split <;> exact org_print _ _

theorem org_stepGround (v : Vt) (b : UInt8) : (v.stepGround b).modes.origin = v.modes.origin := by
  fun_cases Vt.stepGround v b
  all_goals try simp only [org_ctl, org_acceptChar]
  all_goals rfl

theorem org_stepEscInter (v : Vt) (i b : UInt8) :
    (v.stepEscInter i b).modes.origin = v.modes.origin := by rw [frame_stepEscInter]

theorem org_oscFinish (v : Vt) (acc : Array UInt8) :
    (v.oscFinish acc).modes.origin = v.modes.origin := by rw [frame_oscFinish]

theorem org_stepOsc (v : Vt) (acc : Array UInt8) (e : Bool) (b : UInt8) :
    (v.stepOsc acc e b).modes.origin = v.modes.origin := by
  unfold Vt.stepOsc
  repeat' split
  all_goals
    with_reducible
      first
      | rfl
      | exact org_oscFinish _ _

theorem org_abortUtf8 (v : Vt) (b : UInt8) : (v.abortUtf8 b).modes.origin = v.modes.origin := by
  unfold Vt.abortUtf8; split <;> rfl

/-- `stepEsc` preserves `origin` except at `RIS`, which resets it to the
default — `false`, which is what a DECOM-off session wants anyway, so the
statement is "stays false". -/
theorem org_stepEsc {v : Vt} (b : UInt8) (h : v.modes.origin = false) :
    (v.stepEsc b).modes.origin = false := by
  unfold Vt.stepEsc
  dsimp only
  repeat' split
  all_goals try simp only [org_lineFeed, org_carriageReturn, org_reverseIndex]
  all_goals
    first
    | exact h
    | rfl

/-! ### The private-CSI escape hatch

`org_stepCsi` above needs the private marker to be *absent*, because a
private sequence could be DECOM. That is too coarse for the one construct
that has a marker: `csiPriv n final` emits `CSI ? <digits> <final>`, so
every mode replay would be excluded. When the pending parameter is known,
"is this DECOM?" can be decided instead of assumed away — and that is
exactly the state `Render`'s private sequences reach: no pushed parameter,
one pending accumulator, whose value is not 6.
-/

/-- With no previously pushed parameters, the pending parameter is the only
mode `csiFinish` can request. If it is not 6, no `h`/`l` final can be DECOM. -/
theorem org_csiFinish_pending (v : Vt) (s : CsiState) (final : UInt8) (hparams : s.params = #[])
    (hhave : s.haveCur = true) (hne : min s.cur 65535 ≠ 6) :
    (v.csiFinish s final).modes.origin = v.modes.origin := by
  have hsize : ¬(s.params.size ≥ 16) := by
    rw [hparams]; simp
  unfold Vt.csiFinish
  dsimp only
  rw [ite_eq_left hhave, ite_eq_right hsize]
  refine org_csiDispatch _ _ _ ?_
  intro p hp ⟨_, h6⟩
  simp only [hparams, Array.toList_push, List.nil_append, List.mem_singleton] at hp
  subst p
  exact hne h6

/-- `stepCsi` under the same knowledge: no branch can turn `origin` on. -/
theorem org_stepCsi_pending (v : Vt) (s : CsiState) (b : UInt8) (hparams : s.params = #[])
    (hhave : s.haveCur = true) (hne : min s.cur 65535 ≠ 6) :
    (v.stepCsi s b).modes.origin = v.modes.origin := by
  unfold Vt.stepCsi
  simp only [apply_ite (fun w : Vt => w.modes.origin),
    org_csiFinish_pending _ _ _ hparams hhave hne, org_ctl, ite_self]

/-! ### The dispatcher: `origin` across one whole `Vt.step`

The lemmas above are per parser state; a byte-stream proof composes
`Vt.step` itself (`Theorems/Render.lean`). `abortUtf8` runs first inside
`step` and touches only `u8need`/`u8acc`, so each case is its branch
lemma followed by `org_abortUtf8`. -/

theorem org_step_of_ground {v : Vt} (b : UInt8) (hg : v.pstate = .ground) :
    (v.step b).modes.origin = v.modes.origin := by
  rw [step_of_ground b hg, org_stepGround, org_abortUtf8]

/-- From `.esc` the claim has to be "stays false" rather than "unchanged":
`RIS` resets `origin` to its default, which is `false`. -/
theorem org_step_of_esc {v : Vt} (b : UInt8) (hg : v.pstate = .esc) (h : v.modes.origin = false) :
    (v.step b).modes.origin = false := by
  rw [step_of_esc b hg]
  exact
    org_stepEsc b
      (by
        rw [org_abortUtf8]; exact h)

theorem org_step_of_escInter {v : Vt} {i : UInt8} (b : UInt8) (hg : v.pstate = .escInter i) :
    (v.step b).modes.origin = v.modes.origin := by
  rw [step_of_escInter b hg, org_stepEscInter, org_abortUtf8]

theorem org_step_of_osc {v : Vt} {acc : Array UInt8} {e : Bool} (b : UInt8)
    (hg : v.pstate = .osc acc e) : (v.step b).modes.origin = v.modes.origin := by
  rw [step_of_osc b hg, org_stepOsc, org_abortUtf8]

theorem org_step_of_csi {v : Vt} {s : CsiState} (b : UInt8) (hg : v.pstate = .csi s)
    (hp : (s.priv == 0x3F) = false) : (v.step b).modes.origin = v.modes.origin := by
  rw [step_of_csi b hg, org_stepCsi _ _ _ hp, org_abortUtf8]

/-- The marker-tolerant companion of `org_step_of_csi`. -/
theorem org_step_of_csi_pending {v : Vt} {s : CsiState} (b : UInt8) (hg : v.pstate = .csi s)
    (hparams : s.params = #[]) (hhave : s.haveCur = true) (hne : min s.cur 65535 ≠ 6) :
    (v.step b).modes.origin = v.modes.origin := by
  rw [step_of_csi b hg, org_stepCsi_pending _ _ _ hparams hhave hne, org_abortUtf8]

end Linger.Core.Vt
