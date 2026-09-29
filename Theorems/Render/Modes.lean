module

public import Theorems.Render.Keeps
import all Linger.Core.Render
import all Linger.Core.Vt
import all Theorems.Render.Keeps
import all Init.Data.String.Legacy

-- No `public section`: a **public** declaration's type may not mention a private
-- field, and `Vt`'s are private now (the seal, `specs/archive/vt-toolkit.md` Step 1).
-- Module-private is the default, so consumers reach in with `import all`. See the
-- longer note in `Theorems/Vt.lean`.

/-! # §Handback / anchor A5 — the modes, both directions

The lead-in that grounds any receiver, the hand-back's canonical modes
(`leave_canonical`), `MMap` (modes-from-ground with per-chunk transforms), and the
inbound value claims for the modes and the pen. Split out of
`Theorems/Render.lean`. -/

namespace Linger.Core.Render

open Linger.Core.Vt

/-! ## `Sets` — what a chunk establishes, whatever the receiver was doing

`Ends`, `Quiet` and `Keeps` all quantify over a receiver that starts in `ground`, and
the fidelity theorem quantifies over `Vt.init` outright. That is the one receiver
state in which every precondition the emitter depends on already holds, which is
exactly why it hid the mode leak fixed in `87f64b3`
(`specs/archive/restore-conformance.md`, Step 1).

`Sets` has no hypothesis on the receiver at all:

> feeding `bs` to **any** state leaves `P` at `x`.

Two composition laws, and the asymmetry between them is the point. Appending on the
**left** is free — whatever came before is overwritten — which is what makes
both-ways emission provable. Appending on the right requires the suffix to preserve
`P`, which is the same obligation `Keeps` already discharges for the grid. -/

def Sets {α : Type} (P : Vt → α) (x : α) (bs : Bytes) : Prop := ∀ w : Vt, P (w.feed bs) = x

/-- **Anything before is irrelevant.** The load-bearing law: a later emit overwrites
an earlier one, so a chunk that sets a mode can be prefixed by arbitrary bytes. -/
theorem Sets.prefix {α : Type} {P : Vt → α} {x : α} {b : Bytes} (h : Sets P x b) (a : Bytes) :
    Sets P x (a ++ b) := by
  intro w
  rw [feed_append]
  exact h _

/-- A suffix may be appended when it preserves `P` from any state. -/
theorem Sets.suffix {α : Type} {P : Vt → α} {x : α} {a : Bytes} (h : Sets P x a) {b : Bytes}
    (hb : ∀ w : Vt, P (w.feed b) = P w) : Sets P x (a ++ b) := by
  intro w
  rw [feed_append, hb]
  exact h _

theorem Sets.ite {α : Type} {P : Vt → α} {x : α} {c : Prop} [Decidable c] {a b : Bytes}
    (ha : c → Sets P x a) (hb : ¬c → Sets P x b) : Sets P x (if c then a else b) := by
  by_cases h : c
  · rw [ite_eq_left h]; exact ha h
  · rw [ite_eq_right h]; exact hb h

end Linger.Core.Render

namespace Linger.Core.Render

open Linger.Core.Vt

/-! ### The lead-in grounds any receiver

`Ends`, `Quiet` and `Keeps` all assume the receiver starts in `ground`. That
assumption is exactly the kind this spec exists to remove: a client left mid-OSC or
mid-DCS swallows every byte until its terminator, so `restore` fed to one displayed
nothing at all (SCRATCHPAD 2026-08-15).

`prologueAnsi` leads with `ESC \` for that reason, and these are the theorems saying
it works — the `Tests/Render.lean` `midOsc`/`midDcs` cases in proof form, over *all*
receivers rather than five of them. Split in two so that each proof unfolds one
`Vt.step`: where `ESC` lands, and what `\` does from there. -/

theorem un_abortUtf8_esc (w : Vt) : (w.abortUtf8 0x1B).u8need = 0 := by
  unfold Vt.abortUtf8
  by_cases h : w.u8need > 0
  · rw [ite_eq_left (by simp [h])]
  · rw [ite_eq_right (by simp [h])]
    omega

/-- Where `ESC` lands, from anywhere: `.esc` (including an interrupted
intermediate sequence), or one of the two string states with its ST check armed.
The following `\` finishes each of these states. -/
theorem esc_lands (w : Vt) :
    ((w.step 0x1B).pstate = .esc ∨
        (∃ acc, (w.step 0x1B).pstate = .osc acc true) ∨ (w.step 0x1B).pstate = .str true) ∧
      (w.step 0x1B).u8need = 0 := by
  have hun := un_abortUtf8_esc w
  unfold Vt.step
  dsimp only
  match h : (w.abortUtf8 0x1B).pstate with
  | .ground =>
    refine ⟨Or.inl ?_, ?_⟩
    · show ((w.abortUtf8 0x1B).stepGround 0x1B).pstate = PState.esc
      unfold Vt.stepGround
      rw [ite_eq_left (by decide)]
    · show ((w.abortUtf8 0x1B).stepGround 0x1B).u8need = 0
      unfold Vt.stepGround
      rw [ite_eq_left (by decide)]
      exact hun
  | .esc =>
    refine ⟨Or.inl ?_, ?_⟩
    · show ((w.abortUtf8 0x1B).stepEsc 0x1B).pstate = PState.esc
      unfold Vt.stepEsc
      exact h
    · show ((w.abortUtf8 0x1B).stepEsc 0x1B).u8need = 0
      unfold Vt.stepEsc
      exact hun
  | .escInter i => exact ⟨Or.inl rfl, hun⟩
  | .csi s =>
    refine ⟨Or.inl ?_, ?_⟩
    · show ((w.abortUtf8 0x1B).stepCsi s 0x1B).pstate = PState.esc
      unfold Vt.stepCsi
      rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
        ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
        ite_eq_left (by decide)]
    · show ((w.abortUtf8 0x1B).stepCsi s 0x1B).u8need = 0
      unfold Vt.stepCsi
      rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
        ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
        ite_eq_left (by decide)]
      exact hun
  | .osc acc e =>
    refine ⟨Or.inr (Or.inl ⟨acc, ?_⟩), ?_⟩
    · show ((w.abortUtf8 0x1B).stepOsc acc e 0x1B).pstate = PState.osc acc true
      unfold Vt.stepOsc
      rw [ite_eq_right (by simp), ite_eq_right (by decide), ite_eq_left (by decide)]
    · show ((w.abortUtf8 0x1B).stepOsc acc e 0x1B).u8need = 0
      unfold Vt.stepOsc
      rw [ite_eq_right (by simp), ite_eq_right (by decide), ite_eq_left (by decide)]
      exact hun
  | .str e =>
    refine ⟨Or.inr (Or.inr ?_), ?_⟩
    · show ((w.abortUtf8 0x1B).stepStr e 0x1B).pstate = PState.str true
      unfold Vt.stepStr
      rw [ite_eq_right (by simp), ite_eq_left (by decide)]
    · show ((w.abortUtf8 0x1B).stepStr e 0x1B).u8need = 0
      unfold Vt.stepStr
      rw [ite_eq_right (by simp), ite_eq_left (by decide)]
      exact hun

/-- …and `\` finishes every one of them. -/
theorem st_finish (u : Vt) (hu : u.u8need = 0)
    (h :
      u.pstate = .esc ∨
        u.pstate = .ground ∨ (∃ acc, u.pstate = .osc acc true) ∨ u.pstate = .str true) :
    (u.step 0x5C).pstate = .ground ∧ (u.step 0x5C).u8need = 0 := by
  have ha : u.abortUtf8 0x5C = u := by
    unfold Vt.abortUtf8
    rw [ite_eq_right (by simp [hu])]
  unfold Vt.step
  dsimp only
  rw [ha]
  rcases h with h | h | ⟨acc, h⟩ | h
  · rw [h]
    show ((u.stepEsc 0x5C).pstate = _) ∧ ((u.stepEsc 0x5C).u8need = _)
    unfold Vt.stepEsc
    exact ⟨rfl, hu⟩
  · rw [h]
    show ((u.stepGround 0x5C).pstate = _) ∧ ((u.stepGround 0x5C).u8need = _)
    unfold Vt.stepGround
    rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left (by decide)]
    exact ⟨(ps_acceptChar _ _).trans h, (un_acceptChar _ _).trans hu⟩
  · rw [h]
    show ((u.stepOsc acc true 0x5C).pstate = _) ∧ ((u.stepOsc acc true 0x5C).u8need = _)
    unfold Vt.stepOsc
    rw [ite_eq_left (by decide)]
    exact ⟨ps_oscFinish' _ _, (un_oscFinish' _ _).trans hu⟩
  · rw [h]
    show ((u.stepStr true 0x5C).pstate = _) ∧ ((u.stepStr true 0x5C).u8need = _)
    unfold Vt.stepStr
    rw [ite_eq_left (by decide)]
    exact ⟨rfl, hu⟩

/-- **`ESC \` returns any receiver to `ground` with nothing half-decoded.** -/
theorem st_grounds (w : Vt) :
    (w.feed (escSeq 0x5C)).pstate = .ground ∧ (w.feed (escSeq 0x5C)).u8need = 0 := by
  rw [show escSeq 0x5C = [0x1B, 0x5C] from by simp [escSeq, escB],
    show w.feed [(0x1B : UInt8), 0x5C] = (w.step 0x1B).step 0x5C from by simp [Vt.feed]]
  obtain ⟨hstate, hun⟩ := esc_lands w
  exact st_finish _ hun (hstate.elim Or.inl (fun h => Or.inr (Or.inr h)))

/-- **The prologue grounds any receiver**, since `Ends` carries the rest. This is what
lets a `Sets`-shaped claim — one with no hypothesis on the receiver at all — be
composed from the chunk lemmas, which all assume `ground`. -/
theorem prologue_grounds (v w : Vt) : (w.feed (prologueAnsi v)).pstate = .ground := by
  have hrest :
    Ends
      (modeSet 1049 false ++ csiNum 4 0x6C ++ modeSet 6 false ++ modeSet 7 true ++
        csiNum2 1 v.rows 0x72 ++
        escCharset 0x28 0x42 ++
        escCharset 0x29 0x42 ++
        [0x0F]) := by
    refine Ends.append ?_ (Ends.text (bs := [0x0F]) (by decide))
    refine Ends.append ?_ (ends_escCharset 0x29 0x42 (by decide) (by decide) (by decide))
    refine Ends.append ?_ (ends_escCharset 0x28 0x42 (by decide) (by decide) (by decide))
    refine Ends.append ?_ (ends_csiNum2 1 v.rows 0x72 (by decide) (by decide))
    refine Ends.append ?_ (ends_modeSet 7 true)
    refine Ends.append ?_ (ends_modeSet 6 false)
    exact (ends_modeSet 1049 false).append (ends_csiNum 4 0x6C (by decide) (by decide))
  rw [show
      prologueAnsi v =
        escSeq 0x5C ++
          (modeSet 1049 false ++ csiNum 4 0x6C ++ modeSet 6 false ++ modeSet 7 true ++
            csiNum2 1 v.rows 0x72 ++
            escCharset 0x28 0x42 ++
            escCharset 0x29 0x42 ++
            [0x0F])
      from by
      unfold prologueAnsi; simp]
  rw [feed_append]
  exact hrest _ (st_grounds w).1

/-- **`restore` grounds any receiver.** The hypothesis-free form of
`restore_quiesced`: no assumption on the client's parser state at all, which is what
the `ESC \` lead-in buys. The `u8need` half needs the same treatment for every chunk
and is left to `specs/archive/restore-conformance.md` Step 2. -/
theorem restore_placed_grounds (v w : Vt) :
    (w.feed (restoreBody v ++ cursorAnsi v)).pstate = .ground := by
  rw [show
      restoreBody v ++ cursorAnsi v =
        prologueAnsi v ++
          (csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v ++ regionAnsi v ++ tabsAnsi v ++
            savedAnsi v ++
            savedPendingAnsi v ++
            titleAnsi v ++
            modesAnsi v ++
            charsetAnsi v ++
            penSgr v.pen ++
            cursorAnsi v)
      from by
      unfold restoreBody; simp]
  rw [feed_append]
  refine Ends.append ?_ (ends_cursorAnsi v) _ (prologue_grounds v w)
  refine Ends.append ?_ (ends_penSgr v.pen)
  refine Ends.append ?_ (ends_charsetAnsi v)
  refine Ends.append ?_ (ends_modesAnsi v)
  refine Ends.append ?_ (ends_titleAnsi v)
  refine Ends.append ?_ (ends_savedPendingAnsi v)
  refine Ends.append ?_ (ends_savedAnsi v)
  refine Ends.append ?_ (ends_tabsAnsi v)
  refine Ends.append ?_ (ends_regionAnsi v)
  refine Ends.append ?_ (ends_screensAnsi v)
  exact
    (ends_csiNum 0 0x6D (by decide) (by decide)).append (ends_csiNum 2 0x4A (by decide) (by decide))

theorem restore_grounds (v w : Vt) : (w.feed (restore v)).pstate = .ground := by
  unfold restore
  rw [feed_append]
  exact ends_cursorPendingAnsi v _ (restore_placed_grounds v w)

/-! ### …and so does the hand-back

`leaveAnsi` is A5's outbound half (§Handback): whatever the session's last program
left behind, the detaching client returns the terminal to a state the next program
can use. Its parser claim is `restore_grounds` with the same lead-in doing the same
job — a program that died mid-OSC or mid-DCS would swallow the hand-back exactly as
it swallowed the repaint before `cd7c17b` — and the same proof, one chunk longer.

The *value* claims (each mode at its canonical setting, for every receiver) are the
`Sets` instances of `specs/archive/restore-conformance.md` Step 1, which the hand-back is the
easiest instance of: no `ite`, no dependence on a `Vt`. -/

/-- A parameterless CSI: the receiver's own defaults apply. -/
theorem ends_csiPlain (final : UInt8) (h1 : 0x40 ≤ final) (h2 : final ≤ 0x7E) :
    Ends (csiPlain final) := by simpa [csiPlain] using ends_csi_seq [] final ParamBytes.nil h1 h2

-- Unfold one character at a time: reducing the recursive legacy splitter in one
-- step spends the default recursion budget on its termination proof.
private theorem split_empty_title : "2;".splitOn ";" = ["2", ""] := by
  unfold String.splitOn
  rw [ite_eq_right (by decide), String.splitOnAux]
  rw [ite_eq_right (by decide), ite_eq_right (by decide)]
  change String.splitOnAux "2;" ";" ⟨0⟩ ⟨1⟩ ⟨0⟩ [] = _
  rw [String.splitOnAux, ite_eq_right (by decide), ite_eq_left (by decide)]
  change (if true then String.splitOnAux "2;" ";" ⟨2⟩ ⟨2⟩ ⟨0⟩ ["2"] else _) = _
  rw [ite_eq_left (by decide), String.splitOnAux, ite_eq_left (by decide)]
  rfl

private theorem finish_empty_title (v : Vt) :
    v.oscFinish #[0x32, 0x3B] =
      { v with
        pstate := .ground, title := "" } := by
  have hdecode : String.fromUTF8? (ByteArray.mk #[0x32, 0x3B]) = some "2;" := by decide
  simp [Vt.oscFinish, hdecode, split_empty_title, String.intercalate_singleton]

/-- Empty OSC 2 sets the title absolutely. Its leading ESC aborts even a pending
UTF-8 character; every other field is preserved. No title bound or prior value is
assumed. The hand-back supplies the ground premise with its ST lead-in. -/
theorem defaultTitleAnsi_feed {v : Vt} (hg : v.pstate = .ground) :
    v.feed defaultTitleAnsi =
      { v.abortUtf8 0x1B with
        pstate := .ground, title := "" } := by
  let u := v.abortUtf8 0x1B
  have hu : u.u8need = 0 := un_abortUtf8_esc v
  have he : v.step 0x1B = { u with pstate := .esc } := by
    unfold Vt.step
    dsimp only
    rw [ps_abortUtf8, hg]
    rfl
  rw [show v.feed defaultTitleAnsi = ((((v.step 0x1B).step 0x5D).step 0x32).step 0x3B).step 0x07
      from by simp [defaultTitleAnsi, escB, Vt.feed]]
  rw [he]
  rw [show ({ u with pstate := .esc } : Vt).step 0x5D = { u with pstate := .osc #[] false } from by
      rw [step_of_esc_quiet 0x5D rfl (by simpa using hu)]
      rfl]
  rw [show
      ({ u with pstate := .osc #[] false } : Vt).step 0x32 = { u with pstate := .osc #[0x32] false }
      from by
      rw [step_of_osc_quiet 0x32 rfl (by simpa using hu)]
      rfl]
  rw [show
      ({ u with pstate := .osc #[0x32] false } : Vt).step 0x3B =
        { u with pstate := .osc #[0x32, 0x3B] false }
      from by
      rw [step_of_osc_quiet 0x3B rfl (by simpa using hu)]
      rfl]
  rw [step_of_osc_quiet 0x07 rfl (by simpa using hu)]
  change ({ u with pstate := .osc #[0x32, 0x3B] false } : Vt).oscFinish #[0x32, 0x3B] = _
  rw [finish_empty_title]

theorem defaultTitleAnsi_pen {v : Vt} (hg : v.pstate = .ground) :
    (v.feed defaultTitleAnsi).pen = v.pen := by
  rw [defaultTitleAnsi_feed hg]
  show (v.abortUtf8 0x1B).pen = v.pen
  unfold Vt.abortUtf8
  split <;> rfl

/-- **Hand-back establishes a parser boundary and an empty title for every
receiver.** Pending OSC, DCS, CSI, escapes, UTF-8 and alternate-screen state are
all admitted, with no restriction on the old title. -/
theorem leave_boundary_title (w : Vt) :
    (w.feed leaveAnsi).pstate = .ground ∧
      (w.feed leaveAnsi).u8need = 0 ∧ (w.feed leaveAnsi).title = "" := by
  have hrest :
    Ends
      (modeSet 1049 false ++ csiNum 4 0x6C ++ modeSet 25 true ++ modeSet 2004 false ++
        modeSet 1000 false ++
        modeSet 1002 false ++
        modeSet 1003 false ++
        modeSet 1006 false ++
        modeSet 1004 false ++
        modeSet 1 false ++
        escSeq 0x3E ++
        modeSet 6 false ++
        modeSet 7 true ++
        csiPlain 0x72 ++
        escCharset 0x28 0x42 ++
        escCharset 0x29 0x42 ++
        [0x0F] ++
        csiNum2 999 1 0x48 ++
        csiNum 0 0x6D) := by
    refine Ends.append ?_ (ends_csiNum 0 0x6D (by decide) (by decide))
    refine Ends.append ?_ (ends_csiNum2 999 1 0x48 (by decide) (by decide))
    refine Ends.append ?_ (Ends.text (bs := [0x0F]) (by decide))
    refine Ends.append ?_ (ends_escCharset 0x29 0x42 (by decide) (by decide) (by decide))
    refine Ends.append ?_ (ends_escCharset 0x28 0x42 (by decide) (by decide) (by decide))
    refine Ends.append ?_ (ends_csiPlain 0x72 (by decide) (by decide))
    refine Ends.append ?_ (ends_modeSet 7 true)
    refine Ends.append ?_ (ends_modeSet 6 false)
    refine Ends.append ?_ (ends_escSeq 0x3E (by decide))
    refine Ends.append ?_ (ends_modeSet 1 false)
    refine Ends.append ?_ (ends_modeSet 1004 false)
    refine Ends.append ?_ (ends_modeSet 1006 false)
    refine Ends.append ?_ (ends_modeSet 1003 false)
    refine Ends.append ?_ (ends_modeSet 1002 false)
    refine Ends.append ?_ (ends_modeSet 1000 false)
    refine Ends.append ?_ (ends_modeSet 2004 false)
    refine Ends.append ?_ (ends_modeSet 25 true)
    exact (ends_modeSet 1049 false).append (ends_csiNum 4 0x6C (by decide) (by decide))
  rw [show
      leaveAnsi =
        escSeq 0x5C ++
          (modeSet 1049 false ++ csiNum 4 0x6C ++ modeSet 25 true ++ modeSet 2004 false ++
            modeSet 1000 false ++
            modeSet 1002 false ++
            modeSet 1003 false ++
            modeSet 1006 false ++
            modeSet 1004 false ++
            modeSet 1 false ++
            escSeq 0x3E ++
            modeSet 6 false ++
            modeSet 7 true ++
            csiPlain 0x72 ++
            escCharset 0x28 0x42 ++
            escCharset 0x29 0x42 ++
            [0x0F] ++
            csiNum2 999 1 0x48 ++
            csiNum 0 0x6D ++
            defaultTitleAnsi)
      from by
      unfold leaveAnsi; simp]
  rw [feed_append, feed_append, defaultTitleAnsi_feed (hrest _ (st_grounds w).1)]
  exact ⟨rfl, un_abortUtf8_esc _, rfl⟩

/-- **The hand-back grounds any receiver.** No hypothesis on its parser,
UTF-8 decoder, screen or title. -/
theorem leave_grounds (w : Vt) : (w.feed leaveAnsi).pstate = .ground := (leave_boundary_title w).1

/-! ## §Handback / anchor A5 — the hand-back leaves the modes canonical

`leave_grounds` gave the parser half for any receiver; this gives the modes half.
The machinery is a `Modes`-projection analog of `Keeps`: `modeSet_modes` exposes a
private mode set as its `setMode` (the dispatch-exposing bridge the spec named),
`MMap` composes per-chunk modes transforms from ground, and `leave_modes` folds the
hand-back's chunks — each mode set absolutely, each non-mode chunk transparent — to
the default record, for **any** receiver `w`. -/

-- setMode's effect on `modes` is a function of the incoming modes alone.
theorem modes_moveTo (v : Vt) (x y : Nat) : (v.moveTo x y).modes = v.modes := by rfl

theorem modes_leaveAlt (v : Vt) (r : Bool) : (v.leaveAlt r).modes = v.modes := by
  unfold Vt.leaveAlt; split <;> rfl

theorem modes_enterAlt (v : Vt) (s : Bool) : (v.enterAlt s).modes = v.modes := by
  unfold Vt.enterAlt; split <;> rfl

theorem modes_setMode {w1 w2 : Vt} (p : Bool) (n : Nat) (on : Bool) (h : w1.modes = w2.modes) :
    (w1.setMode p n on).modes = (w2.setMode p n on).modes := by
  unfold Vt.setMode
  split <;> (repeat' split) <;> simp_all [modes_moveTo, modes_leaveAlt, modes_enterAlt]

/-- SM/RM project the whole ordered mode batch onto `modes`. -/
theorem modes_csiDispatch_sm (v : Vt) (s : CsiState) (hi : s.ignore = false) :
    (v.csiDispatch s 0x68).modes = (v.setModes (s.priv == 0x3F) s.params.toList true).modes := by
  rw [csiDispatch_sm _ _ hi]

theorem modes_csiDispatch_rm (v : Vt) (s : CsiState) (hi : s.ignore = false) :
    (v.csiDispatch s 0x6C).modes = (v.setModes (s.priv == 0x3F) s.params.toList false).modes := by
  rw [csiDispatch_rm _ _ hi]

/-- One step: `ESC [ ?` sets the private marker without touching the frame. -/
theorem frame_csi_marker_step {v : Vt} {s : CsiState} (hg : v.pstate = .csi s) :
    Frame (v.step 0x3F) = Frame v := by
  have hw : (v.abortUtf8 0x3F).pstate = PState.csi s := by
    rw [Linger.Core.Vt.ps_abortUtf8]; exact hg
  unfold Vt.step
  dsimp only
  rw [hw]
  unfold Vt.stepCsi
  dsimp only
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
    ite_eq_left (by decide)]
  exact frame_abortUtf8 v 0x3F

/-- **The digit-run-and-dispatch tail of a private mode set**, over an abstract
collector already carrying the private marker. Its modes become `setMode true n on`;
the parser returns to ground. Split out so the `ESC [ ?` prologue is applied to the
concrete receiver separately (there is no `set` tactic here — no Mathlib). -/
theorem modeSet_tail (n : Nat) (on : Bool) (hn : 0 < n) (hlt : n < 65535) {w : Vt}
    (hm : w.pstate = .csi ({ priv := 0x3F } : CsiState)) (hwu : w.u8need = 0) :
    (w.feed (digits n ++ [(if on then 0x68 else 0x6C : UInt8)])).modes =
        (w.setMode true n on).modes ∧
      (w.feed (digits n ++ [(if on then 0x68 else 0x6C : UInt8)])).pstate = .ground ∧
      (w.feed (digits n ++ [(if on then 0x68 else 0x6C : UInt8)])).u8need = 0 := by
  have hfinal :
    (0x40 : UInt8) ≤ (if on then 0x68 else 0x6C) ∧
      (if on then (0x68 : UInt8) else 0x6C) ≤ 0x7E := by
    cases on <;> exact ⟨by decide, by decide⟩
  obtain ⟨sa, hfeed, -⟩ := csi_param_run_inter (digits n) hm hwu (paramBytes_digits n)
  obtain ⟨sb, hpsb, hcur', hhave', hpar', hint', hign', -, hpriv'⟩ := csi_digits_value n hm rfl
  have hsab : sa = sb :=
    PState.csi.inj ((by rw [hfeed] : (w.feed (digits n)).pstate = .csi sa).symm.trans hpsb)
  rw [show
      ∀ (u : Vt),
        u.feed (digits n ++ [(if on then 0x68 else 0x6C : UInt8)]) =
          (u.feed (digits n)).feed [(if on then 0x68 else 0x6C : UInt8)]
      from fun u => by simp [Vt.feed, List.foldl_append]]
  rw [show
      ∀ (u : Vt), u.feed [(if on then 0x68 else 0x6C : UInt8)] = u.step (if on then 0x68 else 0x6C)
      from fun _ => rfl,
    hfeed]
  rw [csi_final_step_eq (if on then 0x68 else 0x6C) rfl (by rw [hwu])
      (by
        rw [hsab]; exact hint')
      hfinal.1 hfinal.2]
  unfold Vt.csiFinish
  rw [ite_eq_left
      (by
        rw [hsab]; simpa using hhave'),
    ite_eq_right
      (by
        rw [hsab, hpar']; decide)]
  dsimp only
  refine
    ⟨?_, rfl, by
      rw [un_csiDispatch]; exact hwu⟩
  have hmin : min (min n 65535) 65535 = n := by omega
  -- normalize the closed collector: single parameter `n`, marker set, ignore clear
  have hstate :
    ({ sa with params := sa.params.push (min sa.cur 65535, sa.curSub) } : CsiState) =
      { sa with params := #[(n, sa.curSub)] } := by
    rw [hsab, hpar', hcur', hmin]; rfl
  have hpriv2 : ({ sa with params := #[(n, sa.curSub)] } : CsiState).priv = 0x3F := by
    show sa.priv = 0x3F; rw [hsab]; exact hpriv'
  have hign2 : ({ sa with params := #[(n, sa.curSub)] } : CsiState).ignore = false := by
    show sa.ignore = false; rw [hsab]; exact hign'
  have hopmodes : ({ w with pstate := .csi sa } : Vt).modes = w.modes := by rfl
  show
    (({ w with pstate := .csi sa }).csiDispatch
          { sa with params := sa.params.push (min sa.cur 65535, sa.curSub) }
          (if on then 0x68 else 0x6C)).modes =
      (w.setMode true n on).modes
  rw [hstate]
  cases on
  · show (({ w with pstate := .csi sa }).csiDispatch _ 0x6C).modes = (w.setMode true n false).modes
    rw [csiDispatch_rm_one _ _ n sa.curSub hign2 rfl, hpriv2]
    exact modes_setMode true n false hopmodes
  · show (({ w with pstate := .csi sa }).csiDispatch _ 0x68).modes = (w.setMode true n true).modes
    rw [csiDispatch_sm_one _ _ n sa.curSub hign2 rfl, hpriv2]
    exact modes_setMode true n true hopmodes

theorem modeSet_modes (n : Nat) (on : Bool) (hn : 0 < n) (hlt : n < 65535) {v : Vt}
    (hg : v.pstate = .ground) (hu : v.u8need = 0) :
    (v.feed (modeSet n on)).modes = (v.setMode true n on).modes ∧
      (v.feed (modeSet n on)).pstate = .ground ∧ (v.feed (modeSet n on)).u8need = 0 := by
  rw [show modeSet n on = [0x1B, 0x5B, 0x3F] ++ (digits n ++ [(if on then 0x68 else 0x6C : UInt8)])
      from by simp [modeSet, csiPriv, csiB]]
  rw [show
      ∀ (w : Vt),
        w.feed ([0x1B, 0x5B, 0x3F] ++ (digits n ++ [(if on then 0x68 else 0x6C : UInt8)])) =
          (((w.step 0x1B).step 0x5B).step 0x3F).feed
            (digits n ++ [(if on then 0x68 else 0x6C : UInt8)])
      from fun w => by simp [Vt.feed]]
  -- the `ESC [ ?` prologue: reaches the marked collector, preserving frame + u8need
  have he : (v.step 0x1B) = { v with pstate := .esc } := esc_step_eq hg hu
  have hb : ((v.step 0x1B).step 0x5B).pstate = .csi {} := csi_open_step (by rw [he])
  obtain ⟨hm, -⟩ := csi_marker_step hb (by decide)
  have hframe : Frame (((v.step 0x1B).step 0x5B).step 0x3F) = Frame v :=
    (frame_csi_marker_step hb).trans ((frame_csi_open_step (by rw [he])).trans (frame_esc_step hg))
  have hmodes : (((v.step 0x1B).step 0x5B).step 0x3F).modes = v.modes := congrArg (·.2.2) hframe
  have hun : (((v.step 0x1B).step 0x5B).step 0x3F).u8need = 0 :=
    uz_step 0x3F (by decide) (uz_step 0x5B (by decide) (uz_step_esc v))
  obtain ⟨ht, hp, hu'⟩ := modeSet_tail n on hn hlt hm hun
  refine ⟨?_, hp, hu'⟩
  rw [ht, modes_setMode true n on hmodes]

/-! ## MMap — modes-from-ground, and per-chunk transforms -/

def MMap (f : Modes → Modes) (bs : Bytes) : Prop :=
  ∀ v : Vt,
    v.pstate = .ground →
      v.u8need = 0 →
      (v.feed bs).pstate = .ground ∧ (v.feed bs).u8need = 0 ∧ (v.feed bs).modes = f v.modes

theorem MMap.comp {f g : Modes → Modes} {a b : Bytes} (ha : MMap f a) (hb : MMap g b) :
    MMap (fun m => g (f m)) (a ++ b) := by
  intro v hg hu
  rw [feed_append]
  obtain ⟨h1, h2, h3⟩ := ha v hg hu
  obtain ⟨h4, h5, h6⟩ := hb _ h1 h2
  exact ⟨h4, h5, by rw [h6, h3]⟩

/-- **`MMap` without its `u8need` precondition, for an ESC-leading chunk.**

`MMap` demands `u8need = 0` going in, and after the scrollback stage's *glyph*
bytes nothing in the repo supplies that: `Ends` is deliberately scoped to
`pstate`, `uz_feed` needs the very fact it would prove, and
`gridAnsi_writes_grid'` — the only source of u8-quiescence after a paint —
demands `painted.size = receiver.rows`, which the ring violates by design. So the
mode re-establishment at the end of the stage would have no route.

The case split is what makes it free. With `u8need = 0` the hypothesis applies
directly; with `u8need` positive the leading ESC's `abortUtf8` makes the state
*literally equal* to the quiesced one (it touches `u8need`/`u8acc` and nothing
else), and the quiesced one has the same `modes`. Both branches land on `h`.

This delivers four of `scrollback_entry`'s sixteen conjuncts at once (`u8need`,
`insert`, `wrap`, `origin`) — the fifth, `u8acc`, follows by `u8Ok_feed`. -/
theorem mmap_of_esc_lead {f : Modes → Modes} {rest : Bytes} (h : MMap f ((0x1B : UInt8) :: rest))
    {v : Vt} (hg : v.pstate = .ground) :
    (v.feed ((0x1B : UInt8) :: rest)).pstate = .ground ∧
      (v.feed ((0x1B : UInt8) :: rest)).u8need = 0 ∧
      (v.feed ((0x1B : UInt8) :: rest)).modes = f v.modes := by
  by_cases hu : v.u8need = 0
  · exact h v hg hu
  · have hpos : v.u8need > 0 := Nat.pos_of_ne_zero hu
    have habort :
      v.abortUtf8 (0x1B : UInt8) =
        { v with
          u8need := 0, u8acc := 0 } := by
      unfold Vt.abortUtf8
      rw [ite_eq_left (by simp [hpos])]
    have habort2 :
      ({ v with
                u8need := 0, u8acc := 0 } :
              Vt).abortUtf8
          (0x1B : UInt8) =
        { v with
          u8need := 0, u8acc := 0 } := by
      unfold Vt.abortUtf8
      rw [ite_eq_right (by simp)]
    have hstep :
      v.step (0x1B : UInt8) =
        ({ v with
                u8need := 0, u8acc := 0 } :
              Vt).step
          0x1B := by
      unfold Vt.step
      dsimp only
      rw [habort, habort2]
    rw [show
        v.feed ((0x1B : UInt8) :: rest) =
          ({ v with
                  u8need := 0, u8acc := 0 } :
                Vt).feed
            ((0x1B : UInt8) :: rest)
        from by rw [feed_cons, feed_cons, hstep]]
    exact h _ hg rfl

theorem psBlind_modes : PsBlind (fun v : Vt => v.modes) := fun _ _ => rfl

theorem psBlind_pen : PsBlind (fun v : Vt => v.pen) := fun _ _ => rfl

theorem psBlind_stick : PsBlind stick := fun _ _ => rfl

/-- modes-analog of `keeps_csi_tail`: a parameter run and a final byte whose dispatch
preserves modes leaves modes alone and returns to ground. -/
theorem csi_tail_modes (params : Bytes) (final : UInt8) (hp : ParamBytes params) (h1 : 0x40 ≤ final)
    (h2 : final ≤ 0x7E)
    (hmodes : ∀ (w : Vt) (t : CsiState), (w.csiDispatch t final).modes = w.modes) {v : Vt}
    {s : CsiState} (hg : v.pstate = .csi s) (hu : v.u8need = 0) (hi : s.inter = 0) :
    (v.feed (params ++ [final])).modes = v.modes ∧
      (v.feed (params ++ [final])).pstate = .ground ∧ (v.feed (params ++ [final])).u8need = 0 :=
  csi_tail_proj psBlind_modes params final hp h1 h2 hmodes hg hu hi

theorem mmap_id_csi_seq (params : Bytes) (final : UInt8) (hp : ParamBytes params)
    (h1 : 0x40 ≤ final) (h2 : final ≤ 0x7E)
    (hmodes : ∀ (w : Vt) (t : CsiState), (w.csiDispatch t final).modes = w.modes) :
    MMap id (csiB ++ params ++ [final]) := fixes_csi_seq psBlind_modes params final hp h1 h2 hmodes

/-! ### per-final dispatch-modes facts for the preservers -/

theorem modes_csiDispatch_stbm (v : Vt) (s : CsiState) :
    (v.csiDispatch s 0x72).modes = v.modes := by
  by_cases hi : s.ignore = true
  · simp [Vt.csiDispatch, hi]
  · unfold Vt.csiDispatch
    rw [ite_eq_right (by simp [hi])]
    dsimp only
    -- kill every wrong-final arm by its absurd equation; the DECSTBM arm and the
    -- catch-all are cursor/region moves that never touch modes
    split <;>
      first
      | (rename_i heq; exact absurd heq (by decide))
      |
        ((repeat' split) <;>
            first
            | rfl
            | rw [modes_moveTo])

theorem modes_csiDispatch_cup (v : Vt) (s : CsiState) : (v.csiDispatch s 0x48).modes = v.modes := by
  by_cases hi : s.ignore = true
  · simp [Vt.csiDispatch, hi]
  · unfold Vt.csiDispatch; rw [ite_eq_right (by simp [hi])]; exact modes_moveTo _ _ _

theorem modes_csiDispatch_sgr (v : Vt) (s : CsiState) : (v.csiDispatch s 0x6D).modes = v.modes := by
  by_cases hi : s.ignore = true
  · simp [Vt.csiDispatch, hi]
  · unfold Vt.csiDispatch; rw [ite_eq_right (by simp [hi])]; dsimp only
    split <;>
      first
      | (rename_i heq; exact absurd heq (by decide))
      | ((repeat' split) <;> rfl)

/-! ### per-chunk MMap bridges -/

def smMod (n : Nat) (on : Bool) (m : Modes) : Modes :=
  (Vt.setMode { Vt.init 1 1 with modes := m } true n on).modes

theorem mmap_modeSet (n : Nat) (on : Bool) (hn : 0 < n) (hlt : n < 65535) :
    MMap (smMod n on) (modeSet n on) := by
  intro v hg hu
  obtain ⟨hm, hp, hun⟩ := modeSet_modes n on hn hlt hg hu
  exact
    ⟨hp, hun, by
      rw [hm]; exact modes_setMode true n on rfl⟩

theorem MMap.congr {f g : Modes → Modes} {bs : Bytes} (h : MMap f bs) (hfg : ∀ m, f m = g m) :
    MMap g bs := by
  intro v hg hu; obtain ⟨a, b, c⟩ := h v hg hu; exact ⟨a, b, by rw [c, hfg]⟩

-- IRM: `CSI 4 h/l` (non-private), sets `insert`. The non-private analog of
-- `modeSet_tail` with `n = 4`, so a marker-free walk to the same dispatch shape.
theorem mmap_irm (on : Bool) :
    MMap (fun m => { m with insert := on }) (csiNum 4 (if on then 0x68 else 0x6C)) := by
  intro v hg hu
  have hfinal :
    (0x40 : UInt8) ≤ (if on then 0x68 else 0x6C) ∧
      (if on then (0x68 : UInt8) else 0x6C) ≤ 0x7E := by
    cases on <;> exact ⟨by decide, by decide⟩
  rw [show
      csiNum 4 (if on then 0x68 else 0x6C) =
        [0x1B, 0x5B] ++ (digits 4 ++ [(if on then 0x68 else 0x6C : UInt8)])
      from by simp [csiNum, csiB]]
  rw [show
      ∀ (w : Vt),
        w.feed ([0x1B, 0x5B] ++ (digits 4 ++ [(if on then 0x68 else 0x6C : UInt8)])) =
          (w.feed [0x1B, 0x5B]).feed (digits 4 ++ [(if on then 0x68 else 0x6C : UInt8)])
      from fun w => by simp [Vt.feed, List.foldl_append]]
  rw [keeps_csi_open hg hu]
  obtain ⟨sa, hfeed, -⟩ :=
    csi_param_run_inter (digits 4) (v := { v with pstate := .csi {} }) rfl (by simpa using hu)
      (paramBytes_digits 4)
  obtain ⟨sb, hpsb, hcur', hhave', hpar', hint', hign', -, hpriv'⟩ :=
    csi_digits_value 4 (v := { v with pstate := .csi {} }) rfl rfl
  have hsab : sa = sb :=
    PState.csi.inj
      ((by rw [hfeed] :
            (({ v with pstate := .csi {} } : Vt).feed (digits 4)).pstate = .csi sa).symm.trans
        hpsb)
  rw [show
      ∀ (u : Vt),
        u.feed (digits 4 ++ [(if on then 0x68 else 0x6C : UInt8)]) =
          (u.feed (digits 4)).feed [(if on then 0x68 else 0x6C : UInt8)]
      from fun u => by simp [Vt.feed, List.foldl_append]]
  rw [show
      ∀ (u : Vt), u.feed [(if on then 0x68 else 0x6C : UInt8)] = u.step (if on then 0x68 else 0x6C)
      from fun _ => rfl,
    hfeed]
  rw [csi_final_step_eq (if on then 0x68 else 0x6C) rfl (by rw [hu])
      (by
        rw [hsab]; exact hint')
      hfinal.1 hfinal.2]
  unfold Vt.csiFinish
  rw [ite_eq_left
      (by
        rw [hsab]; simpa using hhave'),
    ite_eq_right
      (by
        rw [hsab, hpar']; decide)]
  dsimp only
  refine
    ⟨rfl, by
      rw [un_csiDispatch]; exact hu, ?_⟩
  have hstate :
    ({ sa with params := sa.params.push (min sa.cur 65535, sa.curSub) } : CsiState) =
      { sa with params := #[(4, sa.curSub)] } := by
    rw [hsab, hpar', hcur']; rfl
  have hpriv2 : ({ sa with params := #[(4, sa.curSub)] } : CsiState).priv = 0 := by
    show sa.priv = 0; rw [hsab]; exact hpriv'
  have hign2 : ({ sa with params := #[(4, sa.curSub)] } : CsiState).ignore = false := by
    show sa.ignore = false; rw [hsab]; exact hign'
  have hop : ({ v with pstate := .csi sa } : Vt).modes = v.modes := by rfl
  show
    (({ v with pstate := .csi sa }).csiDispatch
          { sa with params := sa.params.push (min sa.cur 65535, sa.curSub) }
          (if on then 0x68 else 0x6C)).modes =
      { v.modes with insert := on }
  rw [hstate]
  cases on
  · show (({ v with pstate := .csi sa }).csiDispatch _ 0x6C).modes = _
    rw [csiDispatch_rm_one _ _ 4 sa.curSub hign2 rfl, hpriv2]; rfl
  · show (({ v with pstate := .csi sa }).csiDispatch _ 0x68).modes = _
    rw [csiDispatch_sm_one _ _ 4 sa.curSub hign2 rfl, hpriv2]; rfl

-- Application keypad: `ESC =` (on) / `ESC >` (off)
theorem mmap_keypad (on : Bool) :
    MMap (fun m => { m with appKeypad := on }) (if on then escSeq 0x3D else escSeq 0x3E) := by
  intro v hg hu
  have step :
    ∀ (b : UInt8),
      b = 0x3D ∨ b = 0x3E →
        (v.feed (escSeq b)).pstate = .ground ∧
          (v.feed (escSeq b)).u8need = 0 ∧
          (v.feed (escSeq b)).modes = { v.modes with appKeypad := (b == 0x3D) } := by
    intro b hb
    rw [show escSeq b = [0x1B, b] from rfl,
      show v.feed [0x1B, b] = (v.step 0x1B).step b from by simp [Vt.feed], esc_step_eq hg hu,
      step_of_esc_quiet b rfl (by simpa using hu)]
    rcases hb with h | h <;> subst h <;> (unfold Vt.stepEsc; exact ⟨rfl, by simpa using hu, rfl⟩)
  cases on
  · simpa using step 0x3E (Or.inr rfl)
  · simpa using step 0x3D (Or.inl rfl)

-- Charset designations `ESC ( B` / `ESC ) B` and Shift-In `SI`: modes untouched
theorem mmap_id_charset (i x : UInt8) (hi : i = 0x28 ∨ i = 0x29) (hlo : 0x30 ≤ x) (hhi : x ≤ 0x7E) :
    MMap id (escCharset i x) := by
  intro v hg hu
  rw [show escCharset i x = [0x1B] ++ [i, x] from rfl,
    show ∀ (w : Vt), w.feed ([0x1B] ++ [i, x]) = ((w.step 0x1B).step i).step x from fun w => by
      simp [Vt.feed],
    esc_step_eq hg hu]
  have hinter : ({ v with pstate := .esc } : Vt).step i = { v with pstate := .escInter i } := by
    rcases hi with h | h <;> subst h <;>
      (rw [step_of_esc_quiet _ rfl (by simpa using hu)]; unfold Vt.stepEsc; rfl)
  rw [hinter,
    show
      ({ v with pstate := .escInter i } : Vt).step x =
        ({ v with pstate := .escInter i }).stepEscInter i x
      from by rw [step_of_escInter_quiet x rfl (by simpa using hu)]]
  rw [stepEscInter_final _ i x hlo hhi]
  rcases hi with h | h <;> subst h <;> dsimp only <;> exact ⟨rfl, by simpa using hu, rfl⟩

theorem mmap_id_si : MMap id [0x0F] := by
  intro v hg hu
  have hstep : v.step 0x0F = { v with shiftOut := false } := by
    unfold Vt.step Vt.abortUtf8
    dsimp only
    rw [ite_eq_right (by simp [hu]), hg]
    dsimp only
    unfold Vt.stepGround
    rw [ite_eq_right (by decide), ite_eq_left (by decide)]
    simp only [Vt.ctl]
    congr 1
  rw [show v.feed [0x0F] = v.step 0x0F from rfl, hstep]
  exact ⟨hg, by simpa using hu, rfl⟩

theorem mmap_id_stbm : MMap id (csiPlain 0x72) := by
  rw [show csiPlain 0x72 = csiB ++ [] ++ [0x72] from by simp [csiPlain]]
  exact
    mmap_id_csi_seq [] 0x72 ParamBytes.nil (by decide) (by decide)
      (fun w t => modes_csiDispatch_stbm w t)

theorem mmap_id_cup (a b : Nat) : MMap id (csiNum2 a b 0x48) := by
  rw [show csiNum2 a b 0x48 = csiB ++ (digits a ++ [0x3B] ++ digits b) ++ [0x48] from by
      simp [csiNum2]]
  exact
    mmap_id_csi_seq _ 0x48
      ((paramBytes_digits a |>.append
            (ParamBytes.cons (by decide) (by decide) ParamBytes.nil)).append
        (paramBytes_digits b))
      (by decide) (by decide) (fun w t => modes_csiDispatch_cup w t)

theorem mmap_id_sgr : MMap id (csiNum 0 0x6D) := by
  rw [show csiNum 0 0x6D = csiB ++ digits 0 ++ [0x6D] from by simp [csiNum]]
  exact
    mmap_id_csi_seq (digits 0) 0x6D (paramBytes_digits 0) (by decide) (by decide)
      (fun w t => modes_csiDispatch_sgr w t)

theorem mmap_id_defaultTitleAnsi : MMap id defaultTitleAnsi := by
  intro v hg hu
  rw [defaultTitleAnsi_feed hg]
  unfold Vt.abortUtf8
  rw [ite_eq_right (by simp [hu])]
  exact ⟨rfl, hu, rfl⟩

theorem MMap.id_of {f : Modes → Modes} {bs : Bytes} (h : MMap f bs) (hf : ∀ m, f m = m) :
    MMap id bs := h.congr hf

/-- **The hand-back leaves the modes canonical, for any receiver** (anchor A5,
outbound value half). `leaveAnsi`'s lead-in grounds `w`, then each mode chunk sets
its field absolutely and the non-mode chunks leave modes alone, so the composite is
the default record regardless of what the session left behind. -/
theorem leave_modes (w : Vt) : (w.feed leaveAnsi).modes = ({} : Modes) := by
  -- the tail (everything after the `ESC \` lead-in), right-associated
  have htail :
    MMap (fun _ => ({} : Modes))
      (modeSet 1049 false ++
        (csiNum 4 0x6C ++
          (modeSet 25 true ++
            (modeSet 2004 false ++
              (modeSet 1000 false ++
                (modeSet 1002 false ++
                  (modeSet 1003 false ++
                    (modeSet 1006 false ++
                      (modeSet 1004 false ++
                        (modeSet 1 false ++
                          (escSeq 0x3E ++
                            (modeSet 6 false ++
                              (modeSet 7 true ++
                                (csiPlain 0x72 ++
                                  (escCharset 0x28 0x42 ++
                                    (escCharset 0x29 0x42 ++
                                      ([0x0F] ++
                                        (csiNum2 999 1 0x48 ++ csiNum 0 0x6D)))))))))))))))))) := by
    refine
      MMap.congr ?_
        (by
          intro m; rfl)
    exact
      (mmap_modeSet 1049 false (by decide) (by decide)).comp
        ((mmap_irm false).comp
          ((mmap_modeSet 25 true (by decide) (by decide)).comp
            ((mmap_modeSet 2004 false (by decide) (by decide)).comp
              ((mmap_modeSet 1000 false (by decide) (by decide)).comp
                ((mmap_modeSet 1002 false (by decide) (by decide)).comp
                  ((mmap_modeSet 1003 false (by decide) (by decide)).comp
                    ((mmap_modeSet 1006 false (by decide) (by decide)).comp
                      ((mmap_modeSet 1004 false (by decide) (by decide)).comp
                        ((mmap_modeSet 1 false (by decide) (by decide)).comp
                          ((mmap_keypad false).comp
                            ((mmap_modeSet 6 false (by decide) (by decide)).comp
                              ((mmap_modeSet 7 true (by decide) (by decide)).comp
                                ((mmap_id_stbm).comp
                                  ((mmap_id_charset 0x28 0x42 (Or.inl rfl) (by decide)
                                        (by decide)).comp
                                    ((mmap_id_charset 0x29 0x42 (Or.inr rfl) (by decide)
                                          (by decide)).comp
                                      ((mmap_id_si).comp
                                        ((mmap_id_cup 999 1).comp mmap_id_sgr)))))))))))))))))
  have hlead := st_grounds w
  rw [show
      leaveAnsi =
        escSeq 0x5C ++
          (modeSet 1049 false ++
            (csiNum 4 0x6C ++
              (modeSet 25 true ++
                (modeSet 2004 false ++
                  (modeSet 1000 false ++
                    (modeSet 1002 false ++
                      (modeSet 1003 false ++
                        (modeSet 1006 false ++
                          (modeSet 1004 false ++
                            (modeSet 1 false ++
                              (escSeq 0x3E ++
                                (modeSet 6 false ++
                                  (modeSet 7 true ++
                                    (csiPlain 0x72 ++
                                      (escCharset 0x28 0x42 ++
                                        (escCharset 0x29 0x42 ++
                                          ([0x0F] ++
                                            (csiNum2 999 1 0x48 ++
                                              csiNum 0 0x6D)))))))))))))))))) ++
          defaultTitleAnsi
      from by simp only [leaveAnsi, List.append_assoc]]
  rw [feed_append, feed_append]
  obtain ⟨hg, hu, hm⟩ := htail _ hlead.1 hlead.2
  exact ((mmap_id_defaultTitleAnsi _ hg hu).2.2).trans hm

/-- **A5, outbound.** The hand-back returns the parser to ground with nothing
half-decoded and the modes to the default, for any receiver — the value companion
to `leave_grounds`. -/
theorem leave_canonical (w : Vt) :
    (w.feed leaveAnsi).pstate = .ground ∧ (w.feed leaveAnsi).modes = ({} : Modes) :=
  ⟨leave_grounds w, leave_modes w⟩

/-! ## §Handback / anchor A5 — inbound: restore installs the session's modes

The mirror of `leave_modes`. `restore`'s prologue grounds any receiver; the chunks
up to the title only need to leave the parser in `ground` (the `Ends` ladder, no
modes reasoning — so the repaint is *not* dragged into a modes proof), and the
title's leading `ESC` clears `u8need` (`uz_titleAnsi`); then `modesAnsi` sets every
mode field to the session's value (`mmap_modesAnsi`, a constant transform once the
mouse field is in its allowlist) and the suffix preserves them. -/

theorem MMap.ite {c : Prop} [Decidable c] {f g : Modes → Modes} {a b : Bytes} (ha : c → MMap f a)
    (hb : ¬c → MMap g b) : MMap (if c then f else g) (if c then a else b) := by
  by_cases h : c
  · rw [ite_eq_left h, ite_eq_left h]; exact ha h
  · rw [ite_eq_right h, ite_eq_right h]; exact hb h

theorem MMap.nil : MMap id [] := fun _ hg hu => ⟨hg, hu, rfl⟩

theorem mmap_id_append {a b : Bytes} (ha : MMap id a) (hb : MMap id b) : MMap id (a ++ b) :=
  (ha.comp hb).congr (fun _ => rfl)

/-! ### SUFFIX preservers (modes untouched) -/

/-- `ED` writes cells, never a mode. -/
theorem mmap_id_ed (n : Nat) : MMap id (csiNum n 0x4A) := by
  rw [show csiNum n 0x4A = csiB ++ digits n ++ [0x4A] from rfl]
  refine mmap_id_csi_seq _ 0x4A (paramBytes_digits n) (by decide) (by decide) (fun w t => ?_)
  unfold Vt.csiDispatch
  dsimp only
  split
  · rfl
  · exact modes_eraseScreen w _

theorem mmap_id_sgrOf (codes : List Nat) : MMap id (sgrOf codes) :=
  fixes_sgrOf psBlind_modes codes modes_csiDispatch_sgr

theorem mmap_id_sgrColorSeq (c : Color) (isFg : Bool) : MMap id (sgrColorSeq c isFg) :=
  fixes_sgrColorSeq psBlind_modes c isFg modes_csiDispatch_sgr

theorem mmap_id_penSgr (p : Pen) : MMap id (penSgr p) :=
  fixes_penSgr psBlind_modes p modes_csiDispatch_sgr

theorem mmap_id_so : MMap id [0x0E] := by
  intro v hg hu
  have hstep : v.step 0x0E = { v with shiftOut := true } := by
    unfold Vt.step Vt.abortUtf8
    dsimp only
    rw [ite_eq_right (by simp [hu]), hg]
    dsimp only
    unfold Vt.stepGround
    rw [ite_eq_right (by decide), ite_eq_left (by decide)]
    simp only [Vt.ctl]
    congr 1
  rw [show v.feed [0x0E] = v.step 0x0E from rfl, hstep]
  exact ⟨hg, by simpa using hu, rfl⟩

theorem mmap_id_charsetAnsi (v : Vt) : MMap id (charsetAnsi v) := by
  unfold charsetAnsi
  refine mmap_id_append (mmap_id_append ?_ ?_) ?_
  · split
    · exact mmap_id_charset 0x28 0x30 (Or.inl rfl) (by decide) (by decide)
    · exact mmap_id_charset 0x28 0x42 (Or.inl rfl) (by decide) (by decide)
  · split
    · exact mmap_id_charset 0x29 0x30 (Or.inr rfl) (by decide) (by decide)
    · exact mmap_id_charset 0x29 0x42 (Or.inr rfl) (by decide) (by decide)
  · split
    · exact mmap_id_so
    · exact MMap.nil

theorem mmap_id_cursorAnsi (v : Vt) : MMap id (cursorAnsi v) := by
  unfold cursorAnsi
  split <;> exact mmap_id_cup _ _

/-- Glyph bytes leave modes alone even when the receiver has a partial decoder. -/
theorem modes_glyph_step {v : Vt} (b : UInt8) (hg : v.pstate = .ground) (hb : 0x20 ≤ b) :
    (v.step b).modes = v.modes := by
  have hac (w : Vt) (n : Nat) : (w.acceptChar n).modes = w.modes := by
    unfold Vt.acceptChar
    split <;> exact modes_print' _ _
  have hs (w : Vt) : (w.stepGround b).modes = w.modes := by
    unfold Vt.stepGround
    split
    · rfl
    rw [ite_eq_right
        (show ¬b < (0x20 : UInt8) from by
          simp only [UInt8.lt_iff_toNat_lt]
          have := UInt8.le_iff_toNat_le.mp hb
          omega)]
    split
    · exact hac _ _
    split
    · split
      · rfl
      split
      · exact hac _ _
      · rfl
    repeat' split
    all_goals rfl
  have hp : (v.abortUtf8 b).pstate = .ground := (ps_abortUtf8 _ _).trans hg
  unfold Vt.step
  dsimp only
  rw [hp, hs]
  unfold Vt.abortUtf8
  split <;> rfl

theorem modes_glyph_run :
    ∀ (bs : Bytes) (v : Vt), v.pstate = .ground → (∀ b ∈ bs, 0x20 ≤ b) → (v.feed bs).modes = v.modes
  | [], _, _, _ => rfl
  | b :: bs, v, hg, hb => by
    have h := hb b (by simp)
    rw [feed_cons]
    exact
      (modes_glyph_run bs _
            (ground_step b hg
              (by
                intro he
                subst b
                exact (by decide : ¬(0x20 : UInt8) ≤ 0x1B) h))
            (fun c hc => hb c (by simp [hc]))).trans
        (modes_glyph_step b hg h)

theorem modes_cellText (c : Cell) {v : Vt} (hg : v.pstate = .ground) :
    (v.feed (cellText c)).modes = v.modes := by
  apply modes_glyph_run _ _ hg
  intro b hb
  rcases List.mem_append.mp hb with hb | hb
  · exact (utf8_no_ctl _ (safeChar_ge c.base).1 (safeChar_ge c.base).2 b hb).1
  · exact (utf8s_no_ctl _ b hb).1

theorem mmap_penSgr_of_ground (p : Pen) {v : Vt} (hg : v.pstate = .ground) :
    (v.feed (penSgr p)).pstate = .ground ∧
      (v.feed (penSgr p)).u8need = 0 ∧ (v.feed (penSgr p)).modes = v.modes := by
  have hm := mmap_id_penSgr p
  have he : penSgr p = 0x1B :: (penSgr p).drop 1 := by simp [penSgr, sgrOf, csiB]
  rw [he] at hm ⊢
  exact mmap_of_esc_lead hm hg

theorem mmap_id_pendingAnsi (cols : Nat) (grid : Array Row) (cur : Cursor) (row : Nat) (pen : Pen) :
    MMap id (pendingAnsi cols grid cur row pen) := by
  let cells := grid.getD cur.y #[]
  let x := if (cells.at cur.x).width == 0 then cur.x - 1 else cur.x
  let cell := cellFit (cells.at x)
  change
    MMap id
      (if
          cur.pending && cur.y < grid.size && cur.x < cells.size && cur.x + 1 == cols &&
            charWidth cell.base != 0 &&
            x + charWidth cell.base == cols then
        csiNum2 row (x + 1) 0x48 ++ penSgr cell.pen ++ cellText cell ++ penSgr pen
      else [])
  split
  · intro v hg hu
    rw [feed_append, feed_append, feed_append]
    have hc := mmap_id_cup row (x + 1) v hg hu
    have hp := mmap_id_penSgr cell.pen _ hc.1 hc.2.1
    have ht := modes_cellText cell hp.1
    have hq := mmap_penSgr_of_ground pen (ends_cellText cell _ hp.1)
    exact ⟨hq.1, hq.2.1, hq.2.2.trans (ht.trans (hp.2.2.trans hc.2.2))⟩
  · exact MMap.nil

/-! ### The window title leaves nothing half-decoded -/

/-- Feeding an OSC body from `.osc acc false` with nothing pending keeps `u8need` 0. -/
theorem un_osc_run :
    ∀ (bs : Bytes) {v : Vt} {acc : Array UInt8},
      v.pstate = .osc acc false →
        v.u8need = 0 → (∀ b ∈ bs, b ≠ 0x1B ∧ b ≠ 0x07) → (v.feed bs).u8need = 0
  | [], _, _, _, hu, _ => hu
  | x :: xs, v, acc, hg, hu, h => by
    rw [feed_cons]
    obtain ⟨acc', hs⟩ := osc_accum_step x hg (h x (by simp)).1 (h x (by simp)).2
    have hux : (v.step x).u8need = 0 := by
      rw [step_of_osc_quiet x hg hu, un_stepOsc]; exact hu
    exact un_osc_run xs hs hux (fun b hb => h b (by simp [hb]))

theorem uz_titleAnsi (v : Vt) {g : Vt} (hg : g.pstate = .ground) :
    (g.feed (titleAnsi v)).u8need = 0 := by
  unfold titleAnsi
  rw [show
      (escB ++ [0x5D, 0x32, 0x3B] ++ utf8s v.title.toList ++ [0x07] : Bytes) =
        0x1B :: 0x5D :: 0x32 :: 0x3B :: (utf8s v.title.toList ++ [0x07])
      from by simp [escB]]
  rw [feed_cons, feed_cons, feed_cons, feed_cons]
  have he : (g.step 0x1B).pstate = .esc := esc_step hg
  have hu1 : (g.step 0x1B).u8need = 0 := uz_step_esc g
  have ho : ((g.step 0x1B).step 0x5D).pstate = .osc #[] false := osc_open_step he
  have hu2 : ((g.step 0x1B).step 0x5D).u8need = 0 := by
    rw [step_of_esc_quiet 0x5D he hu1, uz_stepEsc 0x5D hu1]
  obtain ⟨acc2, ho2⟩ := osc_accum_step 0x32 ho (by decide) (by decide)
  have hu3 : (((g.step 0x1B).step 0x5D).step 0x32).u8need = 0 := by
    rw [step_of_osc_quiet 0x32 ho hu2, un_stepOsc]; exact hu2
  obtain ⟨acc3, ho3⟩ := osc_accum_step 0x3B ho2 (by decide) (by decide)
  have hu4 : ((((g.step 0x1B).step 0x5D).step 0x32).step 0x3B).u8need = 0 := by
    rw [step_of_osc_quiet 0x3B ho2 hu3, un_stepOsc]; exact hu3
  -- feed the payload (stays in osc, u8need 0), then BEL (oscFinish preserves u8need)
  rw [show
      ∀ (w : Vt),
        w.feed (utf8s v.title.toList ++ [0x07]) = (w.feed (utf8s v.title.toList)).feed [0x07]
      from fun w => by simp [Vt.feed, List.foldl_append]]
  obtain ⟨acc4, ho4⟩ := osc_accum_feed (utf8s v.title.toList) ho3 (utf8s_no_esc_bel _)
  have hu5 :
    (((((g.step 0x1B).step 0x5D).step 0x32).step 0x3B).feed (utf8s v.title.toList)).u8need = 0 :=
    un_osc_run (utf8s v.title.toList) ho3 hu4 (utf8s_no_esc_bel _)
  rw [show ∀ (w : Vt), w.feed [(0x07 : UInt8)] = w.step 0x07 from fun _ => rfl]
  rw [step_of_osc_quiet 0x07 ho4 hu5, un_stepOsc]
  exact hu5

/-! ### modesAnsi sets every mode to the session's value

Each mode chunk is given its *explicit* record-update transform (not the opaque
`smMod`), so the composite of thirteen is a shallow nest of `{· with field := …}`
that `rfl` collapses — `smMod` nested that deep blows the `whnf` budget. -/

theorem mmap_wrap (b : Bool) : MMap (fun m => { m with wrap := b }) (modeSet 7 b) :=
  (mmap_modeSet 7 b (by decide) (by decide)).congr (fun m => by simp [smMod, Vt.setMode])

theorem mmap_appCursor (b : Bool) : MMap (fun m => { m with appCursor := b }) (modeSet 1 b) :=
  (mmap_modeSet 1 b (by decide) (by decide)).congr (fun m => by simp [smMod, Vt.setMode])

theorem mmap_cursorVis (b : Bool) : MMap (fun m => { m with cursorVisible := b }) (modeSet 25 b) :=
  (mmap_modeSet 25 b (by decide) (by decide)).congr (fun m => by simp [smMod, Vt.setMode])

theorem mmap_bracketed (b : Bool) :
    MMap (fun m => { m with bracketedPaste := b }) (modeSet 2004 b) :=
  (mmap_modeSet 2004 b (by decide) (by decide)).congr (fun m => by simp [smMod, Vt.setMode])

theorem mmap_mouse0 (n : Nat) (hn : 0 < n) (hlt : n < 65535)
    (hn' : n = 1000 ∨ n = 1002 ∨ n = 1003) :
    MMap (fun m => { m with mouse := 0 }) (modeSet n false) :=
  (mmap_modeSet n false hn hlt).congr
    (fun m => by rcases hn' with h | h | h <;> subst h <;> simp [smMod, Vt.setMode])

theorem mmap_mouseSet (n : Nat) (hn : 0 < n) (hlt : n < 65535)
    (hn' : n = 1000 ∨ n = 1002 ∨ n = 1003) :
    MMap (fun m => { m with mouse := n }) (modeSet n true) :=
  (mmap_modeSet n true hn hlt).congr
    (fun m => by rcases hn' with h | h | h <;> subst h <;> simp [smMod, Vt.setMode])

theorem mmap_mouseSgr (b : Bool) : MMap (fun m => { m with mouseSgr := b }) (modeSet 1006 b) :=
  (mmap_modeSet 1006 b (by decide) (by decide)).congr (fun m => by simp [smMod, Vt.setMode])

theorem mmap_focus (b : Bool) : MMap (fun m => { m with focusEvents := b }) (modeSet 1004 b) :=
  (mmap_modeSet 1004 b (by decide) (by decide)).congr (fun m => by simp [smMod, Vt.setMode])

theorem mmap_origin (b : Bool) : MMap (fun m => { m with origin := b }) (modeSet 6 b) :=
  (mmap_modeSet 6 b (by decide) (by decide)).congr (fun m => by simp [smMod, Vt.setMode, Vt.moveTo])

theorem modes_cursorPendingAnsi (v w : Vt) (hg : w.pstate = .ground) (hu : w.u8need = 0)
    (hm : w.modes = v.modes) : (w.feed (cursorPendingAnsi v)).modes = v.modes := by
  unfold cursorPendingAnsi
  split
  · have hstart :=
      ((((mmap_wrap true).comp (mmap_irm false)).comp
                (mmap_id_charset 0x28 0x42 (Or.inl rfl) (by decide) (by decide))).comp
            (mmap_id_charset 0x29 0x42 (Or.inr rfl) (by decide) (by decide))).comp
        mmap_id_si
    have hpaint :=
      hstart.comp
        (mmap_id_pendingAnsi v.cols v.grid v.cursor
          (if v.modes.origin then v.cursor.y - v.top + 1 else v.cursor.y + 1) v.pen)
    have htail :=
      (((hpaint.comp (mmap_wrap v.modes.wrap)).comp (mmap_irm v.modes.insert)).comp
            (mmap_id_charsetAnsi v)).comp
        (mmap_id_penSgr v.pen)
    have h := (htail w hg hu).2.2
    simpa [hm] using h
  · exact hm

/-- **The scrollback stage's mode tail, from a receiver whose decoder may be
mid-sequence.** `scrollbackAnsi` ends with `4l ?6l ?7h`, contiguous and
ESC-leading, and this is the whole reason for that shape: an `MMap` cannot be
pushed backwards across the ring's glyph bytes, so the three modes
`gridAnsi_writes_grid` needs are re-established *after* the paint, where
`mmap_irm`/`mmap_origin`/`mmap_wrap` already close them, and `mmap_of_esc_lead`
supplies the missing `u8need = 0`.

Twelve bytes, and behaviourally inert in every fixture (`prologueAnsi` already
established the same three, and nothing between them and here changes them). So
a test could not catch their removal; what catches it is this theorem — drop them
and `scrollback_entry`'s `insert` and `wrap` conjuncts stop closing. -/
theorem sbTail_modes {y : Vt} (hg : y.pstate = .ground) :
    (y.feed (csiNum 4 0x6C ++ modeSet 6 false ++ modeSet 7 true)).pstate = .ground ∧
      (y.feed (csiNum 4 0x6C ++ modeSet 6 false ++ modeSet 7 true)).u8need = 0 ∧
      (y.feed (csiNum 4 0x6C ++ modeSet 6 false ++ modeSet 7 true)).modes.insert = false ∧
      (y.feed (csiNum 4 0x6C ++ modeSet 6 false ++ modeSet 7 true)).modes.wrap = true ∧
      (y.feed (csiNum 4 0x6C ++ modeSet 6 false ++ modeSet 7 true)).modes.origin = false := by
  have hm :
    MMap
      (fun m =>
        { m with
          insert := false, origin := false, wrap := true })
      (csiNum 4 0x6C ++ modeSet 6 false ++ modeSet 7 true) :=
    (((show MMap (fun m => { m with insert := false }) (csiNum 4 0x6C) from by
                  simpa using mmap_irm false).comp
              (mmap_origin false)).comp
          (mmap_wrap true)).congr
      (fun m => rfl)
  have hcons :
    (csiNum 4 0x6C ++ modeSet 6 false ++ modeSet 7 true) =
      (0x1B : UInt8) ::
        ((csiB ++ digits 4 ++ [(0x6C : UInt8)] ++ modeSet 6 false ++ modeSet 7 true).drop 1) := by
    simp [csiNum, csiB, modeSet, csiPriv]
  rw [hcons] at hm ⊢
  obtain ⟨h1, h2, h3⟩ := mmap_of_esc_lead hm hg
  exact ⟨h1, h2, by rw [h3], by rw [h3], by rw [h3]⟩

theorem Modes.ext' {a b : Modes} (h1 : a.wrap = b.wrap) (h2 : a.origin = b.origin)
    (h3 : a.insert = b.insert) (h4 : a.cursorVisible = b.cursorVisible)
    (h5 : a.appCursor = b.appCursor) (h6 : a.appKeypad = b.appKeypad)
    (h7 : a.bracketedPaste = b.bracketedPaste) (h8 : a.mouse = b.mouse)
    (h9 : a.mouseSgr = b.mouseSgr) (h10 : a.focusEvents = b.focusEvents) : a = b := by
  cases a; cases b; simp_all

theorem mmap_modesAnsi (v : Vt)
    (hmouse :
      v.modes.mouse = 0 ∨ v.modes.mouse = 1000 ∨ v.modes.mouse = 1002 ∨ v.modes.mouse = 1003) :
    MMap (fun _ => v.modes) (modesAnsi v) := by
  unfold modesAnsi
  have hmite :
    MMap
      (if (v.modes.mouse == 1000 || v.modes.mouse == 1002 || v.modes.mouse == 1003) = true then
        (fun m => { m with mouse := v.modes.mouse })
      else id)
      (if v.modes.mouse == 1000 || v.modes.mouse == 1002 || v.modes.mouse == 1003 then
        modeSet v.modes.mouse true
      else []) :=
    MMap.ite (c := (v.modes.mouse == 1000 || v.modes.mouse == 1002 || v.modes.mouse == 1003) = true)
      (fun hc =>
        mmap_mouseSet v.modes.mouse
          (by
            rcases hmouse with h | h | h | h <;>
              (rw [h] at hc ⊢;
               first
               | omega
               | simp at hc))
          (by rcases hmouse with h | h | h | h <;> rw [h] <;> omega)
          (by
            rcases hmouse with h | h | h | h
            · rw [h] at hc; simp at hc
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr h)))
      (fun _ => MMap.nil)
  have h1 := (mmap_wrap v.modes.wrap).comp (mmap_appCursor v.modes.appCursor)
  have h2 := h1.comp (mmap_keypad v.modes.appKeypad)
  have h3 := h2.comp (mmap_cursorVis v.modes.cursorVisible)
  have h4 := h3.comp (mmap_bracketed v.modes.bracketedPaste)
  have h5 := h4.comp (mmap_mouse0 1000 (by decide) (by decide) (Or.inl rfl))
  have h6 := h5.comp (mmap_mouse0 1002 (by decide) (by decide) (Or.inr (Or.inl rfl)))
  have h7 := h6.comp (mmap_mouse0 1003 (by decide) (by decide) (Or.inr (Or.inr rfl)))
  have h8 := h7.comp hmite
  have h9 := h8.comp (mmap_mouseSgr v.modes.mouseSgr)
  have h10 := h9.comp (mmap_focus v.modes.focusEvents)
  have h11 := h10.comp (mmap_origin v.modes.origin)
  have h12 := h11.comp (mmap_irm v.modes.insert)
  refine h12.congr ?_
  intro m
  refine Modes.ext' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    (rcases hmouse with h | h | h | h <;> simp [h])

/-! ### The inbound value claim (A5 inbound) -/

theorem restore_modes_placed (v w : Vt)
    (hmouse :
      v.modes.mouse = 0 ∨ v.modes.mouse = 1000 ∨ v.modes.mouse = 1002 ∨ v.modes.mouse = 1003) :
    (w.feed (restoreBody v ++ cursorAnsi v)).modes = v.modes := by
  -- MID2 = prologue .. saved (before the title); it grounds any receiver
  have hEndsRest :
    Ends
      (csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v ++ regionAnsi v ++ tabsAnsi v ++
        savedAnsi v ++
        savedPendingAnsi v) := by
    refine Ends.append ?_ (ends_savedPendingAnsi v)
    refine Ends.append ?_ (ends_savedAnsi v)
    refine Ends.append ?_ (ends_tabsAnsi v)
    refine Ends.append ?_ (ends_regionAnsi v)
    refine Ends.append ?_ (ends_screensAnsi v)
    exact
      (ends_csiNum 0 0x6D (by decide) (by decide)).append
        (ends_csiNum 2 0x4A (by decide) (by decide))
  have hg2 :
    (w.feed
          (prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v ++ regionAnsi v ++
            tabsAnsi v ++
            savedAnsi v ++
            savedPendingAnsi v)).pstate =
      .ground := by
    rw [show
        prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v ++ regionAnsi v ++
            tabsAnsi v ++
            savedAnsi v ++
            savedPendingAnsi v =
          prologueAnsi v ++
            (csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v ++ regionAnsi v ++ tabsAnsi v ++
              savedAnsi v ++
              savedPendingAnsi v)
        from by simp only [List.append_assoc],
      feed_append]
    exact hEndsRest _ (prologue_grounds v w)
  -- g1 = w.feed (MID2 ++ title): ground, u8need 0
  have hsplitMID :
    restoreBody v ++ cursorAnsi v =
      (prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v ++ regionAnsi v ++
          tabsAnsi v ++
          savedAnsi v ++
          savedPendingAnsi v) ++
        (titleAnsi v ++ (modesAnsi v ++ charsetAnsi v ++ penSgr v.pen ++ cursorAnsi v)) := by
    simp only [restoreBody, List.append_assoc]
  rw [hsplitMID, feed_append, feed_append]
  -- after the title the parser is ground with nothing pending (`ends_titleAnsi`,
  -- `uz_titleAnsi`); the suffix chain `modesAnsi ++ charset ++ pen ++ cursor` is the
  -- constant transform `fun _ => v.modes`
  have htail :=
    (((mmap_modesAnsi v hmouse).comp (mmap_id_charsetAnsi v)).comp (mmap_id_penSgr v.pen)).comp
      (mmap_id_cursorAnsi v)
  exact (htail _ (ends_titleAnsi v _ hg2) (uz_titleAnsi v hg2)).2.2

theorem restore_modes_any (v w : Vt)
    (hmouse :
      v.modes.mouse = 0 ∨ v.modes.mouse = 1000 ∨ v.modes.mouse = 1002 ∨ v.modes.mouse = 1003) :
    (w.feed (restore v)).modes = v.modes := by
  unfold restore
  rw [feed_append]
  apply modes_cursorPendingAnsi
  · exact restore_placed_grounds v w
  · rw [feed_append]
    unfold cursorAnsi csiNum2
    split <;>
      exact
        u8_zero_after_csi _ _
          (by
            exact
              ((paramBytes_digits _).append
                    (ParamBytes.cons (by decide) (by decide) ParamBytes.nil)).append
                (paramBytes_digits _))
          (by decide) _
  · exact restore_modes_placed v w hmouse

/-! ### A5 inbound, continued: the pen (a non-modes restored field)

`restore` installs the session's pen into any receiver — the first non-modes field
lifted from the `dirty`-receiver fixtures to a theorem. `penSgr_feed` sets the pen;
the pen-projection CSI walk (`csi_tail_pen`) shows the trailing `cursorAnsi` (a
`CUP`/`moveTo`) preserves it. -/

theorem pen_moveTo (v : Vt) (x y : Nat) : (v.moveTo x y).pen = v.pen := by rfl

theorem pen_csiDispatch_cup (v : Vt) (s : CsiState) : (v.csiDispatch s 0x48).pen = v.pen := by
  by_cases hi : s.ignore = true
  · simp [Vt.csiDispatch, hi]
  · unfold Vt.csiDispatch; rw [ite_eq_right (by simp [hi])]; exact pen_moveTo _ _ _

/-- pen-projection analog of `csi_tail_modes` — the second instance of
`csi_tail_proj`, which is what showed the walk wanted generalizing. -/
theorem csi_tail_pen (params : Bytes) (final : UInt8) (hp : ParamBytes params) (h1 : 0x40 ≤ final)
    (h2 : final ≤ 0x7E) (hpen : ∀ (w : Vt) (t : CsiState), (w.csiDispatch t final).pen = w.pen)
    {v : Vt} {s : CsiState} (hg : v.pstate = .csi s) (hu : v.u8need = 0) (hi : s.inter = 0) :
    (v.feed (params ++ [final])).pen = v.pen ∧
      (v.feed (params ++ [final])).pstate = .ground ∧ (v.feed (params ++ [final])).u8need = 0 :=
  csi_tail_proj psBlind_pen params final hp h1 h2 hpen hg hu hi

theorem pen_cursorAnsi (v : Vt) {g : Vt} (hg : g.pstate = .ground) (hu : g.u8need = 0) :
    (g.feed (cursorAnsi v)).pen = g.pen := by
  have key : ∀ (a b : Nat), (g.feed (csiNum2 a b 0x48)).pen = g.pen := by
    intro a b
    rw [show csiNum2 a b 0x48 = csiB ++ (digits a ++ [0x3B] ++ digits b) ++ [0x48] from by
        simp [csiNum2]]
    rw [show
        (csiB ++ (digits a ++ [0x3B] ++ digits b) ++ [0x48] : Bytes) =
          [0x1B, 0x5B] ++ ((digits a ++ [0x3B] ++ digits b) ++ [0x48])
        from by
        unfold csiB; simp]
    rw [show
        ∀ (w : Vt),
          w.feed ([0x1B, 0x5B] ++ ((digits a ++ [0x3B] ++ digits b) ++ [0x48])) =
            (w.feed [0x1B, 0x5B]).feed ((digits a ++ [0x3B] ++ digits b) ++ [0x48])
        from fun w => by simp [Vt.feed, List.foldl_append]]
    rw [keeps_csi_open hg hu]
    exact
      (csi_tail_pen _ 0x48
          (((paramBytes_digits a).append
                (ParamBytes.cons (by decide) (by decide) ParamBytes.nil)).append
            (paramBytes_digits b))
          (by decide) (by decide) (fun w t => pen_csiDispatch_cup w t) rfl (by simpa using hu)
          rfl).1
  unfold cursorAnsi
  split <;> exact key _ _

/-- `modesAnsi` ends with `CSI 4 h/l` (IRM), and a CSI final zeroes `u8need`
regardless of what came before. -/
theorem un_modesAnsi (v : Vt) (g : Vt) : (g.feed (modesAnsi v)).u8need = 0 := by
  rw [show
      modesAnsi v =
        (modeSet 7 v.modes.wrap ++ modeSet 1 v.modes.appCursor ++
            (if v.modes.appKeypad then escSeq 0x3D else escSeq 0x3E) ++
            modeSet 25 v.modes.cursorVisible ++
            modeSet 2004 v.modes.bracketedPaste ++
            modeSet 1000 false ++
            modeSet 1002 false ++
            modeSet 1003 false ++
            (if v.modes.mouse == 1000 || v.modes.mouse == 1002 || v.modes.mouse == 1003 then
              modeSet v.modes.mouse true
            else []) ++
            modeSet 1006 v.modes.mouseSgr ++
            modeSet 1004 v.modes.focusEvents ++
            modeSet 6 v.modes.origin) ++
          (csiB ++ digits 4 ++ [(if v.modes.insert then 0x68 else 0x6C : UInt8)])
      from by simp only [modesAnsi, csiNum]]
  rw [feed_append]
  exact u8_zero_after_csi (digits 4) _ (paramBytes_digits 4) (by cases v.modes.insert <;> decide) _

/-- **A5 inbound, the pen.** `restore` installs the session's pen into any receiver:
the body ends `… charsetAnsi ++ penSgr v.pen`, `penSgr_feed` sets the pen to exactly
`v.pen` from the grounded prefix, and the trailing `cursorAnsi` (a `CUP`, i.e.
`moveTo`) preserves it. -/
theorem restore_pen_placed (v w : Vt) : (w.feed (restoreBody v ++ cursorAnsi v)).pen = v.pen := by
  -- C = everything up to (not including) penSgr; it grounds `w` with nothing pending
  have hEndsC :
    Ends
      (csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v ++ regionAnsi v ++ tabsAnsi v ++
        savedAnsi v ++
        savedPendingAnsi v ++
        titleAnsi v ++
        modesAnsi v ++
        charsetAnsi v) :=
    (((((((((ends_csiNum 0 0x6D (by decide) (by decide)).append
                                      (ends_csiNum 2 0x4A (by decide) (by decide))).append
                                  (ends_screensAnsi v)).append
                              (ends_regionAnsi v)).append
                          (ends_tabsAnsi v)).append
                      (ends_savedAnsi v)).append
                  (ends_savedPendingAnsi v)).append
              (ends_titleAnsi v)).append
          (ends_modesAnsi v)).append
      (ends_charsetAnsi v)
  have hCground :
    (w.feed
          (prologueAnsi v ++
            (csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v ++ regionAnsi v ++ tabsAnsi v ++
              savedAnsi v ++
              savedPendingAnsi v ++
              titleAnsi v ++
              modesAnsi v ++
              charsetAnsi v))).pstate =
      .ground := by
    rw [feed_append]; exact hEndsC _ (prologue_grounds v w)
  -- u8need 0 at C: modesAnsi ends in a CSI (→0), and charsetAnsi preserves 0
  have hMground :
    (w.feed
          (prologueAnsi v ++
            (csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v ++ regionAnsi v ++ tabsAnsi v ++
              savedAnsi v ++
              savedPendingAnsi v ++
              titleAnsi v ++
              modesAnsi v))).pstate =
      .ground := by
    rw [feed_append]
    exact
      ((((((((ends_csiNum 0 0x6D (by decide) (by decide)).append
                                    (ends_csiNum 2 0x4A (by decide) (by decide))).append
                                (ends_screensAnsi v)).append
                            (ends_regionAnsi v)).append
                        (ends_tabsAnsi v)).append
                    (ends_savedAnsi v)).append
                (ends_savedPendingAnsi v)).append
            (ends_titleAnsi v)).append
        (ends_modesAnsi v) _ (prologue_grounds v w)
  have hMu :
    (w.feed
          (prologueAnsi v ++
            (csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v ++ regionAnsi v ++ tabsAnsi v ++
              savedAnsi v ++
              savedPendingAnsi v ++
              titleAnsi v ++
              modesAnsi v))).u8need =
      0 := by
    rw [show
        (prologueAnsi v ++
            (csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v ++ regionAnsi v ++ tabsAnsi v ++
              savedAnsi v ++
              savedPendingAnsi v ++
              titleAnsi v ++
              modesAnsi v)) =
          (prologueAnsi v ++
              (csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v ++ regionAnsi v ++ tabsAnsi v ++
                savedAnsi v ++
                savedPendingAnsi v ++
                titleAnsi v)) ++
            modesAnsi v
        from by simp only [List.append_assoc],
      feed_append]
    exact un_modesAnsi v _
  have hCu :
    (w.feed
          (prologueAnsi v ++
            (csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v ++ regionAnsi v ++ tabsAnsi v ++
              savedAnsi v ++
              savedPendingAnsi v ++
              titleAnsi v ++
              modesAnsi v ++
              charsetAnsi v))).u8need =
      0 := by
    rw [show
        (prologueAnsi v ++
            (csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v ++ regionAnsi v ++ tabsAnsi v ++
              savedAnsi v ++
              savedPendingAnsi v ++
              titleAnsi v ++
              modesAnsi v ++
              charsetAnsi v)) =
          (prologueAnsi v ++
              (csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v ++ regionAnsi v ++ tabsAnsi v ++
                savedAnsi v ++
                savedPendingAnsi v ++
                titleAnsi v ++
                modesAnsi v)) ++
            charsetAnsi v
        from by simp only [List.append_assoc],
      feed_append]
    exact (mmap_id_charsetAnsi v _ hMground hMu).2.1
  -- assemble
  rw [show
      restoreBody v ++ cursorAnsi v =
        (prologueAnsi v ++
            (csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v ++ regionAnsi v ++ tabsAnsi v ++
              savedAnsi v ++
              savedPendingAnsi v ++
              titleAnsi v ++
              modesAnsi v ++
              charsetAnsi v)) ++
          penSgr v.pen ++
          cursorAnsi v
      from by simp only [restoreBody, List.append_assoc]]
  rw [feed_append, feed_append, penSgr_feed v.pen hCground hCu]
  rw [pen_cursorAnsi v (by simpa using hCground) (by simpa using hCu)]

theorem pen_cursorPendingAnsi (v w : Vt) (hg : w.pstate = .ground) (hu : w.u8need = 0)
    (hp : w.pen = v.pen) : (w.feed (cursorPendingAnsi v)).pen = v.pen := by
  unfold cursorPendingAnsi
  split
  · have hstart :=
      ((((mmap_wrap true).comp (mmap_irm false)).comp
                (mmap_id_charset 0x28 0x42 (Or.inl rfl) (by decide) (by decide))).comp
            (mmap_id_charset 0x29 0x42 (Or.inr rfl) (by decide) (by decide))).comp
        mmap_id_si
    have hpaint :=
      hstart.comp
        (mmap_id_pendingAnsi v.cols v.grid v.cursor
          (if v.modes.origin then v.cursor.y - v.top + 1 else v.cursor.y + 1) v.pen)
    have h :=
      (((hpaint.comp (mmap_wrap v.modes.wrap)).comp (mmap_irm v.modes.insert)).comp
          (mmap_id_charsetAnsi v))
        w hg hu
    rw [feed_append]
    simpa using congrArg Vt.pen (penSgr_feed v.pen h.1 h.2.1)
  · exact hp

theorem restore_pen_any (v w : Vt) : (w.feed (restore v)).pen = v.pen := by
  unfold restore
  rw [feed_append]
  apply pen_cursorPendingAnsi
  · exact restore_placed_grounds v w
  · rw [feed_append]
    unfold cursorAnsi csiNum2
    split <;>
      exact
        u8_zero_after_csi _ _
          (by
            exact
              ((paramBytes_digits _).append
                    (ParamBytes.cons (by decide) (by decide) ParamBytes.nil)).append
                (paramBytes_digits _))
          (by decide) _
  · exact restore_pen_placed v w

end Linger.Core.Render
