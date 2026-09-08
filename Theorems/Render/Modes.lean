module

public import Theorems.Render.Keeps
import all Linger.Core.Render
import all Linger.Core.Vt
import all Theorems.Render.Keeps

public section

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
(`specs/restore-conformance.md`, Step 1).

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

/-- Where `ESC` lands, from anywhere. The four reachable states are the ones `\` can
finish: `.esc` (from `ground`, `esc`, `csi`), `ground` (from `escInter`, whose
designation `ED 2` and `charsetAnsi` both undo), and the two string states with their
ST check armed. -/
theorem esc_lands (w : Vt) :
    ((w.step 0x1B).pstate = .esc ∨
        (w.step 0x1B).pstate = .ground ∨
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
  | .escInter i =>
    refine ⟨Or.inr (Or.inl ?_), ?_⟩
    · show ((w.abortUtf8 0x1B).stepEscInter i 0x1B).pstate = PState.ground
      unfold Vt.stepEscInter
      dsimp only
      repeat' split
      all_goals rfl
    · show ((w.abortUtf8 0x1B).stepEscInter i 0x1B).u8need = 0
      unfold Vt.stepEscInter
      dsimp only
      repeat' split
      all_goals exact hun
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
    refine ⟨Or.inr (Or.inr (Or.inl ⟨acc, ?_⟩)), ?_⟩
    · show ((w.abortUtf8 0x1B).stepOsc acc e 0x1B).pstate = PState.osc acc true
      unfold Vt.stepOsc
      rw [ite_eq_right (by simp), ite_eq_right (by decide), ite_eq_left (by decide)]
    · show ((w.abortUtf8 0x1B).stepOsc acc e 0x1B).u8need = 0
      unfold Vt.stepOsc
      rw [ite_eq_right (by simp), ite_eq_right (by decide), ite_eq_left (by decide)]
      exact hun
  | .str e =>
    refine ⟨Or.inr (Or.inr (Or.inr ?_)), ?_⟩
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
  exact st_finish _ hun hstate

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
    refine Ends.append ?_ (ends_escCharset 0x29 0x42 (by decide))
    refine Ends.append ?_ (ends_escCharset 0x28 0x42 (by decide))
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
and is left to `specs/restore-conformance.md` Step 2. -/
theorem restore_grounds (v w : Vt) : (w.feed (restore v)).pstate = .ground := by
  rw [show
      restore v =
        prologueAnsi v ++
          (csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v ++ regionAnsi v ++ tabsAnsi v ++
            savedAnsi v ++
            titleAnsi v ++
            modesAnsi v ++
            charsetAnsi v ++
            penSgr v.pen ++
            cursorAnsi v)
      from by
      unfold restore restoreBody; simp]
  rw [feed_append]
  refine Ends.append ?_ (ends_cursorAnsi v) _ (prologue_grounds v w)
  refine Ends.append ?_ (ends_penSgr v.pen)
  refine Ends.append ?_ (ends_charsetAnsi v)
  refine Ends.append ?_ (ends_modesAnsi v)
  refine Ends.append ?_ (ends_titleAnsi v)
  refine Ends.append ?_ (ends_savedAnsi v)
  refine Ends.append ?_ (ends_tabsAnsi v)
  refine Ends.append ?_ (ends_regionAnsi v)
  refine Ends.append ?_ (ends_screensAnsi v)
  exact
    (ends_csiNum 0 0x6D (by decide) (by decide)).append (ends_csiNum 2 0x4A (by decide) (by decide))

/-! ### …and so does the hand-back

`leaveAnsi` is A5's outbound half (§Handback): whatever the session's last program
left behind, the detaching client returns the terminal to a state the next program
can use. Its parser claim is `restore_grounds` with the same lead-in doing the same
job — a program that died mid-OSC or mid-DCS would swallow the hand-back exactly as
it swallowed the repaint before `cd7c17b` — and the same proof, one chunk longer.

The *value* claims (each mode at its canonical setting, for every receiver) are the
`Sets` instances of `specs/restore-conformance.md` Step 1, which the hand-back is the
easiest instance of: no `ite`, no dependence on a `Vt`. -/

/-- A parameterless CSI: the receiver's own defaults apply. -/
theorem ends_csiPlain (final : UInt8) (h1 : 0x40 ≤ final) (h2 : final ≤ 0x7E) :
    Ends (csiPlain final) := by simpa [csiPlain] using ends_csi_seq [] final ParamBytes.nil h1 h2

/-- **The hand-back grounds any receiver.** No hypothesis on `w`: not `ground`, not
`Vt.init`. The receiver here is a real terminal whose last occupant was an
application, so every state it could be in is reachable — which is exactly why the
claim has to be stated this way. -/
theorem leave_grounds (w : Vt) : (w.feed leaveAnsi).pstate = .ground := by
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
    refine Ends.append ?_ (ends_escCharset 0x29 0x42 (by decide))
    refine Ends.append ?_ (ends_escCharset 0x28 0x42 (by decide))
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
            csiNum 0 0x6D)
      from by
      unfold leaveAnsi; simp]
  rw [feed_append]
  exact hrest _ (st_grounds w).1

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

/-- The dispatch of `CSI ? … h`/`l` is `setMode`, on its `modes`. The `match`
on the concrete final byte reduces, so this is `rfl` after the ignore guard. -/
theorem modes_csiDispatch_sm (v : Vt) (s : CsiState) (hi : s.ignore = false) :
    (v.csiDispatch s 0x68).modes = (v.setMode (s.priv == 0x3F) (s.arg 0 0) true).modes := by
  unfold Vt.csiDispatch;
  rw [ite_eq_right
      (by
        rw [hi]; simp)];
  rfl

theorem modes_csiDispatch_rm (v : Vt) (s : CsiState) (hi : s.ignore = false) :
    (v.csiDispatch s 0x6C).modes = (v.setMode (s.priv == 0x3F) (s.arg 0 0) false).modes := by
  unfold Vt.csiDispatch;
  rw [ite_eq_right
      (by
        rw [hi]; simp)];
  rfl

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
  have harg : ({ sa with params := #[(n, sa.curSub)] } : CsiState).arg 0 0 = n := by
    rw [arg_of_one, ite_eq_right (by omega)]
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
    rw [modes_csiDispatch_rm _ _ hign2, harg, hpriv2]
    exact modes_setMode true n false hopmodes
  · show (({ w with pstate := .csi sa }).csiDispatch _ 0x68).modes = (w.setMode true n true).modes
    rw [modes_csiDispatch_sm _ _ hign2, harg, hpriv2]
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

This is the lemma the design review's Step-1 sketch was missing, and it delivers
four of `scrollback_entry`'s sixteen conjuncts at once (`u8need`, `insert`,
`wrap`, `origin`) — the fifth, `u8acc`, follows by `u8Ok_feed`. -/
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

/-- **A projection blind to the parser state.** Every field accessor but `pstate`
is one, by `rfl`. It is the one thing the CSI walk needs of a projection, because
the walk to the final byte is a chain of `pstate` updates and nothing else. -/
def PsBlind {α : Type} (π : Vt → α) : Prop :=
  ∀ (v : Vt) (p : PState), π { v with pstate := p } = π v

theorem psBlind_modes : PsBlind (fun v : Vt => v.modes) := fun _ _ => rfl

theorem psBlind_pen : PsBlind (fun v : Vt => v.pen) := fun _ _ => rfl

theorem psBlind_stick : PsBlind stick := fun _ _ => rfl

/-- **The CSI tail walk, once, for any projection.** `keeps_csi_tail` (the grid),
`csi_tail_modes` and `csi_tail_pen` were this proof three times with a different
field in the hole; the projection is now a parameter and the latter two are
one-line instances. `keeps_csi_tail` *is* the `π = (·.grid)` instance too — the grid
is `PsBlind` by `rfl` and its `hgrid` is exactly `hπ` — but it lives 1200 lines
above this lemma, so collapsing it means hoisting `PsBlind`/`csi_tail_proj` above
the `Keeps` section. Feasible (this proof depends only on `csi_param_run_inter`,
`csi_final_step_eq` and `un_csiDispatch`, all of which precede `Keeps`); not done,
so file order is the reason the third copy survives, not the shape of its
hypothesis.

Read: a parameter run followed by a final byte whose dispatch does not move `π`
leaves `π` alone and returns the parser to ground with nothing half-decoded. -/
theorem csi_tail_proj {α : Type} {π : Vt → α} (hb : PsBlind π) (params : Bytes) (final : UInt8)
    (hp : ParamBytes params) (h1 : 0x40 ≤ final) (h2 : final ≤ 0x7E)
    (hπ : ∀ (w : Vt) (t : CsiState), π (w.csiDispatch t final) = π w) {v : Vt} {s : CsiState}
    (hg : v.pstate = .csi s) (hu : v.u8need = 0) (hi : s.inter = 0) :
    π (v.feed (params ++ [final])) = π v ∧
      (v.feed (params ++ [final])).pstate = .ground ∧ (v.feed (params ++ [final])).u8need = 0 := by
  obtain ⟨s', hs', hsi⟩ := csi_param_run_inter params hg hu hp
  rw [show ∀ (w : Vt), w.feed (params ++ [final]) = (w.feed params).feed [final] from fun w => by
      simp [Vt.feed, List.foldl_append]]
  rw [hs', show ∀ (w : Vt), w.feed [final] = w.step final from fun _ => rfl]
  rw [csi_final_step_eq final (v := { v with pstate := .csi s' }) (s := s') rfl (by simpa using hu)
      (by
        rw [hsi]; exact hi)
      h1 h2]
  unfold Vt.csiFinish
  dsimp only
  refine
    ⟨?_, rfl, by
      rw [un_csiDispatch]; simpa using hu⟩
  rw [hb _ PState.ground, hπ, hb v (PState.csi s')]

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
    MMap id (csiB ++ params ++ [final]) := by
  intro v hg hu
  rw [show (csiB ++ params ++ [final] : Bytes) = [0x1B, 0x5B] ++ (params ++ [final]) from by
      unfold csiB; simp]
  rw [show
      ∀ (w : Vt),
        w.feed ([0x1B, 0x5B] ++ (params ++ [final])) =
          (w.feed [0x1B, 0x5B]).feed (params ++ [final])
      from fun w => by simp [Vt.feed, List.foldl_append]]
  rw [keeps_csi_open hg hu]
  obtain ⟨hmod, hp', hu'⟩ :=
    csi_tail_modes params final hp h1 h2 hmodes (v := { v with pstate := .csi {} }) rfl
      (by simpa using hu) rfl
  exact ⟨hp', hu', hmod⟩

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
  (Vt.setMode { (default : Vt) with modes := m } true n on).modes

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
  have harg : ({ sa with params := #[(4, sa.curSub)] } : CsiState).arg 0 0 = 4 := by
    rw [arg_of_one, ite_eq_right (by decide)]
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
    rw [modes_csiDispatch_rm _ _ hign2, harg, hpriv2]; rfl
  · show (({ v with pstate := .csi sa }).csiDispatch _ 0x68).modes = _
    rw [modes_csiDispatch_sm _ _ hign2, harg, hpriv2]; rfl

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
theorem mmap_id_charset (i x : UInt8) (hi : i = 0x28 ∨ i = 0x29) : MMap id (escCharset i x) := by
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
  unfold Vt.stepEscInter
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
                                  ((mmap_id_charset 0x28 0x42 (Or.inl rfl)).comp
                                    ((mmap_id_charset 0x29 0x42 (Or.inr rfl)).comp
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
                                            (csiNum2 999 1 0x48 ++ csiNum 0 0x6D))))))))))))))))))
      from by simp only [leaveAnsi, List.append_assoc]]
  rw [feed_append]
  exact (htail _ hlead.1 hlead.2).2.2

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

theorem mmap_id_sgrOf (codes : List Nat) : MMap id (sgrOf codes) := by
  rw [show sgrOf codes = csiB ++ joinSemi codes ++ [0x6D] from rfl]
  exact
    mmap_id_csi_seq _ 0x6D (paramBytes_joinSemi codes) (by decide) (by decide)
      (fun w t => modes_csiDispatch_sgr w t)

theorem mmap_id_sgrColorSeq (c : Color) (isFg : Bool) : MMap id (sgrColorSeq c isFg) := by
  unfold sgrColorSeq
  split
  · exact MMap.nil
  · exact mmap_id_sgrOf _

theorem mmap_id_penSgr (p : Pen) : MMap id (penSgr p) := by
  unfold penSgr
  exact
    mmap_id_append (mmap_id_append (mmap_id_sgrOf _) (mmap_id_sgrColorSeq _ _))
      (mmap_id_sgrColorSeq _ _)

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
    · exact mmap_id_charset 0x28 0x30 (Or.inl rfl)
    · exact mmap_id_charset 0x28 0x42 (Or.inl rfl)
  · split
    · exact mmap_id_charset 0x29 0x30 (Or.inr rfl)
    · exact mmap_id_charset 0x29 0x42 (Or.inr rfl)
  · split
    · exact mmap_id_so
    · exact MMap.nil

theorem mmap_id_cursorAnsi (v : Vt) : MMap id (cursorAnsi v) := by
  unfold cursorAnsi
  split <;> exact mmap_id_cup _ _

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

theorem restore_modes_any (v w : Vt)
    (hmouse :
      v.modes.mouse = 0 ∨ v.modes.mouse = 1000 ∨ v.modes.mouse = 1002 ∨ v.modes.mouse = 1003) :
    (w.feed (restore v)).modes = v.modes := by
  -- MID2 = prologue .. saved (before the title); it grounds any receiver
  have hEndsRest :
    Ends
      (csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v ++ regionAnsi v ++ tabsAnsi v ++
        savedAnsi v) :=
    (((((ends_csiNum 0 0x6D (by decide) (by decide)).append
                      (ends_csiNum 2 0x4A (by decide) (by decide))).append
                  (ends_screensAnsi v)).append
              (ends_regionAnsi v)).append
          (ends_tabsAnsi v)).append
      (ends_savedAnsi v)
  have hg2 :
    (w.feed
          (prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v ++ regionAnsi v ++
            tabsAnsi v ++
            savedAnsi v)).pstate =
      .ground := by
    rw [show
        prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v ++ regionAnsi v ++
            tabsAnsi v ++
            savedAnsi v =
          prologueAnsi v ++
            (csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v ++ regionAnsi v ++ tabsAnsi v ++
              savedAnsi v)
        from by simp only [List.append_assoc],
      feed_append]
    exact hEndsRest _ (prologue_grounds v w)
  -- g1 = w.feed (MID2 ++ title): ground, u8need 0
  have hsplitMID :
    restore v =
      (prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v ++ regionAnsi v ++
          tabsAnsi v ++
          savedAnsi v) ++
        (titleAnsi v ++ (modesAnsi v ++ charsetAnsi v ++ penSgr v.pen ++ cursorAnsi v)) := by
    simp only [restore, restoreBody, List.append_assoc]
  rw [hsplitMID, feed_append, feed_append]
  -- after the title the parser is ground with nothing pending (`ends_titleAnsi`,
  -- `uz_titleAnsi`); the suffix chain `modesAnsi ++ charset ++ pen ++ cursor` is the
  -- constant transform `fun _ => v.modes`
  have htail :=
    (((mmap_modesAnsi v hmouse).comp (mmap_id_charsetAnsi v)).comp (mmap_id_penSgr v.pen)).comp
      (mmap_id_cursorAnsi v)
  exact (htail _ (ends_titleAnsi v _ hg2) (uz_titleAnsi v hg2)).2.2

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
theorem restore_pen_any (v w : Vt) : (w.feed (restore v)).pen = v.pen := by
  -- C = everything up to (not including) penSgr; it grounds `w` with nothing pending
  have hEndsC :
    Ends
      (csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v ++ regionAnsi v ++ tabsAnsi v ++
        savedAnsi v ++
        titleAnsi v ++
        modesAnsi v ++
        charsetAnsi v) :=
    ((((((((ends_csiNum 0 0x6D (by decide) (by decide)).append
                                  (ends_csiNum 2 0x4A (by decide) (by decide))).append
                              (ends_screensAnsi v)).append
                          (ends_regionAnsi v)).append
                      (ends_tabsAnsi v)).append
                  (ends_savedAnsi v)).append
              (ends_titleAnsi v)).append
          (ends_modesAnsi v)).append
      (ends_charsetAnsi v)
  have hCground :
    (w.feed
          (prologueAnsi v ++
            (csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v ++ regionAnsi v ++ tabsAnsi v ++
              savedAnsi v ++
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
              titleAnsi v ++
              modesAnsi v))).pstate =
      .ground := by
    rw [feed_append]
    exact
      (((((((ends_csiNum 0 0x6D (by decide) (by decide)).append
                                (ends_csiNum 2 0x4A (by decide) (by decide))).append
                            (ends_screensAnsi v)).append
                        (ends_regionAnsi v)).append
                    (ends_tabsAnsi v)).append
                (ends_savedAnsi v)).append
            (ends_titleAnsi v)).append
        (ends_modesAnsi v) _ (prologue_grounds v w)
  have hMu :
    (w.feed
          (prologueAnsi v ++
            (csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v ++ regionAnsi v ++ tabsAnsi v ++
              savedAnsi v ++
              titleAnsi v ++
              modesAnsi v))).u8need =
      0 := by
    rw [show
        (prologueAnsi v ++
            (csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v ++ regionAnsi v ++ tabsAnsi v ++
              savedAnsi v ++
              titleAnsi v ++
              modesAnsi v)) =
          (prologueAnsi v ++
              (csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v ++ regionAnsi v ++ tabsAnsi v ++
                savedAnsi v ++
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
              titleAnsi v ++
              modesAnsi v ++
              charsetAnsi v))).u8need =
      0 := by
    rw [show
        (prologueAnsi v ++
            (csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v ++ regionAnsi v ++ tabsAnsi v ++
              savedAnsi v ++
              titleAnsi v ++
              modesAnsi v ++
              charsetAnsi v)) =
          (prologueAnsi v ++
              (csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v ++ regionAnsi v ++ tabsAnsi v ++
                savedAnsi v ++
                titleAnsi v ++
                modesAnsi v)) ++
            charsetAnsi v
        from by simp only [List.append_assoc],
      feed_append]
    exact (mmap_id_charsetAnsi v _ hMground hMu).2.1
  -- assemble
  rw [show
      restore v =
        (prologueAnsi v ++
            (csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v ++ regionAnsi v ++ tabsAnsi v ++
              savedAnsi v ++
              titleAnsi v ++
              modesAnsi v ++
              charsetAnsi v)) ++
          penSgr v.pen ++
          cursorAnsi v
      from by simp only [restore, restoreBody, List.append_assoc]]
  rw [feed_append, feed_append, penSgr_feed v.pen hCground hCu]
  rw [pen_cursorAnsi v (by simpa using hCground) (by simpa using hCu)]

end Linger.Core.Render
