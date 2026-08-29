module

public import Theorems.Render.Modes
import all Linger.Core.Render
import all Linger.Core.Vt
import all Theorems.Render.Modes

public section

/-! # §Restore / A5 inbound — the sticky bundle, and the cursor

`SMap` and `Vt.stick`: the scroll region, both charset designations, the shift
state and which screen is current — the restored fields whose proof cannot step
over the repaint — plus the receiver-quantified cursor claim. Split out of
`Theorems/Render.lean`. -/

namespace Linger.Core.Render

open Linger.Core.Vt

/-! ## §Restore / A5 inbound, the sticky fields: region, charsets, screen

The last group of restored fields, and the one whose emitters are *not* all in the
tail: the scroll region is set before the title, and the screen switch is set in
the middle of the repaint. So unlike the modes and the pen, these claims cannot
step over `gridAnsi` — they have to prove the repaint does not disturb them.

That is what `Vt.stick` buys. It is one bundled projection (`Theorems/Vt.lean`
§Restore) rather than four `org_`-style families, so `print` and `csiDispatch` —
the two operations frames could not cover — are paid for once. Here it gets the
stream layer: `SMap`, the `Quiet` shape with `Modes.origin` replaced by the
bundle, and no `u8need` side condition anywhere (an `ESC` drops a half-decoded
character, and nothing sticky rides on it).

The four transforms are exactly the four things in a restore stream that write a
sticky field: `?1049 h/l`, `CSI t;b r`, `ESC ( x` / `ESC ) x`, and `SO`/`SI`.
Everything else — the whole repaint included — is `SMap id`. -/

/-- From a ground parser, `bs` returns to ground and moves the sticky fields by
`f`. No `u8need` hypothesis: the CSI/ESC chunks clear it themselves at their
leading `ESC`, and a text run cannot touch a sticky field whatever is pending. -/
def SMap (f : Sticky → Sticky) (bs : Bytes) : Prop :=
  ∀ v : Vt, v.pstate = .ground →
    (v.feed bs).pstate = .ground ∧ stick (v.feed bs) = f (stick v)

theorem SMap.comp {f g : Sticky → Sticky} {a b : Bytes} (ha : SMap f a) (hb : SMap g b) :
    SMap (fun s => g (f s)) (a ++ b) := by
  intro v hg
  rw [feed_append]
  obtain ⟨h1, h2⟩ := ha v hg
  obtain ⟨h3, h4⟩ := hb _ h1
  exact ⟨h3, by rw [h4, h2]⟩

theorem SMap.nil : SMap id [] := fun _ hg => ⟨hg, rfl⟩

theorem SMap.congr {f g : Sticky → Sticky} {bs : Bytes} (h : SMap f bs)
    (hfg : ∀ s, f s = g s) : SMap g bs := by
  intro v hg; obtain ⟨a, b⟩ := h v hg; exact ⟨a, by rw [b, hfg]⟩

theorem SMap.append {a b : Bytes} (ha : SMap id a) (hb : SMap id b) : SMap id (a ++ b) :=
  (ha.comp hb).congr (fun _ => rfl)

theorem SMap.streamPred : StreamPred (SMap id) := ⟨SMap.nil, fun ha hb => SMap.append ha hb⟩

theorem SMap.ite {c : Prop} [Decidable c] {f g : Sticky → Sticky} {a b : Bytes}
    (ha : c → SMap f a) (hb : ¬c → SMap g b) :
    SMap (if c then f else g) (if c then a else b) := by
  by_cases h : c
  · rw [if_pos h, if_pos h]; exact ha h
  · rw [if_neg h, if_neg h]; exact hb h

/-- **A text run cannot move a sticky field.** True here and false for `Keeps` —
printable bytes are exactly what writes cells — and the two excluded bytes are
`SO`/`SI`, which is why the shift state needs an emitter of its own. -/
theorem smap_ground_run : ∀ (bs : Bytes) (v : Vt), v.pstate = .ground →
    (∀ b ∈ bs, b ≠ 0x1B ∧ b ≠ 0x0E ∧ b ≠ 0x0F) →
    (v.feed bs).pstate = .ground ∧ stick (v.feed bs) = stick v
  | [], _, hg, _ => ⟨hg, rfl⟩
  | x :: xs, v, hg, h => by
    rw [feed_cons]
    obtain ⟨h1, h2, h3⟩ := h x (by simp)
    obtain ⟨hp, hs⟩ := smap_ground_run xs _ (ground_step x hg h1) (fun b hb => h b (by simp [hb]))
    exact ⟨hp, hs.trans (stick_step_of_ground x hg h2 h3)⟩

theorem SMap.text {bs : Bytes} (h : ∀ b ∈ bs, b ≠ 0x1B ∧ b ≠ 0x0E ∧ b ≠ 0x0F) : SMap id bs :=
  fun v hg => smap_ground_run bs v hg h

/-- Scrubbed glyph bytes are ≥ 0x20, so they are none of the three. -/
theorem smap_utf8s (cs : List Char) : SMap id (utf8s cs) :=
  SMap.text (fun b hb => by
    obtain ⟨hge, -⟩ := utf8s_no_ctl cs b hb
    refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩ <;>
      (rw [he] at hge; exact absurd hge (by decide)))

theorem smap_utf8_safe (ch : Char) : SMap id (utf8 (safeChar ch)) :=
  SMap.text (fun b hb => by
    obtain ⟨hge, -⟩ := utf8_no_ctl (safeChar ch) (safeChar_ge ch).1 (safeChar_ge ch).2 b hb
    refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩ <;>
      (rw [he] at hge; exact absurd hge (by decide)))

theorem smap_cellText (c : Cell) : SMap id (cellText c) := by
  unfold cellText
  exact (smap_utf8_safe c.base).append (smap_utf8s c.marks)

theorem smap_crlf : SMap id [0x0D, 0x0A] := SMap.text (by decide)

/-! ### The CSI and ESC walks at the sticky projection -/

theorem stick_csi_open {v : Vt} (hg : v.pstate = .ground) :
    (v.feed [0x1B, 0x5B]).pstate = .csi {} ∧ (v.feed [0x1B, 0x5B]).u8need = 0
      ∧ stick (v.feed [0x1B, 0x5B]) = stick v := by
  rw [show v.feed [(0x1B : UInt8), 0x5B] = (v.step 0x1B).step 0x5B from by simp [Vt.feed]]
  have he : (v.step 0x1B).pstate = .esc := esc_step hg
  refine ⟨csi_open_step he, uz_step 0x5B (by decide) (uz_step_esc v), ?_⟩
  exact (stick_step_of_esc 0x5B he (by decide)).trans
    (stick_step_of_ground 0x1B hg (by decide) (by decide))

/-- A marker-free `CSI … <final>` whose dispatch is transparent to the bundle. -/
theorem smap_id_csi_seq (params : Bytes) (final : UInt8) (hp : ParamBytes params)
    (h1 : 0x40 ≤ final) (h2 : final ≤ 0x7E)
    (hst : ∀ (w : Vt) (t : CsiState), stick (w.csiDispatch t final) = stick w) :
    SMap id (csiB ++ params ++ [final]) := by
  intro v hg
  rw [show (csiB ++ params ++ [final] : Bytes) = [0x1B, 0x5B] ++ (params ++ [final]) from by
    unfold csiB; simp]
  rw [feed_append]
  obtain ⟨hc, hcu, hcs⟩ := stick_csi_open hg
  obtain ⟨ht, hp', -⟩ := csi_tail_proj psBlind_stick params final hp h1 h2 hst hc hcu rfl
  exact ⟨hp', by rw [ht, hcs]; rfl⟩

theorem smap_id_sgrOf (codes : List Nat) : SMap id (sgrOf codes) := by
  rw [show sgrOf codes = csiB ++ joinSemi codes ++ [0x6D] from rfl]
  exact smap_id_csi_seq _ 0x6D (paramBytes_joinSemi codes) (by decide) (by decide)
    (fun w t => stick_csiDispatch_sgr w t)

theorem smap_id_sgrColorSeq (c : Color) (isFg : Bool) : SMap id (sgrColorSeq c isFg) := by
  unfold sgrColorSeq
  split
  · exact SMap.nil
  · exact smap_id_sgrOf _

theorem smap_id_penSgr (p : Pen) : SMap id (penSgr p) := by
  unfold penSgr
  exact ((smap_id_sgrOf _).append (smap_id_sgrColorSeq _ _)).append (smap_id_sgrColorSeq _ _)

theorem smap_id_cup (a b : Nat) : SMap id (csiNum2 a b 0x48) := by
  rw [show csiNum2 a b 0x48 = csiB ++ (digits a ++ [0x3B] ++ digits b) ++ [0x48] from by
    simp [csiNum2]]
  exact smap_id_csi_seq _ 0x48
    (((paramBytes_digits a).append (ParamBytes.cons (by decide) (by decide) ParamBytes.nil)).append
      (paramBytes_digits b)) (by decide) (by decide) (fun w t => stick_csiDispatch_cup w t)

theorem smap_id_home : SMap id (csiB ++ [0x48] : Bytes) := by
  rw [show (csiB ++ [0x48] : Bytes) = csiB ++ [] ++ [0x48] from by simp]
  exact smap_id_csi_seq [] 0x48 ParamBytes.nil (by decide) (by decide)
    (fun w t => stick_csiDispatch_cup w t)

theorem smap_id_cha (n : Nat) : SMap id (csiNum n 0x47) := by
  rw [show csiNum n 0x47 = csiB ++ digits n ++ [0x47] from rfl]
  exact smap_id_csi_seq _ 0x47 (paramBytes_digits n) (by decide) (by decide)
    (fun w t => stick_csiDispatch_cha w t)

theorem smap_id_sgrNum (n : Nat) : SMap id (csiNum n 0x6D) := by
  rw [show csiNum n 0x6D = csiB ++ digits n ++ [0x6D] from rfl]
  exact smap_id_csi_seq _ 0x6D (paramBytes_digits n) (by decide) (by decide)
    (fun w t => stick_csiDispatch_sgr w t)

theorem smap_id_ed (n : Nat) : SMap id (csiNum n 0x4A) := by
  rw [show csiNum n 0x4A = csiB ++ digits n ++ [0x4A] from rfl]
  exact smap_id_csi_seq _ 0x4A (paramBytes_digits n) (by decide) (by decide)
    (fun w t => stick_csiDispatch_ed w t)

theorem smap_id_tbc (n : Nat) : SMap id (csiNum n 0x67) := by
  rw [show csiNum n 0x67 = csiB ++ digits n ++ [0x67] from rfl]
  exact smap_id_csi_seq _ 0x67 (paramBytes_digits n) (by decide) (by decide)
    (fun w t => stick_csiDispatch_tbc w t)

/-! ### The one-parameter CSI walk, for the sequences whose dispatch is NOT
transparent

`csi_tail_proj` discharges a sequence whose final byte cannot move the projection
whatever the collector holds. The mode sets are the other kind: `SM`/`RM` dispatch
to `setMode`, whose effect depends on the *parameter*. So this walk delivers the
closed collector's contents — marker as emitted, `ignore` clear, single parameter
`n` — and is written once for both markers, where `mmap_irm` and `modeSet_tail`
each did it by hand. -/

/-- `arg` from the collector's parameter array, in the two shapes the walks
deliver: one parameter pushed onto nothing, and one pushed onto one. -/
theorem arg_of_one_of {t : CsiState} {n : Nat} {sub : Bool} (d : Nat)
    (h : t.params = (#[] : Array (Nat × Bool)).push (n, sub)) :
    t.arg 0 d = if n = 0 then d else n := by
  unfold CsiState.arg
  rw [h]
  cases n <;> simp

theorem arg_of_two_of {t : CsiState} {a b : Nat} {sa sb : Bool} (d : Nat)
    (h : t.params = (#[(a, sa)] : Array (Nat × Bool)).push (b, sb)) :
    (t.arg 0 d = if a = 0 then d else a) ∧ (t.arg 1 d = if b = 0 then d else b) := by
  constructor <;> (unfold CsiState.arg; rw [h])
  · cases a <;> simp
  · cases b <;> simp

theorem stick_csi_marker_step {v : Vt} {s : CsiState} (hg : v.pstate = .csi s)
    (hu : v.u8need = 0) : stick (v.step 0x3F) = stick v := by
  rw [step_of_csi_quiet 0x3F hg hu]
  unfold Vt.stepCsi
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos (by decide)]
  rfl

theorem stick_priv_open {v : Vt} (hg : v.pstate = .ground) :
    (v.feed [0x1B, 0x5B, 0x3F]).pstate = .csi ({ priv := 0x3F } : CsiState)
      ∧ (v.feed [0x1B, 0x5B, 0x3F]).u8need = 0
      ∧ stick (v.feed [0x1B, 0x5B, 0x3F]) = stick v := by
  rw [show v.feed [(0x1B : UInt8), 0x5B, 0x3F] = ((v.step 0x1B).step 0x5B).step 0x3F from by
    simp [Vt.feed]]
  have he : (v.step 0x1B).pstate = .esc := esc_step hg
  have hb : ((v.step 0x1B).step 0x5B).pstate = .csi {} := csi_open_step he
  obtain ⟨hm, -⟩ := csi_marker_step hb (by decide)
  have hu2 : ((v.step 0x1B).step 0x5B).u8need = 0 := uz_step 0x5B (by decide) (uz_step_esc v)
  refine ⟨hm, uz_step 0x3F (by decide) hu2, ?_⟩
  exact ((stick_csi_marker_step hb hu2).trans (stick_step_of_esc 0x5B he (by decide))).trans
    (stick_step_of_ground 0x1B hg (by decide) (by decide))

theorem stick_csi_arg_tail (n : Nat) (final : UInt8) (f : Sticky → Sticky)
    (hn : 0 < n) (hlt : n < 65535) (h1 : 0x40 ≤ final) (h2 : final ≤ 0x7E)
    {s0 : CsiState} (hs0cur : s0.cur = 0) (_hs0have : s0.haveCur = false)
    (hs0size : s0.params.size < 16) (hs0int : s0.inter = 0) (hs0ign : s0.ignore = false)
    (hst : ∀ (w : Vt) (t : CsiState), t.priv = s0.priv → t.ignore = false →
        t.params = s0.params.push (n, s0.curSub) →
        stick (w.csiDispatch t final) = f (stick w))
    {w : Vt} (hm : w.pstate = .csi s0) (hwu : w.u8need = 0) :
    stick (w.feed (digits n ++ [final])) = f (stick w)
      ∧ (w.feed (digits n ++ [final])).pstate = .ground := by
  obtain ⟨sa, hfeed, -⟩ := csi_param_run_inter (digits n) hm hwu (paramBytes_digits n)
  obtain ⟨sb, hpsb, hcur', hhave', hpar', hint', hign', hsub', hpriv'⟩ :=
    csi_digits_value n hm hs0cur
  have hsab : sa = sb := PState.csi.inj ((by rw [hfeed] :
    (w.feed (digits n)).pstate = .csi sa).symm.trans hpsb)
  rw [show ∀ (u : Vt), u.feed (digits n ++ [final]) = (u.feed (digits n)).feed [final] from
    fun u => by simp [Vt.feed, List.foldl_append]]
  rw [show ∀ (u : Vt), u.feed [final] = u.step final from fun _ => rfl, hfeed]
  rw [csi_final_step_eq final rfl (by rw [hwu]) (by rw [hsab, hint']; exact hs0int) h1 h2]
  unfold Vt.csiFinish
  rw [if_pos (by rw [hsab]; simpa using hhave'),
    if_neg (by rw [hsab, hpar']; omega)]
  dsimp only
  refine ⟨?_, rfl⟩
  have hstate : ({ sa with params := sa.params.push (min sa.cur 65535, sa.curSub) } : CsiState)
      = { sa with params := s0.params.push (n, s0.curSub) } := by
    rw [hsab, hpar', hcur', hsub', show min (min n 65535) 65535 = n from by omega]
  rw [hstate]
  exact hst _ _ (by show sa.priv = s0.priv; rw [hsab]; exact hpriv')
    (by show sa.ignore = false; rw [hsab, hign']; exact hs0ign) rfl

/-- The walk, both markers. `priv` picks `CSI ? <n> <final>` or `CSI <n> <final>`. -/
theorem smap_csi_one_arg (n : Nat) (final : UInt8) (priv : Bool) (f : Sticky → Sticky)
    (hn : 0 < n) (hlt : n < 65535) (h1 : 0x40 ≤ final) (h2 : final ≤ 0x7E)
    (hst : ∀ (w : Vt) (t : CsiState), t.priv = (if priv then (0x3F : UInt8) else 0) →
        t.ignore = false → t.arg 0 0 = n → stick (w.csiDispatch t final) = f (stick w)) :
    SMap f (if priv then csiPriv n final else csiNum n final) := by
  intro v hg
  cases priv
  · rw [if_neg (by decide),
      show csiNum n final = [0x1B, 0x5B] ++ (digits n ++ [final]) from by simp [csiNum, csiB]]
    rw [feed_append]
    obtain ⟨hc, hcu, hcs⟩ := stick_csi_open hg
    obtain ⟨ht, hp⟩ := stick_csi_arg_tail n final f hn hlt h1 h2
      (s0 := ({} : CsiState)) rfl rfl (by decide) rfl rfl
      (fun u t hpv hig hpar => hst u t (by rw [hpv]; rfl) hig
        (by rw [arg_of_one_of 0 hpar, if_neg (by omega)])) hc hcu
    exact ⟨hp, by rw [ht, hcs]⟩
  · rw [if_pos rfl,
      show csiPriv n final = [0x1B, 0x5B, 0x3F] ++ (digits n ++ [final]) from by
        simp [csiPriv, csiB]]
    rw [feed_append]
    obtain ⟨hc, hcu, hcs⟩ := stick_priv_open hg
    obtain ⟨ht, hp⟩ := stick_csi_arg_tail n final f hn hlt h1 h2
      (s0 := ({ priv := 0x3F } : CsiState)) rfl rfl (by decide) rfl rfl
      (fun u t hpv hig hpar => hst u t (by rw [hpv]; rfl) hig
        (by rw [arg_of_one_of 0 hpar, if_neg (by omega)])) hc hcu
    exact ⟨hp, by rw [ht, hcs]⟩

/-- **`?n h`/`l`: the screen-switch modes are the only ones that move a sticky
field**, and `stSetMode` says which. -/
theorem smap_modeSet (n : Nat) (on : Bool) (hn : 0 < n) (hlt : n < 65535) :
    SMap (stSetMode n on) (modeSet n on) := by
  have key : ∀ (w : Vt) (t : CsiState), t.priv = (0x3F : UInt8) → t.ignore = false →
      t.arg 0 0 = n →
      stick (w.csiDispatch t (if on then 0x68 else 0x6C)) = stSetMode n on (stick w) := by
    intro w t hpv hig harg
    have hpb : (t.priv == 0x3F) = true := by rw [hpv]; rfl
    cases on
    · rw [show (if (false : Bool) then (0x68 : UInt8) else 0x6C) = 0x6C from rfl,
        csiDispatch_rm w t hig, harg, hpb]
      exact stick_setMode w n false
    · rw [show (if (true : Bool) then (0x68 : UInt8) else 0x6C) = 0x68 from rfl,
        csiDispatch_sm w t hig, harg, hpb]
      exact stick_setMode w n true
  have h := smap_csi_one_arg n (if on then 0x68 else 0x6C) true (stSetMode n on) hn hlt
    (by cases on <;> decide) (by cases on <;> decide)
    (fun w t hpv hig harg => key w t (by simpa using hpv) hig harg)
  rw [if_pos rfl] at h
  exact h

/-- IRM is a *non*-private `CSI 4 h/l`, so its `setMode` cannot reach a screen
switch at all. -/
theorem smap_id_irm (on : Bool) : SMap id (csiNum 4 (if on then 0x68 else 0x6C)) := by
  have h := smap_csi_one_arg 4 (if on then 0x68 else 0x6C) false id (by decide) (by decide)
    (by cases on <;> decide) (by cases on <;> decide)
    (fun w t hpv hig harg => by
      cases on
      · rw [show (if (false : Bool) then (0x68 : UInt8) else 0x6C) = 0x6C from rfl,
          csiDispatch_rm w t hig, show (t.priv == 0x3F) = false from by
            rw [show t.priv = 0 from by simpa using hpv]; rfl]
        exact stick_setMode_plain w _ _
      · rw [show (if (true : Bool) then (0x68 : UInt8) else 0x6C) = 0x68 from rfl,
          csiDispatch_sm w t hig, show (t.priv == 0x3F) = false from by
            rw [show t.priv = 0 from by simpa using hpv]; rfl]
        exact stick_setMode_plain w _ _)
  rw [if_neg (by decide)] at h
  exact h

/-- The reset form, stated literally: both the prologue and the hand-back emit
`CSI 4 l`, and a chain of `sput_step`s has to match the emitter's bytes
syntactically. -/
theorem smap_id_irm_reset : SMap id (csiNum 4 0x6C) := smap_id_irm false

/-- `ESC <final>` for the two-byte sequences the emitters use — DECSC, HTS, the
keypad pair, and `ST`. None writes a sticky field; `RIS` (`ESC c`), which would,
is not among them. -/
theorem smap_id_escSeq (b : UInt8) (hb : b = 0x37 ∨ b = 0x3D ∨ b = 0x48 ∨ b = 0x3E ∨ b = 0x5C) :
    SMap id (escSeq b) := by
  intro v hg
  refine ⟨ends_escSeq b hb v hg, ?_⟩
  rw [show escSeq b = [0x1B, b] from rfl,
    show v.feed [(0x1B : UInt8), b] = (v.step 0x1B).step b from by simp [Vt.feed]]
  have he : (v.step 0x1B).pstate = .esc := esc_step hg
  exact (stick_step_of_esc b he (by rcases hb with h|h|h|h|h <;> rw [h] <;> decide)).trans
    (stick_step_of_ground 0x1B hg (by decide) (by decide))

/-- A run of non-ESC, non-BEL bytes fed from an OSC state stays there and cannot
move a sticky field — the shape `un_osc_run` has for `u8need`. -/
theorem stick_osc_run : ∀ (bs : Bytes) {v : Vt} {acc : Array UInt8},
    v.pstate = .osc acc false → (∀ b ∈ bs, b ≠ 0x1B ∧ b ≠ 0x07) →
    stick (v.feed bs) = stick v
  | [], _, _, _, _ => rfl
  | x :: xs, v, acc, hg, h => by
    rw [feed_cons]
    obtain ⟨acc', hs⟩ := osc_accum_step x hg (h x (by simp)).1 (h x (by simp)).2
    exact (stick_osc_run xs hs (fun b hb => h b (by simp [hb]))).trans
      (stick_step_of_osc x hg)

/-- The OSC title: everything from `ESC ]` to the `BEL` runs in a string state,
where no byte reaches a sticky field. -/
theorem smap_id_titleAnsi (v : Vt) : SMap id (titleAnsi v) := by
  intro g hg
  refine ⟨ends_titleAnsi v g hg, ?_⟩
  unfold titleAnsi
  rw [show (escB ++ [0x5D, 0x32, 0x3B] ++ utf8s v.title.toList ++ [0x07] : Bytes)
      = 0x1B :: 0x5D :: 0x32 :: 0x3B :: (utf8s v.title.toList ++ [0x07]) from by simp [escB]]
  rw [feed_cons, feed_cons, feed_cons, feed_cons]
  have he : (g.step 0x1B).pstate = .esc := esc_step hg
  have ho : ((g.step 0x1B).step 0x5D).pstate = .osc #[] false := osc_open_step he
  obtain ⟨acc2, ho2⟩ := osc_accum_step 0x32 ho (by decide) (by decide)
  obtain ⟨acc3, ho3⟩ := osc_accum_step 0x3B ho2 (by decide) (by decide)
  obtain ⟨acc4, ho4⟩ := osc_accum_feed (utf8s v.title.toList) ho3 (utf8s_no_esc_bel _)
  rw [show ∀ (u : Vt), u.feed (utf8s v.title.toList ++ [0x07])
      = (u.feed (utf8s v.title.toList)).feed [0x07] from
    fun u => by simp [Vt.feed, List.foldl_append]]
  rw [show ∀ (u : Vt), u.feed [(0x07 : UInt8)] = u.step 0x07 from fun _ => rfl]
  rw [stick_step_of_osc 0x07 ho4,
    stick_osc_run (utf8s v.title.toList) ho3 (utf8s_no_esc_bel _),
    stick_step_of_osc 0x3B ho2, stick_step_of_osc 0x32 ho,
    stick_step_of_esc 0x5D he (by decide),
    stick_step_of_ground 0x1B hg (by decide) (by decide)]
  rfl

/-! ### `CSI a ; b r` — the scroll-region setter, the only two-parameter walk -/

/-- `CSI a ;` — the collector after `;` closes the first parameter. The second
stage is `stick_csi_arg_tail` again, with a one-element collector, rather than a
second copy of the digit walk. -/
theorem stick_csi_semi_open (a : Nat) (halt : a < 65535)
    {g : Vt} (hg : g.pstate = .csi ({} : CsiState)) (hgu : g.u8need = 0) :
    ∃ sB : CsiState, (g.feed (digits a ++ [0x3B])).pstate = .csi sB
      ∧ sB.cur = 0 ∧ sB.haveCur = false ∧ sB.params = #[(a, false)] ∧ sB.curSub = false
      ∧ sB.inter = 0 ∧ sB.ignore = false ∧ sB.priv = 0
      ∧ (g.feed (digits a ++ [0x3B])).u8need = 0
      ∧ stick (g.feed (digits a ++ [0x3B])) = stick g := by
  obtain ⟨sa, hfA, -⟩ := csi_param_run_inter (digits a) hg hgu (paramBytes_digits a)
  obtain ⟨sa', hpsA, hcurA, hhaveA, hparA, hintA, hignA, hsubA, hprivA⟩ :=
    csi_digits_value a hg rfl
  have hsA : sa = sa' := PState.csi.inj
    ((by rw [hfA] : (g.feed (digits a)).pstate = .csi sa).symm.trans hpsA)
  have hfeed : g.feed (digits a ++ [0x3B]) = { g with pstate := .csi (csiPush sa false) } := by
    rw [show ∀ (u : Vt), u.feed (digits a ++ [0x3B]) = (u.feed (digits a)).step 0x3B from
      fun u => by simp [Vt.feed, List.foldl_append], hfA,
      step_of_csi_quiet 0x3B (v := { g with pstate := .csi sa }) rfl (by rw [hgu])]
    unfold Vt.stepCsi
    rw [if_neg (by decide), if_pos (by decide)]
  have hpush : csiPush sa false = { sa with
      params := sa.params.push (min sa.cur 65535, sa.curSub),
      cur := 0, curSub := false, haveCur := false } := by
    unfold csiPush
    rw [if_pos (by rw [hsA, hhaveA]; simp), if_neg (by rw [hsA, hparA]; decide)]
  refine ⟨csiPush sa false, by rw [hfeed], by rw [hpush], by rw [hpush], ?_, by rw [hpush],
    ?_, ?_, ?_, by rw [hfeed]; exact hgu, by rw [hfeed]; rfl⟩
  · rw [hpush]
    show sa.params.push (min sa.cur 65535, sa.curSub) = #[(a, false)]
    rw [hsA, hparA, hcurA, hsubA, show min (min a 65535) 65535 = a from by omega]
    rfl
  · rw [hpush]; show sa.inter = 0; rw [hsA]; exact hintA
  · rw [hpush]; show sa.ignore = false; rw [hsA]; exact hignA
  · rw [hpush]; show sa.priv = 0; rw [hsA]; exact hprivA

theorem smap_stbm (a b : Nat) (ha : 0 < a) (hb : 0 < b) (halt : a < 65535) (hblt : b < 65535) :
    SMap (stStbm (a - 1) (b - 1)) (csiNum2 a b 0x72) := by
  intro v hg
  rw [show csiNum2 a b 0x72
      = [0x1B, 0x5B] ++ ((digits a ++ [0x3B]) ++ (digits b ++ [0x72])) from by
    simp [csiNum2, csiB, List.append_assoc]]
  rw [feed_append, feed_append]
  obtain ⟨hc, hcu, hcs⟩ := stick_csi_open hg
  obtain ⟨sB, hpB, hcurB, hhaveB, hparB, hsubB, hintB, hignB, hprivB, huB, hsB⟩ :=
    stick_csi_semi_open a halt hc hcu
  obtain ⟨ht, hp⟩ := stick_csi_arg_tail b 0x72 (stStbm (a - 1) (b - 1)) hb hblt
    (by decide) (by decide) hcurB hhaveB (by rw [hparB]; simp) hintB hignB
    (fun u t hpv hig hpar => by
      have hpar' : t.params = (#[(a, false)] : Array (Nat × Bool)).push (b, false) := by
        rw [hpar, hparB, hsubB]
      have hpv0 : t.priv = 0 := by rw [hpv]; exact hprivB
      rw [stick_csiDispatch_stbm u t hig hpv0,
        (arg_of_two_of 1 hpar').1, (arg_of_two_of u.rows hpar').2,
        if_neg (by omega), if_neg (by omega)])
    hpB huB
  exact ⟨hp, by rw [ht, hsB, hcs]⟩

/-! ### The charset designations and the shift state -/

theorem smap_charset (i x : UInt8) (hi : i = 0x28 ∨ i = 0x29) :
    SMap (stCharset i x) (escCharset i x) := by
  intro v hg
  refine ⟨ends_escCharset i x hi v hg, ?_⟩
  rw [show escCharset i x = [0x1B] ++ [i, x] from rfl,
    show ∀ (w : Vt), w.feed ([0x1B] ++ [i, x]) = ((w.step 0x1B).step i).step x from
      fun w => by simp [Vt.feed]]
  have he : (v.step 0x1B).pstate = .esc := esc_step hg
  have hu1 : (v.step 0x1B).u8need = 0 := uz_step_esc v
  have hint : ((v.step 0x1B).step i).pstate = .escInter i := by
    rw [step_of_esc_quiet i he hu1]
    unfold Vt.stepEsc
    rcases hi with h | h <;> subst h <;> rfl
  rw [stick_step_of_escInter x hint,
    stick_step_of_esc i he (by rcases hi with h | h <;> rw [h] <;> decide),
    stick_step_of_ground 0x1B hg (by decide) (by decide)]

theorem smap_si : SMap (fun s => { s with so := false }) [0x0F] := by
  intro v hg
  rw [show v.feed [(0x0F : UInt8)] = v.step 0x0F from rfl]
  exact ⟨ground_step 0x0F hg (by decide), stick_step_si hg⟩

theorem smap_so : SMap (fun s => { s with so := true }) [0x0E] := by
  intro v hg
  rw [show v.feed [(0x0E : UInt8)] = v.step 0x0E from rfl]
  exact ⟨ground_step 0x0E hg (by decide), stick_step_so hg⟩

/-! ### The repaint preserves every sticky field

The rung the modes and pen claims did not need: the region, the charsets, the
shift state and the screen selection all have their emitters *around* the paint,
so these claims have to walk through `gridAnsi` rather than step over it. Printing
reads the charsets (translation) and the screen selection (scrollback eligibility)
and writes neither, which is `stick_print`. -/

theorem smap_id_rowAnsi (row : Row) (p : Pen) : SMap id (rowAnsi row p).1 := by
  unfold rowAnsi
  rw [← Array.foldl_toList]
  refine invariant_foldl (fun acc => SMap id acc.1) _ ?_ row.toList ([], p, 0) SMap.nil
  intro acc c hacc
  unfold rowSlot
  dsimp only
  repeat' split
  all_goals first
    | exact hacc.append (smap_utf8s c.marks)
    | exact hacc.append (smap_cellText c)
    | exact (hacc.append (smap_id_penSgr c.pen)).append (smap_cellText c)
    | exact hacc.append ((((smap_utf8_safe c.base).append (smap_id_cha _)).append
        (smap_utf8s c.marks)).append (smap_id_cha _))
    | exact (hacc.append (smap_id_penSgr c.pen)).append ((((smap_utf8_safe c.base).append
        (smap_id_cha _)).append (smap_utf8s c.marks)).append (smap_id_cha _))

theorem smap_id_joinCRLF : ∀ (l : List Bytes), (∀ bs ∈ l, SMap id bs) → SMap id (joinCRLF l)
  | [], _ => SMap.nil
  | [b], h => by unfold joinCRLF; exact h b (by simp)
  | b :: c :: bs, h => by
    unfold joinCRLF
    refine ((h b (by simp)).append smap_crlf).append ?_
    exact smap_id_joinCRLF (c :: bs) (fun x hx => h x (by simp [hx]))

theorem smap_id_gridAnsi (grid : Array Row) : SMap id (gridAnsi grid) := by
  unfold gridAnsi
  dsimp only
  have hrows : ∀ bs ∈ (grid.foldl
      (fun (acc : List Bytes × Pen) row =>
        (acc.1 ++ [(rowAnsi row acc.2).1], (rowAnsi row acc.2).2))
      (([], ({} : Pen)))).1, SMap id bs := by
    rw [← Array.foldl_toList]
    refine invariant_foldl (fun acc => ∀ bs ∈ acc.1, SMap id bs) _ ?_ grid.toList
      (([], ({} : Pen))) (by intro bs hbs; simp at hbs)
    intro acc row hacc bs hbs
    dsimp only at hbs
    rcases List.mem_append.mp hbs with h | h
    · exact hacc bs h
    · simp only [List.mem_singleton] at h
      subst h
      exact smap_id_rowAnsi row acc.2
  exact (smap_id_sgrNum 0).append (smap_id_home.append (smap_id_joinCRLF _ hrows))

/-! ### The remaining constructs -/

theorem smap_id_cursorAnsi (v : Vt) : SMap id (cursorAnsi v) := by
  unfold cursorAnsi
  split <;> exact smap_id_cup _ _

theorem smap_id_savedAnsi (v : Vt) : SMap id (savedAnsi v) := by
  unfold savedAnsi
  exact ((smap_id_penSgr _).append (smap_id_cup _ _)).append (smap_id_escSeq 0x37 (by decide))

theorem smap_id_tabsAnsi (v : Vt) : SMap id (tabsAnsi v) := by
  unfold tabsAnsi
  refine (smap_id_tbc 3).append ?_
  refine SMap.streamPred.flatMap (fun i => ?_)
  exact (smap_id_cha (i + 1)).append (smap_id_escSeq 0x48 (by decide))

/-- **A private mode emit that is not a screen switch moves no sticky field.**
`stSetMode`'s only non-identity case is 47/1047/1049, so naming the three
exclusions is the whole content. Lifted out of `smap_id_modesAnsi`, which was
where it was first needed; the scrollback stage's `?6l`/`?7h` need it too. -/
theorem smap_id_modeSet_safe (n : Nat) (on : Bool) (hn : 0 < n) (hlt : n < 65535)
    (h47 : n ≠ 47) (h1047 : n ≠ 1047) (h1049 : n ≠ 1049) : SMap id (modeSet n on) := by
  refine (smap_modeSet n on hn hlt).congr (fun s => ?_)
  unfold stSetMode
  rw [if_neg (by
    intro h
    simp only [Bool.or_eq_true, beq_iff_eq] at h
    rcases h with (h | h) | h
    · exact h47 h
    · exact h1047 h
    · exact h1049 h)]
  rfl

/-- Every mode `modesAnsi` replays is one `setMode` cannot turn into a screen
switch — including the mouse field, whose *guard* is what rules 47/1047/1049 out
(the same allowlist that `restore_modes_any` needs). -/
theorem smap_id_modesAnsi (v : Vt) : SMap id (modesAnsi v) := by
  have hm : ∀ (n : Nat) (on : Bool), 0 < n → n < 65535 → n ≠ 47 → n ≠ 1047 → n ≠ 1049 →
      SMap id (modeSet n on) := smap_id_modeSet_safe
  have hkey : SMap id (if v.modes.appKeypad then escSeq 0x3D else escSeq 0x3E) :=
    SMap.streamPred.ite (fun _ => smap_id_escSeq 0x3D (by decide))
      (fun _ => smap_id_escSeq 0x3E (by decide))
  have hmouse : SMap id (if v.modes.mouse == 1000 || v.modes.mouse == 1002
      || v.modes.mouse == 1003 then modeSet v.modes.mouse true else []) := by
    refine SMap.streamPred.ite (fun hc => ?_) (fun _ => SMap.nil)
    simp only [Bool.or_eq_true, beq_iff_eq] at hc
    rcases hc with (hc | hc) | hc <;> rw [hc] <;>
      exact hm _ true (by decide) (by decide) (by decide) (by decide) (by decide)
  unfold modesAnsi
  exact ((((((((((((hm 7 v.modes.wrap (by decide) (by decide) (by decide) (by decide)
      (by decide)).append
    (hm 1 v.modes.appCursor (by decide) (by decide) (by decide) (by decide) (by decide))).append
    hkey).append
    (hm 25 v.modes.cursorVisible (by decide) (by decide) (by decide) (by decide)
      (by decide))).append
    (hm 2004 v.modes.bracketedPaste (by decide) (by decide) (by decide) (by decide)
      (by decide))).append
    (hm 1000 false (by decide) (by decide) (by decide) (by decide) (by decide))).append
    (hm 1002 false (by decide) (by decide) (by decide) (by decide) (by decide))).append
    (hm 1003 false (by decide) (by decide) (by decide) (by decide) (by decide))).append
    hmouse).append
    (hm 1006 v.modes.mouseSgr (by decide) (by decide) (by decide) (by decide) (by decide))).append
    (hm 1004 v.modes.focusEvents (by decide) (by decide) (by decide) (by decide)
      (by decide))).append
    (hm 6 v.modes.origin (by decide) (by decide) (by decide) (by decide) (by decide))).append
    (smap_id_irm v.modes.insert)

/-- **`charsetAnsi` sets both designations absolutely and the shift state
set-only.** The `so` component of the transform reads `s.so`, and that is not an
artefact of the proof: the emitter sends `SO` when the session has G1 shifted in
and *nothing* when it does not, so the claim rests on the prologue's `SI` having
already cleared it — a long-range dependency the theorem now makes visible
instead of leaving to inspection. -/
theorem smap_charsetAnsi (v : Vt) :
    SMap (fun s => { s with
      g0 := v.g0Line, g1 := v.g1Line, so := if v.shiftOut then true else s.so })
      (charsetAnsi v) := by
  have h0 : SMap (fun s => { s with g0 := v.g0Line })
      (if v.g0Line then escCharset 0x28 0x30 else escCharset 0x28 0x42) := by
    by_cases hc : v.g0Line = true
    · rw [if_pos hc]
      exact (smap_charset 0x28 0x30 (Or.inl rfl)).congr (fun s => by simp [stCharset, hc])
    · rw [if_neg hc]
      exact (smap_charset 0x28 0x42 (Or.inl rfl)).congr (fun s => by
        simp [stCharset, show v.g0Line = false from by simpa using hc])
  have h1 : SMap (fun s => { s with g1 := v.g1Line })
      (if v.g1Line then escCharset 0x29 0x30 else escCharset 0x29 0x42) := by
    by_cases hc : v.g1Line = true
    · rw [if_pos hc]
      exact (smap_charset 0x29 0x30 (Or.inr rfl)).congr (fun s => by simp [stCharset, hc])
    · rw [if_neg hc]
      exact (smap_charset 0x29 0x42 (Or.inr rfl)).congr (fun s => by
        simp [stCharset, show v.g1Line = false from by simpa using hc])
  have h2 : SMap (fun s => { s with so := if v.shiftOut then true else s.so })
      (if v.shiftOut then [0x0E] else []) := by
    by_cases hc : v.shiftOut = true
    · rw [if_pos hc]
      exact smap_so.congr (fun s => by simp [hc])
    · rw [if_neg hc]
      exact SMap.nil.congr (fun s => by
        simp [show v.shiftOut = false from by simpa using hc])
  unfold charsetAnsi
  exact ((h0.comp h1).comp h2).congr (fun s => rfl)

/-- The flush run moves no sticky field: no ESC, no SO, no SI. -/
theorem smap_id_crlfRun (n : Nat) : SMap id ((List.replicate n crlfB).flatten) :=
  SMap.text (crlfRun_no_esc n)

/-- **The push itself is sticky-transparent** — `ED 3` does not move the region, an
`ED` of any mode is `smap_id_ed`, the paint is generic in the array, and the flush
is text. Named separately from the stage because `scrollback_entry` needs the
parser state at exactly this point: it is where the mode tail's `MMap` picks up. -/
theorem smap_id_sbPush (v : Vt) :
    SMap id (if (sbRows v).isEmpty then []
      else csiNum 3 0x4A ++ gridAnsi (sbRows v) ++ (List.replicate v.rows crlfB).flatten) :=
  (SMap.ite (c := (sbRows v).isEmpty = true) (fun _ => SMap.nil)
    (fun _ => ((smap_id_ed 3).append (smap_id_gridAnsi (sbRows v))).append
      (smap_id_crlfRun v.rows))).congr (fun s => by split <;> rfl)

/-- **The history stage is sticky-transparent.** Nothing in it emits `?1049h`,
`DECSTBM` or a charset designation — which is what keeps `paint_entry`'s region,
charset, shift-state and which-screen conjuncts alive across it, and `SMap`
carries no `u8need` side condition, so those six conjuncts cost one line each in
`scrollback_entry`. -/
theorem smap_id_scrollbackAnsi (v : Vt) : SMap id (scrollbackAnsi v) := by
  unfold scrollbackAnsi
  exact SMap.append (SMap.append (SMap.append (smap_id_sbPush v) smap_id_irm_reset)
    (smap_id_modeSet_safe 6 false (by decide) (by decide) (by decide) (by decide) (by decide)))
    (smap_id_modeSet_safe 7 true (by decide) (by decide) (by decide) (by decide) (by decide))

/-- The alt switch, in the middle of the repaint: `screensAnsi` sends `?1049h`
only when the session *is* on the alt screen, and the prologue's `?1049l` is what
makes that switch land (`enterAlt` is a no-op when already there). The history
stage sits ahead of both branches and is transparent, so the transform is
unchanged. -/
theorem smap_screensAnsi (v : Vt) :
    SMap (if v.altGrid.isSome then stAlt true else id) (screensAnsi v) := by
  have h1049 : SMap (stAlt true) (csiPriv 1049 0x68) := by
    have h := smap_modeSet 1049 true (by decide) (by decide)
    rw [show modeSet 1049 true = csiPriv 1049 0x68 from rfl] at h
    exact h.congr (fun s => by unfold stSetMode; rw [if_pos (by decide)])
  unfold screensAnsi
  refine ((smap_id_scrollbackAnsi v).comp ?_).congr (fun s => rfl)
  rcases hv : v.altGrid with - | x
  · rw [if_neg (by simp)]
    exact smap_id_gridAnsi _
  · obtain ⟨mg, mc, mp⟩ := x
    rw [if_pos (by simp)]
    exact ((((((smap_id_gridAnsi mg).append (smap_id_penSgr mp)).append
      (smap_id_cup _ _)).comp h1049).comp (smap_id_gridAnsi v.grid)).congr (fun s => rfl))

/-- The scroll region. The `[]` branch is the interesting one: it emits nothing,
so the claim there rests on the prologue's `CSI 1 ; rows r` — the second
long-range dependency this section makes visible. -/
theorem smap_regionAnsi (v : Vt) (h1 : v.top + 1 < 65535) (h2 : v.bot + 1 < 65535) :
    SMap (if v.top == 0 && v.bot == v.rows - 1 then id else stStbm v.top v.bot)
      (regionAnsi v) := by
  unfold regionAnsi
  exact SMap.ite (fun _ => SMap.nil)
    (fun _ => (smap_stbm (v.top + 1) (v.bot + 1) (by omega) (by omega) h1 h2).congr
      (fun s => by simp))

/-! ### The claim -/

/-- One rung of the value chain, for a fixed receiver: `a` has left the sticky
state at `x`, `b` maps it by `f`, so `a ++ b` leaves it at `f x`. Values rather
than composed transforms, because a twenty-deep nest of record updates is exactly
what `mmap_modesAnsi` had to stop `rfl` from evaluating. -/
theorem sput_step {w : Vt} {a b : Bytes} {x : Sticky} {f : Sticky → Sticky}
    (ha : (w.feed a).pstate = .ground ∧ stick (w.feed a) = x) (hb : SMap f b) :
    (w.feed (a ++ b)).pstate = .ground ∧ stick (w.feed (a ++ b)) = f x := by
  rw [feed_append]
  obtain ⟨h1, h2⟩ := ha
  obtain ⟨h3, h4⟩ := hb _ h1
  exact ⟨h3, by rw [h4, h2]⟩

/-- …and the normalization that keeps the chain's values small: without it the
twenty applications nest, and every record update duplicates its argument once per
field. -/
theorem sput_congr {w : Vt} {a : Bytes} {x y : Sticky}
    (h : (w.feed a).pstate = .ground ∧ stick (w.feed a) = x) (hxy : x = y) :
    (w.feed a).pstate = .ground ∧ stick (w.feed a) = y := ⟨h.1, h.2.trans hxy⟩

/-- The lead-in cannot change the receiver's **height**, which is all the
prologue's `DECSTBM` needs of it. It *can* change a charset designation — a
receiver caught mid-`ESC (` reads our `ESC` as the designator byte — which is
harmless, since the prologue re-designates both charsets absolutely, and is why
the chain below starts from an unknown sticky value rather than from `stick w`. -/
theorem rows_st_lead (w : Vt) : (w.feed (escSeq 0x5C)).rows = w.rows :=
  congrArg (·.2) (dims_feed_ne_ris (escSeq 0x5C) (by decide))

/-- **A5 inbound, the sticky fields.** For any receiver of the session's height,
`restore` installs the session's scroll region, both charset designations, the
shift state and which screen is current — the last group of restored fields, and
the only one whose proof cannot step over the repaint (the region is set before
the title, and the screen switch in the middle of the paint).

Two hypotheses, both the analog of `restore_modes_any`'s mouse allowlist: a `Vt`
does not only come from `setMode`, so `Checkpoint.load` can hand us a region no
emulator would produce.

* `hlt : v.top < v.bot` together with `hbot : v.bot < v.rows` is the region
  `DECSTBM` will **accept**. The excluded case is a one-row region: `CSI t ; t r` is
  refused here and on every real terminal, so there is nothing to install and
  nothing to claim.
* `hfits : v.rows < 65535` keeps `DECSTBM`'s parameters off the parser's clamp.

The last two are what `Good v` would give (`botLt`, `rowsLe`), but they are taken
directly: `Good` also asserts things about the cursor, the saved slot, the
scrollback and the CSI accumulator that this proof never reads, and a hypothesis a
proof does not use makes the theorem weaker than it is. `restore_sticky_good` is the
`Good`-flavoured entry point for callers that have it. -/
theorem restore_sticky_any (v w : Vt) (hrows : w.rows = v.rows)
    (hlt : v.top < v.bot) (hbot : v.bot < v.rows) (hfits : v.rows < 65535) :
    stick (w.feed (restore v)) = stick v := by
  have hpos : 1 ≤ v.rows := by omega
  rw [show restore v = escSeq 0x5C ++ modeSet 1049 false ++ csiNum 4 0x6C ++ modeSet 6 false
      ++ modeSet 7 true ++ csiNum2 1 v.rows 0x72 ++ escCharset 0x28 0x42
      ++ escCharset 0x29 0x42 ++ [0x0F] ++ csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v
      ++ regionAnsi v ++ tabsAnsi v ++ savedAnsi v ++ titleAnsi v ++ modesAnsi v
      ++ charsetAnsi v ++ penSgr v.pen ++ cursorAnsi v from by
    simp only [restore, restoreBody, prologueAnsi]]
  -- every mode set but the three screen-switch numbers is transparent to `stick`
  have eid : ∀ (n : Nat) (on : Bool) (Y : Sticky), (n == 47 || n == 1047 || n == 1049) = false →
      stSetMode n on Y = Y := by
    intro n on Y h
    unfold stSetMode
    rw [if_neg (by rw [h]; simp)]
  -- the lead-in leaves an unknown sticky state; only its height is known, and
  -- the prologue overwrites every other field absolutely
  obtain ⟨A, hA⟩ : ∃ y : Sticky, stAlt false (stick (w.feed (escSeq 0x5C))) = y := ⟨_, rfl⟩
  have hArows : A.rows = v.rows := by
    rw [← hA, stAlt_rows]
    exact (rows_st_lead w).trans hrows
  have hAalt : A.alt = false := by rw [← hA]; exact stAlt_alt false _
  obtain ⟨Ar, At, Ab, Ag0, Ag1, Aso, Aal⟩ := A
  simp only at hArows hAalt
  subst hArows hAalt
  -- the prologue: `?1049l`, IRM, DECOM, DECAWM, DECSTBM, both charsets, SI
  have h0 : (w.feed (escSeq 0x5C)).pstate = .ground
      ∧ stick (w.feed (escSeq 0x5C)) = stick (w.feed (escSeq 0x5C)) := ⟨(st_grounds w).1, rfl⟩
  have h1 := sput_congr (sput_step h0 (smap_modeSet 1049 false (by decide) (by decide)))
    (show stSetMode 1049 false (stick (w.feed (escSeq 0x5C)))
        = ⟨v.rows, At, Ab, Ag0, Ag1, Aso, false⟩ from by
      rw [show stSetMode 1049 false (stick (w.feed (escSeq 0x5C)))
        = stAlt false (stick (w.feed (escSeq 0x5C))) from by
          unfold stSetMode; rw [if_pos (by decide)]]
      exact hA)
  have h2 := sput_congr (sput_step h1 smap_id_irm_reset) (id_eq _)
  have h3 := sput_congr (sput_step h2 (smap_modeSet 6 false (by decide) (by decide)))
    (eid 6 false _ (by decide))
  have h4 := sput_congr (sput_step h3 (smap_modeSet 7 true (by decide) (by decide)))
    (eid 7 true _ (by decide))
  have h5 := sput_congr
    (sput_step h4 (smap_stbm 1 v.rows (by decide) (by omega) (by decide) (by omega)))
    (show stStbm (1 - 1) (v.rows - 1) (⟨v.rows, At, Ab, Ag0, Ag1, Aso, false⟩ : Sticky)
        = ⟨v.rows, 0, v.rows - 1, Ag0, Ag1, Aso, false⟩ from by
      rw [stStbm_of (by omega) (show v.rows - 1 < (⟨v.rows, At, Ab, Ag0, Ag1, Aso, false⟩
        : Sticky).rows from by simp only; omega)])
  have h6 := sput_congr (sput_step h5 (smap_charset 0x28 0x42 (Or.inl rfl)))
    (show stCharset 0x28 0x42 (⟨v.rows, 0, v.rows - 1, Ag0, Ag1, Aso, false⟩ : Sticky)
        = ⟨v.rows, 0, v.rows - 1, false, Ag1, Aso, false⟩ from by
      unfold stCharset; rw [if_pos (by decide)]; rfl)
  have h7 := sput_congr (sput_step h6 (smap_charset 0x29 0x42 (Or.inr rfl)))
    (show stCharset 0x29 0x42 (⟨v.rows, 0, v.rows - 1, false, Ag1, Aso, false⟩ : Sticky)
        = ⟨v.rows, 0, v.rows - 1, false, false, Aso, false⟩ from by
      unfold stCharset; rw [if_neg (by decide), if_pos (by decide)]; rfl)
  have h8 := sput_congr (sput_step h7 smap_si)
    (show ({ (⟨v.rows, 0, v.rows - 1, false, false, Aso, false⟩ : Sticky) with so := false })
        = ⟨v.rows, 0, v.rows - 1, false, false, false, false⟩ from rfl)
  -- the repaint and the alt switch
  have h9 := sput_congr (sput_step h8 (smap_id_sgrNum 0)) (id_eq _)
  have h10 := sput_congr (sput_step h9 (smap_id_ed 2)) (id_eq _)
  have h11 := sput_congr (sput_step h10 (smap_screensAnsi v))
    (show (if v.altGrid.isSome then stAlt true else id)
        (⟨v.rows, 0, v.rows - 1, false, false, false, false⟩ : Sticky)
        = ⟨v.rows, 0, v.rows - 1, false, false, false, v.altGrid.isSome⟩ from by
      by_cases hv : v.altGrid.isSome = true
      · rw [if_pos hv, hv]
        unfold stAlt
        dsimp only
        rw [if_neg (by simp)]
      · rw [if_neg hv, show v.altGrid.isSome = false from by simpa using hv]
        rfl)
  -- the scroll region
  have h12 := sput_congr (sput_step h11 (smap_regionAnsi v (by omega) (by omega)))
    (show (if v.top == 0 && v.bot == v.rows - 1 then id else stStbm v.top v.bot)
        (⟨v.rows, 0, v.rows - 1, false, false, false, v.altGrid.isSome⟩ : Sticky)
        = ⟨v.rows, v.top, v.bot, false, false, false, v.altGrid.isSome⟩ from by
      by_cases hd : (v.top == 0 && v.bot == v.rows - 1) = true
      · rw [if_pos hd]
        simp only [Bool.and_eq_true, beq_iff_eq] at hd
        rw [hd.1, hd.2]
        rfl
      · rw [if_neg hd, stStbm_of hlt (show v.bot < (⟨v.rows, 0, v.rows - 1, false, false, false,
          v.altGrid.isSome⟩ : Sticky).rows from by simp only; omega)])
  have h13 := sput_congr (sput_step h12 (smap_id_tabsAnsi v)) (id_eq _)
  have h14 := sput_congr (sput_step h13 (smap_id_savedAnsi v)) (id_eq _)
  have h15 := sput_congr (sput_step h14 (smap_id_titleAnsi v)) (id_eq _)
  have h16 := sput_congr (sput_step h15 (smap_id_modesAnsi v)) (id_eq _)
  -- the charsets and the shift state
  have h17 := sput_congr (sput_step h16 (smap_charsetAnsi v))
    (show ({ (⟨v.rows, v.top, v.bot, false, false, false, v.altGrid.isSome⟩ : Sticky) with
        g0 := v.g0Line, g1 := v.g1Line,
        so := if v.shiftOut then true else
          (⟨v.rows, v.top, v.bot, false, false, false, v.altGrid.isSome⟩ : Sticky).so })
        = ⟨v.rows, v.top, v.bot, v.g0Line, v.g1Line, v.shiftOut, v.altGrid.isSome⟩ from by
      cases v.shiftOut <;> rfl)
  have h18 := sput_congr (sput_step h17 (smap_id_penSgr v.pen)) (id_eq _)
  have h19 := sput_congr (sput_step h18 (smap_id_cursorAnsi v)) (id_eq _)
  refine h19.2.trans ?_
  show (⟨v.rows, v.top, v.bot, v.g0Line, v.g1Line, v.shiftOut, v.altGrid.isSome⟩ : Sticky)
    = stick v
  rfl

/-! ### The three field claims the spec asks for, as projections of the bundle

Named separately because they are what THEOREMS.md's A5 row cites and what a
reader looks for; each is one `congrArg` off `restore_sticky_any`, which is the
payoff of bundling rather than proving four `org_`-style families. -/

/-- **The scroll region.** Set by `regionAnsi`, or — when the session's region is
the whole screen and `regionAnsi` therefore emits nothing — by the prologue's
`CSI 1 ; rows r`, through the repaint and the alt switch. -/
theorem restore_region_any (v w : Vt) (hrows : w.rows = v.rows) (hlt : v.top < v.bot)
    (hbot : v.bot < v.rows) (hfits : v.rows < 65535) :
    (w.feed (restore v)).top = v.top ∧ (w.feed (restore v)).bot = v.bot := by
  have h := restore_sticky_any v w hrows hlt hbot hfits
  refine ⟨?_, ?_⟩
  · rw [← stick_top (w.feed (restore v)), h, stick_top]
  · rw [← stick_bot (w.feed (restore v)), h, stick_bot]

/-- **The charset designations and the shift state.** G0 and G1 are set
absolutely by `charsetAnsi`; the shift state is set-only there, so its claim runs
back through the whole repaint to the prologue's `SI`. -/
theorem restore_charset_any (v w : Vt) (hrows : w.rows = v.rows) (hlt : v.top < v.bot)
    (hbot : v.bot < v.rows) (hfits : v.rows < 65535) :
    (w.feed (restore v)).g0Line = v.g0Line ∧ (w.feed (restore v)).g1Line = v.g1Line
      ∧ (w.feed (restore v)).shiftOut = v.shiftOut := by
  have h := restore_sticky_any v w hrows hlt hbot hfits
  refine ⟨?_, ?_, ?_⟩
  · rw [← stick_g0 (w.feed (restore v)), h, stick_g0]
  · rw [← stick_g1 (w.feed (restore v)), h, stick_g1]
  · rw [← stick_so (w.feed (restore v)), h, stick_so]

/-- **Which screen is current.** The one claim that cannot avoid the repaint at
all: `screensAnsi` switches in the *middle* of it, and the switch only lands
because the prologue left the receiver on the main screen (`enterAlt` is a no-op
when the receiver is already in alt — the hazard `prologueAnsi`'s first comment
names, now a theorem rather than a comment). -/
theorem restore_alt_any (v w : Vt) (hrows : w.rows = v.rows) (hlt : v.top < v.bot)
    (hbot : v.bot < v.rows) (hfits : v.rows < 65535) :
    (w.feed (restore v)).altGrid.isSome = v.altGrid.isSome := by
  rw [← stick_alt (w.feed (restore v)), restore_sticky_any v w hrows hlt hbot hfits, stick_alt]

/-- The `Good`-flavoured entry point: the codebase's standard sanity invariant
supplies both arithmetic facts, so a caller holding `Good v` (every live-reachable
session — `good_of_liveReachable`) needs nothing else. -/
theorem restore_sticky_good (v w : Vt) (hgood : Good v) (hrows : w.rows = v.rows)
    (hlt : v.top < v.bot) : stick (w.feed (restore v)) = stick v :=
  restore_sticky_any v w hrows hlt hgood.botLt (by have := hgood.rowsLe; omega)

/-! ### Step 2's second half — `u8need`, for any receiver

`restore_grounds` gave the parser state for any receiver; this gives the decoder.
It needs no ladder at all, and the reason is worth stating: `restore` **ends** with
`cursorAnsi`, which is one `CSI … H`, and `u8_zero_after_csi` zeroes `u8need`
whatever the incoming state was — a CSI's final byte cannot leave a character
half-decoded. So the whole stream in front of it is irrelevant to this half, where
`restore_quiesced` had to assume a fresh `Vt.init`. -/

theorem restore_u8_zero (v w : Vt) : (w.feed (restore v)).u8need = 0 := by
  unfold restore
  rw [show ∀ (u : Vt), u.feed (restoreBody v ++ cursorAnsi v)
        = (u.feed (restoreBody v)).feed (cursorAnsi v) from
      fun u => by simp [Vt.feed, List.foldl_append]]
  unfold cursorAnsi
  split
  all_goals
    (unfold csiNum2
     refine u8_zero_after_csi _ 0x48 ?_ (by decide) _
     exact ((paramBytes_digits _).append
       (ParamBytes.cons (by decide) (by decide) ParamBytes.nil)).append
       (paramBytes_digits _))

/-- **§Replay's parser half, receiver-quantified** — Step 2's exit for `restore`.
`restore_quiesced` said this of a fresh `Vt.init`; a client is never that. Any
receiver in any parser state, mid-escape or mid-OSC or holding a half-decoded
character, is left `ground` with nothing pending. -/
theorem restore_quiesced_any (v w : Vt) :
    (w.feed (restore v)).pstate = .ground ∧ (w.feed (restore v)).u8need = 0 :=
  ⟨restore_grounds v w, restore_u8_zero v w⟩

/-- **The first of `restore_grid_of_paint`'s three hypotheses, discharged for any
receiver.** The clear-and-paint prefix leaves the parser in `ground`: the prologue
grounds `w` whatever state it was in (`prologue_grounds`, Step 2's first half) and
the three constructs after it are each `Ends`.

The `u8need` one is *not* free the same way, and the asymmetry is worth naming: the
whole stream ends in a `CSI … H`, whose final byte cannot leave a character
half-decoded (`restore_u8_zero`), but this **prefix** ends in glyph bytes. So that
hypothesis belongs with the cell induction, where the UTF-8 completeness of what
`rowAnsi` emits is in scope anyway. -/
theorem paint_grounds (v w : Vt) :
    (w.feed (prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v)).pstate
      = .ground := by
  rw [show prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v
      = prologueAnsi v ++ (csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v) from by
    simp only [List.append_assoc], feed_append]
  exact (((ends_csiNum 0 0x6D (by decide) (by decide)).append
    (ends_csiNum 2 0x4A (by decide) (by decide))).append (ends_screensAnsi v)) _
    (prologue_grounds v w)

/-! ### A5 outbound, the same fields — `leave_canonical`'s other half

Definition-of-done item 2b names the charset flags, the scroll region, the
alt-screen flag *and* the pen for the hand-back, not just the modes. With `SMap`
in hand they cost one more chain, and leaving the outbound half at "modes only"
while the inbound half is complete would be exactly the asymmetry that let the
hand-back ship in the first place. -/

/-- `CSI r` — `DECSTBM` with **no** parameters, which is how the hand-back names
"the whole screen" without knowing the receiver's height: both arguments fall
back to their defaults, `1` and the receiver's own `rows`. Not an instance of
`smap_csi_one_arg` (there is no parameter to walk) and not of `csi_tail_proj` (the
dispatch is the point), so the walk is short and direct. -/
theorem smap_stbm_plain : SMap (fun s => stStbm 0 (s.rows - 1) s) (csiPlain 0x72) := by
  intro v hg
  rw [show csiPlain 0x72 = [0x1B, 0x5B] ++ [(0x72 : UInt8)] from by simp [csiPlain, csiB]]
  rw [feed_append]
  obtain ⟨hc, hcu, hcs⟩ := stick_csi_open hg
  rw [show ∀ (u : Vt), u.feed [(0x72 : UInt8)] = u.step 0x72 from fun _ => rfl]
  rw [csi_final_step_eq 0x72 hc hcu rfl (by decide) (by decide)]
  unfold Vt.csiFinish
  rw [if_neg (by decide)]
  refine ⟨rfl, ?_⟩
  show stick ((v.feed [(0x1B : UInt8), 0x5B]).csiDispatch ({} : CsiState) 0x72)
    = stStbm 0 ((stick v).rows - 1) (stick v)
  rw [stick_csiDispatch_stbm _ _ rfl rfl,
    show (({} : CsiState)).arg 0 1 = 1 from rfl,
    show (({} : CsiState)).arg 1 (v.feed [(0x1B : UInt8), 0x5B]).rows
      = (v.feed [(0x1B : UInt8), 0x5B]).rows from rfl,
    show (v.feed [(0x1B : UInt8), 0x5B]).rows = (stick (v.feed [0x1B, 0x5B])).rows from rfl,
    hcs]

/-- **A5 outbound, in full.** For any receiver at least two rows tall, the
hand-back leaves the parser `ground`, the modes at the default record, the scroll
region whole, both charsets ASCII with G0 shifted in, the main screen current, and
the pen reset. Two rows is the one exclusion, and it is the same one as inbound:
`DECSTBM` refuses a one-row region here and on every real terminal, so there is
nothing to establish. -/
theorem leave_canonical_all (w : Vt) (h2 : 2 ≤ w.rows) :
    (w.feed leaveAnsi).pstate = .ground
      ∧ (w.feed leaveAnsi).modes = ({} : Modes)
      ∧ stick (w.feed leaveAnsi)
          = ⟨w.rows, 0, w.rows - 1, false, false, false, false⟩
      ∧ (w.feed leaveAnsi).pen = ({} : Pen) := by
  have eid : ∀ (n : Nat) (on : Bool) (Y : Sticky), (n == 47 || n == 1047 || n == 1049) = false →
      stSetMode n on Y = Y := by
    intro n on Y h
    unfold stSetMode
    rw [if_neg (by rw [h]; simp)]
  obtain ⟨B, hB⟩ : ∃ y : Sticky, stAlt false (stick (w.feed (escSeq 0x5C))) = y := ⟨_, rfl⟩
  have hBrows : B.rows = w.rows := by rw [← hB, stAlt_rows]; exact rows_st_lead w
  have hBalt : B.alt = false := by rw [← hB]; exact stAlt_alt false _
  obtain ⟨Br, Bt, Bb, Bg0, Bg1, Bso, Bal⟩ := B
  simp only at hBrows hBalt
  subst hBrows hBalt
  have l0 : (w.feed (escSeq 0x5C)).pstate = .ground
      ∧ stick (w.feed (escSeq 0x5C)) = stick (w.feed (escSeq 0x5C)) := ⟨(st_grounds w).1, rfl⟩
  have l1 := sput_congr (sput_step l0 (smap_modeSet 1049 false (by decide) (by decide)))
    (show stSetMode 1049 false (stick (w.feed (escSeq 0x5C)))
        = ⟨w.rows, Bt, Bb, Bg0, Bg1, Bso, false⟩ from by
      rw [show stSetMode 1049 false (stick (w.feed (escSeq 0x5C)))
        = stAlt false (stick (w.feed (escSeq 0x5C))) from by
          unfold stSetMode; rw [if_pos (by decide)]]
      exact hB)
  have l2 := sput_congr (sput_step l1 smap_id_irm_reset) (id_eq _)
  have l3 := sput_congr (sput_step l2 (smap_modeSet 25 true (by decide) (by decide)))
    (eid 25 true _ (by decide))
  have l4 := sput_congr (sput_step l3 (smap_modeSet 2004 false (by decide) (by decide)))
    (eid 2004 false _ (by decide))
  have l5 := sput_congr (sput_step l4 (smap_modeSet 1000 false (by decide) (by decide)))
    (eid 1000 false _ (by decide))
  have l6 := sput_congr (sput_step l5 (smap_modeSet 1002 false (by decide) (by decide)))
    (eid 1002 false _ (by decide))
  have l7 := sput_congr (sput_step l6 (smap_modeSet 1003 false (by decide) (by decide)))
    (eid 1003 false _ (by decide))
  have l8 := sput_congr (sput_step l7 (smap_modeSet 1006 false (by decide) (by decide)))
    (eid 1006 false _ (by decide))
  have l9 := sput_congr (sput_step l8 (smap_modeSet 1004 false (by decide) (by decide)))
    (eid 1004 false _ (by decide))
  have l10 := sput_congr (sput_step l9 (smap_modeSet 1 false (by decide) (by decide)))
    (eid 1 false _ (by decide))
  have l11 := sput_congr (sput_step l10 (smap_id_escSeq 0x3E (by decide))) (id_eq _)
  have l12 := sput_congr (sput_step l11 (smap_modeSet 6 false (by decide) (by decide)))
    (eid 6 false _ (by decide))
  have l13 := sput_congr (sput_step l12 (smap_modeSet 7 true (by decide) (by decide)))
    (eid 7 true _ (by decide))
  have l14 := sput_congr (sput_step l13 smap_stbm_plain)
    (show stStbm 0 ((⟨w.rows, Bt, Bb, Bg0, Bg1, Bso, false⟩ : Sticky).rows - 1)
        (⟨w.rows, Bt, Bb, Bg0, Bg1, Bso, false⟩ : Sticky)
        = ⟨w.rows, 0, w.rows - 1, Bg0, Bg1, Bso, false⟩ from by
      rw [stStbm_of (show 0 < (⟨w.rows, Bt, Bb, Bg0, Bg1, Bso, false⟩ : Sticky).rows - 1 from by
        simp only; omega) (by simp only; omega)])
  have l15 := sput_congr (sput_step l14 (smap_charset 0x28 0x42 (Or.inl rfl)))
    (show stCharset 0x28 0x42 (⟨w.rows, 0, w.rows - 1, Bg0, Bg1, Bso, false⟩ : Sticky)
        = ⟨w.rows, 0, w.rows - 1, false, Bg1, Bso, false⟩ from by
      unfold stCharset; rw [if_pos (by decide)]; rfl)
  have l16 := sput_congr (sput_step l15 (smap_charset 0x29 0x42 (Or.inr rfl)))
    (show stCharset 0x29 0x42 (⟨w.rows, 0, w.rows - 1, false, Bg1, Bso, false⟩ : Sticky)
        = ⟨w.rows, 0, w.rows - 1, false, false, Bso, false⟩ from by
      unfold stCharset; rw [if_neg (by decide), if_pos (by decide)]; rfl)
  have l17 := sput_congr (sput_step l16 smap_si)
    (show ({ (⟨w.rows, 0, w.rows - 1, false, false, Bso, false⟩ : Sticky) with so := false })
        = ⟨w.rows, 0, w.rows - 1, false, false, false, false⟩ from rfl)
  have l18 := sput_congr (sput_step l17 (smap_id_cup 999 1)) (id_eq _)
  have l19 := sput_congr (sput_step l18 (smap_id_sgrNum 0)) (id_eq _)
  -- the pen: the trailing `SGR 0` **is** `penSgr {}`, fed from the grounded prefix
  have hps : penSgr ({} : Pen) = csiNum 0 0x6D := by
    show csiNum 0 0x6D ++ [] ++ [] = csiNum 0 0x6D
    simp
  have hu18 : (w.feed (escSeq 0x5C ++ modeSet 1049 false ++ csiNum 4 0x6C
      ++ modeSet 25 true ++ modeSet 2004 false ++ modeSet 1000 false ++ modeSet 1002 false
      ++ modeSet 1003 false ++ modeSet 1006 false ++ modeSet 1004 false ++ modeSet 1 false
      ++ escSeq 0x3E ++ modeSet 6 false ++ modeSet 7 true ++ csiPlain 0x72
      ++ escCharset 0x28 0x42 ++ escCharset 0x29 0x42 ++ [0x0F] ++ csiNum2 999 1 0x48)).u8need = 0 := by
    rw [show (escSeq 0x5C ++ modeSet 1049 false ++ csiNum 4 0x6C
      ++ modeSet 25 true ++ modeSet 2004 false ++ modeSet 1000 false ++ modeSet 1002 false
      ++ modeSet 1003 false ++ modeSet 1006 false ++ modeSet 1004 false ++ modeSet 1 false
      ++ escSeq 0x3E ++ modeSet 6 false ++ modeSet 7 true ++ csiPlain 0x72
      ++ escCharset 0x28 0x42 ++ escCharset 0x29 0x42 ++ [0x0F] ++ csiNum2 999 1 0x48)
        = (escSeq 0x5C ++ modeSet 1049 false ++ csiNum 4 0x6C
        ++ modeSet 25 true ++ modeSet 2004 false ++ modeSet 1000 false ++ modeSet 1002 false
        ++ modeSet 1003 false ++ modeSet 1006 false ++ modeSet 1004 false ++ modeSet 1 false
        ++ escSeq 0x3E ++ modeSet 6 false ++ modeSet 7 true ++ csiPlain 0x72
        ++ escCharset 0x28 0x42 ++ escCharset 0x29 0x42 ++ [0x0F])
          ++ (csiB ++ (digits 999 ++ [0x3B] ++ digits 1) ++ [0x48]) from by
      simp only [csiNum2, List.append_assoc]]
    rw [feed_append]
    exact u8_zero_after_csi _ 0x48
      (((paramBytes_digits 999).append
        (ParamBytes.cons (by decide) (by decide) ParamBytes.nil)).append
        (paramBytes_digits 1)) (by decide) _
  have hpen : (w.feed leaveAnsi).pen = ({} : Pen) := by
    rw [show leaveAnsi = (escSeq 0x5C ++ modeSet 1049 false ++ csiNum 4 0x6C
      ++ modeSet 25 true ++ modeSet 2004 false ++ modeSet 1000 false ++ modeSet 1002 false
      ++ modeSet 1003 false ++ modeSet 1006 false ++ modeSet 1004 false ++ modeSet 1 false
      ++ escSeq 0x3E ++ modeSet 6 false ++ modeSet 7 true ++ csiPlain 0x72
      ++ escCharset 0x28 0x42 ++ escCharset 0x29 0x42 ++ [0x0F] ++ csiNum2 999 1 0x48) ++ penSgr ({} : Pen) from by
      rw [hps]; simp only [leaveAnsi]]
    rw [feed_append, penSgr_feed ({} : Pen) l18.1 hu18]
  exact ⟨leave_grounds w, leave_modes w, l19.2, hpen⟩

/-! ## §Replay stage 3d — the two byte→cursor bridges the paint needs

`cup_places_cursor` says where a two-argument `CUP` puts the cursor. The repaint uses
two *other* addressing forms and neither had a bridge, so the row induction could not
say where it was writing:

* `gridAnsi` homes with a bare `CSI H` — both arguments defaulted — which is what
  establishes column 0, row 0 for the first cell;
* `rowAnsi`'s wide-with-marks branch parks the cursor with `CHA` (`CSI n G`), twice,
  because a mark on a wide glyph must land between the glyph and its shadow (§Replay
  fix 8) and no relative move can express that.

Both are the same walk as `cup_places_cursor`, one parameter shorter. -/

/-- **A bare `CSI H` homes the cursor.** With no parameters both arguments fall back
to `1`, so this is `moveTo 0 0` — and with DECOM off that is the true origin rather
than the scroll region's top, which is why `prologueAnsi` resets `?6l` before the
paint. -/
theorem home_places_cursor {v : Vt} (hg : v.pstate = .ground) (hu : v.u8need = 0)
    (ho : v.modes.origin = false) :
    (v.feed (csiB ++ [0x48])).cursor.x = 0 ∧ (v.feed (csiB ++ [0x48])).cursor.y = 0
      ∧ (v.feed (csiB ++ [0x48])).cursor.pending = false := by
  rw [show (csiB ++ [0x48] : Bytes) = [0x1B, 0x5B] ++ [(0x48 : UInt8)] from by simp [csiB]]
  rw [feed_append, keeps_csi_open hg hu,
    show ∀ (u : Vt), u.feed [(0x48 : UInt8)] = u.step 0x48 from fun _ => rfl]
  rw [csi_final_step_eq 0x48 (v := { v with pstate := .csi ({} : CsiState) })
    (s := ({} : CsiState)) rfl (by simpa using hu) rfl (by decide) (by decide)]
  unfold Vt.csiFinish
  rw [if_neg (by decide)]
  show ((({ v with pstate := .csi ({} : CsiState) } : Vt).csiDispatch
      ({} : CsiState) 0x48).cursor.x = 0)
    ∧ ((({ v with pstate := .csi ({} : CsiState) } : Vt).csiDispatch
      ({} : CsiState) 0x48).cursor.y = 0)
    ∧ ((({ v with pstate := .csi ({} : CsiState) } : Vt).csiDispatch
      ({} : CsiState) 0x48).cursor.pending = false)
  rw [show ({ v with pstate := .csi ({} : CsiState) } : Vt).csiDispatch ({} : CsiState) 0x48
      = ({ v with pstate := .csi ({} : CsiState) } : Vt).moveTo 0 0 from by
    unfold Vt.csiDispatch
    rw [if_neg (by decide)]
    rfl]
  unfold Vt.moveTo
  rw [if_neg (show ¬(({ v with pstate := .csi ({} : CsiState) } : Vt).modes.origin = true) from by
    show ¬(v.modes.origin = true); rw [ho]; simp)]
  refine ⟨?_, ?_, rfl⟩ <;> simp

/-- **`CHA` places the column.** `CSI n G` is `setCol (n-1)`: the row is untouched and
wrap-pending is cleared, which is exactly what the wide-with-marks branch needs of
it — the mark must attach to the base at `n-2`, and `printMark` steps one left from
a cursor that is *not* wrap-pending.

The `min` is not decoration. The branch's *trailing* `CHA` addresses the column after
the pair, and for a pair that ends at the margin that column does not exist — so it
clamps, and the row exits with the cursor on the last column and wrap-pending
**clear**. An in-range-only statement would have left that case unprovable rather than
false, which is the shape of hypothesis this spec exists to remove. -/
theorem cha_places_cursor {v : Vt} (n : Nat) (hg : v.pstate = .ground) (hu : v.u8need = 0)
    (hn : 0 < n) (hlt : n < 65535) :
    (v.feed (csiNum n 0x47)).cursor.x = min (n - 1) (v.cols - 1)
      ∧ (v.feed (csiNum n 0x47)).cursor.y = v.cursor.y
      ∧ (v.feed (csiNum n 0x47)).cursor.pending = false := by
  rw [show csiNum n 0x47 = [0x1B, 0x5B] ++ (digits n ++ [(0x47 : UInt8)]) from by
    simp [csiNum, csiB]]
  rw [feed_append, keeps_csi_open hg hu]
  obtain ⟨s', heq, hcur', hhave, hpar, hint, hsub⟩ :=
    csi_digits_run_eq n (v := { v with pstate := .csi ({} : CsiState) })
      (s := ({} : CsiState)) rfl (by simpa using hu) rfl
  rw [show ∀ (u : Vt), u.feed (digits n ++ [(0x47 : UInt8)])
      = (u.feed (digits n)).feed [(0x47 : UInt8)] from
    fun u => by simp [Vt.feed, List.foldl_append]]
  rw [heq, show ∀ (u : Vt), u.feed [(0x47 : UInt8)] = u.step 0x47 from fun _ => rfl]
  rw [csi_final_step_eq 0x47 rfl (by simpa using hu) (by rw [hint]) (by decide) (by decide)]
  unfold Vt.csiFinish
  rw [if_pos (by simpa using hhave), if_neg (by rw [hpar]; decide)]
  dsimp only
  have harg : ({ s' with params := s'.params.push (min s'.cur 65535, s'.curSub) }
      : CsiState).arg 0 1 = n := by
    rw [arg_of_one_of 1 (show ({ s' with params := s'.params.push (min s'.cur 65535, s'.curSub) }
        : CsiState).params = (#[] : Array (Nat × Bool)).push (n, s'.curSub) from by
      rw [hpar, hcur', show min (min n 65535) 65535 = n from by omega]),
      if_neg (by omega)]
  rw [show ∀ (u : Vt), u.csiDispatch
      ({ s' with params := s'.params.push (min s'.cur 65535, s'.curSub) } : CsiState) 0x47
      = u.setCol (n - 1) from by
    intro u
    unfold Vt.csiDispatch
    rw [if_neg (show ¬(({ s' with params := s'.params.push (min s'.cur 65535, s'.curSub) }
      : CsiState)).ignore = true from by
      show ¬(s'.ignore = true)
      rw [show s'.ignore = ({} : CsiState).ignore from by
        have := csi_digits_value n (v := { v with pstate := .csi ({} : CsiState) })
          (s := ({} : CsiState)) rfl rfl
        obtain ⟨s2, hps2, -, -, -, -, hign2, -, -⟩ := this
        have : s' = s2 := PState.csi.inj ((by rw [heq] :
          ((({ v with pstate := .csi ({} : CsiState) } : Vt)).feed (digits n)).pstate
            = PState.csi s').symm.trans hps2)
        rw [this]; exact hign2]
      simp)]
    show u.setCol (({ s' with params := s'.params.push (min s'.cur 65535, s'.curSub) }
      : CsiState).arg 0 1 - 1) = u.setCol (n - 1)
    rw [harg]]
  unfold Vt.setCol
  exact ⟨rfl, rfl, rfl⟩

/-- **`CHA` as a state equation**: feeding it *is* `setCol (n-1)`. `csiFinish` returns to
ground and `setCol` keeps the ground `pstate` a `Matches` receiver already has, so every
non-cursor field frames through `setCol` at once — which is what a `Matches`-across-`CHA`
step needs, rather than one preservation lemma per field. -/
theorem cha_feed_eq {v : Vt} (n : Nat) (hg : v.pstate = .ground) (hu : v.u8need = 0)
    (hn : 0 < n) (hlt : n < 65535) : v.feed (csiNum n 0x47) = v.setCol (n - 1) := by
  rw [show csiNum n 0x47 = [0x1B, 0x5B] ++ (digits n ++ [(0x47 : UInt8)]) from by
    simp [csiNum, csiB]]
  rw [feed_append, keeps_csi_open hg hu]
  obtain ⟨s', heq, hcur', hhave, hpar, hint, hsub⟩ :=
    csi_digits_run_eq n (v := { v with pstate := .csi ({} : CsiState) })
      (s := ({} : CsiState)) rfl (by simpa using hu) rfl
  rw [show ∀ (u : Vt), u.feed (digits n ++ [(0x47 : UInt8)])
      = (u.feed (digits n)).feed [(0x47 : UInt8)] from
    fun u => by simp [Vt.feed, List.foldl_append]]
  rw [heq, show ∀ (u : Vt), u.feed [(0x47 : UInt8)] = u.step 0x47 from fun _ => rfl]
  rw [csi_final_step_eq 0x47 rfl (by simpa using hu) (by rw [hint]) (by decide) (by decide)]
  unfold Vt.csiFinish
  rw [if_pos (by simpa using hhave), if_neg (by rw [hpar]; decide)]
  dsimp only
  have harg : ({ s' with params := s'.params.push (min s'.cur 65535, s'.curSub) }
      : CsiState).arg 0 1 = n := by
    rw [arg_of_one_of 1 (show ({ s' with params := s'.params.push (min s'.cur 65535, s'.curSub) }
        : CsiState).params = (#[] : Array (Nat × Bool)).push (n, s'.curSub) from by
      rw [hpar, hcur', show min (min n 65535) 65535 = n from by omega]),
      if_neg (by omega)]
  rw [show ∀ (u : Vt), u.csiDispatch
      ({ s' with params := s'.params.push (min s'.cur 65535, s'.curSub) } : CsiState) 0x47
      = u.setCol (n - 1) from by
    intro u
    unfold Vt.csiDispatch
    rw [if_neg (show ¬(({ s' with params := s'.params.push (min s'.cur 65535, s'.curSub) }
      : CsiState)).ignore = true from by
      show ¬(s'.ignore = true)
      rw [show s'.ignore = ({} : CsiState).ignore from by
        have := csi_digits_value n (v := { v with pstate := .csi ({} : CsiState) })
          (s := ({} : CsiState)) rfl rfl
        obtain ⟨s2, hps2, -, -, -, -, hign2, -, -⟩ := this
        have : s' = s2 := PState.csi.inj ((by rw [heq] :
          ((({ v with pstate := .csi ({} : CsiState) } : Vt)).feed (digits n)).pstate
            = PState.csi s').symm.trans hps2)
        rw [this]; exact hign2]
      simp)]
    show u.setCol (({ s' with params := s'.params.push (min s'.cur 65535, s'.curSub) }
      : CsiState).arg 0 1 - 1) = u.setCol (n - 1)
    rw [harg]]
  -- the residue is `{ (…).setCol (n-1) with pstate := .ground }`; `setCol` already keeps
  -- the ground pstate the receiver had, so the wrapper is the identity
  show ({ ({ v with pstate := .csi ({} : CsiState) } : Vt).setCol (n - 1) with
    pstate := .ground } : Vt) = v.setCol (n - 1)
  unfold Vt.setCol
  rw [hg]

/-! ## §Replay — the cursor, for any receiver

`restore_cursor` was stated over `Vt.init v.cols v.rows`, and that was an artefact of
when it was written rather than of what it needs: the claim is about the stream's
**final** `CUP`, which addresses absolutely. Three facts about the state `restoreBody`
leaves are what the fresh-emulator form got for free, and each is now available for any
receiver — the parser is ground (the prologue's lead-in), DECOM is off (`modesAnsi`
sets it to the session's value, which the hypothesis says is off), and the dimensions
are unchanged.

`Good w` on the receiver is doing one job: `dims_feed` needs it, because `RIS`
(`ESC c`) rebuilds the state through `Vt.init`, which re-clamps. No linger stream
emits `RIS` — but the painted text certainly contains the byte `0x63`, so
`dims_feed_ne_ris` is too crude here and the invariant is the honest route. Every
client's emulator satisfies it (`good_of_liveReachable`). -/

theorem restoreBody_grounds (v w : Vt) : (w.feed (restoreBody v)).pstate = .ground := by
  rw [show restoreBody v = prologueAnsi v ++ (csiNum 0 0x6D ++ csiNum 2 0x4A
      ++ screensAnsi v ++ regionAnsi v ++ tabsAnsi v ++ savedAnsi v ++ titleAnsi v
      ++ modesAnsi v ++ charsetAnsi v ++ penSgr v.pen) from by
    simp only [restoreBody, List.append_assoc], feed_append]
  exact ((((((((((ends_csiNum 0 0x6D (by decide) (by decide)).append
    (ends_csiNum 2 0x4A (by decide) (by decide))).append (ends_screensAnsi v)).append
    (ends_regionAnsi v)).append (ends_tabsAnsi v)).append (ends_savedAnsi v)).append
    (ends_titleAnsi v)).append (ends_modesAnsi v)).append (ends_charsetAnsi v)).append
    (ends_penSgr v.pen)) _ (prologue_grounds v w)

/-- The modes at the end of `restoreBody` — `restore_modes_any` one chunk earlier, so
the final `CUP` can be told whether DECOM is on before it is read. -/
theorem restoreBody_modes_any (v w : Vt)
    (hmouse : v.modes.mouse = 0 ∨ v.modes.mouse = 1000 ∨ v.modes.mouse = 1002
      ∨ v.modes.mouse = 1003) :
    (w.feed (restoreBody v)).modes = v.modes := by
  have hEndsRest : Ends (csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v
      ++ regionAnsi v ++ tabsAnsi v ++ savedAnsi v) :=
    (((((ends_csiNum 0 0x6D (by decide) (by decide)).append
      (ends_csiNum 2 0x4A (by decide) (by decide))).append
      (ends_screensAnsi v)).append (ends_regionAnsi v)).append (ends_tabsAnsi v)).append
      (ends_savedAnsi v)
  have hg2 : (w.feed (prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v
      ++ regionAnsi v ++ tabsAnsi v ++ savedAnsi v)).pstate = .ground := by
    rw [show prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v
        ++ regionAnsi v ++ tabsAnsi v ++ savedAnsi v
        = prologueAnsi v ++ (csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v
          ++ regionAnsi v ++ tabsAnsi v ++ savedAnsi v) from by simp only [List.append_assoc],
      feed_append]
    exact hEndsRest _ (prologue_grounds v w)
  rw [show restoreBody v = (prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A
      ++ screensAnsi v ++ regionAnsi v ++ tabsAnsi v ++ savedAnsi v)
      ++ (titleAnsi v ++ (modesAnsi v ++ charsetAnsi v ++ penSgr v.pen)) from by
    simp only [restoreBody, List.append_assoc], feed_append, feed_append]
  exact ((((mmap_modesAnsi v hmouse).comp (mmap_id_charsetAnsi v)).comp
    (mmap_id_penSgr v.pen)) _ (ends_titleAnsi v _ hg2) (uz_titleAnsi v hg2)).2.2

/-- **§Replay (cursor), receiver-quantified.** The final `CUP` lands where the session
had it in *any* client's emulator of the session's size, not only a fresh one. -/
theorem restore_cursor_any (v w : Vt) (hgood : Good v) (hgw : Good w)
    (hcols : w.cols = v.cols) (hrows : w.rows = v.rows) (ho : v.modes.origin = false)
    (hmouse : v.modes.mouse = 0 ∨ v.modes.mouse = 1000 ∨ v.modes.mouse = 1002
      ∨ v.modes.mouse = 1003) :
    ((w.feed (restore v)).cursor.x = v.cursor.x)
      ∧ ((w.feed (restore v)).cursor.y = v.cursor.y) := by
  rw [show restore v = restoreBody v ++ cursorAnsi v from rfl, feed_append]
  rw [show cursorAnsi v = csiNum2 (v.cursor.y + 1) (v.cursor.x + 1) 0x48 from by
    simp only [cursorAnsi, ho]; rfl]
  have hpg : (w.feed (restoreBody v)).pstate = .ground := restoreBody_grounds v w
  have hpo : (w.feed (restoreBody v)).modes.origin = false := by
    rw [restoreBody_modes_any v w hmouse]; exact ho
  have hd := dims_feed (restoreBody v) hgw
  have hdc : (w.feed (restoreBody v)).cols = v.cols := by
    rw [← dims_fst (w.feed (restoreBody v)), hd, dims_fst]; exact hcols
  have hdr : (w.feed (restoreBody v)).rows = v.rows := by
    rw [← dims_snd (w.feed (restoreBody v)), hd, dims_snd]; exact hrows
  obtain ⟨hx, hy⟩ := cup_places_cursor (v.cursor.y + 1) (v.cursor.x + 1) hpg
    (by omega) (by omega)
    (by have := hgood.curY; have := hgood.rowsLe; omega)
    (by have := hgood.curX; have := hgood.colsLe; omega)
    (by rw [hdr]; simpa using hgood.curY)
    (by rw [hdc]; simpa using hgood.curX) hpo
  exact ⟨by simpa using hx, by simpa using hy⟩



end Linger.Core.Render
