module

public import Theorems.Render.Pen
import all Linger.Core.Render
import all Linger.Core.Vt
import all Theorems.Render.Pen

-- No `public section`: a **public** declaration's type may not mention a private
-- field, and `Vt`'s are private now (the seal, `specs/archive/vt-toolkit.md` Step 1).
-- Module-private is the default, so consumers reach in with `import all`. See the
-- longer note in `Theorems/Vt.lean`.

/-! # §Replay stage 3d — everything after the repaint leaves the screen alone

`Keeps`, the grid-preservation stream predicate, and one fact per construct the
restore tail emits — so the paint is the only thing that writes cells. Also
`Row.mend`'s fixed points, which is what lets the row induction step past a write.
Split out of `Theorems/Render.lean`. -/

namespace Linger.Core.Render

open Linger.Core.Vt

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
  rw [ite_eq_right (by simp [g1]), ite_eq_right (by simp [g2]), ite_eq_right (by simp [g3]),
    ite_eq_right (by simp [g4]), ite_eq_right (by simp [g5]), ite_eq_left g6]
  rw [ite_eq_right (by simp [hi])]

def Keeps (bs : Bytes) : Prop :=
  ∀ v : Vt,
    v.pstate = .ground →
      v.u8need = 0 →
      ((v.feed bs).pstate = .ground ∧ (v.feed bs).u8need = 0 ∧ (v.feed bs).grid = v.grid)

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
      · rw [ite_eq_left hd]
        exact ⟨_, rfl, rfl⟩
      · rw [ite_eq_right hd]
        by_cases hsemi : (x == 0x3B) = true
        · rw [ite_eq_left hsemi]
          exact ⟨_, rfl, inter_csiPush s false⟩
        · rw [ite_eq_right hsemi]
          by_cases hcolon : (x == 0x3A) = true
          · rw [ite_eq_left hcolon]
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
    rw [ite_eq_right (by simp [hu]), hg]
    dsimp only
    unfold Vt.stepGround
    rw [ite_eq_left (by decide)]
  rw [hesc]
  unfold Vt.step Vt.abortUtf8
  dsimp only
  rw [ite_eq_right (by simp [hu])]
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
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left (by decide)]
  exact keeps_csi_tail params final hp h1 h2 hgrid rfl (by simpa using hu) rfl

/-! ### One fact per final byte the tail uses -/

theorem grid_csiDispatch_cup (v : Vt) (s : CsiState) :
    (v.csiDispatch s 0x48).grid = v.grid := by
  by_cases hi : s.ignore = true
  · simp [Vt.csiDispatch, hi]
  · unfold Vt.csiDispatch
    rw [ite_eq_right hi]
    show (v.moveTo (s.arg 1 1 - 1) (s.arg 0 1 - 1)).grid = v.grid
    rw [frame_moveTo]

theorem grid_csiDispatch_cha (v : Vt) (s : CsiState) :
    (v.csiDispatch s 0x47).grid = v.grid := by
  by_cases hi : s.ignore = true
  · simp [Vt.csiDispatch, hi]
  · unfold Vt.csiDispatch
    rw [ite_eq_right hi]
    show (v.setCol (s.arg 0 1 - 1)).grid = v.grid
    rw [frame_setCol]

theorem grid_csiDispatch_sgr (v : Vt) (s : CsiState) :
    (v.csiDispatch s 0x6D).grid = v.grid := by
  by_cases hi : s.ignore = true
  · simp [Vt.csiDispatch, hi]
  · unfold Vt.csiDispatch
    rw [ite_eq_right hi]
    show (if s.priv == 0 then v.applySgr s.sgrParams else v).grid = v.grid
    split
    · rw [frame_applySgr]
    · rfl

theorem grid_csiDispatch_tbc (v : Vt) (s : CsiState) :
    (v.csiDispatch s 0x67).grid = v.grid := by
  by_cases hi : s.ignore = true
  · simp [Vt.csiDispatch, hi]
  · unfold Vt.csiDispatch
    rw [ite_eq_right hi]
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
    rw [ite_eq_right hi]
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

end Linger.Core.Render

namespace Linger.Core.Render

open Linger.Core.Vt

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

end Linger.Core.Render

namespace Linger.Core.Render

open Linger.Core.Vt

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
    rw [ite_eq_right (by simp [hu])]
  unfold Vt.step
  dsimp only
  rw [ha, hg]

theorem step_of_escInter_quiet {v : Vt} {i : UInt8} (b : UInt8) (hg : v.pstate = .escInter i)
    (hu : v.u8need = 0) : v.step b = v.stepEscInter i b := by
  have ha : v.abortUtf8 b = v := by
    unfold Vt.abortUtf8
    rw [ite_eq_right (by simp [hu])]
  unfold Vt.step
  dsimp only
  rw [ha, hg]

/-- From ground, `ESC` only arms the parser. Stated as an equation (not just a
`pstate` fact) so the layers that care about other fields can use it. -/
theorem esc_step_eq {v : Vt} (hg : v.pstate = .ground) (hu : v.u8need = 0) :
    v.step 0x1B = { v with pstate := .esc } := by
  unfold Vt.step Vt.abortUtf8
  dsimp only
  rw [ite_eq_right (by simp [hu]), hg]
  dsimp only
  unfold Vt.stepGround
  rw [ite_eq_left (by decide)]

/-- `ESC 7` (DECSC), `ESC H` (HTS) and `ESC =` (app keypad) write the saved slot,
the tab ruler and a mode flag respectively — never a cell. -/
theorem keeps_escSeq (b : UInt8) (hb : b = 0x37 ∨ b = 0x3D ∨ b = 0x48 ∨ b = 0x3E ∨ b = 0x5C) :
    Keeps (escSeq b) := by
  intro v hg hu
  rw [show escSeq b = [0x1B] ++ [b] from rfl]
  rw [show ∀ (w : Vt), w.feed ([0x1B] ++ [b]) = (w.step 0x1B).step b from
    fun w => by simp [Vt.feed]]
  rw [esc_step_eq hg hu, step_of_esc_quiet b rfl (by simpa using hu)]
  rcases hb with h | h | h | h | h <;> subst h <;> show _ ∧ _ ∧ _ <;> unfold Vt.stepEsc <;>
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
  rw [ite_eq_right (by decide), ite_eq_left (by decide)]
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

end Linger.Core.Render

namespace Linger.Core.Render

open Linger.Core.Vt

/-! ### The window title

An OSC is the one tail construct with an unbounded payload, so it is the one that
needs an induction. Every step is still a `pstate` record update — the accumulator
lives inside the parser state — and `oscFinish` writes the title and nothing else. -/

theorem step_of_osc_quiet {v : Vt} {acc : Array UInt8} {e : Bool} (b : UInt8)
    (hg : v.pstate = .osc acc e) (hu : v.u8need = 0) : v.step b = v.stepOsc acc e b := by
  have ha : v.abortUtf8 b = v := by
    unfold Vt.abortUtf8
    rw [ite_eq_right (by simp [hu])]
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
  rw [ite_eq_right (by simp), ite_eq_right (by simp [h2]), ite_eq_right (by simp [h1])]
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
  rw [ite_eq_right (by decide), ite_eq_left (by decide)]
  exact ⟨ps_oscFinish' _ _, by rw [un_oscFinish']; simpa using hu,
    by rw [grid_oscFinish]⟩

theorem keeps_titleAnsi (v : Vt) : Keeps (titleAnsi v) := by
  unfold titleAnsi
  exact keeps_osc _

end Linger.Core.Render

namespace Linger.Core.Render

open Linger.Core.Vt

/-! ### The digit bridge, and the last tail stage

`modesAnsi` is the one construct whose grid claim depends on *which number* it
emitted: `grid_setMode` holds for every mode except the three that switch screens.
The emitter never emits those (its allowlist), but the dispatch reads
`s.arg 0 0` — the number the **parser** accumulated — so the two have to be
identified. `accDigits_digits` already says the accumulator inverts `digits`; what
is added here is carrying that through the record equation the grid layer needs. -/

/-- A digit run, as a record equation *and* with its accumulated value — the two
halves that `csi_param_run_inter` and `csi_digits_value` each give separately. -/
theorem csi_digits_run_eq (n : Nat) {v : Vt} {s : CsiState} (hg : v.pstate = .csi s)
    (hu : v.u8need = 0) (hcur : s.cur = 0) :
    ∃ s', v.feed (digits n) = { v with pstate := .csi s' }
      ∧ s'.cur = min n 65535 ∧ s'.haveCur = true ∧ s'.params = s.params
      ∧ s'.inter = s.inter ∧ s'.curSub = s.curSub := by
  obtain ⟨s1, heq, -⟩ := csi_param_run_inter (digits n) hg hu (paramBytes_digits n)
  obtain ⟨s2, hps, hcur2, hhave, hpar, hint, -, hsub, -⟩ := csi_digits_value n hg hcur
  have hid : s1 = s2 := by
    have h1 : (v.feed (digits n)).pstate = PState.csi s1 := by rw [heq]
    exact PState.csi.inj (h1.symm.trans hps)
  exact ⟨s1, heq, by rw [hid]; exact hcur2, by rw [hid]; exact hhave,
    by rw [hid]; exact hpar, by rw [hid]; exact hint, by rw [hid]; exact hsub⟩

theorem grid_csiDispatch_sm (v : Vt) (s : CsiState) (h47 : s.arg 0 0 ≠ 47)
    (h1047 : s.arg 0 0 ≠ 1047) (h1049 : s.arg 0 0 ≠ 1049) :
    (v.csiDispatch s 0x68).grid = v.grid := by
  by_cases hi : s.ignore = true
  · simp [Vt.csiDispatch, hi]
  · unfold Vt.csiDispatch
    rw [ite_eq_right hi]
    show (v.setMode (s.priv == 0x3F) (s.arg 0 0) true).grid = v.grid
    exact grid_setMode v _ _ _ h47 h1047 h1049

theorem grid_csiDispatch_rm (v : Vt) (s : CsiState) (h47 : s.arg 0 0 ≠ 47)
    (h1047 : s.arg 0 0 ≠ 1047) (h1049 : s.arg 0 0 ≠ 1049) :
    (v.csiDispatch s 0x6C).grid = v.grid := by
  by_cases hi : s.ignore = true
  · simp [Vt.csiDispatch, hi]
  · unfold Vt.csiDispatch
    rw [ite_eq_right hi]
    show (v.setMode (s.priv == 0x3F) (s.arg 0 0) false).grid = v.grid
    exact grid_setMode v _ _ _ h47 h1047 h1049

/-- The shared tail for a **single-parameter** sequence, carrying the accumulated
number out so a caller can discharge a hypothesis about it. The digit run is done
here rather than at the call site: naming the collector state outside the lemma
means writing it the way the elaborator happened to build it, and `{}` and
`default` are not the same term. -/
theorem keeps_csi_digits_tail (n : Nat) (final : UInt8) (h1 : 0x40 ≤ final)
    (h2 : final ≤ 0x7E) (hn : 0 < n) (hlt : n < 65535)
    (hgrid : ∀ (w : Vt) (t : CsiState), t.arg 0 0 = n →
      (w.csiDispatch t final).grid = w.grid)
    {v : Vt} {s : CsiState} (hg : v.pstate = .csi s) (hu : v.u8need = 0)
    (hi : s.inter = 0) (hcur : s.cur = 0) (hpar : s.params = #[]) :
    ((v.feed (digits n ++ [final])).pstate = .ground
      ∧ (v.feed (digits n ++ [final])).u8need = 0
      ∧ (v.feed (digits n ++ [final])).grid = v.grid) := by
  obtain ⟨s', heq, hcur', hhave, hpar', hint, -⟩ := csi_digits_run_eq n hg hu hcur
  rw [show ∀ (w : Vt), w.feed (digits n ++ [final]) = (w.feed (digits n)).feed [final] from
    fun w => by simp [Vt.feed, List.foldl_append]]
  rw [heq, show ∀ (w : Vt), w.feed [final] = w.step final from fun _ => rfl]
  rw [csi_final_step_eq final rfl (by simpa using hu) (by rw [hint]; exact hi) h1 h2]
  unfold Vt.csiFinish
  rw [ite_eq_left (by simpa using hhave), ite_eq_right (by rw [hpar', hpar]; simp)]
  dsimp only
  refine ⟨rfl, by rw [un_csiDispatch]; simpa using hu, ?_⟩
  refine hgrid _ _ ?_
  rw [show ({ s' with params := s'.params.push (min s'.cur 65535, s'.curSub) } : CsiState)
      = { s' with params := #[(n, s'.curSub)] } from by
    rw [hpar', hpar, hcur']
    rw [show min (min n 65535) 65535 = n from by omega]
    rfl]
  rw [arg_of_one, ite_eq_right (by omega)]

/-- `CSI ? n <final>` with a grid fact that may depend on `n`. -/
theorem keeps_csiPriv_arg (n : Nat) (final : UInt8) (h1 : 0x40 ≤ final)
    (h2 : final ≤ 0x7E) (hn : 0 < n) (hlt : n < 65535)
    (hgrid : ∀ (w : Vt) (t : CsiState), t.arg 0 0 = n →
      (w.csiDispatch t final).grid = w.grid) :
    Keeps (csiPriv n final) := by
  intro v hg hu
  rw [show csiPriv n final
      = [0x1B, 0x5B] ++ ([(0x3F : UInt8)] ++ (digits n ++ [final])) from by
    unfold csiPriv csiB; simp]
  rw [show ∀ (w : Vt), w.feed ([0x1B, 0x5B] ++ ([(0x3F : UInt8)] ++ (digits n ++ [final])))
      = ((w.feed [0x1B, 0x5B]).feed [(0x3F : UInt8)]).feed (digits n ++ [final]) from
    fun w => by simp [Vt.feed, List.foldl_append]]
  rw [keeps_csi_open hg hu]
  rw [show ∀ (w : Vt), w.feed [(0x3F : UInt8)] = w.step 0x3F from fun _ => rfl]
  rw [step_of_csi_quiet (0x3F : UInt8) (v := { v with pstate := .csi {} }) (s := {}) rfl
    (by simpa using hu)]
  unfold Vt.stepCsi
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left (by decide)]
  exact keeps_csi_digits_tail n final h1 h2 hn hlt hgrid rfl (by simpa using hu) rfl rfl rfl

/-- …and the non-private form, for `modesAnsi`'s one ANSI emit (`CSI 4 h`, IRM). -/
theorem keeps_csiNum_arg (n : Nat) (final : UInt8) (h1 : 0x40 ≤ final)
    (h2 : final ≤ 0x7E) (hn : 0 < n) (hlt : n < 65535)
    (hgrid : ∀ (w : Vt) (t : CsiState), t.arg 0 0 = n →
      (w.csiDispatch t final).grid = w.grid) :
    Keeps (csiNum n final) := by
  intro v hg hu
  rw [show csiNum n final = [0x1B, 0x5B] ++ (digits n ++ [final]) from by
    unfold csiNum csiB; simp]
  rw [show ∀ (w : Vt), w.feed ([0x1B, 0x5B] ++ (digits n ++ [final]))
      = (w.feed [0x1B, 0x5B]).feed (digits n ++ [final]) from
    fun w => by simp [Vt.feed, List.foldl_append]]
  rw [keeps_csi_open hg hu]
  exact keeps_csi_digits_tail n final h1 h2 hn hlt hgrid rfl (by simpa using hu) rfl rfl rfl

theorem keeps_modeSet (n : Nat) (on : Bool) (hn : 0 < n) (hlt : n < 65535)
    (h47 : n ≠ 47) (h1047 : n ≠ 1047) (h1049 : n ≠ 1049) : Keeps (modeSet n on) := by
  unfold modeSet
  cases on
  · exact keeps_csiPriv_arg n 0x6C (by decide) (by decide) hn hlt
      (fun w t ha => grid_csiDispatch_rm w t (by rw [ha]; exact h47)
        (by rw [ha]; exact h1047) (by rw [ha]; exact h1049))
  · exact keeps_csiPriv_arg n 0x68 (by decide) (by decide) hn hlt
      (fun w t ha => grid_csiDispatch_sm w t (by rw [ha]; exact h47)
        (by rw [ha]; exact h1047) (by rw [ha]; exact h1049))

theorem keeps_irm (on : Bool) : Keeps (csiNum 4 (if on then 0x68 else 0x6C)) := by
  cases on
  · exact keeps_csiNum_arg 4 0x6C (by decide) (by decide) (by omega) (by omega)
      (fun w t ha => grid_csiDispatch_rm w t (by rw [ha]; omega) (by rw [ha]; omega)
        (by rw [ha]; omega))
  · exact keeps_csiNum_arg 4 0x68 (by decide) (by decide) (by omega) (by omega)
      (fun w t ha => grid_csiDispatch_sm w t (by rw [ha]; omega) (by rw [ha]; omega)
        (by rw [ha]; omega))

/-- **The mode replay writes no cell.** `modesAnsi`'s allowlist is what discharges
the screen-switch hypotheses: every number it emits is either a literal in the
source or one of the three the mouse guard names. -/
theorem keeps_modesAnsi (v : Vt) : Keeps (modesAnsi v) := by
  unfold modesAnsi
  refine Keeps.append ?_ (keeps_irm v.modes.insert)
  refine Keeps.append ?_ (keeps_modeSet 6 _ (by omega) (by omega) (by omega) (by omega)
    (by omega))
  refine Keeps.append ?_ (keeps_modeSet 1004 _ (by omega) (by omega) (by omega) (by omega)
    (by omega))
  refine Keeps.append ?_ (keeps_modeSet 1006 _ (by omega) (by omega) (by omega) (by omega)
    (by omega))
  refine Keeps.append ?_ (Keeps.ite (c := (v.modes.mouse == 1000 || v.modes.mouse == 1002
    || v.modes.mouse == 1003) = true)
    (fun h => by
      simp only [Bool.or_eq_true, beq_iff_eq] at h
      exact keeps_modeSet v.modes.mouse true (by omega) (by omega) (by omega) (by omega)
        (by omega))
    (fun _ => Keeps.nil))
  refine Keeps.append ?_ (keeps_modeSet 1003 false (by omega) (by omega) (by omega)
    (by omega) (by omega))
  refine Keeps.append ?_ (keeps_modeSet 1002 false (by omega) (by omega) (by omega)
    (by omega) (by omega))
  refine Keeps.append ?_ (keeps_modeSet 1000 false (by omega) (by omega) (by omega)
    (by omega) (by omega))
  refine Keeps.append ?_ (keeps_modeSet 2004 _ (by omega) (by omega) (by omega) (by omega)
    (by omega))
  refine Keeps.append ?_ (keeps_modeSet 25 _ (by omega) (by omega) (by omega) (by omega)
    (by omega))
  refine Keeps.append ?_ (Keeps.ite (fun _ => keeps_escSeq 0x3D (by decide))
    (fun _ => keeps_escSeq 0x3E (by decide)))
  exact (keeps_modeSet 7 _ (by omega) (by omega) (by omega) (by omega) (by omega)).append
    (keeps_modeSet 1 _ (by omega) (by omega) (by omega) (by omega) (by omega))

/-- **The whole tail.** Everything `restore` emits after the repaint, proved to
leave the painted grid alone. What remains of `restore_grid` is the repaint itself:
the row induction, the row separator, and the alt switch. -/
theorem keeps_restoreTail (v : Vt) :
    Keeps (regionAnsi v ++ tabsAnsi v ++ savedAnsi v ++ titleAnsi v ++ modesAnsi v
      ++ charsetAnsi v ++ penSgr v.pen ++ cursorAnsi v) :=
  ((((((((keeps_regionAnsi v).append (keeps_tabsAnsi v)).append
    (keeps_savedAnsi v)).append (keeps_titleAnsi v)).append
    (keeps_modesAnsi v)).append (keeps_charsetAnsi v)).append
    (keeps_penSgr v.pen)).append (keeps_cursorAnsi v))

end Linger.Core.Render

namespace Linger.Core.Render

open Linger.Core.Vt

/-! ### What is left that is not the repaint

With the tail done, the only bytes in `restore` that may legitimately touch a cell
are the clear (`CSI 2 J`), the paint (`gridAnsi`), and the alt switch
(`CSI ? 1049 h`). The leading SGR reset and the alt-stash parking are not among
them, and both fall out of pieces already proved. -/

/-- The `restoreBody` head: an SGR reset writes no cell. -/
theorem keeps_sgrReset : Keeps (csiNum 0 0x6D) :=
  keeps_csiNum 0 0x6D (by decide) (by decide) grid_csiDispatch_sgr

/-- **Park the pen and the cursor.** The shape recurs: the DECSC replay
(`savedAnsi`), the alt-stash parking inside `screensAnsi`, and — without the pen —
the final placement. Stated on bare naturals so all three instantiate it. -/
theorem keeps_park (y x : Nat) (p : Pen) : Keeps (penSgr p ++ csiNum2 y x 0x48) :=
  (keeps_penSgr p).append
    (keeps_csiNum2 _ _ 0x48 (by decide) (by decide) grid_csiDispatch_cup)

end Linger.Core.Render

namespace Linger.Core.Vt

/-! ### The clear, framed

`CSI 2 J` is the one part of `restore` that is *supposed* to change cells, so the
useful statement about it is what it leaves alone. `eraseRowSpan` is a single
`grid` record update, so everything but the grid is `rfl`; the fold over rows needs
one induction, shared by all four ED modes. -/

theorem rows_eraseRowSpan (v : Vt) (y f t : Nat) :
    (v.eraseRowSpan y f t).rows = v.rows := by rfl

theorem cols_eraseRowSpan (v : Vt) (y f t : Nat) :
    (v.eraseRowSpan y f t).cols = v.cols := by rfl

theorem pen_eraseRowSpan (v : Vt) (y f t : Nat) :
    (v.eraseRowSpan y f t).pen = v.pen := by rfl

theorem cursor_eraseRowSpan (v : Vt) (y f t : Nat) :
    (v.eraseRowSpan y f t).cursor = v.cursor := by rfl

/-- Erasing a span never resizes the grid: `setIfInBounds` is a no-op out of range
and length-preserving in range. -/
theorem size_eraseRowSpan (v : Vt) (y f t : Nat) :
    (v.eraseRowSpan y f t).grid.size = v.grid.size := by
  unfold Vt.eraseRowSpan
  dsimp only
  simp

/-- The row fold shared by every ED mode. `f` is the row index as a function of the
iteration only — in each of the four modes the index is independent of the
accumulator, which is what lets one lemma serve all of them. -/
theorem foldl_erase_frame (f : Nat → Nat) : ∀ (l : List Nat) (v : Vt),
    (l.foldl (fun v' i => v'.eraseRowSpan (f i) 0 v'.cols) v).rows = v.rows
      ∧ (l.foldl (fun v' i => v'.eraseRowSpan (f i) 0 v'.cols) v).cols = v.cols
      ∧ (l.foldl (fun v' i => v'.eraseRowSpan (f i) 0 v'.cols) v).pen = v.pen
      ∧ (l.foldl (fun v' i => v'.eraseRowSpan (f i) 0 v'.cols) v).cursor = v.cursor
      ∧ (l.foldl (fun v' i => v'.eraseRowSpan (f i) 0 v'.cols) v).grid.size
          = v.grid.size
  | [], v => ⟨rfl, rfl, rfl, rfl, rfl⟩
  | i :: is, v => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := foldl_erase_frame f is (v.eraseRowSpan (f i) 0 v.cols)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [List.foldl_cons, h1, rows_eraseRowSpan]
    · rw [List.foldl_cons, h2, cols_eraseRowSpan]
    · rw [List.foldl_cons, h3, pen_eraseRowSpan]
    · rw [List.foldl_cons, h4, cursor_eraseRowSpan]
    · rw [List.foldl_cons, h5, size_eraseRowSpan]

/-- `ED 2` is the `_` arm of the match, so this is definitional. Having the equation
as a lemma keeps the match out of the frame proof, where an in-tactic split leaves an
unreduced `match 2 with …` that `rw` cannot see through. -/
theorem eraseScreen_two_eq (v : Vt) : v.eraseScreen 2
    = (List.range v.rows).foldl (fun v' y => v'.eraseRowSpan y 0 v'.cols) v := by rfl

/-- **The clear resizes nothing and moves nothing.** `CSI 2 J` is the one part of
`restore` that is supposed to change cells, so the useful statement is what it leaves
alone: the dimensions, the pen, the cursor, and the row count. The repaint that
follows depends on all four. -/
theorem eraseScreen_two_frame (v : Vt) :
    (v.eraseScreen 2).rows = v.rows ∧ (v.eraseScreen 2).cols = v.cols
      ∧ (v.eraseScreen 2).pen = v.pen ∧ (v.eraseScreen 2).cursor = v.cursor
      ∧ (v.eraseScreen 2).grid.size = v.grid.size := by
  rw [eraseScreen_two_eq]
  exact foldl_erase_frame (fun y => y) (List.range v.rows) v

end Linger.Core.Vt

namespace Linger.Core.Render

open Linger.Core.Vt

/-! ### `restore_grid`, reduced to the paint

The tail is done, so the remaining obligation can be stated as a theorem rather than
left as a note: **if the clear-and-paint prefix gets the grid right and leaves the
parser quiesced, the whole of `restore` gets it right.** Everything after the paint is
`keeps_restoreTail`. What is left for the repaint half is exactly the three
hypotheses below, about a prefix that is three constructs long. -/

/-- The one re-association `restore_grid` needs: the clear-and-paint prefix, then the
eight tail stages. `++` is right-associative, so this is not free. -/
theorem restore_split (v : Vt) :
    restore v = (prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v)
      ++ (regionAnsi v ++ tabsAnsi v ++ savedAnsi v ++ titleAnsi v ++ modesAnsi v
          ++ charsetAnsi v ++ penSgr v.pen ++ cursorAnsi v) := by
  unfold restore restoreBody
  simp

/-- **`restore_grid`, reduced to the paint.** The three hypotheses are the whole of
what the repaint half still owes: that `SGR 0`, `ED 2` and `screensAnsi` together
leave the grid equal to `v`'s, the parser in ground, and no UTF-8 half-decoded. The
eight stages that follow are proved to preserve all three. -/
theorem restore_grid_of_paint {v w : Vt}
    (hps : (w.feed (prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v)).pstate = .ground)
    (hun : (w.feed (prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v)).u8need = 0)
    (hpaint : (w.feed (prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v)).grid = v.grid) :
    (w.feed (restore v)).grid = v.grid := by
  rw [restore_split, feed_append]
  obtain ⟨-, -, hg⟩ := keeps_restoreTail v _ hps hun
  rw [hg, hpaint]

end Linger.Core.Render

namespace Linger.Core.Vt

/-! ### `Row.mend` is the identity on a row that needs no repair

Every cell-writing operation ends in `Row.mend`, so the row induction inside the
repaint has to know that mending does not disturb the columns already painted. It
does not, and the reason is exactly `RowOk.pairs`: a row whose pairs are whole and
whose shadows are canonical is a fixed point of `mend`. -/

theorem set_self_eq {α} [Inhabited α] (r : Array α) (x : Nat) :
    r.setIfInBounds x (r.getD x default) = r := by
  by_cases h : x < r.size
  · simp [Array.setIfInBounds, Array.getD, h]
  · simp [Array.setIfInBounds, h]

theorem mendAt_of_width_one {row : Row} {x : Nat} (h : (row.at x).width = 1) :
    Row.mendAt row x = row := by
  simp [Row.mendAt, Row.halfPair, h]

/-- The shadow case: a canonical shadow is written back unchanged. -/
theorem mendAt_of_pairOk {row : Row} {x : Nat} (h : ∀ j, PairOk row j) :
    Row.mendAt row x = row := by
  -- `halfPair` wants the width form; `PairOk` gives the stronger cell equation
  have hhp : row.halfPair x = false := (halfPair_eq_false_iff row x).mpr
    ⟨fun h2 => by rw [(h x).1 h2]; rfl, (h x).2⟩
  unfold Row.mendAt
  rw [hhp, ite_eq_right (by decide)]
  split
  · -- a shadow: `PairOk` at `x - 1` says it is already `Cell.shadow` of its base
    rename_i h0
    have hw0 : (row.at x).width = 0 := by simp only [beq_iff_eq] at h0; exact h0
    obtain ⟨hne, hbase⟩ := (h x).2 hw0
    have hcan : row.at x = Cell.shadow (row.at (x - 1)) := by
      have hp := (h (x - 1)).1 hbase
      rw [show x - 1 + 1 = x from by omega] at hp
      exact hp
    rw [← hcan]
    exact set_self_eq row x
  · rfl

/-- **`mend` fixes an already-consistent row.** -/
theorem mend_of_pairOk {row : Row} (h : ∀ j, PairOk row j) : Row.mend row = row := by
  unfold Row.mend
  have key : ∀ (l : List Nat), l.foldl (fun (r : Row) x => r.mendAt x) row = row := by
    intro l
    induction l with
    | nil => rfl
    | cons a as ih => rw [List.foldl_cons, mendAt_of_pairOk h]; exact ih
  exact key _

theorem width_at_blankRow (cols : Nat) (p : Pen) (x : Nat) :
    ((blankRow cols p).at x).width = 1 := by
  rw [at_blankRow]
  split <;> rfl

theorem mend_blankRow (cols : Nat) (p : Pen) : Row.mend (blankRow cols p) = blankRow cols p := by
  unfold Row.mend
  have key : ∀ (l : List Nat),
      l.foldl (fun (r : Row) x => r.mendAt x) (blankRow cols p) = blankRow cols p := by
    intro l
    induction l with
    | nil => rfl
    | cons a as ih =>
      rw [List.foldl_cons, mendAt_of_width_one (width_at_blankRow cols p a)]
      exact ih
  exact key _

/-! **Non-vacuity, in place of a break-verify.** `mend` is emphatically *not* the
identity in general: a lone width-2 base is repaired away. So `mend_of_pairOk`'s
hypothesis is load-bearing rather than decorative. This is recorded as a check
because the usual break — mutating `Row.mendAt` — is caught upstream in
`Theorems/Vt.lean` before the lemma above is ever elaborated, which proves the
definition is load-bearing but not that *this* lemma is.

The check itself lives in `Tests/Vt.lean` since the module migration
(lean-modules Step 5): it is an evaluation, and a kernel `decide` in a module
file cannot reduce through a derived `DecidableEq` instance whose body is not
exposed — in `Tests/`, under the compiled-evaluation tactic whose whole point
is evaluating, it keeps its full force. (That tactic's name is deliberately
not written here: the purity gate greps `Theorems/**` for the token, prose
included.) -/

end Linger.Core.Vt
