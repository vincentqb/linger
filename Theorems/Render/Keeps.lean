module

import all Linger.Core.Render
import all Linger.Core.Vt
import all Theorems.Render.Pen

-- Module-private by default: `Vt`'s fields are sealed (see `Theorems/Vt/State.lean`).

/-! # §Replay stage 3d — everything after the repaint leaves the screen alone

`Keeps`, the grid-preservation stream predicate, and one fact per construct the
restore tail emits — so the paint is the only thing that writes cells. Split out
of `Theorems/Render.lean`. -/

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

/-- **A projection blind to the parser state.** Every field accessor but `pstate`
is one, by `rfl`. It is the one thing the CSI walk needs of a projection, because
the walk to the final byte is a chain of `pstate` updates and nothing else. -/
def PsBlind {α : Type} (π : Vt → α) : Prop :=
  ∀ (v : Vt) (p : PState), π { v with pstate := p } = π v

/-! ## Stream preservation for any projection -/

def Fixes {α : Type} (π : Vt → α) (bs : Bytes) : Prop :=
  ∀ v : Vt,
    v.pstate = .ground →
      v.u8need = 0 → ((v.feed bs).pstate = .ground ∧ (v.feed bs).u8need = 0 ∧ π (v.feed bs) = π v)

theorem Fixes.nil {α : Type} (π : Vt → α) : Fixes π [] := fun _ hg hu => ⟨hg, hu, rfl⟩

theorem Fixes.append {α : Type} {π : Vt → α} {a b : Bytes} (ha : Fixes π a) (hb : Fixes π b) :
    Fixes π (a ++ b) := by
  intro v hg hu
  rw [feed_append]
  obtain ⟨h1, h2, h3⟩ := ha v hg hu
  obtain ⟨h4, h5, h6⟩ := hb _ h1 h2
  exact ⟨h4, h5, h6.trans h3⟩

theorem Fixes.streamPred {α : Type} (π : Vt → α) : StreamPred (Fixes π) :=
  ⟨Fixes.nil π, fun ha hb => Fixes.append ha hb⟩

def Keeps (bs : Bytes) : Prop := Fixes (fun v : Vt => v.grid) bs

theorem psBlind_grid : PsBlind (fun v : Vt => v.grid) := fun _ _ => rfl

theorem Keeps.nil : Keeps [] := fun _ hg hu => ⟨hg, hu, rfl⟩

theorem Keeps.append {a b : Bytes} (ha : Keeps a) (hb : Keeps b) : Keeps (a ++ b) :=
  Fixes.append ha hb

theorem Keeps.streamPred : StreamPred Keeps := ⟨Keeps.nil, fun ha hb => Keeps.append ha hb⟩

/-- Both branches, with the condition available — `modesAnsi`'s screen-switch
guard is what will discharge `grid_setMode`'s hypotheses. -/
theorem Keeps.ite {c : Prop} [Decidable c] {a b : Bytes}
    (ha : c → Keeps a) (hb : ¬c → Keeps b) : Keeps (if c then a else b) :=
  Keeps.streamPred.ite ha hb

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
  | [], v, s, hg, _, _ => ⟨s, by rw [feed_nil, ← hg], rfl⟩
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
            grind
    obtain ⟨t, hxs, hti⟩ := hstep
    rw [feed_cons, hxs]
    obtain ⟨s', hs', hsi⟩ := csi_param_run_inter xs (v := { v with pstate := .csi t })
      (s := t) rfl hu (fun b hb => hp b (by simp [hb]))
    exact ⟨s', by rw [hs'], hsi.trans hti⟩

/-- From ground, `ESC [` lands in a fresh collector with nothing else touched. -/
theorem keeps_csi_open {v : Vt} (hg : v.pstate = .ground) (hu : v.u8need = 0) :
    v.feed [0x1B, 0x5B] = { v with pstate := .csi {} } := csi_open_feed hg hu

/-- `ESC [ ?` opens a private CSI: the full state equation, not just the parser state. -/
theorem csi_priv_open_eq {v : Vt} (hg : v.pstate = .ground) (hu : v.u8need = 0) :
    v.feed [0x1B, 0x5B, 0x3F] = { v with pstate := .csi ({ priv := 0x3F } : CsiState) } := by
  rw [show v.feed [(0x1B : UInt8), 0x5B, 0x3F] = (v.feed [0x1B, 0x5B]).step 0x3F from by
      simp [Vt.feed],
    keeps_csi_open hg hu]
  unfold Vt.step Vt.abortUtf8
  dsimp only
  rw [ite_eq_right (by simp [hu])]
  show
    (({ v with pstate := .csi ({} : CsiState) } : Vt).stepCsi ({} : CsiState) 0x3F) =
      { v with pstate := .csi ({ priv := 0x3F } : CsiState) }
  unfold Vt.stepCsi
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
    ite_eq_left (by decide)]

/-- A parameter run and a final byte whose dispatch preserves `π` return to
ground with no pending UTF-8 and leave `π` unchanged. -/
theorem csi_tail_proj {α : Type} {π : Vt → α} (hb : PsBlind π) (params : Bytes) (final : UInt8)
    (hp : ParamBytes params) (h1 : 0x40 ≤ final) (h2 : final ≤ 0x7E)
    (hπ : ∀ (w : Vt) (t : CsiState), π (w.csiDispatch t final) = π w) {v : Vt} {s : CsiState}
    (hg : v.pstate = .csi s) (hu : v.u8need = 0) (hi : s.inter = 0) :
    π (v.feed (params ++ [final])) = π v ∧
      (v.feed (params ++ [final])).pstate = .ground ∧ (v.feed (params ++ [final])).u8need = 0 := by
  obtain ⟨s', hs', hsi⟩ := csi_param_run_inter params hg hu hp
  rw [feed_append]
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

/-- The CSI walk, for any projection: `csi_tail_proj` does the work, this adds the
`ESC [` opener. -/
theorem fixes_csi_seq {α : Type} {π : Vt → α} (hb : PsBlind π) (params : Bytes) (final : UInt8)
    (hp : ParamBytes params) (h1 : 0x40 ≤ final) (h2 : final ≤ 0x7E)
    (hπ : ∀ (w : Vt) (t : CsiState), π (w.csiDispatch t final) = π w) :
    Fixes π (csiB ++ params ++ [final]) := by
  intro v hg hu
  rw [show (csiB ++ params ++ [final] : Bytes) = [0x1B, 0x5B] ++ (params ++ [final]) from by
      unfold csiB; simp]
  rw [feed_append]
  rw [keeps_csi_open hg hu]
  obtain ⟨hπ', hp', hu'⟩ :=
    csi_tail_proj hb params final hp h1 h2 hπ (v := { v with pstate := .csi {} }) rfl
      (by simpa using hu) rfl
  exact ⟨hp', hu', by rw [hπ', hb v (PState.csi {})]⟩

/-- The private form (`CSI ? n h/l`), which is what a mode replay is made of. -/
theorem fixes_csi_priv_seq {α : Type} {π : Vt → α} (hb : PsBlind π) (params : Bytes) (final : UInt8)
    (hp : ParamBytes params) (h1 : 0x40 ≤ final) (h2 : final ≤ 0x7E)
    (hπ : ∀ (w : Vt) (t : CsiState), π (w.csiDispatch t final) = π w) :
    Fixes π (csiB ++ ([0x3F] ++ params) ++ [final]) := by
  intro v hg hu
  rw [show
      (csiB ++ ([0x3F] ++ params) ++ [final] : Bytes) = [0x1B, 0x5B, 0x3F] ++ (params ++ [final])
      from by
      unfold csiB; simp]
  rw [feed_append]
  rw [csi_priv_open_eq hg hu]
  obtain ⟨hπ', hp', hu'⟩ :=
    csi_tail_proj hb params final hp h1 h2 hπ (v :=
      { v with pstate := .csi ({ priv := 0x3F } : CsiState) }) rfl (by simpa using hu) rfl
  exact ⟨hp', hu', by rw [hπ', hb v (PState.csi ({ priv := 0x3F } : CsiState))]⟩

theorem fixes_csiNum {α : Type} {π : Vt → α} (hb : PsBlind π) (n : Nat) (final : UInt8)
    (h1 : 0x40 ≤ final) (h2 : final ≤ 0x7E)
    (hπ : ∀ (w : Vt) (t : CsiState), π (w.csiDispatch t final) = π w) :
    Fixes π (csiNum n final) := fixes_csi_seq hb _ _ (paramBytes_digits n) h1 h2 hπ

theorem fixes_csiNum2 {α : Type} {π : Vt → α} (hb : PsBlind π) (a b : Nat) (final : UInt8)
    (h1 : 0x40 ≤ final) (h2 : final ≤ 0x7E)
    (hπ : ∀ (w : Vt) (t : CsiState), π (w.csiDispatch t final) = π w) :
    Fixes π (csiNum2 a b final) := by
  rw [show csiNum2 a b final = csiB ++ (digits a ++ [0x3B] ++ digits b) ++ [final] from by
      unfold csiNum2; simp]
  exact fixes_csi_seq hb _ _ (paramBytes_digits2 a b) h1 h2 hπ

theorem fixes_csiPriv {α : Type} {π : Vt → α} (hb : PsBlind π) (n : Nat) (final : UInt8)
    (h1 : 0x40 ≤ final) (h2 : final ≤ 0x7E)
    (hπ : ∀ (w : Vt) (t : CsiState), π (w.csiDispatch t final) = π w) :
    Fixes π (csiPriv n final) := by
  rw [show csiPriv n final = csiB ++ ([0x3F] ++ digits n) ++ [final] from by
      unfold csiPriv; simp]
  exact fixes_csi_priv_seq hb _ _ (paramBytes_digits n) h1 h2 hπ

theorem fixes_sgrOf {α : Type} {π : Vt → α} (hb : PsBlind π) (codes : List Nat)
    (hπ : ∀ (w : Vt) (t : CsiState), π (w.csiDispatch t 0x6D) = π w) : Fixes π (sgrOf codes) := by
  unfold sgrOf
  exact fixes_csi_seq hb _ _ (paramBytes_joinSemi codes) (by decide) (by decide) hπ

theorem fixes_sgrColorSeq {α : Type} {π : Vt → α} (hb : PsBlind π) (c : Color) (isFg : Bool)
    (hπ : ∀ (w : Vt) (t : CsiState), π (w.csiDispatch t 0x6D) = π w) :
    Fixes π (sgrColorSeq c isFg) := by
  unfold sgrColorSeq
  split
  · exact Fixes.nil π
  · exact fixes_sgrOf hb _ hπ

theorem fixes_penSgr {α : Type} {π : Vt → α} (hb : PsBlind π) (p : Pen)
    (hπ : ∀ (w : Vt) (t : CsiState), π (w.csiDispatch t 0x6D) = π w) : Fixes π (penSgr p) := by
  unfold penSgr
  exact
    ((fixes_sgrOf hb _ hπ).append (fixes_sgrColorSeq hb _ _ hπ)).append
      (fixes_sgrColorSeq hb _ _ hπ)

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
    show (if s.priv == 0 then v.applySgr s.params.toList else v).grid = v.grid
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
    all_goals rfl

/-! ### The CSI-shaped constructs in the tail -/

theorem keeps_csiNum (n : Nat) (final : UInt8) (h1 : 0x40 ≤ final) (h2 : final ≤ 0x7E)
    (hgrid : ∀ (w : Vt) (t : CsiState), (w.csiDispatch t final).grid = w.grid) :
    Keeps (csiNum n final) := fixes_csiNum psBlind_grid n final h1 h2 hgrid

theorem keeps_csiNum2 (a b : Nat) (final : UInt8) (h1 : 0x40 ≤ final) (h2 : final ≤ 0x7E)
    (hgrid : ∀ (w : Vt) (t : CsiState), (w.csiDispatch t final).grid = w.grid) :
    Keeps (csiNum2 a b final) := fixes_csiNum2 psBlind_grid a b final h1 h2 hgrid

/-! ### The SGR pen, and the one mode fact the replay turns on -/

/-- **An SGR pen writes no cell**, for any pen — 16-colour, 256-colour or
truecolour, and however `penSgr` splits it across sequences. This is the piece
`savedAnsi` and `restoreBody`'s trailing pen both rest on. -/
theorem keeps_penSgr (p : Pen) : Keeps (penSgr p) := fixes_penSgr psBlind_grid p grid_csiDispatch_sgr

/-- **A mode set writes no cell — unless it switches screens.** `47`, `1047` and
`1049` swap the grid for the alternate one, and nothing else in `setMode` touches
a cell. `modesAnsi` never emits those three, which is the same guarded-emit
argument `quiet_modesAnsi` makes for DECOM (mode 6): the emitter is what keeps the
claim true, so the hypothesis is discharged where the bytes are chosen rather than
assumed about the parser. -/
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

/-- Every requested mode must preserve the grid; a later screen switch matters
just as much as the first parameter. -/
theorem grid_setModes (v : Vt) (priv : Bool) (ps : List (Nat × Bool)) (on : Bool)
    (h : ∀ p ∈ ps, p.1 ≠ 47 ∧ p.1 ≠ 1047 ∧ p.1 ≠ 1049) :
    (v.setModes priv ps on).grid = v.grid :=
  setModes_invariant (fun w => w.grid = v.grid) priv on ps
    (fun w p hp hw =>
      (grid_setMode w priv p.1 on (h p hp).1 (h p hp).2.1 (h p hp).2.2).trans hw) v rfl

/-! ### The non-CSI tail

`ESC`-singles (DECSC, HTS, app-keypad), charset designations and the shift-out
byte. Each is a two- or three-byte walk, and at each step the grid is untouched
because every branch `stepEsc`/`stepEscInter`/`ctl` takes for these bytes is a
record update on some *other* field — the saved slot, the tab ruler, a mode flag,
the charset flags, `shiftOut`. -/

theorem step_of_esc_quiet {v : Vt} (b : UInt8) (hg : v.pstate = .esc) (hu : v.u8need = 0) :
    v.step b = v.stepEsc b := by
  rw [step_of_esc b hg, abortUtf8_of_uz b hu]

theorem step_of_escInter_quiet {v : Vt} {i : UInt8} (b : UInt8) (hg : v.pstate = .escInter i)
    (hu : v.u8need = 0) : v.step b = v.stepEscInter i b := by
  rw [step_of_escInter b hg, abortUtf8_of_uz b hu]

/-- `ESC 7` (DECSC), `ESC H` (HTS), `ESC =`/`ESC >` (keypad modes) and `ESC \` (ST)
write the saved slot, the tab ruler, a mode flag or nothing — never a cell. -/
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
theorem keeps_escCharset (i x : UInt8) (hi : i = 0x28 ∨ i = 0x29)
    (hlo : 0x30 ≤ x) (hhi : x ≤ 0x7E) :
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
  rw [stepEscInter_final _ i x hlo hhi]
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
  refine ((Keeps.ite (fun _ => keeps_escCharset 0x28 0x30 (by decide) (by decide) (by decide))
    (fun _ => keeps_escCharset 0x28 0x42 (by decide) (by decide) (by decide))).append
    (Keeps.ite (fun _ => keeps_escCharset 0x29 0x30 (by decide) (by decide) (by decide))
      (fun _ => keeps_escCharset 0x29 0x42 (by decide) (by decide) (by decide)))).append ?_
  exact Keeps.ite (fun _ => keeps_shiftOut) (fun _ => Keeps.nil)

/-! ### The window title

An OSC is the one tail construct with an unbounded payload, so it is the one that
needs an induction. Every step is still a `pstate` record update — the accumulator
lives inside the parser state — and `oscFinish` writes the title and nothing else. -/

theorem step_of_osc_quiet {v : Vt} {acc : Array UInt8} {e : Bool} (b : UInt8)
    (hg : v.pstate = .osc acc e) (hu : v.u8need = 0) : v.step b = v.stepOsc acc e b := by
  rw [step_of_osc b hg, abortUtf8_of_uz b hu]

theorem grid_oscFinish (v : Vt) (acc : Array UInt8) : (v.oscFinish acc).grid = v.grid := by
  unfold Vt.oscFinish
  dsimp only
  repeat' split
  all_goals rfl

theorem ps_oscFinish (v : Vt) (acc : Array UInt8) : (v.oscFinish acc).pstate = .ground := by
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
  | [], v, acc, hg, _, _ => ⟨acc, by rw [feed_nil, ← hg]⟩
  | x :: xs, v, acc, hg, hu, h => by
    obtain ⟨acc1, hx⟩ := osc_accum_eq x hg hu (h x (by simp)).1 (h x (by simp)).2
    rw [feed_cons, hx]
    obtain ⟨acc2, hrest⟩ := osc_accum_run xs (v := { v with pstate := .osc acc1 false })
      (acc := acc1) rfl (by simpa using hu) (fun b hb => h b (by simp [hb]))
    exact ⟨acc2, by rw [hrest]⟩

/-- The OSC walk, for any projection: `ESC ] 2 ;` opens the string, the scrubbed
payload accumulates without dispatching, `BEL` finishes. The only field-dependent
step is what `oscFinish` does, and `frame_oscFinish` says it moves `pstate` and
`title` and nothing else. -/
theorem fixes_osc {α : Type} {π : Vt → α} (hb : PsBlind π) (payload : List Char)
    (hπ : ∀ (w : Vt) (acc : Array UInt8), π (w.oscFinish acc) = π w) :
    Fixes π (escB ++ [0x5D, 0x32, 0x3B] ++ utf8s payload ++ [0x07]) := by
  intro v hg hu
  rw [show
      (escB ++ [0x5D, 0x32, 0x3B] ++ utf8s payload ++ [0x07] : Bytes) =
        [0x1B] ++ ([0x5D] ++ ([0x32, 0x3B] ++ (utf8s payload ++ [0x07])))
      from by simp [escB]]
  rw [show
      ∀ (w : Vt),
        w.feed ([0x1B] ++ ([0x5D] ++ ([0x32, 0x3B] ++ (utf8s payload ++ [0x07])))) =
          ((((w.step 0x1B).step 0x5D).feed [0x32, 0x3B]).feed (utf8s payload)).step 0x07
      from fun w => by simp [Vt.feed, List.foldl_append]]
  rw [esc_step_eq hg hu]
  rw [show ({ v with pstate := .esc } : Vt).step 0x5D = { v with pstate := .osc #[] false } from by
      rw [step_of_esc_quiet 0x5D rfl (by simpa using hu)]
      unfold Vt.stepEsc
      rfl]
  obtain ⟨acc1, h1⟩ :=
    osc_accum_run [0x32, 0x3B] (v := { v with pstate := .osc #[] false }) (acc := #[]) rfl
      (by simpa using hu)
      (by
        intro b hb; rcases List.mem_cons.mp hb with h | h
        · subst h; exact ⟨by decide, by decide⟩
        · rw [show b = 0x3B from by simpa using h]; exact ⟨by decide, by decide⟩)
  rw [h1]
  obtain ⟨acc2, h2⟩ :=
    osc_accum_run (utf8s payload) (v := { v with pstate := .osc acc1 false }) (acc := acc1) rfl
      (by simpa using hu) (utf8s_no_esc_bel payload)
  rw [h2]
  rw [step_of_osc_quiet (0x07 : UInt8) rfl (by simpa using hu)]
  unfold Vt.stepOsc
  rw [ite_eq_right (by decide), ite_eq_left (by decide)]
  exact
    ⟨ps_oscFinish _ _, by
      rw [un_oscFinish]; simpa using hu, by rw [hπ, hb v (PState.osc acc2 false)]⟩

/-- **The title writes no cell.** The payload cannot terminate its own sequence:
`utf8s` puts every byte at or above `0x20`, so neither `ESC` nor `BEL` can appear
in it — the same fact that makes `ends_osc` work. -/
theorem keeps_osc (payload : List Char) :
    Keeps (escB ++ [0x5D, 0x32, 0x3B] ++ utf8s payload ++ [0x07]) := fixes_osc psBlind_grid payload grid_oscFinish

theorem keeps_titleAnsi (v : Vt) : Keeps (titleAnsi v) := by
  unfold titleAnsi
  exact keeps_osc _

/-! ### The digit bridge, and the last tail stage

`modesAnsi` is the one construct whose grid claim depends on *which number* it
emitted: `grid_setMode` holds for every mode except the three that switch screens.
The emitter never emits those (its allowlist), and its collector contains exactly
one parameter. `accDigits_digits` already says the accumulator inverts `digits`;
the record equation carries both the value and singleton shape to the grid layer. -/

/-- Digits update exactly the collector's number and presence flag. The complete
state equation preserves every receiver field, including parser metadata that
later dispatches inspect. The number is clamped for every `Nat`, including zero. -/
theorem csi_digits_feed_eq (n : Nat) {v : Vt} {s : CsiState} (hg : v.pstate = .csi s)
    (hu : v.u8need = 0) (hcur : s.cur = 0) :
    v.feed (digits n) =
      { v with pstate := .csi { s with cur := min n 65535, haveCur := true } } := by
  obtain ⟨s', heq⟩ := csi_param_run_frame (digits n) hg hu (paramBytes_digits n)
  have hne : digits n ≠ [] := by
    unfold digits
    split <;> simp
  have hp := csi_digits_feed (digits n) hg (digits_range n) hne
  rw [heq] at hp
  simp only [hcur, accDigits_digits] at hp
  rw [heq, PState.csi.inj hp]

/-- A digit run, as a record equation *and* with its accumulated value. -/
theorem csi_digits_run_eq (n : Nat) {v : Vt} {s : CsiState} (hg : v.pstate = .csi s)
    (hu : v.u8need = 0) (hcur : s.cur = 0) :
    ∃ s', v.feed (digits n) = { v with pstate := .csi s' }
      ∧ s'.cur = min n 65535 ∧ s'.haveCur = true ∧ s'.params = s.params
      ∧ s'.inter = s.inter ∧ s'.curSub = s.curSub := by
  exact ⟨_, csi_digits_feed_eq n hg hu hcur, rfl, rfl, rfl, rfl, rfl⟩

/-- A decimal tail extends the collector by one clamped parameter, then dispatches.
Its full state equation supports both preservation and state changes, retaining
the private marker and ignore flag. The parameter prefix need only have room for
one more entry; no positivity or upper-bound premise is needed for the number. -/
theorem csi_digits_tail_eq (n : Nat) (final : UInt8) (h1 : 0x40 ≤ final)
    (h2 : final ≤ 0x7E) {v : Vt} {s : CsiState} (hg : v.pstate = .csi s)
    (hu : v.u8need = 0) (hi : s.inter = 0) (hcur : s.cur = 0) (hsize : s.params.size < 16) :
    let t : CsiState := { s with cur := min n 65535, haveCur := true }
    v.feed (digits n ++ [final]) =
      { ({ v with pstate := .csi t } : Vt).csiDispatch
          { t with params := s.params.push (min n 65535, s.curSub) } final with
        pstate := .ground } := by
  dsimp only
  rw [feed_append, csi_digits_feed_eq n hg hu hcur]
  rw [show ∀ w : Vt, w.feed [final] = w.step final from fun _ => rfl]
  rw [csi_final_step_eq final
      (v := { v with pstate := .csi { s with cur := min n 65535, haveCur := true } })
      rfl hu hi h1 h2]
  simp [Vt.csiFinish, Nat.not_le.mpr hsize, Nat.min_assoc]

theorem grid_csiDispatch_sm (v : Vt) (s : CsiState)
    (h : ∀ p ∈ s.params.toList, p.1 ≠ 47 ∧ p.1 ≠ 1047 ∧ p.1 ≠ 1049) :
    (v.csiDispatch s 0x68).grid = v.grid := by
  by_cases hi : s.ignore = true
  · simp [Vt.csiDispatch, hi]
  · unfold Vt.csiDispatch
    rw [ite_eq_right hi]
    exact grid_setModes v _ _ true h

theorem grid_csiDispatch_rm (v : Vt) (s : CsiState)
    (h : ∀ p ∈ s.params.toList, p.1 ≠ 47 ∧ p.1 ≠ 1047 ∧ p.1 ≠ 1049) :
    (v.csiDispatch s 0x6C).grid = v.grid := by
  by_cases hi : s.ignore = true
  · simp [Vt.csiDispatch, hi]
  · unfold Vt.csiDispatch
    rw [ite_eq_right hi]
    exact grid_setModes v _ _ false h

/-- The shared tail for a **single-parameter** sequence, carrying the accumulated
number out so a caller can discharge a hypothesis about it. The digit run is done
here rather than at the call site: naming the collector state outside the lemma
means writing it the way the elaborator happened to build it, and `{}` and
`default` are not the same term. -/
theorem keeps_csi_digits_tail (n : Nat) (final : UInt8) (h1 : 0x40 ≤ final)
    (h2 : final ≤ 0x7E) (hlt : n < 65535)
    (hgrid : ∀ (w : Vt) (t : CsiState) (sub : Bool), t.params = #[(n, sub)] →
      (w.csiDispatch t final).grid = w.grid)
    {v : Vt} {s : CsiState} (hg : v.pstate = .csi s) (hu : v.u8need = 0)
    (hi : s.inter = 0) (hcur : s.cur = 0) (hpar : s.params = #[]) :
    ((v.feed (digits n ++ [final])).pstate = .ground
      ∧ (v.feed (digits n ++ [final])).u8need = 0
      ∧ (v.feed (digits n ++ [final])).grid = v.grid) := by
  rw [csi_digits_tail_eq n final h1 h2 hg hu hi hcur (by simp [hpar])]
  rw [show min n 65535 = n from by omega]
  dsimp only
  refine ⟨rfl, by rw [un_csiDispatch]; simpa using hu, ?_⟩
  exact hgrid _ _ s.curSub (by simp [hpar])

/-- `CSI ? n <final>` with a grid fact that may depend on `n`. -/
theorem keeps_csiPriv_arg (n : Nat) (final : UInt8) (h1 : 0x40 ≤ final)
    (h2 : final ≤ 0x7E) (hlt : n < 65535)
    (hgrid : ∀ (w : Vt) (t : CsiState) (sub : Bool), t.params = #[(n, sub)] →
      (w.csiDispatch t final).grid = w.grid) :
    Keeps (csiPriv n final) := by
  intro v hg hu
  rw [show csiPriv n final
      = [0x1B, 0x5B] ++ ([(0x3F : UInt8)] ++ (digits n ++ [final])) from by
    unfold csiPriv csiB; simp]
  rw [feed_append, feed_append]
  rw [keeps_csi_open hg hu]
  rw [show ∀ (w : Vt), w.feed [(0x3F : UInt8)] = w.step 0x3F from fun _ => rfl]
  rw [step_of_csi_quiet (0x3F : UInt8) (v := { v with pstate := .csi {} }) (s := {}) rfl
    (by simpa using hu)]
  unfold Vt.stepCsi
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left (by decide)]
  exact keeps_csi_digits_tail n final h1 h2 hlt hgrid rfl (by simpa using hu) rfl rfl rfl

/-- …and the non-private form, for `modesAnsi`'s one ANSI emit (`CSI 4 h`, IRM). -/
theorem keeps_csiNum_arg (n : Nat) (final : UInt8) (h1 : 0x40 ≤ final)
    (h2 : final ≤ 0x7E) (hlt : n < 65535)
    (hgrid : ∀ (w : Vt) (t : CsiState) (sub : Bool), t.params = #[(n, sub)] →
      (w.csiDispatch t final).grid = w.grid) :
    Keeps (csiNum n final) := by
  intro v hg hu
  rw [show csiNum n final = [0x1B, 0x5B] ++ (digits n ++ [final]) from by
    unfold csiNum csiB; simp]
  rw [feed_append]
  rw [keeps_csi_open hg hu]
  exact keeps_csi_digits_tail n final h1 h2 hlt hgrid rfl (by simpa using hu) rfl rfl rfl

theorem keeps_modeSet (n : Nat) (on : Bool) (hlt : n < 65535)
    (h47 : n ≠ 47) (h1047 : n ≠ 1047) (h1049 : n ≠ 1049) : Keeps (modeSet n on) := by
  unfold modeSet
  cases on
  · exact keeps_csiPriv_arg n 0x6C (by decide) (by decide) hlt
      (fun w t sub ha => grid_csiDispatch_rm w t
        (by simpa [ha] using And.intro h47 (And.intro h1047 h1049)))
  · exact keeps_csiPriv_arg n 0x68 (by decide) (by decide) hlt
      (fun w t sub ha => grid_csiDispatch_sm w t
        (by simpa [ha] using And.intro h47 (And.intro h1047 h1049)))

theorem keeps_irm (on : Bool) : Keeps (csiNum 4 (if on then 0x68 else 0x6C)) := by
  cases on
  · exact keeps_csiNum_arg 4 0x6C (by decide) (by decide) (by omega)
      (fun w t sub ha => grid_csiDispatch_rm w t (by simp [ha]))
  · exact keeps_csiNum_arg 4 0x68 (by decide) (by decide) (by omega)
      (fun w t sub ha => grid_csiDispatch_sm w t (by simp [ha]))

/-- **The mode replay writes no cell.** `modesAnsi`'s allowlist is what discharges
the screen-switch hypotheses: every number it emits is either a literal in the
source or one of the three the mouse guard names. -/
theorem keeps_modesAnsi (v : Vt) : Keeps (modesAnsi v) := by
  unfold modesAnsi
  refine Keeps.append ?_ (keeps_irm v.modes.insert)
  refine Keeps.append ?_ (keeps_modeSet 6 _ (by omega) (by omega) (by omega)
    (by omega))
  refine Keeps.append ?_ (keeps_modeSet 1004 _ (by omega) (by omega) (by omega)
    (by omega))
  refine Keeps.append ?_ (keeps_modeSet 1006 _ (by omega) (by omega) (by omega)
    (by omega))
  refine Keeps.append ?_ (Keeps.ite (c := (v.modes.mouse == 1000 || v.modes.mouse == 1002
    || v.modes.mouse == 1003) = true)
    (fun h => by
      simp only [Bool.or_eq_true, beq_iff_eq] at h
      exact keeps_modeSet v.modes.mouse true (by omega) (by omega) (by omega)
        (by omega))
    (fun _ => Keeps.nil))
  refine Keeps.append ?_ (keeps_modeSet 1003 false (by omega) (by omega)
    (by omega) (by omega))
  refine Keeps.append ?_ (keeps_modeSet 1002 false (by omega) (by omega)
    (by omega) (by omega))
  refine Keeps.append ?_ (keeps_modeSet 1000 false (by omega) (by omega)
    (by omega) (by omega))
  refine Keeps.append ?_ (keeps_modeSet 2004 _ (by omega) (by omega) (by omega)
    (by omega))
  refine Keeps.append ?_ (keeps_modeSet 25 _ (by omega) (by omega) (by omega)
    (by omega))
  refine Keeps.append ?_ (Keeps.ite (fun _ => keeps_escSeq 0x3D (by decide))
    (fun _ => keeps_escSeq 0x3E (by decide)))
  exact (keeps_modeSet 7 _ (by omega) (by omega) (by omega) (by omega)).append
    (keeps_modeSet 1 _ (by omega) (by omega) (by omega) (by omega))

/-- **Park the pen and the cursor**: the alt-stash parking inside `screensAnsi`
writes no cell. Stated on bare naturals so the stashed cursor instantiates it. -/
theorem keeps_park (y x : Nat) (p : Pen) : Keeps (penSgr p ++ csiNum2 y x 0x48) :=
  (keeps_penSgr p).append
    (keeps_csiNum2 _ _ 0x48 (by decide) (by decide) grid_csiDispatch_cup)

end Linger.Core.Render

namespace Linger.Core.Vt

/-- `ED 2` is the `_` arm of the match, so this is definitional. Having the equation
as a lemma keeps the match out of callers' proofs, where an in-tactic split leaves an
unreduced `match 2 with …` that `rw` cannot see through. -/
theorem eraseScreen_two_eq (v : Vt) : v.eraseScreen 2
    = (List.range v.rows).foldl (fun v' y => v'.eraseRowSpan y 0 v'.cols) v := by rfl

end Linger.Core.Vt

namespace Linger.Core.Render

open Linger.Core.Vt

/-! ### The paint and its continuation tail

The control stages are framed by their `keeps_*` lemmas. The saved and active
deferred-wrap stages also print an existing cell, so `Grid.lean` composes those
frames with the complete-state equations in `PendingWrap.lean`. -/

/-- Re-associate the clear-and-paint prefix and the ten tail stages, including
the saved and active deferred-wrap repairs. -/
theorem restore_split (v : Vt) :
    restore v = (prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v)
      ++ (regionAnsi v ++ tabsAnsi v ++ savedAnsi v ++ savedPendingAnsi v ++ titleAnsi v ++ modesAnsi v
          ++ charsetAnsi v ++ penSgr v.pen ++ cursorAnsi v ++ cursorPendingAnsi v) := by
  unfold restore restoreBody
  simp

end Linger.Core.Render
