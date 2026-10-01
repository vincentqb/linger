module

public import Linger.Core.Vt
import all Linger.Core.Vt

-- No `public section`, and that is forced by the `Vt` seal
-- (`specs/archive/vt-toolkit.md` Step 1). `import all` grants *access* to a private
-- field, but a **public** declaration's type may still not mention one — so
-- `structure Good` and every theorem stating `v.cols`/`v.cursor`/… must be
-- module-private. Default visibility in a `module` file is exactly that, so the
-- fix is the absence of one line rather than `private` on a hundred. Consumers
-- reach in with `import all Theorems.Vt`, which `Theorems/Render/Ends.lean` and
-- `Theorems/Session.lean` already do.

/-! # §Total / §Chunk / §Bound — the emulator theorems

THEOREMS.md rows for `Vt`:
* §Chunk — `feed` is invariant under re-chunking (definitional, from
  `feed = foldl step`, but stated so a rewrite cannot silently lose it).
* §Bound — no field of `Vt` grows with input
  volume. Scrollback ≤ `sbCap`, OSC accumulator ≤ 2048, CSI params
  ≤ 16, UTF-8 pending ≤ 3 — preserved by `step` for ANY byte, hence by
  `feed` for ANY byte stream.
* §Total — `step` preserves the structural sanity of the screen: grid
  dimensions don't change, and the cursor (plus every stashed cursor)
  stays strictly inside them. Together with "no `partial def` in
  `Linger/Core`" (checked by grep in e2e) this is the no-crash statement.

The invariant is one structure, `Good`, so each preservation lemma is
one implication and `step` is a case-bash over the parser states.
-/

namespace Linger.Core.Vt

/-! ## The read-only window

`Vt.colCount`/`rowCount`/`cursorPos`/`inAlt` are the public reading of four sealed
fields (`Linger/Core/Vt.lean`), for consumers outside the toolkit —
`Linger/Core/Session.lean` and the resume path in `Linger/Runtime/Daemon.lean`. Each
is a projection, so its claim is the equation that says so, and `@[simp]` is what
earns these their keep: a proof that has a hypothesis about a field and a goal about
the accessor needs the bridge, and without it `onMsg_attach_same_size_vt` and two
`Session` rungs stop closing. Equations, not bounds — there is nothing here that
could be wrong, only something that could be missing. -/

@[simp]
theorem colCount_eq (v : Vt) : v.colCount = v.cols := rfl

@[simp]
theorem rowCount_eq (v : Vt) : v.rowCount = v.rows := rfl

@[simp]
theorem cursorPos_eq (v : Vt) : v.cursorPos = (v.cursor.x, v.cursor.y) := rfl

@[simp]
theorem inAlt_eq (v : Vt) : v.inAlt = v.altGrid.isSome := rfl

/-- A final byte ends an ESC intermediate sequence. Only single G0/G1
designations change a charset; unsupported intermediates are consumed. -/
theorem stepEscInter_final (v : Vt) (i b : UInt8) (hlo : 0x30 ≤ b) (hhi : b ≤ 0x7E) :
    v.stepEscInter i b =
      if i == 0x28 then
        { v with
          pstate := .ground, g0Line := b == 0x30 }
      else
        if i == 0x29 then
          { v with
            pstate := .ground, g1Line := b == 0x30 }
        else { v with pstate := .ground } := by
  simp [Vt.stepEscInter, hlo, hhi]

/-- Everything §Total and §Bound need, as one induction hypothesis. -/
structure Good (v : Vt) : Prop where
  colsPos : 1 ≤ v.cols
  rowsPos : 1 ≤ v.rows
  colsLe : v.cols ≤ 1000
  rowsLe : v.rows ≤ 1000
  curX : v.cursor.x < v.cols
  curY : v.cursor.y < v.rows
  savX : v.saved.cur.x < v.cols
  savY : v.saved.cur.y < v.rows
  altCur : ∀ g c p, v.altGrid = some (g, c, p) → c.x < v.cols ∧ c.y < v.rows
  topLe : v.top ≤ v.bot
  botLt : v.bot < v.rows
  sbLe : v.sb.size ≤ sbCap
  u8Le : v.u8need ≤ 3
  csiLe : ∀ s, v.pstate = .csi s → s.params.size ≤ 16
  oscLe : ∀ acc e, v.pstate = .osc acc e → acc.size ≤ 2048

/-- The state a fresh session starts in is Good. -/
theorem good_init (cols rows : Nat) : Good (Vt.init cols rows) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Vt.init, clampDim, Ring.size, sbCap] <;>
    omega

/-! ### The decoder's door

`Vt.ofDecoded` (`Linger/Core/Vt.lean`) is the only way a `Vt` comes into existence
other than `Vt.init`, and unlike `init` its inputs are *attacker-controlled*: they are
whatever `Linger/Core/Checkpoint.lean`'s `rVt` read out of a file. Three claims — the
spec of the check, the guarantee, and what stops the guarantee being achieved by
refusing everything. -/

/-- What the decoder's check actually decides, in `Good`'s own vocabulary. Stated so the
`Bool` and the `Prop` cannot drift: `ofDecoded_good` and `ofDecoded_of_good` both go
through this rather than unfolding twelve `&&`s twice. -/
theorem decodedOk_iff {cols rows top bot : Nat} {cursor : Cursor} {sb : Ring} {saved : Saved}
    {altGrid : Option (Array Row × Cursor × Pen)} :
    Vt.decodedOk cols rows cursor top bot sb altGrid saved = true ↔
      1 ≤ cols ∧
        cols ≤ 1000 ∧
        1 ≤ rows ∧
        rows ≤ 1000 ∧
        cursor.x < cols ∧
        cursor.y < rows ∧
        saved.cur.x < cols ∧
        saved.cur.y < rows ∧
        top ≤ bot ∧
        bot < rows ∧
        sb.size ≤ sbCap ∧ ∀ g c p, altGrid = some (g, c, p) → c.x < cols ∧ c.y < rows := by
  unfold Vt.decodedOk
  cases altGrid with
  | none =>
    simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc, and_true]; simp
  | some x =>
    obtain ⟨g₀, c₀, p₀⟩ := x
    simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc, Option.some.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, hx, hy⟩
      refine ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, ?_⟩
      rintro g c p ⟨rfl, rfl, rfl⟩
      exact ⟨hx, hy⟩
    · rintro ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, halt⟩
      obtain ⟨hx, hy⟩ := halt g₀ c₀ p₀ ⟨rfl, rfl, rfl⟩
      exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, hx, hy⟩

/-- **Nothing bad comes out of the decoder's door.** Whatever a checkpoint file says,
if `Vt.ofDecoded` returns a `Vt` at all then that `Vt` is `Good`: the dimensions are in
`[1,1000]`, both cursors and every stashed cursor are inside the screen, the scroll
region is non-empty and on-screen, and the scrollback is within `sbCap`.

This is the claim `specs/archive/vt-toolkit.md` Step 2 exists for. Before it, `rVt` built a
`Vt` field-by-field, so `cols := 0` — a state no `init`/`resize`/`feed` path can reach,
and one the emulator's own theorems are all false of — was one hostile byte away. -/
theorem ofDecoded_good {cols rows : Nat} {grid : Array Row} {cursor : Cursor} {pen : Pen}
    {modes : Modes} {top bot : Nat} {tabs : Array Bool} {sb : Ring}
    {altGrid : Option (Array Row × Cursor × Pen)} {saved : Saved} {title : String}
    {g0Line g1Line shiftOut bell : Bool} {v : Vt}
    (h :
      Vt.ofDecoded cols rows grid cursor pen modes top bot tabs sb altGrid saved title g0Line g1Line
          shiftOut bell =
        some v) :
    Good v := by
  unfold Vt.ofDecoded at h
  split at h
  · rename_i hg
    simp only [Bool.and_eq_true] at hg
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, halt⟩ := decodedOk_iff.mp hg.1
    cases h
    exact
      ⟨h1, h3, h2, h4, h5, h6, h7, h8, halt, h9, h10, h11, Nat.zero_le 3, fun s hs =>
        absurd hs (by simp), fun acc e hs => absurd hs (by simp)⟩
  · exact absurd h (by simp)

/-! **The other half of the door's claim — "nothing good is rejected" — is
`ofDecoded_of_good`, and it is NOT here.** It lives in §The decoder's door, part two,
below, because after R2 the door also decides `Renderable`, so the statement names a
predicate nothing this early in the file can mention. `ofDecoded_good` above would be
satisfied by a constructor that returned `none` always; that is what the other half
rules out, so read them as a pair even though the file cannot state them as one. -/

/-- **Junk dimensions are refused, not clamped**, and this is the concrete shape of
that: `cols = 0` is the canonical corrupt value — no live session can hold it, `Good`
is false of it, and every `Render` theorem is vacuous at it — so the door shuts.

Clamping was the alternative and it is worse, for a reason that is about the *grid*
rather than the dimension: `clampDim cols` would satisfy `Good` while leaving the
decoded rows at their own width, producing a state that is `Good` and not `Renderable`
— and `Renderable` is what every `Render.restore` theorem needs. Establishing it by
clamping means rebuilding the grid, i.e. `Vt.resize`, which the resume path refuses
because it resets the scroll region and the tab ruler. Rejecting needs no new
behaviour: `load` is already `Option`-valued, and its `none` already means "start
fresh". -/
theorem ofDecoded_none_of_cols_zero {rows : Nat} {grid : Array Row} {cursor : Cursor} {pen : Pen}
    {modes : Modes} {top bot : Nat} {tabs : Array Bool} {sb : Ring}
    {altGrid : Option (Array Row × Cursor × Pen)} {saved : Saved} {title : String}
    {g0Line g1Line shiftOut bell : Bool} :
    Vt.ofDecoded 0 rows grid cursor pen modes top bot tabs sb altGrid saved title g0Line g1Line
        shiftOut bell =
      none := by
  have hno :
    (Vt.decodedOk 0 rows cursor top bot sb altGrid saved &&
        Vt.decodedRenderable 0 rows grid tabs altGrid) ≠
      true := by
    intro hg
    simp only [Bool.and_eq_true] at hg
    exact absurd (decodedOk_iff.mp hg.1).1 (by omega)
  unfold Vt.ofDecoded
  rw [ite_eq_right hno]

/-- **Fold invariance, once.** Any predicate preserved by one step is preserved
by a whole `List.foldl`. Five lemmas in this repo were this statement written out
for a specific predicate (`Good`, `Renderable`, a row's cells, a grid's rows, and
`Ends`/`Quiet` over the row painter's accumulator); they are now derivations that
keep their own names, so no call site changed. A sixth predicate costs one line. -/
theorem invariant_foldl {α β : Type} (P : β → Prop) (f : β → α → β)
    (hf : ∀ acc a, P acc → P (f acc a)) : ∀ (l : List α) (acc : β), P acc → P (l.foldl f acc)
  | [], _, h => h
  | a :: as, acc, h => invariant_foldl P f hf as (f acc a) (hf acc a h)

/-- Ordered mode batches compose as whole states, including cursor saves and
screen switches. Splitting a batch never changes which mode sees which state. -/
theorem setModes_append (v : Vt) (priv : Bool) (xs ys : List (Nat × Bool)) (on : Bool) :
    v.setModes priv (xs ++ ys) on = (v.setModes priv xs on).setModes priv ys on := by
  simp only [Vt.setModes, List.foldl_append]

theorem setModes_nil (v : Vt) (priv on : Bool) : v.setModes priv [] on = v := rfl

theorem setModes_cons (v : Vt) (priv : Bool) (p : Nat × Bool) (ps : List (Nat × Bool)) (on : Bool) :
    v.setModes priv (p :: ps) on = (v.setMode priv p.1 on).setModes priv ps on := rfl

/-- A singleton batch retains the full single-mode behavior, without a
restriction on the mode number or on the incoming emulator state. -/
theorem setModes_one (v : Vt) (priv : Bool) (n : Nat) (sub on : Bool) :
    v.setModes priv [(n, sub)] on = v.setMode priv n on := rfl

/-- A batch preserves any invariant preserved by every requested mode. Membership
matters for conditional frames such as excluding screen-switch parameters. -/
theorem setModes_invariant (P : Vt → Prop) (priv on : Bool) (ps : List (Nat × Bool))
    (hstep : ∀ w p, p ∈ ps → P w → P (w.setMode priv p.1 on)) (v : Vt) (h : P v) :
    P (v.setModes priv ps on) := by
  induction ps generalizing v with
  | nil => exact h
  | cons p ps ih =>
    rw [setModes_cons]
    exact ih (fun w q hq => hstep w q (List.mem_cons_of_mem p hq)) _ (hstep v p (by simp) h)

end Linger.Core.Vt

namespace Linger.Core.Vt.Good

open Linger.Core.Vt

/-- "Preserves Good and the screen dimensions." Every constituent of
`step` gets one of these; `step` composes them. -/
def Pres (f : Vt → Vt) : Prop :=
  ∀ v, Good v → Good (f v) ∧ (f v).cols = v.cols ∧ (f v).rows = v.rows

theorem Pres.id : Pres (fun v => v) := fun _ h => ⟨h, rfl, rfl⟩

theorem Pres.comp {f g : Vt → Vt} (hf : Pres f) (hg : Pres g) : Pres (fun v => g (f v)) := by
  intro v h
  obtain ⟨h1, hc1, hr1⟩ := hf v h
  obtain ⟨h2, hc2, hr2⟩ := hg (f v) h1
  exact ⟨h2, by rw [hc2, hc1], by rw [hr2, hr1]⟩

theorem Pres.foldl {α : Type} {f : Vt → α → Vt} (hf : ∀ a, Pres (f · a)) :
    ∀ (l : List α), Pres (fun v => l.foldl f v)
  | [] => Pres.id
  | a :: l => by
    have := Pres.comp (hf a) (Pres.foldl hf l)
    simpa [List.foldl_cons] using this

/-- Replacing only the grid touches nothing Good watches. Same for
pen, modes, tabs, title, bell — all definitional repacks. -/
theorem set_grid {v : Vt} (g : Array Row) (h : Good v) : Good { v with grid := g } := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h
  exact ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩

theorem set_pen {v : Vt} (p : Pen) (h : Good v) : Good { v with pen := p } := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h
  exact ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩

theorem set_modes {v : Vt} (m : Modes) (h : Good v) : Good { v with modes := m } := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h
  exact ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩

theorem set_ground {v : Vt} (h : Good v) : Good { v with pstate := .ground } := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, -, -⟩ := h
  exact
    ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, (fun _ h => nomatch h),
      (fun _ _ h => nomatch h)⟩

theorem set_tabs {v : Vt} (t : Array Bool) (h : Good v) : Good { v with tabs := t } := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h
  exact ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩

end Linger.Core.Vt.Good

namespace Linger.Core.Vt.Good

/-! ## Cursor-writing primitives -/

theorem clearPending {v : Vt} (h : Good v) : Good v.clearPending := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h
  exact ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩

theorem moveTo {v : Vt} (x y : Nat) (h : Good v) : Good (v.moveTo x y) := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h
  unfold Vt.moveTo
  refine ⟨cp, rp, cl, rl, ?_, ?_, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩
  · dsimp only; omega
  · by_cases ho : v.modes.origin <;> simp [ho] <;> omega

theorem moveRel {v : Vt} (dx dy : Int) (h : Good v) : Good (v.moveRel dx dy) := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h
  unfold Vt.moveRel
  refine ⟨cp, rp, cl, rl, ?_, ?_, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩
  · dsimp only; omega
  · by_cases hr : (v.cursor.y ≥ v.top && v.cursor.y ≤ v.bot) <;> simp [hr] <;> omega

theorem carriageReturn {v : Vt} (h : Good v) : Good v.carriageReturn := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h
  exact
    ⟨cp, rp, cl, rl, by
      dsimp only [Vt.carriageReturn]; omega, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩

theorem backspace {v : Vt} (h : Good v) : Good v.backspace := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h
  unfold Vt.backspace Vt.clearPending
  split
  · exact ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩
  · exact
      ⟨cp, rp, cl, rl, by
        dsimp only; omega, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩

theorem tab {v : Vt} (h : Good v) : Good v.tab := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h
  unfold Vt.tab Vt.clearPending
  exact
    ⟨cp, rp, cl, rl, by
      dsimp only; omega, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩

theorem backTab {v : Vt} (h : Good v) : Good v.backTab := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h
  unfold Vt.backTab
  exact
    ⟨cp, rp, cl, rl, by
      dsimp only; omega, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩

/-! ## Scrolling — grid + ring only; the cursor is untouched -/

theorem ring_push_le {r : Ring} (row : Row) (h : r.size ≤ sbCap) : (r.push row).size ≤ sbCap := by
  unfold Ring.size at h ⊢
  unfold Ring.push
  split
  · simp only [Array.size_push]
    omega
  · simpa [Array.size_setIfInBounds] using h

theorem scrollUpIn {v : Vt} (t b : Nat) (allowSb : Bool) (h : Good v) :
    Good (v.scrollUpIn t b allowSb) := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h
  unfold Vt.scrollUpIn
  dsimp only
  split
  · exact ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, ring_push_le _ sb, u8, hcsi, hosc⟩
  · exact ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩

theorem scrollDownIn {v : Vt} (t b : Nat) (h : Good v) : Good (v.scrollDownIn t b) := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h
  exact ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩

theorem scrollUp {v : Vt} (h : Good v) : Good v.scrollUp := scrollUpIn _ _ _ h

theorem scrollDown {v : Vt} (h : Good v) : Good v.scrollDown := scrollDownIn _ _ h

theorem lineFeed {v : Vt} (h : Good v) : Good v.lineFeed := by
  have h' := clearPending h
  unfold Vt.lineFeed
  dsimp only
  split
  · exact scrollUp h'
  · split
    · obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h'
      exact
        ⟨cp, rp, cl, rl, cx, by
          dsimp only; omega, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩
    · exact h'

theorem reverseIndex {v : Vt} (h : Good v) : Good v.reverseIndex := by
  have h' := clearPending h
  unfold Vt.reverseIndex
  dsimp only
  split
  · exact scrollDown h'
  · obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h'
    exact
      ⟨cp, rp, cl, rl, cx, by
        dsimp only; omega, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩

theorem setCol {v : Vt} (x : Nat) (h : Good v) : Good (v.setCol x) := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h
  exact
    ⟨cp, rp, cl, rl, by
      dsimp only [Vt.setCol]; omega, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩

/-! ## Folded repetitions -/

theorem good_foldl {α : Type} {f : Vt → α → Vt} (hf : ∀ v a, Good v → Good (f v a)) :
    ∀ (l : List α) {v : Vt}, Good v → Good (l.foldl f v) := fun l _ h =>
  Linger.Core.Vt.invariant_foldl Good f hf l _ h

/-! ## Erase / insert / delete — grid-only (plus ED 3's scrollback reset) -/

theorem eraseRowSpan {v : Vt} (y a b : Nat) (h : Good v) : Good (v.eraseRowSpan y a b) := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h
  exact ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩

theorem eraseLine {v : Vt} (m : Nat) (h : Good v) : Good (v.eraseLine m) := by
  unfold Vt.eraseLine
  split <;> exact eraseRowSpan _ _ _ h

theorem eraseScreen {v : Vt} (m : Nat) (h : Good v) : Good (v.eraseScreen m) := by
  unfold Vt.eraseScreen
  split
  · exact good_foldl (fun v' i hh => eraseRowSpan _ _ _ hh) _ (eraseLine _ h)
  · exact good_foldl (fun v' y hh => eraseRowSpan _ _ _ hh) _ (eraseLine _ h)
  · -- ED 3: also drops scrollback; an empty ring is within any cap
    have h' : Good ((List.range v.rows).foldl (fun v' y => v'.eraseRowSpan y 0 v'.cols) v) :=
      good_foldl (fun v' y hh => eraseRowSpan _ _ _ hh) _ h
    obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, -, u8, hcsi, hosc⟩ := h'
    exact ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, by simp [Ring.size], u8, hcsi, hosc⟩
  · exact good_foldl (fun v' y hh => eraseRowSpan _ _ _ hh) _ h

theorem insertLines {v : Vt} (n : Nat) (h : Good v) : Good (v.insertLines n) := by
  unfold Vt.insertLines
  split
  · exact h
  · exact good_foldl (fun v a hh => scrollDownIn _ _ hh) _ h

theorem deleteLines {v : Vt} (n : Nat) (h : Good v) : Good (v.deleteLines n) := by
  unfold Vt.deleteLines
  split
  · exact h
  · exact good_foldl (fun v a hh => scrollUpIn _ _ _ hh) _ h

theorem deleteChars {v : Vt} (n : Nat) (h : Good v) : Good (v.deleteChars n) := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h
  exact ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩

theorem insertChars {v : Vt} (n : Nat) (h : Good v) : Good (v.insertChars n) := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h
  exact ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩

theorem eraseChars {v : Vt} (n : Nat) (h : Good v) : Good (v.eraseChars n) := eraseRowSpan _ _ _ h

theorem applySgr {v : Vt} (ps : List (Nat × Bool)) (h : Good v) : Good (v.applySgr ps) := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h
  exact ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩

/-! ## Alt screen -/

theorem enterAlt {v : Vt} (saveCursor : Bool) (h : Good v) : Good (v.enterAlt saveCursor) := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h
  unfold Vt.enterAlt
  split
  · exact ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩
  · refine ⟨cp, rp, cl, rl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, sb, u8, hcsi, hosc⟩
    · dsimp only; omega
    · dsimp only; omega
    · dsimp only
      split
      · exact cx
      · exact sx
    · dsimp only
      split
      · exact cy
      · exact sy
    · intro g c p heq
      simp only [Option.some.injEq, Prod.mk.injEq] at heq
      obtain ⟨-, hc, -⟩ := heq
      subst hc
      exact ⟨cx, cy⟩
    · dsimp only; omega
    · dsimp only; omega

theorem leaveAlt {v : Vt} (restoreCursor : Bool) (h : Good v) :
    Good (v.leaveAlt restoreCursor) := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h
  unfold Vt.leaveAlt
  split
  · exact ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩
  · rename_i g cur pen heq
    obtain ⟨hax, hay⟩ := ac g cur pen heq
    refine
      ⟨cp, rp, cl, rl, ?_, ?_, sx, sy, (fun _ _ _ hh => nomatch hh), ?_, ?_, sb, u8, hcsi, hosc⟩
    · dsimp only
      split
      · exact hax
      · exact cx
    · dsimp only
      split
      · exact hay
      · exact cy
    · dsimp only; omega
    · dsimp only; omega

/-! ## Mode switching -/

theorem setMode {v : Vt} (priv : Bool) (n : Nat) (on : Bool) (h : Good v) :
    Good (v.setMode priv n on) := by
  unfold Vt.setMode
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h
  have h' : Good v := ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩
  split <;> split
  all_goals
    first
    | exact h'
    | exact set_modes _ h'
    | exact moveTo 0 0 (set_modes _ h')
    |
      (split <;>
          first
          | exact enterAlt _ h'
          | exact leaveAlt _ h'
          | exact ⟨cp, rp, cl, rl, cx, cy, cx, cy, ac, tl, bl, sb, u8, hcsi, hosc⟩
          | exact ⟨cp, rp, cl, rl, sx, sy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩)

theorem setModes {v : Vt} (priv : Bool) (ps : List (Nat × Bool)) (on : Bool) (h : Good v) :
    Good (v.setModes priv ps on) :=
  setModes_invariant Good priv on ps (fun _ p _ hh => setMode priv p.1 on hh) v h

/-! ## CSI dispatch -/

theorem csiDispatch {v : Vt} (s : CsiState) (final : UInt8) (h : Good v) :
    Good (v.csiDispatch s final) := by
  unfold Vt.csiDispatch
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h
  have h' : Good v := ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩
  split
  · exact h'
  · split
    all_goals
      first
      | exact h'
      | exact insertChars _ h'
      | exact moveRel _ _ h'
      | exact carriageReturn (moveRel _ _ h')
      | exact setCol _ h'
      | exact moveTo _ _ h'
      | exact eraseScreen _ h'
      | exact eraseLine _ h'
      | exact insertLines _ h'
      | exact deleteLines _ h'
      | exact deleteChars _ h'
      | exact eraseChars _ h'
      | exact setModes _ _ _ h'
      | exact good_foldl (fun v' i hh => tab hh) _ h'
      | exact good_foldl (fun v' i hh => scrollUp hh) _ h'
      | exact good_foldl (fun v' i hh => scrollDown hh) _ h'
      | exact good_foldl (fun v' i hh => backTab hh) _ h'
      |
        exact
          ⟨cp, rp, cl, rl, cx, by
            dsimp only; omega, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩
      | exact ⟨cp, rp, cl, rl, cx, cy, cx, cy, ac, tl, bl, sb, u8, hcsi, hosc⟩
      | exact ⟨cp, rp, cl, rl, sx, sy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩
      |
        (split <;>
            first
            | exact applySgr _ h'
            | exact set_tabs _ h'
            | exact h'
            | exact ⟨cp, rp, cl, rl, sx, sy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩
            | ( dsimp only
                split <;>
                  first
                  | exact h'
                  | ( rename_i hg
                      simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
                      refine
                          moveTo 0 0
                            ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, ?_, ?_, sb, u8, hcsi, hosc⟩ <;>
                        (dsimp only; omega))))

/-- Private final-`u` sequences (notably kitty's `CSI ? u` query) are
state-neutral; only public ANSI `CSI u` is DECRC. -/
theorem csiDispatch_private_u (v : Vt) (s : CsiState) (hi : s.ignore = false) (hp : s.priv ≠ 0) :
    v.csiDispatch s 0x75 = v := by simp [Vt.csiDispatch, hi, hp]

/-- Public ANSI `CSI u` still restores the saved cursor and pen. -/
theorem csiDispatch_public_u (v : Vt) (s : CsiState) (hi : s.ignore = false) (hp : s.priv = 0) :
    v.csiDispatch s 0x75 =
      { v with
        cursor := v.saved.cur, pen := v.saved.pen } := by
  simp [Vt.csiDispatch, hi, hp]

/-! ## Printing -/

theorem putCell {v : Vt} (x y : Nat) (c : Cell) (h : Good v) : Good (v.putCell x y c) := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h
  exact ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩

/-! ### Wide-pair repair

`mendAt` and `mendRow` are grid-only record updates, so `Good` passes
straight through them. Stated as their own lemmas rather than left to `split`:
their guards read cells through `getD` chains, and letting a proof descend into
those is what made `Good.printPut` time out at `whnf`. -/

theorem mendAt {v : Vt} (x y : Nat) (h : Good v) : Good (v.mendAt x y) := set_grid _ h

theorem mendRow {v : Vt} (y : Nat) (h : Good v) : Good (v.mendRow y) := set_grid _ h

theorem printWrap {v : Vt} (h : Good v) : Good v.printWrap := by
  unfold Vt.printWrap
  split
  · exact lineFeed (carriageReturn h)
  · exact clearPending h

theorem printWideWrap {v : Vt} (w : Nat) (h : Good v) : Good (v.printWideWrap w) := by
  unfold Vt.printWideWrap
  split
  · exact lineFeed (carriageReturn h)
  · exact h

theorem printShift {v : Vt} (w : Nat) (h : Good v) : Good (v.printShift w) := by
  unfold Vt.printShift
  split
  · exact set_grid _ h
  · exact h

theorem printPut {v : Vt} (ch : Char) (w : Nat) (h : Good v) : Good (v.printPut ch w) := by
  unfold Vt.printPut
  dsimp only
  split
  · exact mendRow _ (putCell _ _ _ h)
  · split
    · exact mendRow _ (putCell _ _ _ (putCell _ _ _ h))
    · exact mendRow _ (putCell _ _ _ h)

theorem printAdvance {v : Vt} (w : Nat) (h : Good v) : Good (v.printAdvance w) := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h
  unfold Vt.printAdvance
  dsimp only
  split
  · exact
      ⟨cp, rp, cl, rl, by
        dsimp only; omega, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩
  · exact
      ⟨cp, rp, cl, rl, by
        dsimp only; omega, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩

theorem printMark {v : Vt} (ch : Char) (h : Good v) : Good (v.printMark ch) := by
  unfold Vt.printMark
  dsimp only
  repeat' split
  all_goals
    first
    | exact h
    | exact mendRow _ (putCell _ _ _ h)

theorem print {v : Vt} (ch : Char) (h : Good v) : Good (v.print ch) := by
  unfold Vt.print
  dsimp only
  split
  · exact printMark _ h
  · exact printAdvance _ (printPut _ _ (printShift _ (printWideWrap _ (printWrap h))))

theorem acceptChar {v : Vt} (n : Nat) (h : Good v) : Good (v.acceptChar n) := by
  unfold Vt.acceptChar
  split
  · exact print _ h
  · exact print _ h

/-! ## Control bytes and parser transitions -/

theorem ctl {v : Vt} (b : UInt8) (h : Good v) : Good (v.ctl b) := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h
  have h' : Good v := ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩
  unfold Vt.ctl
  split
  all_goals
    first
    | exact h'
    | exact backspace h'
    | exact tab h'
    | exact lineFeed h'
    | exact carriageReturn h'
    | exact ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩

theorem oscFinish {v : Vt} (acc : Array UInt8) (h : Good v) : Good (v.oscFinish acc) := by
  unfold Vt.oscFinish
  dsimp only
  have hg := set_ground h
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := hg
  split
  · split
    · exact ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩
    · exact ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩
  · exact ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩

theorem csiFinish {v : Vt} (s : CsiState) (final : UInt8) (h : Good v) :
    Good (v.csiFinish s final) := by
  unfold Vt.csiFinish
  exact set_ground (csiDispatch _ _ h)

/-! ## Parser-state setters within their §Bound caps -/

theorem set_pstate_csi {v : Vt} (s : CsiState) (hp : s.params.size ≤ 16) (h : Good v) :
    Good { v with pstate := .csi s } := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, -, -⟩ := h
  refine ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, ?_, ?_⟩
  · intro s' heq
    simp only [PState.csi.injEq] at heq
    subst heq
    exact hp
  · intro _ _ heq
    exact nomatch heq

theorem set_pstate_osc {v : Vt} (acc : Array UInt8) (e : Bool) (hacc : acc.size ≤ 2048)
    (h : Good v) : Good { v with pstate := .osc acc e } := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, -, -⟩ := h
  refine ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, ?_, ?_⟩
  · intro _ heq
    exact nomatch heq
  · intro acc' e' heq
    simp only [PState.osc.injEq] at heq
    obtain ⟨h1, -⟩ := heq
    subst h1
    exact hacc

theorem set_pstate_esc {v : Vt} (h : Good v) : Good { v with pstate := .esc } := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, -, -⟩ := h
  exact
    ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, (fun _ heq => nomatch heq),
      (fun _ _ heq => nomatch heq)⟩

theorem set_pstate_escInter {v : Vt} (b : UInt8) (h : Good v) :
    Good { v with pstate := .escInter b } := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, -, -⟩ := h
  exact
    ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, (fun _ heq => nomatch heq),
      (fun _ _ heq => nomatch heq)⟩

theorem set_pstate_str {v : Vt} (e : Bool) (h : Good v) : Good { v with pstate := .str e } := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, -, -⟩ := h
  exact
    ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, (fun _ heq => nomatch heq),
      (fun _ _ heq => nomatch heq)⟩

theorem csiPush_le (s : CsiState) (sub : Bool) (hp : s.params.size ≤ 16) :
    (csiPush s sub).params.size ≤ 16 := by
  unfold csiPush
  split
  · exact hp
  · simp only [Array.size_push]
    omega

theorem set_u8 {v : Vt} (n a : Nat) (hn : n ≤ 3) (h : Good v) :
    Good
      { v with
        u8need := n, u8acc := a } := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, -, hcsi, hosc⟩ := h
  exact ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, hn, hcsi, hosc⟩

theorem set_sb {v : Vt} (r : Ring) (hr : r.size ≤ sbCap) (h : Good v) :
    Good { v with sb := r } := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, -, u8, hcsi, hosc⟩ := h
  exact ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, hr, u8, hcsi, hosc⟩

/-! ## Per-parser-state steps -/

theorem stepGround {v : Vt} (b : UInt8) (h : Good v) : Good (v.stepGround b) := by
  -- Follow the dispatch instead of trying every lemma on every goal: mismatched
  -- applications unfold the print chain and used to require a raised recursion limit.
  unfold Vt.stepGround
  have u8 := h.u8Le
  split
  · exact set_pstate_esc h
  split
  · exact ctl _ h
  split
  · exact acceptChar _ h
  split
  · split
    · exact h
    split
    · exact acceptChar _ (set_u8 0 0 (by omega) h)
    · exact set_u8 (v.u8need - 1) _ (by omega) h
  split
  · exact set_u8 1 _ (by omega) h
  split
  · exact set_u8 2 _ (by omega) h
  split
  · exact set_u8 3 _ (by omega) h
  · exact h

theorem stepEsc {v : Vt} (b : UInt8) (h : Good v) : Good (v.stepEsc b) := by
  unfold Vt.stepEsc
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h
  have h' : Good v := ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩
  split
  all_goals
    first
    | exact h'
    | exact set_pstate_csi {} (by simp) h'
    | exact set_pstate_osc #[] false (by simp) h'
    | exact set_pstate_str _ h'
    | exact set_pstate_escInter _ h'
    | exact set_ground h'
    | exact set_ground (lineFeed h')
    | exact set_ground (lineFeed (carriageReturn h'))
    | exact set_ground (reverseIndex h')
    | -- DECSC: save cursor + ground
      exact
        ⟨cp, rp, cl, rl, cx, cy, cx, cy, ac, tl, bl, sb, u8, (fun _ heq => nomatch heq),
          (fun _ _ heq => nomatch heq)⟩
    | -- DECRC: restore cursor + ground
      exact
        ⟨cp, rp, cl, rl, sx, sy, sx, sy, ac, tl, bl, sb, u8, (fun _ heq => nomatch heq),
          (fun _ _ heq => nomatch heq)⟩
    | -- HTS: tabs + ground
      exact
        ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, (fun _ heq => nomatch heq),
          (fun _ _ heq => nomatch heq)⟩
    | -- RIS: fresh screen, scrollback conditionally carried
      ( dsimp only
        split
        · exact set_sb _ sb (good_init v.cols v.rows)
        · exact set_sb _ (by simp [Ring.size]) (good_init v.cols v.rows))
    | ( repeat' split
        all_goals
          first
          | exact set_pstate_escInter _ h'
          | exact set_ground h'
          | exact h')

theorem stepEscInter {v : Vt} (i b : UInt8) (h : Good v) : Good (v.stepEscInter i b) := by
  unfold Vt.stepEscInter
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, -, -⟩ := h
  dsimp only
  repeat' split
  all_goals
    exact
      ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, (fun _ heq => nomatch heq),
        (fun _ _ heq => nomatch heq)⟩

theorem stepCsi {v : Vt} (s : CsiState) (b : UInt8) (hs : s.params.size ≤ 16) (h : Good v) :
    Good (v.stepCsi s b) := by
  unfold Vt.stepCsi
  repeat' split
  all_goals
    first
    | exact h
    | exact set_pstate_csi _ hs h
    | exact set_pstate_csi _ (csiPush_le s _ hs) h
    | exact csiFinish _ _ h
    | exact set_pstate_esc h
    | exact ctl _ h
    | exact set_ground h

theorem stepOsc {v : Vt} (acc : Array UInt8) (e : Bool) (b : UInt8) (hacc : acc.size ≤ 2048)
    (h : Good v) : Good (v.stepOsc acc e b) := by
  unfold Vt.stepOsc
  split
  · exact oscFinish _ h
  · split
    · exact oscFinish _ h
    · split
      · exact set_pstate_osc _ _ hacc h
      · split
        · exact set_pstate_osc _ _ hacc h
        · rename_i hlt
          refine set_pstate_osc _ _ ?_ h
          simp only [Array.size_push]
          omega

theorem stepStr {v : Vt} (e : Bool) (b : UInt8) (h : Good v) : Good (v.stepStr e b) := by
  unfold Vt.stepStr
  split
  · exact set_ground h
  · split
    · exact set_pstate_str _ h
    · exact set_pstate_str _ h

/-! ## §Total + §Bound, one byte and a whole stream -/

/-- `step` preserves the composite invariant for ANY byte: the cursor
and every stashed cursor stay in bounds, and no buffer exceeds its cap.
This is the §Bound theorem at the emulator layer. -/
theorem step {v : Vt} (b : UInt8) (h : Good v) : Good (v.step b) := by
  unfold Vt.step Vt.abortUtf8
  dsimp only
  by_cases hc : (v.u8need > 0 && (b < 0x80 || b ≥ 0xC0)) = true
  · rw [ite_eq_left hc]
    have h' := set_u8 0 0 (by omega) h
    split
    all_goals
      first
      | exact stepGround _ h'
      | exact stepEsc _ h'
      | exact stepEscInter _ _ h'
      | (rename_i heq; exact stepCsi _ _ (h'.csiLe _ heq) h')
      | (rename_i heq; exact stepOsc _ _ _ (h'.oscLe _ _ heq) h')
      | exact stepStr _ _ h'
  · rw [ite_eq_right hc]
    split
    all_goals
      first
      | exact stepGround _ h
      | exact stepEsc _ h
      | exact stepEscInter _ _ h
      | (rename_i heq; exact stepCsi _ _ (h.csiLe _ heq) h)
      | (rename_i heq; exact stepOsc _ _ _ (h.oscLe _ _ heq) h)
      | exact stepStr _ _ h

/-- The stream form: any byte stream, fed to a Good `Vt`, leaves it
Good. With `Vt.init`'s `good_init` this covers every state the daemon
can ever hold. -/
theorem feed {v : Vt} (bytes : List UInt8) (h : Good v) : Good (v.feed bytes) :=
  good_foldl (fun _ b hh => step b hh) bytes h

/-- Resize lands Good regardless of requested dimensions. -/
theorem resize {v : Vt} (cols rows : Nat) (h : Good v) : Good (v.resize cols rows) := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h
  unfold Vt.resize
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, sb, u8, hcsi, hosc⟩
  · simp [clampDim] <;> omega
  · simp [clampDim] <;> omega
  · simp [clampDim] <;> omega
  · simp [clampDim] <;> omega
  · simp [clampDim] <;> omega
  · simp [clampDim] <;> omega
  · simp [clampDim] <;> omega
  · simp [clampDim] <;> omega
  · intro g c p heq
    simp only at heq
    rcases hv : v.altGrid with - | x
    · rw [hv] at heq
      exact nomatch heq
    · obtain ⟨g0, c0, p0⟩ := x
      rw [hv] at heq
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at heq
      obtain ⟨-, hcc, -⟩ := heq
      subst hcc
      constructor
      · simp [clampDim] <;> omega
      · simp [clampDim] <;> omega
  · simp [clampDim] <;> omega
  · simp [clampDim] <;> omega

/-! ## §Chunk — re-chunking invariance, definitional by design -/

/-- Feeding `a ++ b` is feeding `a` then `b`. `Vt.feed` is a `foldl`,
so this is `List.foldl_append` — stated so a future rewrite of `feed`
into something chunk-sensitive cannot survive the build. -/
theorem feed_append (v : Vt) (a b : List UInt8) : v.feed (a ++ b) = (v.feed a).feed b := by
  simp [Vt.feed]

/-- Byte-at-a-time equals one-shot: the strongest §Chunk corollary
(any chunking refines to single bytes). -/
theorem feed_singletons (v : Vt) (bytes : List UInt8) :
    v.feed bytes = bytes.foldl (fun acc b => acc.feed [b]) v := by
  induction bytes generalizing v with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldl_cons, ← ih]
    rfl

end Linger.Core.Vt.Good

namespace Linger.Core.Vt

/-! ## Frames: the generalization of the four invariance layers

`pstate`, `u8need`, `dims` and `origin` above are ~110 lemmas that are
~28 written four times: "operation X does not write field F". The general
statement is a **frame condition** — X's footprint, stated once, covering
every field at once:

```
theorem frame_putCell : v.putCell x y c = { v with grid := (v.putCell x y c).grid }
```

Read: *`putCell` writes only `grid`*. Every field invariance is then a
corollary by rewriting, including fields nobody has thought of yet — so a
fifth layer costs nothing instead of another 28 lemmas.

Why this beats the two ideas recorded in THEOREMS.md:

* Better than *bundling* the four fields, which fixes only the fields we
  happened to need.
* Better than *splitting* `Vt` into `{screen, parser, meta}`, because the
  read/write distinction is **per-operation**: `print` reads `cols`/`rows`
  to clamp and reads `modes` for wrap/insert while writing neither, so a
  partition that groups `dims` with the cells still lets `Screen → Screen`
  resize the grid. The refactor that *would* capture it moves read-only
  data into parameter position (`print : Dims → Modes → … `), which is far
  larger and mostly subsumed by frames anyway.

What frames do **not** buy, and this is the honest limit: a frame says
what an operation leaves alone, never what the written fields *become*.
Grid fidelity (§Replay stage 3d — the replayed cells equal the saved
cells) needs the positive specification, which is real content, not
bookkeeping. Frames retire the sprawl; they do not shorten the road to
3d.

The leaf frames also supply the step hypothesis for `frame_grid_foldl`:
an exact frame is itself an invariant, preserved by overwriting the grid.
This extends the frame to line edits and screen erasure without changing
the state representation or introducing a field-set calculus. Printing uses
the existing `offScreen` observation to compose its stages; dispatch retains
conditional claims for operations such as `RIS` and `setMode`.
-/

/-- Pure record update: `rfl` suffices. -/
theorem frame_putCell (v : Vt) (x y : Nat) (c : Cell) :
    v.putCell x y c = { v with grid := (v.putCell x y c).grid } := by rfl

theorem frame_moveTo (v : Vt) (x y : Nat) :
    v.moveTo x y = { v with cursor := (v.moveTo x y).cursor } := by rfl

theorem frame_eraseRowSpan (v : Vt) (y a b : Nat) :
    v.eraseRowSpan y a b = { v with grid := (v.eraseRowSpan y a b).grid } := by rfl

/-- Branching operation: one `split`, both branches record updates.
`scrollUpIn` may also push the evicted line to scrollback. -/
theorem frame_scrollUpIn (v : Vt) (t b : Nat) (a : Bool) :
    v.scrollUpIn t b a =
      { v with
        grid := (v.scrollUpIn t b a).grid, sb := (v.scrollUpIn t b a).sb } := by
  unfold Vt.scrollUpIn; dsimp only; split <;> rfl

/-- Composite over stages: `lineFeed` moves the cursor and may scroll. -/
theorem frame_lineFeed (v : Vt) :
    v.lineFeed =
      { v with
        grid := v.lineFeed.grid, cursor := v.lineFeed.cursor, sb := v.lineFeed.sb } := by
  unfold Vt.lineFeed Vt.scrollUp Vt.scrollUpIn Vt.clearPending
  dsimp only
  repeat' split
  all_goals rfl

/-! ### The collapse, demonstrated

Each of these four is an instance of the layers above — and each is now a
one-line consequence of a single frame, for *any* field rather than a
chosen one. -/

example (v : Vt) (t b : Nat) (a : Bool) : (v.scrollUpIn t b a).pstate = v.pstate := by
  rw [frame_scrollUpIn]

example (v : Vt) (t b : Nat) (a : Bool) : (v.scrollUpIn t b a).u8need = v.u8need := by
  rw [frame_scrollUpIn]

example (v : Vt) (t b : Nat) (a : Bool) : (v.scrollUpIn t b a).cols = v.cols := by
  rw [frame_scrollUpIn]

example (v : Vt) (t b : Nat) (a : Bool) : (v.scrollUpIn t b a).modes.origin = v.modes.origin := by
  rw [frame_scrollUpIn]

/-- …and a field no layer ever covered, free: the scroll region. -/
example (v : Vt) (t b : Nat) (a : Bool) : (v.scrollUpIn t b a).top = v.top := by
  rw [frame_scrollUpIn]

/-- …and the saved-cursor slot, also free. -/
example (v : Vt) : v.lineFeed.saved = v.saved := by rw [frame_lineFeed]

end Linger.Core.Vt

namespace Linger.Core.Vt

/-! ### The frame set for the leaf operations

One frame per operation, replacing what was four single-field lemmas
each. Every field invariance — including fields no layer covers — is one
`rw` away, so a new field costs nothing here.

Leaf updates prove directly by reduction. The folds below instead use the
same step frames as hypotheses of `invariant_foldl`; their final values do
not need to reduce to syntactic record updates.
-/

theorem frame_clearPending (v : Vt) :
    v.clearPending = { v with cursor := v.clearPending.cursor } := by rfl

theorem frame_carriageReturn (v : Vt) :
    v.carriageReturn = { v with cursor := v.carriageReturn.cursor } := by rfl

theorem frame_moveRel (v : Vt) (dx dy : Int) :
    v.moveRel dx dy = { v with cursor := (v.moveRel dx dy).cursor } := by rfl

theorem frame_setCol (v : Vt) (x : Nat) :
    v.setCol x = { v with cursor := (v.setCol x).cursor } := by rfl

theorem frame_scrollDownIn (v : Vt) (t b : Nat) :
    v.scrollDownIn t b = { v with grid := (v.scrollDownIn t b).grid } := by rfl

theorem frame_deleteChars (v : Vt) (n : Nat) :
    v.deleteChars n = { v with grid := (v.deleteChars n).grid } := by rfl

theorem frame_insertChars (v : Vt) (n : Nat) :
    v.insertChars n = { v with grid := (v.insertChars n).grid } := by rfl

theorem frame_applySgr (v : Vt) (ps : List (Nat × Bool)) :
    v.applySgr ps = { v with pen := (v.applySgr ps).pen } := by rfl

theorem frame_backTab (v : Vt) : v.backTab = { v with cursor := v.backTab.cursor } := by rfl

theorem frame_eraseChars (v : Vt) (n : Nat) :
    v.eraseChars n = { v with grid := (v.eraseChars n).grid } := by rfl

theorem frame_backspace (v : Vt) : v.backspace = { v with cursor := v.backspace.cursor } := by
  unfold Vt.backspace; split <;> rfl

theorem frame_tab (v : Vt) : v.tab = { v with cursor := v.tab.cursor } := by
  unfold Vt.tab Vt.clearPending; dsimp only

theorem frame_eraseLine (v : Vt) (m : Nat) :
    v.eraseLine m = { v with grid := (v.eraseLine m).grid } := by
  unfold Vt.eraseLine; repeat' split
  all_goals rfl

/-- Iterating grid-only updates preserves the exact complement of the grid.
The invariant is a record equation; successive grid replacements compose. -/
theorem frame_grid_foldl {α : Type} (f : Vt → α → Vt)
    (hf : ∀ w a, f w a = { w with grid := (f w a).grid }) (l : List α) (v : Vt) :
    l.foldl f v = { v with grid := (l.foldl f v).grid } := by
  refine invariant_foldl (fun w => w = { v with grid := w.grid }) f ?_ l v rfl
  intro w a hw
  exact (hf w a).trans (congrArg (fun u => { u with grid := (f w a).grid }) hw)

/-- Inserting lines leaves the cursor, history and all metadata unchanged,
even for an arbitrary incoming record. -/
theorem frame_insertLines (v : Vt) (n : Nat) :
    v.insertLines n = { v with grid := (v.insertLines n).grid } := by
  unfold Vt.insertLines
  dsimp only
  split
  · rfl
  · exact frame_grid_foldl _ (fun w _ => frame_scrollDownIn w _ _) _ _

/-- Deleting lines never adds history, including at the full-screen region. -/
theorem frame_deleteLines (v : Vt) (n : Nat) :
    v.deleteLines n = { v with grid := (v.deleteLines n).grid } := by
  unfold Vt.deleteLines
  dsimp only
  split
  · rfl
  · exact frame_grid_foldl _ (fun _ _ => rfl) _ _

/-- Screen erasure writes only cells and, in mode 3, clears the history.
Every other field, including complete tab contents and saved state, is exact. -/
theorem frame_eraseScreen (v : Vt) (m : Nat) :
    v.eraseScreen m =
      { v with
        grid := (v.eraseScreen m).grid, sb := if m = 3 then {} else v.sb } := by
  unfold Vt.eraseScreen
  split
  · exact
      (frame_grid_foldl _ (fun w _ => frame_eraseRowSpan w _ _ _) _ _).trans
        (congrArg (fun (w : Vt) => { w with grid := (v.eraseScreen 0).grid }) (frame_eraseLine v 0))
  · exact
      (frame_grid_foldl _ (fun w _ => frame_eraseRowSpan w _ _ _) _ _).trans
        (congrArg (fun (w : Vt) => { w with grid := (v.eraseScreen 1).grid }) (frame_eraseLine v 1))
  · exact
      congrArg (fun w => { w with sb := {} })
        (frame_grid_foldl _ (fun w _ => frame_eraseRowSpan w _ _ _) _ _)
  · simpa only [ite_eq_right (by assumption : m ≠ 3)] using
      (frame_grid_foldl _ (fun w _ => frame_eraseRowSpan w _ _ _) _ v)

theorem frame_reverseIndex (v : Vt) :
    v.reverseIndex =
      { v with
        grid := v.reverseIndex.grid, cursor := v.reverseIndex.cursor } := by
  unfold Vt.reverseIndex Vt.scrollDown Vt.scrollDownIn Vt.clearPending
  dsimp only
  repeat' split
  all_goals rfl

theorem frame_printWrap (v : Vt) :
    v.printWrap =
      { v with
        grid := v.printWrap.grid, cursor := v.printWrap.cursor, sb := v.printWrap.sb } := by
  unfold Vt.printWrap Vt.carriageReturn Vt.lineFeed Vt.clearPending Vt.scrollUp Vt.scrollUpIn
  dsimp only
  repeat' split
  all_goals rfl

theorem frame_printWideWrap (v : Vt) (w : Nat) :
    v.printWideWrap w =
      { v with
        grid := (v.printWideWrap w).grid, cursor := (v.printWideWrap w).cursor,
        sb := (v.printWideWrap w).sb } := by
  unfold Vt.printWideWrap Vt.carriageReturn Vt.lineFeed Vt.clearPending Vt.scrollUp Vt.scrollUpIn
  dsimp only
  repeat' split
  all_goals rfl

theorem frame_printShift (v : Vt) (w : Nat) :
    v.printShift w = { v with grid := (v.printShift w).grid } := by
  unfold Vt.printShift; dsimp only; split <;> rfl

/-- Wide-pair repair writes only the grid. One frame covers all four layers
below, plus any field a later one adds. -/
theorem frame_mendAt (v : Vt) (x y : Nat) :
    v.mendAt x y = { v with grid := (v.mendAt x y).grid } := by rfl

theorem frame_mendRow (v : Vt) (y : Nat) : v.mendRow y = { v with grid := (v.mendRow y).grid } := by
  rfl

theorem frame_printPut (v : Vt) (ch : Char) (w : Nat) :
    v.printPut ch w = { v with grid := (v.printPut ch w).grid } := by
  unfold Vt.printPut
  dsimp only
  repeat' split
  all_goals (rw [frame_mendRow]; rfl)

theorem frame_printMark (v : Vt) (ch : Char) :
    v.printMark ch = { v with grid := (v.printMark ch).grid } := by
  unfold Vt.printMark
  dsimp only
  repeat' split
  all_goals
    first
    | rfl
    | (rw [frame_mendRow]; rfl)

theorem frame_printAdvance (v : Vt) (w : Nat) :
    v.printAdvance w = { v with cursor := (v.printAdvance w).cursor } := by
  unfold Vt.printAdvance; dsimp only; split <;> rfl

theorem frame_enterAlt (v : Vt) (s : Bool) :
    v.enterAlt s =
      { v with
        grid := (v.enterAlt s).grid, cursor := (v.enterAlt s).cursor, saved := (v.enterAlt s).saved,
        altGrid := (v.enterAlt s).altGrid, top := (v.enterAlt s).top,
        bot := (v.enterAlt s).bot } := by
  unfold Vt.enterAlt; dsimp only; split <;> rfl

theorem frame_leaveAlt (v : Vt) (s : Bool) :
    v.leaveAlt s =
      { v with
        grid := (v.leaveAlt s).grid, cursor := (v.leaveAlt s).cursor, pen := (v.leaveAlt s).pen,
        altGrid := (v.leaveAlt s).altGrid, top := (v.leaveAlt s).top,
        bot := (v.leaveAlt s).bot } := by
  unfold Vt.leaveAlt; split <;> rfl

theorem frame_stepEscInter (v : Vt) (i b : UInt8) :
    v.stepEscInter i b =
      { v with
        pstate := (v.stepEscInter i b).pstate, g0Line := (v.stepEscInter i b).g0Line,
        g1Line := (v.stepEscInter i b).g1Line } := by
  unfold Vt.stepEscInter; dsimp only; repeat' split
  all_goals rfl

theorem frame_stepStr (v : Vt) (e : Bool) (b : UInt8) :
    v.stepStr e b = { v with pstate := (v.stepStr e b).pstate } := by
  unfold Vt.stepStr; repeat' split
  all_goals rfl

theorem frame_oscFinish (v : Vt) (acc : Array UInt8) :
    v.oscFinish acc =
      { v with
        pstate := (v.oscFinish acc).pstate, title := (v.oscFinish acc).title } := by
  unfold Vt.oscFinish; dsimp only; repeat' split
  all_goals rfl

end Linger.Core.Vt

namespace Linger.Core.Vt

/-! ### The cut `print` induces — everything it does not write

Each print stage writes only `grid`, `cursor` or `sb`. The existing `offScreen`
observation contains their exact complement, so its stage equalities compose
by transitivity. All printing layers below project this one contract, including
the row painter's pen and mode claims and the byte decoder's accumulator.
Neither a monolithic unfold nor another state partition is needed. -/

structure OffScreen where
  cols : Nat
  rows : Nat
  pen : Pen
  modes : Modes
  top : Nat
  bot : Nat
  tabs : Array Bool
  saved : Saved
  title : String
  g0 : Bool
  g1 : Bool
  so : Bool
  alt : Option (Array Row × Cursor × Pen)
  pstate : PState
  u8need : Nat
  u8acc : Nat
  bell : Bool

def offScreen (v : Vt) : OffScreen :=
  { cols := v.cols, rows := v.rows, pen := v.pen, modes := v.modes, top := v.top, bot := v.bot,
    tabs := v.tabs, saved := v.saved, title := v.title, g0 := v.g0Line, g1 := v.g1Line,
    so := v.shiftOut, alt := v.altGrid, pstate := v.pstate, u8need := v.u8need, u8acc := v.u8acc,
    bell := v.bell }

/-! The stages, one `rw` each — the payoff of the frames pass. -/

theorem off_printWrap (v : Vt) : offScreen v.printWrap = offScreen v := by
  rw [frame_printWrap]; rfl

theorem off_printWideWrap (v : Vt) (w : Nat) : offScreen (v.printWideWrap w) = offScreen v := by
  rw [frame_printWideWrap]; rfl

theorem off_printShift (v : Vt) (w : Nat) : offScreen (v.printShift w) = offScreen v := by
  rw [frame_printShift]; rfl

theorem off_printPut (v : Vt) (ch : Char) (w : Nat) :
    offScreen (v.printPut ch w) = offScreen v := by
  rw [frame_printPut]; rfl

theorem off_printAdvance (v : Vt) (w : Nat) : offScreen (v.printAdvance w) = offScreen v := by
  rw [frame_printAdvance]; rfl

theorem off_printMark (v : Vt) (ch : Char) : offScreen (v.printMark ch) = offScreen v := by
  rw [frame_printMark]; rfl

/-- Printing preserves every field outside the grid, cursor and history. -/
theorem off_print (v : Vt) (ch : Char) : offScreen (v.print ch) = offScreen v := by
  unfold Vt.print
  dsimp only
  split
  · exact off_printMark _ _
  · exact
      ((((off_printAdvance _ _).trans (off_printPut _ _ _)).trans (off_printShift _ _)).trans
            (off_printWideWrap _ _)).trans
        (off_printWrap _)

/-! The corollaries the row induction asks for. Each is a `congrArg`, so a field the
next layer wants costs one line rather than a proof. -/

theorem pen_print (v : Vt) (ch : Char) : (v.print ch).pen = v.pen :=
  congrArg OffScreen.pen (off_print v ch)

theorem modes_print' (v : Vt) (ch : Char) : (v.print ch).modes = v.modes :=
  congrArg OffScreen.modes (off_print v ch)

theorem ins_print (v : Vt) (ch : Char) : (v.print ch).modes.insert = v.modes.insert :=
  congrArg Modes.insert (modes_print' v ch)

theorem wrap_print (v : Vt) (ch : Char) : (v.print ch).modes.wrap = v.modes.wrap :=
  congrArg Modes.wrap (modes_print' v ch)

theorem cols_print (v : Vt) (ch : Char) : (v.print ch).cols = v.cols :=
  congrArg OffScreen.cols (off_print v ch)

theorem rows_print (v : Vt) (ch : Char) : (v.print ch).rows = v.rows :=
  congrArg OffScreen.rows (off_print v ch)

theorem g0_print (v : Vt) (ch : Char) : (v.print ch).g0Line = v.g0Line :=
  congrArg OffScreen.g0 (off_print v ch)

theorem g1_print (v : Vt) (ch : Char) : (v.print ch).g1Line = v.g1Line :=
  congrArg OffScreen.g1 (off_print v ch)

theorem so_print (v : Vt) (ch : Char) : (v.print ch).shiftOut = v.shiftOut :=
  congrArg OffScreen.so (off_print v ch)

theorem ua_print' (v : Vt) (ch : Char) : (v.print ch).u8acc = v.u8acc :=
  congrArg OffScreen.u8acc (off_print v ch)

/-! ## Parser-state invariance of the printing path

Feeding a *printable* byte must not disturb the parser: only ESC (and
the sequence states it opens) may change `pstate`. That is obvious by
inspection of the code — no printing or cursor operation mentions
`pstate` — but "obvious by inspection" is what these lemmas replace.

They are the missing rung under §Replay stage 3b
(`Theorems/Render.lean`): a restore stream's grid repaint is a long run
of printable bytes, and the theorem that a restore leaves the parser
quiesced needs each of them to be parser-neutral.

Leaf frames and `off_print` supply the printing path's invariance;
the byte parser then combines it with its control-byte cases.
-/

theorem ps_clearPending (v : Vt) : v.clearPending.pstate = v.pstate := by rfl

theorem ps_carriageReturn (v : Vt) : v.carriageReturn.pstate = v.pstate := by rfl

theorem ps_putCell (v : Vt) (x y : Nat) (c : Cell) : (v.putCell x y c).pstate = v.pstate := by rfl

theorem ps_moveTo (v : Vt) (x y : Nat) : (v.moveTo x y).pstate = v.pstate := by rfl

theorem ps_moveRel (v : Vt) (dx dy : Int) : (v.moveRel dx dy).pstate = v.pstate := by rfl

theorem ps_setCol (v : Vt) (x : Nat) : (v.setCol x).pstate = v.pstate := by rfl

theorem ps_scrollDownIn (v : Vt) (t b : Nat) : (v.scrollDownIn t b).pstate = v.pstate := by rfl

theorem ps_eraseRowSpan (v : Vt) (y a b : Nat) : (v.eraseRowSpan y a b).pstate = v.pstate := by rfl

theorem ps_scrollUpIn (v : Vt) (t b : Nat) (a : Bool) : (v.scrollUpIn t b a).pstate = v.pstate := by
  unfold Vt.scrollUpIn; dsimp only; split <;> rfl

theorem ps_scrollUp (v : Vt) : v.scrollUp.pstate = v.pstate := ps_scrollUpIn _ _ _ _

theorem ps_scrollDown (v : Vt) : v.scrollDown.pstate = v.pstate := ps_scrollDownIn _ _ _

theorem ps_lineFeed (v : Vt) : v.lineFeed.pstate = v.pstate := by rw [frame_lineFeed]

theorem ps_reverseIndex (v : Vt) : v.reverseIndex.pstate = v.pstate := by rw [frame_reverseIndex]

theorem ps_backspace (v : Vt) : v.backspace.pstate = v.pstate := by
  unfold Vt.backspace; split <;> rfl

theorem ps_tab (v : Vt) : v.tab.pstate = v.pstate := by
  unfold Vt.tab; dsimp only; exact ps_clearPending v

theorem ps_printWrap (v : Vt) : v.printWrap.pstate = v.pstate := by rw [frame_printWrap]

theorem ps_printWideWrap (v : Vt) (w : Nat) : (v.printWideWrap w).pstate = v.pstate := by
  rw [frame_printWideWrap]

theorem ps_printShift (v : Vt) (w : Nat) : (v.printShift w).pstate = v.pstate := by
  unfold Vt.printShift; dsimp only; split <;> rfl

theorem ps_mendRow (v : Vt) (y : Nat) : (v.mendRow y).pstate = v.pstate := by rw [frame_mendRow]

theorem ps_printPut (v : Vt) (ch : Char) (w : Nat) : (v.printPut ch w).pstate = v.pstate := by
  unfold Vt.printPut
  dsimp only
  repeat' split
  all_goals (rw [ps_mendRow]; rfl)

theorem ps_printAdvance (v : Vt) (w : Nat) : (v.printAdvance w).pstate = v.pstate := by
  unfold Vt.printAdvance; dsimp only; split <;> rfl

/-- The composite: printing a glyph never touches the parser. -/
theorem ps_printMark (v : Vt) (ch : Char) : (v.printMark ch).pstate = v.pstate := by
  rw [frame_printMark]

theorem ps_print (v : Vt) (c : Char) : (v.print c).pstate = v.pstate :=
  congrArg OffScreen.pstate (off_print v c)

theorem ps_acceptChar (v : Vt) (n : Nat) : (v.acceptChar n).pstate = v.pstate := by
  unfold Vt.acceptChar; split <;> exact ps_print _ _

/-- Printing preserves the UTF-8 accumulator, so a run of glyphs retains the
decoder's precondition between cells. The `u8need` twin is `un_print`. -/
theorem ua_print (v : Vt) (c : Char) : (v.print c).u8acc = v.u8acc :=
  congrArg OffScreen.u8acc (off_print v c)

theorem ua_acceptChar (v : Vt) (n : Nat) : (v.acceptChar n).u8acc = v.u8acc := by
  unfold Vt.acceptChar; split <;> exact ua_print _ _

/-- A C0 control byte executes without changing the parser state. -/
theorem ps_ctl (v : Vt) (b : UInt8) : (v.ctl b).pstate = v.pstate := by
  unfold Vt.ctl
  repeat' split
  all_goals
    first
    | exact ps_backspace v
    | exact ps_tab v
    | exact ps_lineFeed v
    | exact ps_carriageReturn v
    | rfl

theorem ps_abortUtf8 (v : Vt) (b : UInt8) : (v.abortUtf8 b).pstate = v.pstate := by
  unfold Vt.abortUtf8; split <;> rfl

/-- §Replay's rung: from `ground`, any byte other than ESC leaves the
parser in `ground`. (`u8need` may change — a UTF-8 lead byte — which is
why `Ends` tracks it separately.) -/
theorem ps_stepGround (v : Vt) (b : UInt8) (hb : b ≠ 0x1B) :
    (v.stepGround b).pstate = v.pstate := by
  have hesc : (b == 0x1B) = false := beq_eq_false_iff_ne.mpr hb
  unfold Vt.stepGround
  simp only [hesc, Bool.false_eq_true, ite_false]
  repeat' split
  -- rewriting with the stage lemmas is *guided* (matches only the right
  -- shape); a blind `exact` on the wrong branch whnf's the print chain
  all_goals try simp only [ps_ctl, ps_acceptChar]
  all_goals rfl

end Linger.Core.Vt

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
    ∀ (l : List α) (v : Vt), (l.foldl f v).u8need = v.u8need
  | [], _ => rfl
  | a :: as, v => (un_foldl f hf as (f v a)).trans (hf v a)

theorem un_clearPending (v : Vt) : v.clearPending.u8need = v.u8need := by rfl

theorem un_carriageReturn (v : Vt) : v.carriageReturn.u8need = v.u8need := by rfl

theorem un_moveTo (v : Vt) (x y : Nat) : (v.moveTo x y).u8need = v.u8need := by rfl

theorem un_moveRel (v : Vt) (dx dy : Int) : (v.moveRel dx dy).u8need = v.u8need := by rfl

theorem un_setCol (v : Vt) (x : Nat) : (v.setCol x).u8need = v.u8need := by rfl

theorem un_putCell (v : Vt) (x y : Nat) (c : Cell) : (v.putCell x y c).u8need = v.u8need := by rfl

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

/-- Mode-preserving operations remain mode-preserving over any fold. -/
theorem modes_foldl {α : Type} (f : Vt → α → Vt) (hf : ∀ v a, (f v a).modes = v.modes) :
    ∀ (l : List α) (v : Vt), (l.foldl f v).modes = v.modes
  | [], _ => rfl
  | a :: as, v => (modes_foldl f hf as (f v a)).trans (hf v a)

theorem modes_eraseRowSpan (v : Vt) (y a b : Nat) : (v.eraseRowSpan y a b).modes = v.modes := by
  rw [frame_eraseRowSpan]

theorem modes_eraseLine (v : Vt) (m : Nat) : (v.eraseLine m).modes = v.modes := by
  rw [frame_eraseLine]

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

theorem un_printWrap (v : Vt) : v.printWrap.u8need = v.u8need := by rw [frame_printWrap]

theorem un_printWideWrap (v : Vt) (w : Nat) : (v.printWideWrap w).u8need = v.u8need := by
  rw [frame_printWideWrap]

theorem un_printShift (v : Vt) (w : Nat) : (v.printShift w).u8need = v.u8need := by
  unfold Vt.printShift; dsimp only; split <;> rfl

theorem un_mendRow (v : Vt) (y : Nat) : (v.mendRow y).u8need = v.u8need := by rw [frame_mendRow]

theorem un_printPut (v : Vt) (ch : Char) (w : Nat) : (v.printPut ch w).u8need = v.u8need := by
  unfold Vt.printPut
  dsimp only
  repeat' split
  all_goals (rw [un_mendRow]; rfl)

theorem un_printAdvance (v : Vt) (w : Nat) : (v.printAdvance w).u8need = v.u8need := by
  unfold Vt.printAdvance; dsimp only; split <;> rfl

theorem un_printMark (v : Vt) (ch : Char) : (v.printMark ch).u8need = v.u8need := by
  rw [frame_printMark]

theorem un_print (v : Vt) (c : Char) : (v.print c).u8need = v.u8need :=
  congrArg OffScreen.u8need (off_print v c)

theorem un_acceptChar (v : Vt) (n : Nat) : (v.acceptChar n).u8need = v.u8need := by
  unfold Vt.acceptChar; split <;> exact un_print _ _

theorem un_ctl (v : Vt) (b : UInt8) : (v.ctl b).u8need = v.u8need := by
  unfold Vt.ctl
  repeat' split
  all_goals
    first
    | exact un_backspace v
    | exact un_tab v
    | exact un_lineFeed v
    | exact un_carriageReturn v
    | rfl

theorem un_csiDispatch (v : Vt) (s : CsiState) (final : UInt8) :
    (v.csiDispatch s final).u8need = v.u8need := by
  unfold Vt.csiDispatch
  dsimp only
  repeat' split
  all_goals
    try
      simp only [un_insertChars, un_moveRel, un_carriageReturn, un_setCol, un_moveTo,
        un_eraseScreen, un_eraseLine, un_insertLines, un_deleteLines, un_deleteChars, un_eraseChars,
        un_setModes, un_applySgr]
  all_goals
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
    ∀ (l : List α) (v : Vt), (l.foldl f v).u8acc = v.u8acc
  | [], _ => rfl
  | a :: as, v => (ua_foldl f hf as (f v a)).trans (hf v a)

theorem ua_clearPending (v : Vt) : v.clearPending.u8acc = v.u8acc := by rfl

theorem ua_carriageReturn (v : Vt) : v.carriageReturn.u8acc = v.u8acc := by rfl

theorem ua_moveTo (v : Vt) (x y : Nat) : (v.moveTo x y).u8acc = v.u8acc := by rfl

theorem ua_moveRel (v : Vt) (dx dy : Int) : (v.moveRel dx dy).u8acc = v.u8acc := by rfl

theorem ua_setCol (v : Vt) (x : Nat) : (v.setCol x).u8acc = v.u8acc := by rfl

theorem ua_putCell (v : Vt) (x y : Nat) (c : Cell) : (v.putCell x y c).u8acc = v.u8acc := by rfl

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

theorem ua_printWrap (v : Vt) : v.printWrap.u8acc = v.u8acc := by rw [frame_printWrap]

theorem ua_printWideWrap (v : Vt) (w : Nat) : (v.printWideWrap w).u8acc = v.u8acc := by
  rw [frame_printWideWrap]

theorem ua_printShift (v : Vt) (w : Nat) : (v.printShift w).u8acc = v.u8acc := by
  unfold Vt.printShift; dsimp only; split <;> rfl

theorem ua_mendRow (v : Vt) (y : Nat) : (v.mendRow y).u8acc = v.u8acc := by rw [frame_mendRow]

theorem ua_printPut (v : Vt) (ch : Char) (w : Nat) : (v.printPut ch w).u8acc = v.u8acc := by
  unfold Vt.printPut
  dsimp only
  repeat' split
  all_goals (rw [ua_mendRow]; rfl)

theorem ua_printAdvance (v : Vt) (w : Nat) : (v.printAdvance w).u8acc = v.u8acc := by
  unfold Vt.printAdvance; dsimp only; split <;> rfl

theorem ua_printMark (v : Vt) (ch : Char) : (v.printMark ch).u8acc = v.u8acc := by
  rw [frame_printMark]

theorem ua_ctl (v : Vt) (b : UInt8) : (v.ctl b).u8acc = v.u8acc := by
  unfold Vt.ctl
  repeat' split
  all_goals
    first
    | exact ua_backspace v
    | exact ua_tab v
    | exact ua_lineFeed v
    | exact ua_carriageReturn v
    | rfl

theorem ua_csiDispatch (v : Vt) (s : CsiState) (final : UInt8) :
    (v.csiDispatch s final).u8acc = v.u8acc := by
  unfold Vt.csiDispatch
  dsimp only
  repeat' split
  all_goals
    try
      simp only [ua_insertChars, ua_moveRel, ua_carriageReturn, ua_setCol, ua_moveTo,
        ua_eraseScreen, ua_eraseLine, ua_insertLines, ua_deleteLines, ua_deleteChars, ua_eraseChars,
        ua_setModes, ua_applySgr]
  all_goals
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
    first
    | exact Or.inl ⟨rfl, rfl⟩
    | exact Or.inr ⟨rfl, rfl⟩
    | exact Or.inl ⟨un_lineFeed _, ua_lineFeed _⟩
    |
      exact
        Or.inl
          ⟨(un_lineFeed _).trans (un_carriageReturn _), (ua_lineFeed _).trans (ua_carriageReturn _)⟩
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
theorem uaz_step {v : Vt} (b : UInt8) (hb : b < 0x80) (hn : v.u8need = 0) (h : v.u8acc = 0) :
    (v.step b).u8acc = 0 := by
  have hab : (v.abortUtf8 b).u8acc = 0 := by
    unfold Vt.abortUtf8
    split
    · rfl
    · exact h
  have habn : (v.abortUtf8 b).u8need = 0 := by
    unfold Vt.abortUtf8
    split
    · rfl
    · exact hn
  unfold Vt.step
  dsimp only
  split
  all_goals try simp only [ua_stepEscInter, ua_stepCsi, ua_stepOsc, ua_stepStr]
  all_goals
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
    rw [show v.feed (b :: bs) = (v.step b).feed bs from rfl]
    exact
      uaz_feed bs (fun x hx => hb x (List.mem_cons_of_mem b hx))
        (uz_step b (ascii_lt_c0 (hb b (List.mem_cons_self))) hn)
        (uaz_step b (hb b (List.mem_cons_self)) hn ha)

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
    first
    | exact hab
    | exact uz_stepGround _ (by decide) hab
    | exact uz_stepEsc _ hab

/-- A run of non-lead bytes keeps `u8need` at zero. -/
theorem uz_feed :
    ∀ (bs : List UInt8) (v : Vt), (∀ b ∈ bs, b < 0xC0) → v.u8need = 0 → (v.feed bs).u8need = 0
  | [], _, _, h => h
  | x :: xs, v, hb, h => by
    have hstep : v.feed (x :: xs) = (v.step x).feed xs := by simp [Vt.feed]
    rw [hstep]
    exact uz_feed xs _ (fun b hm => hb b (by simp [hm])) (uz_step x (hb x (by simp)) h)

end Linger.Core.Vt

namespace Linger.Core.Vt

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
    ∀ (l : List α) (v : Vt), dims (l.foldl f v) = dims v
  | [], _ => rfl
  | a :: as, v => (dims_foldl f hf as (f v a)).trans (hf v a)

theorem dims_clearPending (v : Vt) : dims v.clearPending = dims v := by rfl

theorem dims_carriageReturn (v : Vt) : dims v.carriageReturn = dims v := by rfl

theorem dims_moveTo (v : Vt) (x y : Nat) : dims (v.moveTo x y) = dims v := by rfl

theorem dims_moveRel (v : Vt) (dx dy : Int) : dims (v.moveRel dx dy) = dims v := by rfl

theorem dims_setCol (v : Vt) (x : Nat) : dims (v.setCol x) = dims v := by rfl

theorem dims_putCell (v : Vt) (x y : Nat) (c : Cell) : dims (v.putCell x y c) = dims v := by rfl

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

theorem dims_printWrap (v : Vt) : dims v.printWrap = dims v := by
  rw [frame_printWrap]
  rfl

theorem dims_printWideWrap (v : Vt) (w : Nat) : dims (v.printWideWrap w) = dims v := by
  rw [frame_printWideWrap]
  rfl

theorem dims_printShift (v : Vt) (w : Nat) : dims (v.printShift w) = dims v := by
  unfold Vt.printShift; dsimp only; split <;> rfl

theorem dims_mendRow (v : Vt) (y : Nat) : dims (v.mendRow y) = dims v := by
  rw [frame_mendRow]; rfl

theorem dims_printPut (v : Vt) (ch : Char) (w : Nat) : dims (v.printPut ch w) = dims v := by
  unfold Vt.printPut
  dsimp only
  repeat' split
  all_goals (rw [dims_mendRow]; rfl)

theorem dims_printAdvance (v : Vt) (w : Nat) : dims (v.printAdvance w) = dims v := by
  unfold Vt.printAdvance; dsimp only; split <;> rfl

theorem dims_printMark (v : Vt) (ch : Char) : dims (v.printMark ch) = dims v := by
  rw [frame_printMark]; rfl

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
  have hcp := h.colsPos
  have hcl := h.colsLe
  have hrp := h.rowsPos
  have hrl := h.rowsLe
  have hc : clampDim v.cols = v.cols := by
    unfold clampDim; omega
  have hr : clampDim v.rows = v.rows := by
    unfold clampDim; omega
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
  unfold Vt.stepGround
  repeat' split
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
    first
    | exact hd
    | exact (dims_stepEsc _ hg).trans hd

/-- **The dims layer's payoff.** No byte stream changes the grid
dimensions: what a client's emulator is told to paint, it paints at the
size it already had. -/
theorem dims_feed : ∀ (bs : List UInt8) {v : Vt}, Good v → dims (v.feed bs) = dims v
  | [], _, _ => rfl
  | x :: xs, v, h => by
    have hstep : v.feed (x :: xs) = (v.step x).feed xs := by simp [Vt.feed]
    rw [hstep]
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
    first
    | exact hd
    | exact (dims_stepEsc_ne_ris _ h).trans hd

theorem dims_feed_ne_ris :
    ∀ (bs : List UInt8) {v : Vt}, (∀ b ∈ bs, b ≠ 0x63) → dims (v.feed bs) = dims v
  | [], _, _ => rfl
  | x :: xs, v, h => by
    rw [show v.feed (x :: xs) = (v.step x).feed xs from by simp [Vt.feed]]
    exact
      (dims_feed_ne_ris xs (fun b hb => h b (by simp [hb]))).trans
        (dims_step_ne_ris x (h x (by simp)))

/-! ## §Ruler — the tab stops keep pace with the width

The fifth instance of the invariance-layer recipe the `dims`/`org` sections
above set up, and the one `Theorems/Render/Tabs.lean` asked for by name: its
`restore_tabs_reachable` says "proving `tabs.size = cols` an invariant of every
reachable state is a `tabs_*` frame family of its own — worth doing, not needed
here". Here it is, because the harvest is what it is for
(`specs/archive/vt-toolkit.md` Step 3).

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

/-- **A ruler as wide as the screen.** The invariant `Render.restore_tabs_any`
needs of the session it replays: `Render.tabsAnsi` walks `v.cols` columns and
reads `v.tabs`, so a ruler of any other length makes the walk and the array
disagree. `Good` and `Renderable` both say nothing about it — `Good` bounds the
dimensions and `Renderable` speaks of the grid — which is why it is a predicate
of its own rather than a clause of either. -/
def TabsOk (v : Vt) : Prop := v.tabs.size = v.cols

/-- Transfer along the two projections: an operation that moves neither the
ruler's length nor the width keeps them equal. Every arm of the sweep below is
this lemma plus the pair of equations for its operation. -/
theorem TabsOk.transfer {v w : Vt} (h : TabsOk v) (ht : tsz w = tsz v) (hc : dims w = dims v) :
    TabsOk w := by
  unfold TabsOk tsz at *
  rw [ht, show w.cols = v.cols from congrArg Prod.fst hc]
  exact h

theorem tsz_foldl {α : Type} (f : Vt → α → Vt) (hf : ∀ v a, tsz (f v a) = tsz v) :
    ∀ (l : List α) (v : Vt), tsz (l.foldl f v) = tsz v
  | [], _ => rfl
  | a :: as, v => (tsz_foldl f hf as (f v a)).trans (hf v a)

theorem tsz_clearPending (v : Vt) : tsz v.clearPending = tsz v := by rfl

theorem tsz_carriageReturn (v : Vt) : tsz v.carriageReturn = tsz v := by rfl

theorem tsz_moveTo (v : Vt) (x y : Nat) : tsz (v.moveTo x y) = tsz v := by rfl

theorem tsz_moveRel (v : Vt) (dx dy : Int) : tsz (v.moveRel dx dy) = tsz v := by rfl

theorem tsz_setCol (v : Vt) (x : Nat) : tsz (v.setCol x) = tsz v := by rfl

theorem tsz_putCell (v : Vt) (x y : Nat) (c : Cell) : tsz (v.putCell x y c) = tsz v := by rfl

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

theorem tsz_printWrap (v : Vt) : tsz v.printWrap = tsz v := by
  rw [frame_printWrap]
  rfl

theorem tsz_printWideWrap (v : Vt) (w : Nat) : tsz (v.printWideWrap w) = tsz v := by
  rw [frame_printWideWrap]
  rfl

theorem tsz_printShift (v : Vt) (w : Nat) : tsz (v.printShift w) = tsz v := by
  unfold Vt.printShift; dsimp only; split <;> rfl

theorem tsz_mendRow (v : Vt) (y : Nat) : tsz (v.mendRow y) = tsz v := by
  rw [frame_mendRow]; rfl

theorem tsz_printPut (v : Vt) (ch : Char) (w : Nat) : tsz (v.printPut ch w) = tsz v := by
  unfold Vt.printPut
  dsimp only
  repeat' split
  all_goals (rw [tsz_mendRow]; rfl)

theorem tsz_printAdvance (v : Vt) (w : Nat) : tsz (v.printAdvance w) = tsz v := by
  unfold Vt.printAdvance; dsimp only; split <;> rfl

theorem tsz_printMark (v : Vt) (ch : Char) : tsz (v.printMark ch) = tsz v := by
  rw [frame_printMark]; rfl

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
  unfold Vt.stepGround
  repeat' split
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
  unfold Vt.stepCsi
  repeat' split
  all_goals
    first
    | exact h
    | exact tabsOk_csiFinish _ _ h
    | exact h.transfer (tsz_ctl _ _) (dims_ctl _ _)

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
  all_goals
    first
    | exact hab.transfer (tsz_stepGround _ _) (dims_stepGround _ _)
    | exact tabsOk_stepEsc _ hab
    | exact hab.transfer (tsz_stepEscInter _ _ _) (dims_stepEscInter _ _ _)
    | exact tabsOk_stepCsi _ _ hab
    | exact hab.transfer (tsz_stepOsc _ _ _ _) (dims_stepOsc _ _ _ _)
    | exact hab.transfer (tsz_stepStr _ _ _) (dims_stepStr _ _ _)

/-- The stream form. -/
theorem tabsOk_feed : ∀ (bs : List UInt8) {v : Vt}, TabsOk v → TabsOk (v.feed bs)
  | [], _, h => h
  | b :: bs, v, h => by
    rw [show v.feed (b :: bs) = (v.step b).feed bs from rfl]
    exact tabsOk_feed bs (tabsOk_step b h)

end Linger.Core.Vt

namespace Linger.Core.Vt

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
    ∀ (l : List α) (v : Vt), (l.foldl f v).modes.origin = v.modes.origin
  | [], _ => rfl
  | a :: as, v => (org_foldl f hf as (f v a)).trans (hf v a)

theorem org_clearPending (v : Vt) : v.clearPending.modes.origin = v.modes.origin := by rfl

theorem org_carriageReturn (v : Vt) : v.carriageReturn.modes.origin = v.modes.origin := by rfl

theorem org_moveTo (v : Vt) (x y : Nat) : (v.moveTo x y).modes.origin = v.modes.origin := by rfl

theorem org_moveRel (v : Vt) (dx dy : Int) : (v.moveRel dx dy).modes.origin = v.modes.origin := by
  rfl

theorem org_setCol (v : Vt) (x : Nat) : (v.setCol x).modes.origin = v.modes.origin := by rfl

theorem org_putCell (v : Vt) (x y : Nat) (c : Cell) :
    (v.putCell x y c).modes.origin = v.modes.origin := by rfl

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

theorem org_printWrap (v : Vt) : v.printWrap.modes.origin = v.modes.origin := by
  rw [frame_printWrap]

theorem org_printWideWrap (v : Vt) (w : Nat) :
    (v.printWideWrap w).modes.origin = v.modes.origin := by rw [frame_printWideWrap]

theorem org_printShift (v : Vt) (w : Nat) : (v.printShift w).modes.origin = v.modes.origin := by
  unfold Vt.printShift; dsimp only; split <;> rfl

theorem org_mendRow (v : Vt) (y : Nat) : (v.mendRow y).modes.origin = v.modes.origin := by
  rw [frame_mendRow]

theorem org_printPut (v : Vt) (ch : Char) (w : Nat) :
    (v.printPut ch w).modes.origin = v.modes.origin := by
  unfold Vt.printPut
  dsimp only
  repeat' split
  all_goals (rw [org_mendRow]; rfl)

theorem org_printAdvance (v : Vt) (w : Nat) : (v.printAdvance w).modes.origin = v.modes.origin := by
  unfold Vt.printAdvance; dsimp only; split <;> rfl

theorem org_printMark (v : Vt) (ch : Char) : (v.printMark ch).modes.origin = v.modes.origin := by
  rw [frame_printMark]

theorem org_print (v : Vt) (c : Char) : (v.print c).modes.origin = v.modes.origin :=
  congrArg (fun s => s.modes.origin) (off_print v c)

theorem org_acceptChar (v : Vt) (n : Nat) : (v.acceptChar n).modes.origin = v.modes.origin := by
  unfold Vt.acceptChar; split <;> exact org_print _ _

theorem org_stepGround (v : Vt) (b : UInt8) : (v.stepGround b).modes.origin = v.modes.origin := by
  unfold Vt.stepGround
  repeat' split
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
    first
    | rfl
    | exact org_oscFinish _ _

theorem org_stepStr (v : Vt) (e : Bool) (b : UInt8) :
    (v.stepStr e b).modes.origin = v.modes.origin := by rw [frame_stepStr]

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
  have hw : (v.abortUtf8 b).pstate = PState.ground := by
    rw [ps_abortUtf8]; exact hg
  unfold Vt.step
  dsimp only
  rw [hw, org_stepGround, org_abortUtf8]

/-- From `.esc` the claim has to be "stays false" rather than "unchanged":
`RIS` resets `origin` to its default, which is `false`. -/
theorem org_step_of_esc {v : Vt} (b : UInt8) (hg : v.pstate = .esc) (h : v.modes.origin = false) :
    (v.step b).modes.origin = false := by
  have hw : (v.abortUtf8 b).pstate = PState.esc := by
    rw [ps_abortUtf8]; exact hg
  unfold Vt.step
  dsimp only
  rw [hw]
  exact
    org_stepEsc b
      (by
        rw [org_abortUtf8]; exact h)

theorem org_step_of_escInter {v : Vt} {i : UInt8} (b : UInt8) (hg : v.pstate = .escInter i) :
    (v.step b).modes.origin = v.modes.origin := by
  have hw : (v.abortUtf8 b).pstate = PState.escInter i := by
    rw [ps_abortUtf8]; exact hg
  unfold Vt.step
  dsimp only
  rw [hw, org_stepEscInter, org_abortUtf8]

theorem org_step_of_osc {v : Vt} {acc : Array UInt8} {e : Bool} (b : UInt8)
    (hg : v.pstate = .osc acc e) : (v.step b).modes.origin = v.modes.origin := by
  have hw : (v.abortUtf8 b).pstate = PState.osc acc e := by
    rw [ps_abortUtf8]; exact hg
  unfold Vt.step
  dsimp only
  rw [hw, org_stepOsc, org_abortUtf8]

theorem org_step_of_csi {v : Vt} {s : CsiState} (b : UInt8) (hg : v.pstate = .csi s)
    (hp : (s.priv == 0x3F) = false) : (v.step b).modes.origin = v.modes.origin := by
  have hw : (v.abortUtf8 b).pstate = PState.csi s := by
    rw [ps_abortUtf8]; exact hg
  unfold Vt.step
  dsimp only
  rw [hw, org_stepCsi _ _ _ hp, org_abortUtf8]

/-- The marker-tolerant companion of `org_step_of_csi`. -/
theorem org_step_of_csi_pending {v : Vt} {s : CsiState} (b : UInt8) (hg : v.pstate = .csi s)
    (hparams : s.params = #[]) (hhave : s.haveCur = true) (hne : min s.cur 65535 ≠ 6) :
    (v.step b).modes.origin = v.modes.origin := by
  have hw : (v.abortUtf8 b).pstate = PState.csi s := by
    rw [ps_abortUtf8]; exact hg
  unfold Vt.step
  dsimp only
  rw [hw, org_stepCsi_pending _ _ _ hparams hhave hne, org_abortUtf8]

end Linger.Core.Vt

namespace Linger.Core.Vt

/-! ## Wide pairs: the repair's postcondition

`Render.rowAnsi` can express a row only if every wide glyph in it is whole: a
width-2 base immediately followed by its width-0 shadow, that shadow carrying
nothing of its own (the painter emits the base and nothing else), and no shadow
without a base. Half a pair is not displayable either — a lone base re-wraps on
replay, a lone shadow paints nothing while still occupying a column — so rather
than adding side conditions to the replay theorem, the emulator does not reach
those shapes. Every cell-writing operation ends in `Row.mend`.

This section proves the postcondition that makes those calls worth anything:
after `Row.mend`, **every column satisfies `PairOk`**. It is what `Renderable`
rests on, and proving it once here is what keeps the pair invariant out of every
individual mutation's proof.
-/

/-- Reading back the cell a `setIfInBounds` wrote. -/
theorem getD_set_self {α} [Inhabited α] (r : Array α) (x : Nat) (c d : α) (h : x < r.size) :
    (r.setIfInBounds x c).getD x d = c := by simp [Array.getD, Array.setIfInBounds, h]

/-- …and reading back any other cell. -/
theorem getD_set_ne {α} [Inhabited α] (r : Array α) (x j : Nat) (c d : α) (h : j ≠ x) :
    (r.setIfInBounds x c).getD j d = r.getD j d := by
  simp only [Array.getD, Array.setIfInBounds]
  split
  · simp only [Array.size_set]
    split
    · simp [Array.getElem_set, Ne.symm h]
    · rfl
  · rfl

/-- Out of range reads a default (width-1) cell, which is what lets the pair
rules treat "no neighbour" and "a narrow neighbour" alike. -/
theorem at_of_size_le (row : Row) (x : Nat) (h : row.size ≤ x) : row.at x = default := by
  unfold Row.at
  simp [Array.getD, Nat.not_lt.mpr h]

/-- **The pair rule for one column**, in `Prop`: a base keeps its shadow (and
that shadow is exactly what repainting the base re-creates), and a shadow keeps
its base. -/
def PairOk (row : Row) (x : Nat) : Prop :=
  ((row.at x).width = 2 → row.at (x + 1) = Cell.shadow (row.at x)) ∧
    ((row.at x).width = 0 → x ≠ 0 ∧ (row.at (x - 1)).width = 2)

/-- `halfPair` reads nothing but the three neighbouring widths. -/
theorem halfPair_congr {row row' : Row} (x : Nat)
    (h0 : (row'.at (x - 1)).width = (row.at (x - 1)).width)
    (h1 : (row'.at x).width = (row.at x).width)
    (h2 : (row'.at (x + 1)).width = (row.at (x + 1)).width) : row'.halfPair x = row.halfPair x := by
  simp only [Row.halfPair]
  rw [h0, h1, h2]

/-- `halfPair` in `Prop` — the width half of `PairOk`. -/
theorem halfPair_eq_false_iff (row : Row) (x : Nat) :
    row.halfPair x = false ↔
      ((row.at x).width = 2 → (row.at (x + 1)).width = 0) ∧
        ((row.at x).width = 0 → x ≠ 0 ∧ (row.at (x - 1)).width = 2) := by
  unfold Row.halfPair
  simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, beq_eq_false_iff_ne, bne_eq_false_iff_eq,
    ne_eq]
  constructor
  · intro h
    refine ⟨fun h2 => ?_, fun h0 => ?_⟩
    · rcases h.1 with hc | hs
      · exact absurd h2 hc
      · exact hs
    · rcases h.2 with hc | hs
      · exact absurd h0 hc
      · exact ⟨hs.1, hs.2⟩
  · intro h
    refine ⟨?_, ?_⟩
    · by_cases h2 : (row.at x).width = 2
      · exact Or.inr (h.1 h2)
      · exact Or.inl h2
    · by_cases h0 : (row.at x).width = 0
      · exact Or.inr ⟨(h.2 h0).1, (h.2 h0).2⟩
      · exact Or.inl h0

/-- A width-1 cell is not half of anything, so a blanked column is repaired. -/
theorem halfPair_of_width_one (row : Row) (x : Nat) (h : (row.at x).width = 1) :
    row.halfPair x = false := by
  rw [halfPair_eq_false_iff]
  exact
    ⟨fun h2 => absurd (h.symm.trans h2) (by decide), fun h0 => absurd (h.symm.trans h0) (by decide)⟩

/-! ### One repair step -/

theorem size_mendAt (row : Row) (x : Nat) : (Row.mendAt row x).size = row.size := by
  unfold Row.mendAt
  repeat' split
  all_goals
    first
    | simp
    | rfl

theorem mendAt_ne (row : Row) (x j : Nat) (h : j ≠ x) : (Row.mendAt row x).at j = row.at j := by
  unfold Row.mendAt Row.at
  repeat' split
  all_goals
    first
    | exact getD_set_ne _ _ _ _ _ h
    | rfl

/-- A half pair becomes a blank. -/
theorem mendAt_self_blank (row : Row) (x : Nat) (hx : x < row.size) (h : row.halfPair x = true) :
    (Row.mendAt row x).at x = Cell.erased (row.at x).pen := by
  unfold Row.mendAt Row.at
  rw [ite_eq_left h]
  exact getD_set_self _ _ _ _ hx

/-- A whole pair's shadow becomes canonical. -/
theorem mendAt_self_shadow (row : Row) (x : Nat) (hx : x < row.size) (h : row.halfPair x = false)
    (hw : (row.at x).width = 0) : (Row.mendAt row x).at x = Cell.shadow (row.at (x - 1)) := by
  unfold Row.mendAt Row.at
  rw [ite_eq_right (by simp [h]),
    ite_eq_left
      (by
        simp [Row.at] at hw ⊢; exact hw)]
  exact getD_set_self _ _ _ _ hx

/-- Anything else is left alone. -/
theorem mendAt_self_id (row : Row) (x : Nat) (h : row.halfPair x = false)
    (hw : (row.at x).width ≠ 0) : (Row.mendAt row x).at x = row.at x := by
  unfold Row.mendAt Row.at
  rw [ite_eq_right (by simp [h]),
    ite_eq_right
      (by
        simp only [Row.at] at hw ⊢; simpa using hw)]

/-- A repair that does not blank preserves every width, since a canonical
shadow is still a shadow. -/
theorem width_mendAt_of_whole (row : Row) (x j : Nat) (h : row.halfPair x = false) :
    ((Row.mendAt row x).at j).width = (row.at j).width := by
  by_cases hj : j = x
  · subst hj
    by_cases hw : (row.at j).width = 0
    · by_cases hb : j < row.size
      · rw [mendAt_self_shadow row j hb h hw]; rw [hw]; rfl
      · rw [at_of_size_le row j (by omega)] at hw
        exact absurd hw (by decide)
    · rw [mendAt_self_id row j h hw]
  · rw [mendAt_ne row x j hj]

/-! ### The sweep -/

/-- The repaired column comes out repaired. -/
theorem halfPair_mendAt_self (row : Row) (n : Nat) (hn : n < row.size) :
    (Row.mendAt row n).halfPair n = false := by
  by_cases h : row.halfPair n = true
  · refine halfPair_of_width_one _ _ ?_
    rw [mendAt_self_blank row n hn h]
    rfl
  · have h' : row.halfPair n = false := by simpa using h
    rw [halfPair_congr n (width_mendAt_of_whole row n _ h') (width_mendAt_of_whole row n _ h')
        (width_mendAt_of_whole row n _ h')]
    exact h'

/-- …and so does its shadow clause. -/
theorem shadow_mendAt_self (row : Row) (n : Nat) (hn : n < row.size)
    (hw : ((Row.mendAt row n).at n).width = 0) :
    n ≠ 0 ∧ (Row.mendAt row n).at n = Cell.shadow ((Row.mendAt row n).at (n - 1)) := by
  by_cases h : row.halfPair n = true
  · rw [mendAt_self_blank row n hn h] at hw
    simp [Cell.erased] at hw
  · have h' : row.halfPair n = false := by simpa using h
    have hw0 : (row.at n).width = 0 := by
      rw [width_mendAt_of_whole row n n h'] at hw; exact hw
    have hne : n ≠ 0 := ((halfPair_eq_false_iff row n).mp h').2 hw0 |>.1
    refine ⟨hne, ?_⟩
    rw [mendAt_self_shadow row n hn h' hw0, mendAt_ne row n (n - 1) (by omega)]

/-- A repair step leaves every column below it repaired.

The content is that a *whole* pair is never touched: blanking column `n` could
only orphan a base at `n - 1` if `n` were that base's shadow, and such a shadow
is exactly what `mendAt`'s guard protects. That argument is direction-free,
which is why the sweep's order does not matter (see `Row.mend`); the `j < n`
form is what the sweep induction consumes. -/
theorem halfPair_mendAt_lt (row : Row) (n j : Nat) (hj : j < n) (h : row.halfPair j = false) :
    (Row.mendAt row n).halfPair j = false := by
  rw [halfPair_eq_false_iff] at h ⊢
  have hj0 : (Row.mendAt row n).at j = row.at j := mendAt_ne row n j (by omega)
  have hjm : (Row.mendAt row n).at (j - 1) = row.at (j - 1) := mendAt_ne row n (j - 1) (by omega)
  refine ⟨fun h2 => ?_, fun h0 => ?_⟩
  · rw [hj0] at h2
    by_cases hn : j + 1 = n
    · -- the column being repaired is this base's shadow, so it is not blanked
      subst hn
      have hshadow : row.halfPair (j + 1) = false := by
        rw [halfPair_eq_false_iff]
        have hw : (row.at (j + 1)).width = 0 := h.1 h2
        exact ⟨fun hc => absurd (hw.symm.trans hc) (by decide), fun _ => ⟨by omega, h2⟩⟩
      rw [width_mendAt_of_whole row (j + 1) (j + 1) hshadow]
      exact h.1 h2
    · rw [mendAt_ne row n (j + 1) (by omega)]
      exact h.1 h2
  · rw [hj0] at h0
    exact
      ⟨(h.2 h0).1, by
        rw [hjm]; exact (h.2 h0).2⟩

/-- …including their shadow clause, which reads only columns at or below `j`. -/
theorem shadow_mendAt_lt (row : Row) (n j : Nat) (hj : j < n)
    (h : (row.at j).width = 0 → j ≠ 0 ∧ row.at j = Cell.shadow (row.at (j - 1))) :
    ((Row.mendAt row n).at j).width = 0 →
      j ≠ 0 ∧ (Row.mendAt row n).at j = Cell.shadow ((Row.mendAt row n).at (j - 1)) := by
  intro hw
  have hj0 : (Row.mendAt row n).at j = row.at j := mendAt_ne row n j (by omega)
  have hjm : (Row.mendAt row n).at (j - 1) = row.at (j - 1) := mendAt_ne row n (j - 1) (by omega)
  rw [hj0] at hw
  exact
    ⟨(h hw).1, by
      rw [hj0, hjm]; exact (h hw).2⟩

/-- The sweep, up to a bound: every column below `n` is repaired — both the
width rule and the canonical-shadow rule — and the row keeps its size. -/
theorem mendUpto_spec (row : Row) :
    ∀ n,
      ((List.range n).foldl (fun r x => Row.mendAt r x) row).size = row.size ∧
        ∀ j,
          j < n →
            n ≤ row.size →
            (((List.range n).foldl (fun r x => Row.mendAt r x) row).halfPair j = false ∧
              ((((List.range n).foldl (fun r x => Row.mendAt r x) row).at j).width = 0 →
                j ≠ 0 ∧
                  ((List.range n).foldl (fun r x => Row.mendAt r x) row).at j =
                    Cell.shadow
                      (((List.range n).foldl (fun r x => Row.mendAt r x) row).at (j - 1))))
  | 0 => ⟨rfl, fun _ hj => absurd hj (by omega)⟩
  | n + 1 => by
    have ih := mendUpto_spec row n
    have hstep :
      (List.range (n + 1)).foldl (fun r x => Row.mendAt r x) row =
        Row.mendAt ((List.range n).foldl (fun r x => Row.mendAt r x) row) n := by
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine
      ⟨by
        rw [hstep, size_mendAt]; exact ih.1, fun j hj hn => ?_⟩
    rw [hstep]
    by_cases hje : j = n
    · subst hje
      have hlt : j < ((List.range j).foldl (fun r x => Row.mendAt r x) row).size := by
        rw [ih.1]; omega
      exact ⟨halfPair_mendAt_self _ _ hlt, fun hw => shadow_mendAt_self _ _ hlt hw⟩
    · have hprev := ih.2 j (by omega) (by omega)
      exact ⟨halfPair_mendAt_lt _ _ _ (by omega) hprev.1, shadow_mendAt_lt _ _ _ (by omega) hprev.2⟩

theorem size_mend (row : Row) : (Row.mend row).size = row.size := by
  unfold Row.mend
  exact (mendUpto_spec row row.size).1

theorem mend_halfPair (row : Row) (x : Nat) (hx : x < row.size) :
    (Row.mend row).halfPair x = false := by
  unfold Row.mend
  exact ((mendUpto_spec row row.size).2 x hx (by omega)).1

theorem mend_shadow (row : Row) (x : Nat) (hx : x < row.size)
    (hw : ((Row.mend row).at x).width = 0) :
    x ≠ 0 ∧ (Row.mend row).at x = Cell.shadow ((Row.mend row).at (x - 1)) := by
  unfold Row.mend at hw ⊢
  exact ((mendUpto_spec row row.size).2 x hx (by omega)).2 hw

/-- **The repair's postcondition.** Every column of a mended row satisfies the
pair rule — for any input row at all, which is what lets every mutation end in
`Row.mend` and lets `Renderable` be an invariant rather than a hypothesis. -/
theorem mend_pairOk (row : Row) (x : Nat) (hx : x < row.size) : PairOk (Row.mend row) x := by
  have hsz : (Row.mend row).size = row.size := size_mend row
  refine ⟨fun h2 => ?_, fun h0 => ?_⟩
  · -- a base keeps its shadow, and that shadow is canonical
    have hhp := (halfPair_eq_false_iff (Row.mend row) x).mp (mend_halfPair row x hx)
    have hw : ((Row.mend row).at (x + 1)).width = 0 := hhp.1 h2
    have hb : x + 1 < (Row.mend row).size := by
      rcases Nat.lt_or_ge (x + 1) (Row.mend row).size with h | h
      · exact h
      · rw [at_of_size_le _ _ h] at hw
        exact absurd hw (by decide)
    have hsh :=
      mend_shadow row (x + 1)
        (by
          rw [hsz] at hb; exact hb)
        hw
    have hx1 : x + 1 - 1 = x := by omega
    rw [hx1] at hsh
    exact hsh.2
  · have hhp := (halfPair_eq_false_iff (Row.mend row) x).mp (mend_halfPair row x hx)
    exact hhp.2 h0

/-! ### What the sweep leaves alone

A repaint reads back the cell it just wrote, so the sweep must be the identity
on a cell that is already well formed. Two cases cover every write: a narrow
glyph, and a wide glyph together with its canonical shadow. -/

private theorem mendUpto_keeps_narrow (row : Row) (x : Nat) (h : (row.at x).width = 1) :
    ∀ n, ((List.range n).foldl (fun r y => Row.mendAt r y) row).at x = row.at x
  | 0 => rfl
  | n + 1 => by
    have ih := mendUpto_keeps_narrow row x h n
    have hstep :
      (List.range (n + 1)).foldl (fun r y => Row.mendAt r y) row =
        Row.mendAt ((List.range n).foldl (fun r y => Row.mendAt r y) row) n := by
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hstep]
    by_cases hn : n = x
    · subst hn
      have hw1 : (((List.range n).foldl (fun r y => Row.mendAt r y) row).at n).width = 1 := by
        rw [ih]; exact h
      rw [mendAt_self_id _ _ (halfPair_of_width_one _ _ hw1)
          (by
            rw [hw1]; decide)]
      exact ih
    · rw [mendAt_ne _ _ _ (fun hc => hn hc.symm)]
      exact ih

/-- The sweep is the identity on a narrow cell. -/
theorem mend_keeps_narrow (row : Row) (x : Nat) (h : (row.at x).width = 1) :
    (Row.mend row).at x = row.at x := mendUpto_keeps_narrow row x h row.size

private theorem mendUpto_keeps_wide (row : Row) (x : Nat) (h2 : (row.at x).width = 2)
    (hs : row.at (x + 1) = Cell.shadow (row.at x)) :
    ∀ n,
      ((List.range n).foldl (fun r y => Row.mendAt r y) row).at x = row.at x ∧
        ((List.range n).foldl (fun r y => Row.mendAt r y) row).at (x + 1) = row.at (x + 1)
  | 0 => ⟨rfl, rfl⟩
  | n + 1 => by
    have ih := mendUpto_keeps_wide row x h2 hs n
    have hstep :
      (List.range (n + 1)).foldl (fun r y => Row.mendAt r y) row =
        Row.mendAt ((List.range n).foldl (fun r y => Row.mendAt r y) row) n := by
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    -- the two columns still hold a whole pair, so neither repair branch moves them
    have hb : (((List.range n).foldl (fun r y => Row.mendAt r y) row).at x).width = 2 := by
      rw [ih.1]; exact h2
    have hsh : (((List.range n).foldl (fun r y => Row.mendAt r y) row).at (x + 1)).width = 0 := by
      rw [ih.2, hs]; rfl
    have hwhole : ((List.range n).foldl (fun r y => Row.mendAt r y) row).halfPair x = false := by
      rw [halfPair_eq_false_iff]
      exact ⟨fun _ => hsh, fun h0 => absurd (hb.symm.trans h0) (by decide)⟩
    have hwhole1 :
      ((List.range n).foldl (fun r y => Row.mendAt r y) row).halfPair (x + 1) = false := by
      rw [halfPair_eq_false_iff]
      refine ⟨fun hc => absurd (hsh.symm.trans hc) (by decide), fun _ => ⟨by omega, ?_⟩⟩
      simpa using hb
    rw [hstep]
    refine ⟨?_, ?_⟩
    · by_cases hn : n = x
      · subst hn
        rw [mendAt_self_id _ _ hwhole
            (by
              rw [hb]; decide)]
        exact ih.1
      · rw [mendAt_ne _ _ _ (fun hc => hn hc.symm)]
        exact ih.1
    · by_cases hn : n = x + 1
      · subst hn
        rw [mendAt_self_shadow _ _ ?_ hwhole1 hsh]
        · rw [show x + 1 - 1 = x from by omega, ih.1, hs]
        · -- the column is in range, or its cell would read as a width-1 default
          rcases
            Nat.lt_or_ge (x + 1)
              ((List.range (x + 1)).foldl (fun r y => Row.mendAt r y) row).size with
            hlt | hge
          · exact hlt
          · rw [at_of_size_le _ _ hge] at hsh
            exact absurd hsh (by decide)
      · rw [mendAt_ne _ _ _ (fun hc => hn hc.symm)]
        exact ih.2

/-- The sweep is the identity on a wide glyph and its canonical shadow. -/
theorem mend_keeps_wide (row : Row) (x : Nat) (h2 : (row.at x).width = 2)
    (hs : row.at (x + 1) = Cell.shadow (row.at x)) :
    (Row.mend row).at x = row.at x ∧ (Row.mend row).at (x + 1) = row.at (x + 1) :=
  mendUpto_keeps_wide row x h2 hs row.size

/-! ### Reading a mended row back out of the grid -/

theorem getCell_mendRow_same (v : Vt) (y x : Nat) (hy : y < v.grid.size) :
    (v.mendRow y).getCell x y = (v.getRow y).mend.at x := by
  unfold Vt.mendRow Vt.getCell Vt.getRow Row.at
  dsimp only
  rw [getD_set_self _ _ _ _ hy]

theorem getCell_mendRow_other (v : Vt) (y y' x : Nat) (h : y' ≠ y) :
    (v.mendRow y).getCell x y' = v.getCell x y' := by
  unfold Vt.mendRow Vt.getCell Vt.getRow
  dsimp only
  rw [getD_set_ne _ _ _ _ _ h]

/-! ### Write a cell, mend the row, read it back

What a repaint needs at every glyph. The write survives the sweep exactly when
it did not leave a half pair, and the two shapes a print produces are a narrow
cell and a wide base whose shadow the same print already wrote. -/

theorem grid_size_putCell (u : Vt) (x y : Nat) (c : Cell) :
    (u.putCell x y c).grid.size = u.grid.size := by
  unfold Vt.putCell
  simp

theorem getRow_putCell_same (u : Vt) (x y : Nat) (c : Cell) (hy : y < u.grid.size) :
    (u.putCell x y c).getRow y = (u.getRow y).setIfInBounds x c := by
  unfold Vt.putCell Vt.getRow
  dsimp only
  rw [getD_set_self _ _ _ _ hy]

theorem size_getRow_putCell (u : Vt) (x y : Nat) (c : Cell) (hy : y < u.grid.size) :
    ((u.putCell x y c).getRow y).size = (u.getRow y).size := by
  rw [getRow_putCell_same u x y c hy]
  simp

theorem getRow_putCell_self (u : Vt) (x y : Nat) (c : Cell) (hy : y < u.grid.size)
    (hx : x < (u.getRow y).size) : ((u.putCell x y c).getRow y).at x = c := by
  rw [getRow_putCell_same u x y c hy]
  unfold Row.at
  exact getD_set_self _ _ _ _ hx

/-- One narrow write survives the repair sweep. -/
theorem getCell_write_mendRow_narrow (u : Vt) (x y : Nat) (c : Cell) (hc : c.width = 1)
    (hy : y < u.grid.size) (hx : x < (u.getRow y).size) :
    ((u.putCell x y c).mendRow y).getCell x y = c := by
  have hcell := getRow_putCell_self u x y c hy hx
  rw [getCell_mendRow_same _ _ _
      (by
        rw [grid_size_putCell]; exact hy)]
  rw [mend_keeps_narrow _ _
      (by
        rw [hcell]; exact hc)]
  exact hcell

/-- A wide write and its shadow survive together. -/
theorem getCell_write_mendRow_wide (u : Vt) (x y : Nat) (cb : Cell) (h2 : cb.width = 2)
    (hy : y < u.grid.size) (hx : x + 1 < (u.getRow y).size) :
    (((u.putCell x y cb).putCell (x + 1) y (Cell.shadow cb)).mendRow y).getCell x y = cb ∧
      (((u.putCell x y cb).putCell (x + 1) y (Cell.shadow cb)).mendRow y).getCell (x + 1) y =
        Cell.shadow cb := by
  have hy' : y < (u.putCell x y cb).grid.size := by
    rw [grid_size_putCell]; exact hy
  have hrow' : ((u.putCell x y cb).getRow y).size = (u.getRow y).size :=
    size_getRow_putCell u x y cb hy
  have hshadow :=
    getRow_putCell_self (u.putCell x y cb) (x + 1) y (Cell.shadow cb) hy'
      (by
        rw [hrow']; exact hx)
  have hbase : (((u.putCell x y cb).putCell (x + 1) y (Cell.shadow cb)).getRow y).at x = cb := by
    rw [getRow_putCell_same _ (x + 1) y _ hy']
    unfold Row.at
    rw [getD_set_ne _ _ _ _ _ (by omega)]
    have := getRow_putCell_self u x y cb hy (by omega)
    unfold Row.at at this
    exact this
  have hkeep :=
    mend_keeps_wide (((u.putCell x y cb).putCell (x + 1) y (Cell.shadow cb)).getRow y) x
      (by
        rw [hbase]; exact h2)
      (by rw [hbase, hshadow])
  have hgs : y < ((u.putCell x y cb).putCell (x + 1) y (Cell.shadow cb)).grid.size := by
    rw [grid_size_putCell]; exact hy'
  rw [getCell_mendRow_same _ _ _ hgs, getCell_mendRow_same _ _ _ hgs]
  exact
    ⟨by
      rw [hkeep.1]; exact hbase, by
      rw [hkeep.2]; exact hshadow⟩

/-! #### Shapes: the repair sweep resizes nothing

`Matches` carries two shape facts — the painted row is `cols` long and its index is in
the grid — and no frame covers them, because both are about the grid a write *does*
touch. `mendAt` and `putCell` both go through `setIfInBounds`, so both are preserved
(`size_mendAt`/`size_mend` above); these lift that to the `Vt` level. -/

theorem size_getRow_putCell_any (u : Vt) (x y : Nat) (c : Cell) (hy : y < u.grid.size) (y' : Nat) :
    ((u.putCell x y c).getRow y').size = (u.getRow y').size := by
  by_cases h : y' = y
  · subst h; exact size_getRow_putCell _ _ _ _ hy
  · unfold Vt.putCell Vt.getRow
    dsimp only
    rw [getD_set_ne _ _ _ _ _ h]

/-- Structure equality by fields; there is no `ext` without Mathlib. -/
theorem Cell.ext' {a b : Cell} (hb : a.base = b.base) (hm : a.marks = b.marks)
    (hw : a.width = b.width) (hp : a.pen = b.pen) : a = b := by
  cases a; cases b; simp_all

theorem grid_size_mendRow (u : Vt) (y : Nat) : (u.mendRow y).grid.size = u.grid.size := by
  unfold Vt.mendRow
  simp

theorem size_getRow_mendRow (u : Vt) (y : Nat) (hy : y < u.grid.size) (y' : Nat) :
    ((u.mendRow y).getRow y').size = (u.getRow y').size := by
  by_cases h : y' = y
  · subst h
    unfold Vt.mendRow Vt.getRow
    dsimp only
    rw [getD_set_self _ _ _ _ hy, size_mend]
  · unfold Vt.mendRow Vt.getRow
    dsimp only
    rw [getD_set_ne _ _ _ _ _ h]

/-- **The write term's shape**, as the row induction needs it: a cell write, its repair
sweep and the cursor advance change no dimension, no row length and no row count. Stated
about the composite rather than about `print`, because under `print_narrow_eq`'s
hypotheses that composite *is* the print — and the general statement for `print` would
have to reason through `printWrap`'s scroll, which these hypotheses rule out. -/
theorem write_shape (u : Vt) (x y : Nat) (c : Cell) (n : Nat) (hy : y < u.grid.size) :
    (((u.putCell x y c).mendRow y).printAdvance n).cols = u.cols ∧
      (((u.putCell x y c).mendRow y).printAdvance n).grid.size = u.grid.size ∧
      ∀ y',
        ((((u.putCell x y c).mendRow y).printAdvance n).getRow y').size = (u.getRow y').size := by
  have hgs : y < (u.putCell x y c).grid.size := by
    rw [grid_size_putCell]; exact hy
  refine ⟨?_, ?_, ?_⟩
  · rw [frame_printAdvance, frame_mendRow, frame_putCell]
  · rw [frame_printAdvance, grid_size_mendRow, grid_size_putCell]
  · intro y'
    rw [show
        (((u.putCell x y c).mendRow y).printAdvance n).getRow y' =
          ((u.putCell x y c).mendRow y).getRow y'
        from by
        unfold Vt.getRow
        rw [frame_printAdvance]]
    rw [size_getRow_mendRow _ y hgs y', size_getRow_putCell_any u x y c hy y']

/-- The same for a wide glyph, which writes its base and its shadow before the sweep. -/
theorem write_shape2 (u : Vt) (x y : Nat) (c1 c2 : Cell) (n : Nat) (hy : y < u.grid.size) :
    ((((u.putCell x y c1).putCell (x + 1) y c2).mendRow y).printAdvance n).cols = u.cols ∧
      ((((u.putCell x y c1).putCell (x + 1) y c2).mendRow y).printAdvance n).grid.size =
        u.grid.size ∧
      ∀ y',
        (((((u.putCell x y c1).putCell (x + 1) y c2).mendRow y).printAdvance n).getRow y').size =
          (u.getRow y').size := by
  have h1 : y < (u.putCell x y c1).grid.size := by
    rw [grid_size_putCell]; exact hy
  obtain ⟨hc, hg, hr⟩ := write_shape (u.putCell x y c1) (x + 1) y c2 n h1
  refine ⟨?_, ?_, ?_⟩
  · rw [hc, frame_putCell]
  · rw [hg, grid_size_putCell]
  · intro y'
    rw [hr y', size_getRow_putCell_any u x y c1 hy y']

/-- `Cell.shadow` reads only the pen, so two cells with the same pen have the same
shadow — which is what identifies the shadow a wide print writes with the one the source
row holds. -/
theorem shadow_congr {a b : Cell} (h : a.pen = b.pen) : Cell.shadow a = Cell.shadow b := by
  unfold Cell.shadow
  rw [h]

/-! #### The within-row frame — the k-th write does not disturb columns already painted

The frames above cover the columns a write *touches* and every other *row*. The row
induction needs the third case and it is the delicate one: another column of the **same**
row. `Vt.mendRow` sweeps the whole row, and on a row whose pairs are broken `mendAt` may
rewrite any column — which is exactly the situation mid-paint, because every column the
paint has not reached still holds the previous occupant's junk.

So these are stated **per column, with that column's own shape** rather than with a
hypothesis about the row. `mend_keeps_narrow`/`mend_keeps_wide` need no global
pair-consistency, which is what makes that possible: a narrow cell, or a whole pair,
survives the sweep whatever surrounds it. Carrying the shape is the price of quantifying
over an arbitrary receiver, and it is a price the induction can pay — it painted those
columns and knows what it put there. -/

/-- Reading back another column of the written row: the write is invisible there. -/
theorem at_putCell_ne (u : Vt) (x y : Nat) (c : Cell) (x' : Nat) (hne : x' ≠ x)
    (hy : y < u.grid.size) : ((u.putCell x y c).getRow y).at x' = (u.getRow y).at x' := by
  rw [getRow_putCell_same u x y c hy]
  unfold Row.at
  exact getD_set_ne _ _ _ _ _ hne

/-- **A narrow cell at another column survives the write and the sweep.** -/
theorem getCell_write_mendRow_keep_narrow (u : Vt) (x y : Nat) (c : Cell) (x' : Nat) (hne : x' ≠ x)
    (hy : y < u.grid.size) (hnarrow : (u.getCell x' y).width = 1) :
    ((u.putCell x y c).mendRow y).getCell x' y = u.getCell x' y := by
  have hat : ((u.putCell x y c).getRow y).at x' = (u.getRow y).at x' :=
    at_putCell_ne u x y c x' hne hy
  rw [getCell_mendRow_same _ _ _
      (by
        rw [grid_size_putCell]; exact hy)]
  rw [mend_keeps_narrow _ x'
      (by
        rw [hat]; exact hnarrow),
    hat]
  rfl

/-- **…and so does a whole pair**, which is the case a painted wide glyph below `k`
lands in. Both halves are named because `mend` only leaves them alone together. -/
theorem getCell_write_mendRow_keep_wide (u : Vt) (x y : Nat) (c : Cell) (x' : Nat) (hne : x' ≠ x)
    (hne1 : x' + 1 ≠ x) (hy : y < u.grid.size) (hwide : (u.getCell x' y).width = 2)
    (hshadow : (u.getRow y).at (x' + 1) = Cell.shadow ((u.getRow y).at x')) :
    ((u.putCell x y c).mendRow y).getCell x' y = u.getCell x' y ∧
      ((u.putCell x y c).mendRow y).getCell (x' + 1) y = u.getCell (x' + 1) y := by
  have hat : ((u.putCell x y c).getRow y).at x' = (u.getRow y).at x' :=
    at_putCell_ne u x y c x' hne hy
  have hat1 : ((u.putCell x y c).getRow y).at (x' + 1) = (u.getRow y).at (x' + 1) :=
    at_putCell_ne u x y c (x' + 1) hne1 hy
  have hgs : y < (u.putCell x y c).grid.size := by
    rw [grid_size_putCell]; exact hy
  obtain ⟨h0, h1⟩ :=
    mend_keeps_wide ((u.putCell x y c).getRow y) x'
      (by
        rw [hat]; exact hwide)
      (by
        rw [hat, hat1]; exact hshadow)
  rw [getCell_mendRow_same _ _ _ hgs, getCell_mendRow_same _ _ _ hgs, h0, h1, hat, hat1]
  exact ⟨rfl, rfl⟩

/-- A write plus repair on one row leaves every other row alone. -/
theorem getCell_write_mendRow_other (u : Vt) (x y : Nat) (c : Cell) (x' y' : Nat) (h : y' ≠ y) :
    ((u.putCell x y c).mendRow y).getCell x' y' = u.getCell x' y' := by
  rw [getCell_mendRow_other _ _ _ _ h]
  unfold Vt.putCell Vt.getCell Vt.getRow
  dsimp only
  exact congrArg (fun r => Array.getD r x' default) (getD_set_ne _ _ _ _ _ h)

/-! ### `print`, reduced to its write

Three shape lemmas so the per-glyph fidelity theorems never have to walk
`print`'s five stages. Each is stated with `v.cursor` and `v.pen` rather than
`v.clearPending`'s, which are definitionally the same — `clearPending` writes
only the wrap flag. -/

theorem getCell_printAdvance (v : Vt) (n x y : Nat) :
    (v.printAdvance n).getCell x y = v.getCell x y := by
  unfold Vt.getCell Vt.getRow
  rw [frame_printAdvance]

/-! #### Off the written row — what the *grid* walk needs and the row walk did not

`Matches` is a statement about **one** row, so it cannot say that painting row `y` leaves
row `y'` alone. The grid walk needs exactly that: its invariant is "rows below `y` are
already painted", and each later row's paint must not disturb them. Every clause here is
about the composite a print reduces to (`print_narrow_eq` and friends), for the same
reason `write_shape` is — the general statement for `print` would have to reason through
`printWrap`'s scroll, which is the cross-row catastrophe those hypotheses rule out. -/

theorem grid_clearPending (u : Vt) : u.clearPending.grid = u.grid := by rw [frame_clearPending]

theorem getCell_clearPending (u : Vt) (x y : Nat) : u.clearPending.getCell x y = u.getCell x y := by
  unfold Vt.getCell Vt.getRow
  rw [frame_clearPending]

/-- **One narrow write touches no other row.** -/
theorem getCell_write_off (u : Vt) (x y : Nat) (c : Cell) (n : Nat) (x' y' : Nat) (hne : y' ≠ y) :
    ((((u.putCell x y c).mendRow y).printAdvance n).getCell x' y') = u.getCell x' y' := by
  rw [getCell_printAdvance]
  exact getCell_write_mendRow_other u x y c x' y' hne

/-- …and neither does a wide one, which writes its base and its shadow. -/
theorem getCell_write2_off (u : Vt) (x y : Nat) (c1 c2 : Cell) (n : Nat) (x' y' : Nat)
    (hne : y' ≠ y) :
    (((((u.putCell x y c1).putCell (x + 1) y c2).mendRow y).printAdvance n).getCell x' y') =
      u.getCell x' y' := by
  rw [getCell_printAdvance, getCell_write_mendRow_other (u.putCell x y c1) (x + 1) y c2 x' y' hne]
  unfold Vt.putCell Vt.getCell Vt.getRow
  dsimp only
  exact congrArg (fun r => Array.getD r x' default) (getD_set_ne _ _ _ _ _ hne)

/-- …nor a combining mark, whose write has no advance after it. -/
theorem getCell_mark_off (u : Vt) (x y : Nat) (c : Cell) (x' y' : Nat) (hne : y' ≠ y) :
    (((u.putCell x y c).mendRow y).getCell x' y') = u.getCell x' y' :=
  getCell_write_mendRow_other u x y c x' y' hne

theorem print_narrow_eq {v : Vt} {ch : Char} (hpc : v.printChar ch = ch) (hw : charWidth ch = 1)
    (hins : v.modes.insert = false) (hpend : v.cursor.pending = false) :
    v.print ch =
      ((v.clearPending.putCell v.cursor.x v.cursor.y
                { base := ch, marks := [], width := 1, pen := v.pen }).mendRow
            v.cursor.y).printAdvance
        1 := by
  unfold Vt.print
  simp only [hpc, hw]
  rw [ite_eq_right (by decide)]
  have h1 : v.printWrap = v.clearPending := by
    unfold Vt.printWrap; rw [ite_eq_right (by simp [hpend])]
  have h2 : ∀ (w : Vt), w.printWideWrap 1 = w := by
    intro w; unfold Vt.printWideWrap; rw [ite_eq_right (by simp)]
  have h3 : ∀ (w : Vt), w.modes.insert = false → w.printShift 1 = w := by
    intro w hw'; unfold Vt.printShift; rw [ite_eq_right (by simp [hw'])]
  have h4 :
    ∀ (w : Vt) (c : Char),
      w.printPut c 1 =
        (w.putCell w.cursor.x w.cursor.y
              { base := c, marks := [], width := 1, pen := w.pen }).mendRow
          w.cursor.y := by
    intro w c
    unfold Vt.printPut
    dsimp only
    rw [ite_eq_right (by simp), ite_eq_right (by decide)]
  rw [h1, h2,
    h3 _
      (by
        rw [frame_clearPending]; exact hins),
    h4]
  rfl

theorem print_wide_eq {v : Vt} {ch : Char} (hpc : v.printChar ch = ch) (hw : charWidth ch = 2)
    (hins : v.modes.insert = false) (hpend : v.cursor.pending = false)
    (hfit : v.cursor.x + 1 < v.cols) :
    v.print ch =
      (((v.clearPending.putCell v.cursor.x v.cursor.y
                    { base := ch, marks := [], width := 2, pen := v.pen }).putCell
                (v.cursor.x + 1) v.cursor.y
                (Cell.shadow { base := ch, marks := [], width := 2, pen := v.pen })).mendRow
            v.cursor.y).printAdvance
        2 := by
  unfold Vt.print
  simp only [hpc, hw]
  rw [ite_eq_right (by decide)]
  have hcp : v.clearPending = { v with cursor := { v.cursor with pending := false } } := by rfl
  have h1 : v.printWrap = v.clearPending := by
    unfold Vt.printWrap; rw [ite_eq_right (by simp [hpend])]
  have h2 : v.clearPending.printWideWrap 2 = v.clearPending := by
    unfold Vt.printWideWrap
    rw [ite_eq_right
        (by
          first
          | (simp [hcp]; done)
          | (simp [hcp]; omega))]
  have h3 : ∀ (w : Vt), w.modes.insert = false → w.printShift 2 = w := by
    intro w hw'; unfold Vt.printShift; rw [ite_eq_right (by simp [hw'])]
  have h4 :
    ∀ (w : Vt) (c : Char),
      w.cursor.x + 1 < w.cols →
        w.printPut c 2 =
          ((w.putCell w.cursor.x w.cursor.y
                    { base := c, marks := [], width := 2, pen := w.pen }).putCell
                (w.cursor.x + 1) w.cursor.y
                (Cell.shadow { base := c, marks := [], width := 2, pen := w.pen })).mendRow
            w.cursor.y := by
    intro w c hf
    unfold Vt.printPut
    dsimp only
    rw [ite_eq_right
        (by
          first
          | (simp; done)
          | (simp; omega)),
      ite_eq_left (by decide)]
    rfl
  rw [h1, h2,
    h3 _
      (by
        rw [frame_clearPending]; exact hins),
    h4 _ ch
      (by
        first
        | (simp [hcp]; done)
        | (simp [hcp]; omega))]
  rfl

theorem print_mark_eq {v : Vt} {m : Char} (hpc : v.printChar m = m) (hw : charWidth m = 0)
    (hpend : v.cursor.pending = false) (hnw : (v.getCell (v.cursor.x - 1) v.cursor.y).width ≠ 0)
    (hcap : (v.getCell (v.cursor.x - 1) v.cursor.y).marks.length < 8) :
    v.print m =
      (v.putCell (v.cursor.x - 1) v.cursor.y
            { v.getCell (v.cursor.x - 1) v.cursor.y with
              marks := (v.getCell (v.cursor.x - 1) v.cursor.y).marks ++ [m] }).mendRow
        v.cursor.y := by
  unfold Vt.print
  simp only [hpc, hw]
  rw [ite_eq_left (by decide)]
  unfold Vt.printMark
  simp only [hpend, ite_false, Bool.false_eq_true]
  rw [ite_eq_right
      (show ¬(((v.getCell (v.cursor.x - 1) v.cursor.y).width == 0 && v.cursor.x - 1 != 0) = true)
        from by
        simp only [Bool.and_eq_true, beq_iff_eq]
        exact fun h => hnw h.1)]
  rw [ite_eq_right (show ¬((v.getCell (v.cursor.x - 1) v.cursor.y).marks.length ≥ 8) from by omega)]

/-- The same, for a receiver with **wrap pending**. Not a variation for its own sake:
the row painter reaches this state on every marked cell in the final column. There the
advance clamped the column and armed wrap-pending instead of moving, so the glyph the
mark belongs to sits *at* the cursor rather than one to its left — which is precisely
the position `printMark`'s `pending` branch exists to name, and the one no absolute
cursor move can address. -/
theorem print_mark_pending_eq {v : Vt} {m : Char} (hpc : v.printChar m = m) (hw : charWidth m = 0)
    (hpend : v.cursor.pending = true) (hnw : (v.getCell v.cursor.x v.cursor.y).width ≠ 0)
    (hcap : (v.getCell v.cursor.x v.cursor.y).marks.length < 8) :
    v.print m =
      (v.putCell v.cursor.x v.cursor.y
            { v.getCell v.cursor.x v.cursor.y with
              marks := (v.getCell v.cursor.x v.cursor.y).marks ++ [m] }).mendRow
        v.cursor.y := by
  unfold Vt.print
  simp only [hpc, hw]
  rw [ite_eq_left (by decide)]
  unfold Vt.printMark
  simp only [hpend, ite_true]
  rw [ite_eq_right
      (show ¬(((v.getCell v.cursor.x v.cursor.y).width == 0 && v.cursor.x != 0) = true) from by
        simp only [Bool.and_eq_true, beq_iff_eq]
        exact fun h => hnw h.1)]
  rw [ite_eq_right (show ¬((v.getCell v.cursor.x v.cursor.y).marks.length ≥ 8) from by omega)]

end Linger.Core.Vt

namespace Linger.Core.Vt

/-! ## §Renderable — the emulator only reaches grids a repaint can reproduce

`Good` bounds the emulator; this bounds what it *stores*. `Render.restore`
paints a grid by emitting one glyph per cell, so a cell it can reproduce must
hold a printable base of the width it claims, at most eight zero-width marks,
and — for a wide glyph — its shadow, carrying nothing of its own.

The point of proving this is negative: it means the replay theorem needs no side
conditions. Every clause is established at the write, not assumed: controls are
neutralized on store (`printableChar`), marks are capped and land on a base
(`printMark`), and pairs are repaired at every row mutation (`Row.mend`), so
`mend_pairOk` discharges the pair clause uniformly.

The predicate is stated over the grid *array* with a fixed default row, not over
`Vt.getRow` (whose default carries the current pen). That is what lets every
operation which does not touch `grid`/`cols`/`rows`/`altGrid` be discharged by
its frame — most of `csiDispatch` — instead of by its own lemma.
-/

/-- A codepoint the emitter reproduces as itself: not a C0 control and not DEL.

Stated concretely rather than as `printableChar c = c`, which would be a
tautology against the very function that establishes it — mutating
`printableChar` would weaken the predicate and the storer together and
`renderable_print` would still prove. This way such a mutation has to break
`printableChar_emittable`, which is a claim about `printableChar`'s *range*. -/
def Emittable (c : Char) : Prop := 0x20 ≤ c.toNat ∧ c.toNat ≠ 0x7F

theorem printableChar_emittable (c : Char) : Emittable (printableChar c) := by
  unfold Emittable printableChar
  split
  · exact ⟨by decide, by decide⟩
  · rename_i h
    simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, not_or, Nat.not_lt] at h
    exact ⟨h.1, h.2⟩

theorem emittable_space : Emittable ' ' := ⟨by decide, by decide⟩

/-! ### The width tables (pin-the-gaps item 4)

`isZeroWidth` and `isWide` decide how many columns a glyph owns, and until this
section they were named **nowhere in the repo** outside their own definitions and
`charWidth` — 50 theorem statements mention `charWidth`, every one generic over
the tables, so a shifted range was invisible to the entire proof tree and to every
fixture. `CellOk.width` above is what makes them load-bearing: it ties a stored
cell's `width` field to `charWidth c.base`, so a table edit silently redefines
which grids are well-formed.

Both take `Nat`, not `Char`, so the pins are **closed propositions** decided by
the kernel — no `Char` literal (Lean's `\uXXXX` cannot reach plane 2), and no
compiled evaluation, which `tests/gates.sh` bans in `Theorems/` (and which greps
prose as well as code, so this sentence may not name the tactic). Each edge is
pinned on **both
sides** (`lo-1 = false, lo = true`), so shifting a bound either way falsifies a
conjunct. Deliberately *not* stated as `∀ c, isWide c = true ↔ <the disjunction>`:
that is a verbatim second copy of the table whose repair after a regression is to
edit the copy — the same anti-tautology argument as `Emittable` above.

**Two seams are unobservable, and are recorded rather than pretended.**
`0x3041-0x33FF ∪ 0x3400-0x4DBF` and `0x4E00-0x9FFF ∪ 0xA000-0xA4CF` are each one
contiguous run written as two clauses; moving a split point in *both* clauses
changes no value of the function, so no oracle can see it. The unions' outer edges
carry the content and are pinned; the seam interiors are pinned as `true` on both
sides, which catches a one-sided shrink (it opens a gap) but not an overlap.

**And a third thing nothing here can catch, found by break-verifying this
section:** `charWidth`'s *branch order*. Swapping its two `if`s is a semantic
no-op — and `zeroWidth_not_wide` below is exactly why, since disjoint tables mean
at most one branch can ever fire. So the order is a readability choice, not a
decision, and a theorem shaped `charWidth c = 2 ↔ (isZeroWidth … = false ∧ isWide
… = true)` would look like it pinned the order while pinning nothing. Those were
weighed and declined for that reason; the disjointness claim is what carries the
content they appeared to. -/

/-- **The low wall: nothing below U+1100 is wide.** One claim covering 4352
codepoints, and the property the grid actually rests on — every ASCII, Latin-1
and box-drawing glyph owns exactly one column, so a clause whose lower bound
slipped into the low plane mis-aligns every row of every restore. Tight: the
minimum `lo` in the table *is* `0x1100`, so lowering any of them breaks this. -/
theorem isWide_low (n : Nat) (h : n < 0x1100) : isWide n = false := by
  unfold isWide
  simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not, Nat.not_le]
  omega

/-- The same wall for the zero-width table, at U+0300. -/
theorem isZeroWidth_low (n : Nat) (h : n < 0x0300) : isZeroWidth n = false := by
  unfold isZeroWidth
  simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not, Nat.not_le,
    beq_eq_false_iff_ne, ne_eq]
  omega

/-- The consequence the row painter consumes: ASCII and Latin-1 are one column
wide. Composes the two walls through `charWidth`'s branch order. -/
theorem charWidth_low (c : Char) (h : c.toNat < 0x0300) : charWidth c = 1 := by
  unfold charWidth
  simp only [isZeroWidth_low _ h, isWide_low _ (by omega : c.toNat < 0x1100), Bool.false_eq_true,
    ite_false]

/-- Hangul Jamo leads (U+1100–U+115F), both edges. -/
theorem isWide_hangulJamo :
    isWide 0x10FF = false ∧
      isWide 0x1100 = true ∧ isWide 0x115F = true ∧ isWide 0x1160 = false := by
  decide

/-- CJK radicals through punctuation (U+2E80–U+303E). `0x303F` is the ideographic
half-fill space, narrow — and the gap to the next clause is two codepoints, the
tightest in the table. -/
theorem isWide_cjkRadicals :
    isWide 0x2E7F = false ∧
      isWide 0x2E80 = true ∧ isWide 0x303E = true ∧ isWide 0x303F = false := by
  decide

/-- Kana and CJK misc, the U+3041–U+4DBF run written as two clauses. The outer
edges carry the content; `0x33FF`/`0x3400` is the unobservable seam. -/
theorem isWide_kanaCjk :
    isWide 0x3040 = false ∧
      isWide 0x3041 = true ∧
      isWide 0x33FF = true ∧
      isWide 0x3400 = true ∧ isWide 0x4DBF = true ∧ isWide 0x4DC0 = false := by
  decide

/-- CJK unified through Yi, the U+4E00–U+A4CF run written as two clauses.
`0x9FFF`/`0xA000` is the second unobservable seam. -/
theorem isWide_cjkUnified :
    isWide 0x4DFF = false ∧
      isWide 0x4E00 = true ∧
      isWide 0x9FFF = true ∧
      isWide 0xA000 = true ∧ isWide 0xA4CF = true ∧ isWide 0xA4D0 = false := by
  decide

/-- Hangul syllables (U+AC00–U+D7A3). Both probes sit below the surrogate block,
so neither is an invalid scalar. -/
theorem isWide_hangulSyllables :
    isWide 0xABFF = false ∧
      isWide 0xAC00 = true ∧ isWide 0xD7A3 = true ∧ isWide 0xD7A4 = false := by
  decide

/-- CJK compatibility ideographs (U+F900–U+FAFF). -/
theorem isWide_cjkCompat :
    isWide 0xF8FF = false ∧
      isWide 0xF900 = true ∧ isWide 0xFAFF = true ∧ isWide 0xFB00 = false := by
  decide

/-- CJK compatibility forms (U+FE30–U+FE4F). Its `lo-1` is U+FE2F, the last
variation selector supplement — **zero-width**, not narrow: this edge is where
the two tables touch, and `zeroWidth_not_wide` below is what keeps them apart. -/
theorem isWide_cjkForms :
    isWide 0xFE2F = false ∧
      isWide 0xFE30 = true ∧ isWide 0xFE4F = true ∧ isWide 0xFE50 = false := by
  decide

/-- Fullwidth forms (U+FF00–U+FF60) and fullwidth signs (U+FFE0–U+FFE6). The
first `lo-1` is U+FEFF, the BOM — the second place the tables touch. -/
theorem isWide_fullwidth :
    isWide 0xFEFF = false ∧
      isWide 0xFF00 = true ∧
      isWide 0xFF60 = true ∧
      isWide 0xFF61 = false ∧
      isWide 0xFFDF = false ∧
      isWide 0xFFE0 = true ∧ isWide 0xFFE6 = true ∧ isWide 0xFFE7 = false := by
  decide

/-- Emoji (U+1F300–U+1F64F) and supplemental symbols (U+1F900–U+1F9FF), above
the BMP — reachable here only because `isWide` takes a `Nat`. -/
theorem isWide_emoji :
    isWide 0x1F2FF = false ∧
      isWide 0x1F300 = true ∧
      isWide 0x1F64F = true ∧
      isWide 0x1F650 = false ∧
      isWide 0x1F8FF = false ∧
      isWide 0x1F900 = true ∧ isWide 0x1F9FF = true ∧ isWide 0x1FA00 = false := by
  decide

/-- Planes 2 and 3 (U+20000–U+2FFFD, U+30000–U+3FFFD). Both `hi+1` probes are
noncharacters; Lean validates scalar-value-ness, not assignment. -/
theorem isWide_planes23 :
    isWide 0x1FFFF = false ∧
      isWide 0x20000 = true ∧
      isWide 0x2FFFD = true ∧
      isWide 0x2FFFE = false ∧
      isWide 0x2FFFF = false ∧
      isWide 0x30000 = true ∧ isWide 0x3FFFD = true ∧ isWide 0x3FFFE = false := by
  decide

/-- Combining diacritics (U+0300–U+036F). -/
theorem isZeroWidth_combining :
    isZeroWidth 0x02FF = false ∧
      isZeroWidth 0x0300 = true ∧ isZeroWidth 0x036F = true ∧ isZeroWidth 0x0370 = false := by
  decide

/-- Vedic extensions and combining marks (U+1AB0–U+1AFF, U+20D0–U+20FF). -/
theorem isZeroWidth_marks :
    isZeroWidth 0x1AAF = false ∧
      isZeroWidth 0x1AB0 = true ∧
      isZeroWidth 0x1AFF = true ∧
      isZeroWidth 0x1B00 = false ∧
      isZeroWidth 0x20CF = false ∧
      isZeroWidth 0x20D0 = true ∧ isZeroWidth 0x20FF = true ∧ isZeroWidth 0x2100 = false := by
  decide

/-- The zero-width joiner cluster (U+200B, U+200C, U+200D) — three **mutually
adjacent singletons**, so no neighbour probe can detect the loss of any one of
them. Each is pinned individually; U+200A and U+200E are the only outside probes
the cluster has. -/
theorem isZeroWidth_joiners :
    isZeroWidth 0x200A = false ∧
      isZeroWidth 0x200B = true ∧
      isZeroWidth 0x200C = true ∧ isZeroWidth 0x200D = true ∧ isZeroWidth 0x200E = false := by
  decide

/-- Variation selectors (U+FE00–U+FE0F) and their supplement (U+FE20–U+FE2F).
`0xFE30` is `false` here because it belongs to the *wide* table. -/
theorem isZeroWidth_varSel :
    isZeroWidth 0xFDFF = false ∧
      isZeroWidth 0xFE00 = true ∧
      isZeroWidth 0xFE0F = true ∧
      isZeroWidth 0xFE10 = false ∧
      isZeroWidth 0xFE1F = false ∧
      isZeroWidth 0xFE20 = true ∧ isZeroWidth 0xFE2F = true ∧ isZeroWidth 0xFE30 = false := by
  decide

/-- The BOM (U+FEFF), a singleton whose `hi+1` is the fullwidth block's `lo`. -/
theorem isZeroWidth_bom :
    isZeroWidth 0xFEFE = false ∧ isZeroWidth 0xFEFF = true ∧ isZeroWidth 0xFF00 = false := by decide

/-- **The tables never overlap.** They are adjacent at exactly two places, gap
one — U+FE2F/U+FE30 and U+FEFF/U+FF00 — and a one-codepoint slip in *either*
table at *either* place would make a codepoint both zero-width and wide, which
`charWidth`'s branch order then resolves silently. No per-table edge pin sees
that; this is false the moment it happens. -/
theorem zeroWidth_not_wide (n : Nat) (h : isZeroWidth n = true) : isWide n = false := by
  unfold isZeroWidth at h
  unfold isWide
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not, Nat.not_le]
  omega

/-- A cell a repaint can reproduce. -/
structure CellOk (c : Cell) : Prop where
  base : Emittable c.base
  width : c.width ≠ 0 → charWidth c.base = c.width
  marksLe : c.marks.length ≤ 8
  marks : ∀ m ∈ c.marks, charWidth m = 0 ∧ Emittable m

theorem cellOk_erased (p : Pen) : CellOk (Cell.erased p) :=
  ⟨emittable_space, fun _ => rfl, Nat.zero_le _, fun _ hm => nomatch hm⟩

theorem cellOk_shadow (c : Cell) : CellOk (Cell.shadow c) :=
  ⟨emittable_space, fun h => absurd rfl h, Nat.zero_le _, fun _ hm => nomatch hm⟩

theorem cellOk_default : CellOk (default : Cell) :=
  ⟨emittable_space, fun _ => rfl, Nat.zero_le _, fun _ hm => nomatch hm⟩

/-- A row a repaint can reproduce: exact width, reproducible cells, whole
pairs. Cells are quantified over *all* indices — an out-of-range read is a
default cell, which is fine — so no proof has to carry column bounds. -/
structure RowOk (cols : Nat) (row : Row) : Prop where
  size : row.size = cols
  cells : ∀ x, CellOk (row.at x)
  pairs : ∀ x, PairOk row x

/-- A width-1 row is trivially paired. -/
theorem pairOk_of_width_one {row : Row} (h : ∀ x, (row.at x).width = 1) (x : Nat) : PairOk row x :=
  ⟨fun h2 => absurd ((h x).symm.trans h2) (by decide), fun h0 =>
    absurd ((h x).symm.trans h0) (by decide)⟩

theorem at_blankRow (cols : Nat) (p : Pen) (x : Nat) :
    (blankRow cols p).at x = if x < cols then Cell.erased p else default := by
  unfold Row.at blankRow
  by_cases h : x < cols
  · rw [ite_eq_left h]
    simp [Array.getD, h]
  · rw [ite_eq_right h]
    simp [Array.getD, h]

theorem rowOk_blankRow (cols : Nat) (p : Pen) : RowOk cols (blankRow cols p) := by
  refine ⟨by simp [blankRow], fun x => ?_, pairOk_of_width_one (fun x => ?_)⟩
  · rw [at_blankRow]
    split
    · exact cellOk_erased p
    · exact cellOk_default
  · rw [at_blankRow]
    split <;> rfl

/-- A grid a repaint can reproduce. -/
def GridOk (cols rows : Nat) (g : Array Row) : Prop :=
  g.size = rows ∧ ∀ y, RowOk cols (g.getD y (blankRow cols {}))

structure Renderable (v : Vt) : Prop where
  main : GridOk v.cols v.rows v.grid
  alt : ∀ g c p, v.altGrid = some (g, c, p) → GridOk v.cols v.rows g

theorem gridOk_replicate (cols rows : Nat) (p : Pen) :
    GridOk cols rows (Array.replicate rows (blankRow cols p)) := by
  refine ⟨by simp, fun y => ?_⟩
  by_cases h : y < rows
  · rw [show (Array.replicate rows (blankRow cols p)).getD y (blankRow cols {}) = blankRow cols p
        from by simp [Array.getD, h]]
    exact rowOk_blankRow cols p
  · rw [show (Array.replicate rows (blankRow cols p)).getD y (blankRow cols {}) = blankRow cols {}
        from by simp [Array.getD, h]]
    exact rowOk_blankRow cols {}

theorem renderable_init (cols rows : Nat) : Renderable (Vt.init cols rows) :=
  ⟨gridOk_replicate _ _ _, fun _ _ _ h => nomatch h⟩

/-! ### The decoder's door, part two — the shape half (finding R2)

`decodedOk_iff` above decides `Good`'s content, and `Good` says nothing about the grid.
The audit recorded in SCRATCHPAD.md reached a `Good ∧ ¬Renderable` state **from disk**
with one flipped byte of a real checkpoint and refuted `resume_grid`'s conclusion at it,
which makes this an observable defect rather than a missing hypothesis. `Vt.decodedRenderable`
(`Linger/Core/Vt.lean`) is the second half of the door's check; these are its claims.

They live here, four thousand lines below the door's other claims, for one reason:
`Renderable` and its `GridOk`/`RowOk`/`CellOk`/`PairOk` ladder are defined just above, and
nothing earlier in this file can name them. One `iff` per rung, so the `Bool` and the
`Prop` cannot drift apart at any level — the same discipline as `decodedOk_iff`, five
times.

**The mirror lands here too.** `ofDecoded_of_good` is the same predicate seen from the
other side — the door's *non-rejection* — so it now asks for `Renderable` and `TabsOk`,
and everything above it inherits them: `Checkpoint.rt_vt` → `load_save` →
`load_save_exact` → the five `resume_*` claims that never read the grid. Every claim that
gained one says so in its own docstring, `renderable_of_liveReachable` and
`tabsOk_of_liveReachable` discharge them for any live session, and for the three claims
that *do* read the grid (`resume_grid`, `resume_sb`, `resume_tabs`) the new hypothesis was
already there. That trade was declined once, on the ground that a hypothesis a proof does
not use makes a theorem weaker than it is; the override is that the old unconditional
statements were also true of a screen the emitter cannot reproduce, which is a defect and
not a strength. -/

/-- Past its width a row reads default (width-1) cells, so no column out there is half of
a wide pair. With `cellOk_default` this is what makes `decodedRowOk`'s finite scan decide
`RowOk`'s two unbounded quantifiers. -/
theorem pairOk_of_size_le {row : Row} {x : Nat} (h : row.size ≤ x) : PairOk row x := by
  unfold PairOk
  rw [at_of_size_le row x h]
  exact ⟨fun h2 => absurd h2 (by decide), fun h0 => absurd h0 (by decide)⟩

/-- What the door decides about one codepoint, in `Emittable`'s vocabulary. -/
theorem decodedCharOk_iff {c : Char} : Vt.decodedCharOk c = true ↔ Emittable c := by
  unfold Vt.decodedCharOk Emittable
  simp

/-- …about one cell, in `CellOk`'s. The `width = 0` disjunct is `CellOk.width`'s
implication: a shadow's blank base is not the width it claims, and must not be. -/
theorem decodedCellOk_iff {c : Cell} : Vt.decodedCellOk c = true ↔ CellOk c := by
  unfold Vt.decodedCellOk
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    decodedCharOk_iff]
  constructor
  · rintro ⟨⟨⟨hb, hw⟩, hml⟩, hm⟩
    exact ⟨hb, fun hne => hw.resolve_left hne, hml, fun m hmem => hm m hmem⟩
  · rintro ⟨hb, hw, hml, hm⟩
    refine ⟨⟨⟨hb, ?_⟩, hml⟩, fun m hmem => hm m hmem⟩
    by_cases h0 : c.width = 0
    · exact Or.inl h0
    · exact Or.inr (hw h0)

/-- …and about one column pair, in `PairOk`'s. -/
theorem decodedPairOk_iff {row : Row} {x : Nat} : Vt.decodedPairOk row x = true ↔ PairOk row x := by
  unfold Vt.decodedPairOk PairOk
  simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
  constructor
  · rintro ⟨h2, h0⟩
    exact ⟨fun hw => h2.resolve_left (by omega), fun hw => h0.resolve_left (by omega)⟩
  · rintro ⟨h2, h0⟩
    constructor
    · by_cases hw : (row.at x).width = 2
      · exact Or.inr (h2 hw)
      · exact Or.inl hw
    · by_cases hw : (row.at x).width = 0
      · exact Or.inr (h0 hw)
      · exact Or.inl hw

/-- **A finite scan decides an unbounded quantifier.** `RowOk` quantifies over every `x`,
not over `x < cols`; the door checks `[0, cols)` and the two agree, because a read past
the width is the default cell — `cellOk_default` for the cells and `pairOk_of_size_le` for
the pairs. That is what made the per-cell half affordable at all. -/
theorem decodedRowOk_iff {cols : Nat} {row : Row} :
    Vt.decodedRowOk cols row = true ↔ RowOk cols row := by
  unfold Vt.decodedRowOk
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, decodedCellOk_iff,
    decodedPairOk_iff]
  constructor
  · rintro ⟨hsz, hall⟩
    refine ⟨hsz, fun x => ?_, fun x => ?_⟩
    · by_cases hx : x < cols
      · exact (hall x hx).1
      · rw [at_of_size_le row x (by omega)]
        exact cellOk_default
    · by_cases hx : x < cols
      · exact (hall x hx).2
      · exact pairOk_of_size_le (by omega)
  · rintro ⟨hsz, hc, hp⟩
    exact ⟨hsz, fun x _ => ⟨hc x, hp x⟩⟩

/-- …and one row per row decides the grid. Indexed with `GridOk`'s own
`getD … (blankRow cols {})`, so the two cannot disagree past the last row: there both read
a blank row of the right width, which `rowOk_blankRow` accepts. -/
theorem decodedGridOk_iff {cols rows : Nat} {g : Array Row} :
    Vt.decodedGridOk cols rows g = true ↔ GridOk cols rows g := by
  unfold Vt.decodedGridOk GridOk
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, decodedRowOk_iff]
  constructor
  · rintro ⟨hsz, hall⟩
    refine ⟨hsz, fun y => ?_⟩
    by_cases hy : y < rows
    · exact hall y hy
    · rw [show g.getD y (blankRow cols {}) = blankRow cols {} from by simp [Array.getD, hsz, hy]]
      exact rowOk_blankRow cols {}
  · rintro ⟨hsz, hall⟩
    exact ⟨hsz, fun y _ => hall y⟩

/-- **What the second stage decides, in `Renderable`'s vocabulary plus the ruler's.** The
alt clause is the sub-clause that was checked *nowhere* before: `decodedOk` looks at the
stashed cursor and never at the stashed grid. -/
theorem decodedRenderable_iff {cols rows : Nat} {grid : Array Row} {tabs : Array Bool}
    {altGrid : Option (Array Row × Cursor × Pen)} :
    Vt.decodedRenderable cols rows grid tabs altGrid = true ↔
      GridOk cols rows grid ∧
        tabs.size = cols ∧ ∀ g c p, altGrid = some (g, c, p) → GridOk cols rows g := by
  unfold Vt.decodedRenderable
  cases altGrid with
  | none =>
    simp only [Bool.and_eq_true, beq_iff_eq, decodedGridOk_iff, and_true]
    simp
  | some x =>
    obtain ⟨g₀, c₀, p₀⟩ := x
    simp only [Bool.and_eq_true, beq_iff_eq, decodedGridOk_iff, Option.some.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hg, ht⟩, ha⟩
      refine ⟨hg, ht, ?_⟩
      rintro g c p ⟨rfl, rfl, rfl⟩
      exact ha
    · rintro ⟨hg, ht, ha⟩
      exact ⟨⟨hg, ht⟩, ha g₀ c₀ p₀ ⟨rfl, rfl, rfl⟩⟩

/-- **Nothing the emitter cannot reproduce comes out of the decoder's door.** Whatever a
checkpoint file says, if `Vt.ofDecoded` returns a `Vt` at all then that `Vt` is
`Renderable`: the grid has exactly `rows` rows, each exactly `cols` wide, every cell holds
an emittable base of the width it claims with at most eight zero-width marks, every wide
glyph keeps its shadow — and the same of the stashed alt screen.

This is the claim finding R2 exists for. Before it, the door never saw the grid, so a
record whose `rows` byte disagreed with its grid's length decoded happily into a screen
`Render.restore` cannot repaint. `Checkpoint.load_renderable` is the same claim on the
real path, for *arbitrary bytes*. -/
theorem ofDecoded_renderable {cols rows : Nat} {grid : Array Row} {cursor : Cursor} {pen : Pen}
    {modes : Modes} {top bot : Nat} {tabs : Array Bool} {sb : Ring}
    {altGrid : Option (Array Row × Cursor × Pen)} {saved : Saved} {title : String}
    {g0Line g1Line shiftOut bell : Bool} {v : Vt}
    (h :
      Vt.ofDecoded cols rows grid cursor pen modes top bot tabs sb altGrid saved title g0Line g1Line
          shiftOut bell =
        some v) :
    Renderable v := by
  unfold Vt.ofDecoded at h
  split at h
  · rename_i hg
    simp only [Bool.and_eq_true] at hg
    obtain ⟨hgrid, -, halt⟩ := decodedRenderable_iff.mp hg.2
    cases h
    exact ⟨hgrid, halt⟩
  · exact absurd h (by simp)

/-- …and the tab ruler is the width of the screen. Split from `ofDecoded_renderable`
because `TabsOk` is not one of `Renderable`'s clauses and the claims that consume it
(`Render.restore_tabs_any`, `Resume.resume_tabs`) ask for it separately. -/
theorem ofDecoded_tabsOk {cols rows : Nat} {grid : Array Row} {cursor : Cursor} {pen : Pen}
    {modes : Modes} {top bot : Nat} {tabs : Array Bool} {sb : Ring}
    {altGrid : Option (Array Row × Cursor × Pen)} {saved : Saved} {title : String}
    {g0Line g1Line shiftOut bell : Bool} {v : Vt}
    (h :
      Vt.ofDecoded cols rows grid cursor pen modes top bot tabs sb altGrid saved title g0Line g1Line
          shiftOut bell =
        some v) :
    TabsOk v := by
  unfold Vt.ofDecoded at h
  split at h
  · rename_i hg
    simp only [Bool.and_eq_true] at hg
    obtain ⟨-, htabs, -⟩ := decodedRenderable_iff.mp hg.2
    cases h
    exact htabs
  · exact absurd h (by simp)

/-- **Nothing good is rejected.** The other half of the door: a `Vt` that is `Good`,
`Renderable` and ruler-consistent — which every live session's is, by `good_init`,
`renderable_init` and the `Pres`/frame machinery, and uniformly by
`good_of_liveReachable`/`renderable_of_liveReachable`/`tabsOk_of_liveReachable` — survives
the door unchanged, modulo the parser state a checkpoint deliberately forgets.

Without this, `ofDecoded_good` and `ofDecoded_renderable` would both be satisfied by a
constructor that returned `none` always, and §Restore would be a claim about a codec that
never restores anything. It is also exactly what `Checkpoint.rt_vt` needs, which is why
the round-trip theorem carries the same three hypotheses.

**This is the mirror**, and the two added hypotheses are its whole cost: `hren` and
`htabs` propagate from here to `rt_vt`, `load_save`, `load_save_exact` and five
`resume_*` claims. They cannot be dropped in favour of deriving them at the door — that
is what "validate, not clamp" means, and establishing `Renderable` from a bad record
would mean rebuilding the grid, which is `Vt.resize`, which the resume path refuses. -/
theorem ofDecoded_of_good {v : Vt} (h : Good v) (hren : Renderable v) (htabs : TabsOk v) :
    Vt.ofDecoded v.cols v.rows v.grid v.cursor v.pen v.modes v.top v.bot v.tabs v.sb v.altGrid
        v.saved v.title v.g0Line v.g1Line v.shiftOut v.bell =
      some v.quiesce := by
  unfold Vt.ofDecoded
  rw [ite_eq_left
      (by
        simp only [Bool.and_eq_true]
        exact
          ⟨decodedOk_iff.mpr
              ⟨h.colsPos, h.colsLe, h.rowsPos, h.rowsLe, h.curX, h.curY, h.savX, h.savY, h.topLe,
                h.botLt, h.sbLe, h.altCur⟩,
            decodedRenderable_iff.mpr ⟨hren.main, htabs, hren.alt⟩⟩)]
  cases v
  rfl

/-- **The exhibited attack, refused.** A record whose row count disagrees with its grid's
length is exactly finding R2's one-flipped-byte checkpoint — the `rows` byte of a real 4×2
record changed 2 → 3 — and it is `Good` for every clause `decodedOk` checks, which is why
it used to load. Now it does not.

The twin of `ofDecoded_none_of_cols_zero`, and the more instructive of the two: `cols = 0`
is refused by a dimension check anyone would think to write, and this one needed the
decoder to be handed the grid. `Tests/Checkpoint.lean` pins the byte-level version. -/
theorem ofDecoded_none_of_rows_mismatch {cols rows : Nat} {grid : Array Row} {cursor : Cursor}
    {pen : Pen} {modes : Modes} {top bot : Nat} {tabs : Array Bool} {sb : Ring}
    {altGrid : Option (Array Row × Cursor × Pen)} {saved : Saved} {title : String}
    {g0Line g1Line shiftOut bell : Bool} (hne : grid.size ≠ rows) :
    Vt.ofDecoded cols rows grid cursor pen modes top bot tabs sb altGrid saved title g0Line g1Line
        shiftOut bell =
      none := by
  have hno :
    (Vt.decodedOk cols rows cursor top bot sb altGrid saved &&
        Vt.decodedRenderable cols rows grid tabs altGrid) ≠
      true := by
    intro hg
    simp only [Bool.and_eq_true] at hg
    exact absurd (decodedRenderable_iff.mp hg.2).1.1 hne
  unfold Vt.ofDecoded
  rw [ite_eq_right hno]

/-! ### Frames discharge everything that does not write the grid -/

/-- An operation that leaves `grid`, `cols`, `rows` and `altGrid` alone
preserves `Renderable`. Most of `csiDispatch` is this. -/
theorem renderable_congr {v w : Vt} (h : Renderable v) (hg : w.grid = v.grid) (hc : w.cols = v.cols)
    (hr : w.rows = v.rows) (ha : w.altGrid = v.altGrid) : Renderable w := by
  refine
    ⟨by
      rw [hg, hc, hr]; exact h.main, fun g c p hs => ?_⟩
  rw [hc, hr]
  exact
    h.alt g c p
      (by
        rw [← ha]; exact hs)

/-! ### Writing cells -/

theorem cells_set {row : Row} (i : Nat) (c : Cell) (hrow : ∀ x, CellOk (row.at x)) (hc : CellOk c) :
    ∀ x, CellOk (Row.at (row.setIfInBounds i c) x) := by
  intro x
  unfold Row.at
  unfold Row.at at hrow
  by_cases hx : x = i
  · subst hx
    by_cases hb : x < row.size
    · rw [getD_set_self _ _ _ _ hb]; exact hc
    · rw [show row.setIfInBounds x c = row from by
          simp only [Array.setIfInBounds]; rw [dite_eq_right hb]]
      exact hrow x
  · rw [getD_set_ne _ _ _ _ _ hx]; exact hrow x

theorem cells_foldl {β : Type} {f : Row → β → Row}
    (hf : ∀ (r : Row) (b : β), (∀ x, CellOk (r.at x)) → ∀ x, CellOk ((f r b).at x)) :
    ∀ (l : List β) (row : Row),
      (∀ x, CellOk (row.at x)) →
        ∀ x, CellOk ((l.foldl f row).at x) := invariant_foldl (fun r => ∀ x, CellOk (r.at x)) f hf

theorem cells_mendAt {row : Row} (i : Nat) (hrow : ∀ x, CellOk (row.at x)) :
    ∀ x, CellOk ((Row.mendAt row i).at x) := by
  unfold Row.mendAt
  repeat' split
  all_goals
    first
    | exact cells_set _ _ hrow (cellOk_erased _)
    | exact cells_set _ _ hrow (cellOk_shadow _)
    | exact hrow

theorem cells_mend {row : Row} (hrow : ∀ x, CellOk (row.at x)) :
    ∀ x, CellOk ((Row.mend row).at x) := by
  unfold Row.mend
  exact cells_foldl (fun r b h => cells_mendAt b h) _ row hrow

/-- **The row-mutation workhorse.** A row whose cells are reproducible becomes a
reproducible row once mended — pairs included, by `mend_pairOk`. Every row
mutation ends in `Row.mend`, so every row mutation ends here. -/
theorem rowOk_mend {cols : Nat} {row : Row} (hsize : row.size = cols)
    (hcells : ∀ x, CellOk (row.at x)) : RowOk cols (Row.mend row) := by
  refine
    ⟨by
      rw [size_mend]; exact hsize, cells_mend hcells, fun x => ?_⟩
  by_cases hx : x < row.size
  · exact mend_pairOk row x hx
  · -- past the end every read is a default width-1 cell
    have hz : ∀ j, row.size ≤ j → (Row.mend row).at j = default := by
      intro j hj
      exact
        at_of_size_le _ _
          (by
            rw [size_mend]; exact hj)
    refine
      ⟨fun h2 =>
        absurd ((by rw [hz x (by omega)] : (Row.mend row).at x = default) ▸ h2) (by decide),
        fun h0 => ?_⟩
    exact absurd ((by rw [hz x (by omega)] : (Row.mend row).at x = default) ▸ h0) (by decide)

end Linger.Core.Vt

namespace Linger.Core.Vt

/-! ### One row at a time

Every cell-writing operation has the same shape: write into one row, then mend
it. `GridOkExcept y` is the state in between — every row reproducible except
row `y`, which has the right width and reproducible cells but no pair claim yet.
`mendRow` closes it. -/

theorem getD_of_lt {α} (g : Array α) (y : Nat) (d d' : α) (h : y < g.size) :
    g.getD y d = g.getD y d' := by simp [Array.getD, h]

def GridOkExcept (cols rows y : Nat) (g : Array Row) : Prop :=
  g.size = rows ∧
    (∀ y', y' ≠ y → RowOk cols (g.getD y' (blankRow cols {}))) ∧
    (g.getD y (blankRow cols {})).size = cols ∧ (∀ x, CellOk ((g.getD y (blankRow cols {})).at x))

theorem gridOkExcept_of_gridOk {cols rows : Nat} {g : Array Row} (y : Nat)
    (h : GridOk cols rows g) : GridOkExcept cols rows y g :=
  ⟨h.1, fun y' _ => h.2 y', (h.2 y).size, (h.2 y).cells⟩

/-- Writing one reproducible cell into the excepted row keeps the shape. -/
theorem gridOkExcept_set {cols rows y : Nat} {g : Array Row} (h : GridOkExcept cols rows y g)
    (x : Nat) (c : Cell) (hc : CellOk c) (d : Row)
    (hd : y < g.size → g.getD y d = g.getD y (blankRow cols {})) :
    GridOkExcept cols rows y (g.setIfInBounds y ((g.getD y d).setIfInBounds x c)) := by
  obtain ⟨hsz, hother, hrsz, hcells⟩ := h
  refine ⟨by simp [hsz], fun y' hy' => ?_, ?_, ?_⟩
  · rw [getD_set_ne _ _ _ _ _ hy']; exact hother y' hy'
  · by_cases hb : y < g.size
    · rw [getD_set_self _ _ _ _ hb, Array.size_setIfInBounds, hd hb]; exact hrsz
    · rw [show g.setIfInBounds y ((g.getD y d).setIfInBounds x c) = g from by
          simp only [Array.setIfInBounds]; rw [dite_eq_right hb]]
      exact hrsz
  · by_cases hb : y < g.size
    · rw [getD_set_self _ _ _ _ hb, hd hb]
      exact cells_set _ _ hcells hc
    · rw [show g.setIfInBounds y ((g.getD y d).setIfInBounds x c) = g from by
          simp only [Array.setIfInBounds]; rw [dite_eq_right hb]]
      exact hcells

/-- Replacing the excepted row wholesale, with a row built from it. -/
theorem gridOkExcept_replace {cols rows y : Nat} {g : Array Row} (h : GridOkExcept cols rows y g)
    (r : Row) (hsz : r.size = cols) (hcells : ∀ x, CellOk (r.at x)) :
    GridOkExcept cols rows y (g.setIfInBounds y r) := by
  obtain ⟨hgsz, hother, hrsz, hocells⟩ := h
  refine ⟨by simp [hgsz], fun y' hy' => ?_, ?_, ?_⟩
  · rw [getD_set_ne _ _ _ _ _ hy']; exact hother y' hy'
  · by_cases hb : y < g.size
    · rw [getD_set_self _ _ _ _ hb]; exact hsz
    · rw [show g.setIfInBounds y r = g from by
          simp only [Array.setIfInBounds]; rw [dite_eq_right hb]]
      exact hrsz
  · by_cases hb : y < g.size
    · rw [getD_set_self _ _ _ _ hb]; exact hcells
    · rw [show g.setIfInBounds y r = g from by
          simp only [Array.setIfInBounds]; rw [dite_eq_right hb]]
      exact hocells

/-- …and the repair closes it. -/
theorem gridOk_of_except {cols rows y : Nat} {g : Array Row} (h : GridOkExcept cols rows y g) :
    GridOk cols rows (g.setIfInBounds y (Row.mend (g.getD y (blankRow cols {})))) := by
  obtain ⟨hsz, hother, hrsz, hcells⟩ := h
  refine ⟨by simp [hsz], fun y' => ?_⟩
  by_cases hy' : y' = y
  · subst hy'
    by_cases hb : y' < g.size
    · rw [getD_set_self _ _ _ _ hb]
      exact rowOk_mend hrsz hcells
    · rw [show g.setIfInBounds y' (Row.mend (g.getD y' (blankRow cols {}))) = g from by
          simp only [Array.setIfInBounds]; rw [dite_eq_right hb]]
      -- out of range: the read is the default row, which is reproducible
      rw [show g.getD y' (blankRow cols {}) = blankRow cols {} from by simp [Array.getD, hb]]
      exact rowOk_blankRow cols {}
  · rw [getD_set_ne _ _ _ _ _ hy']
    exact hother y' hy'

/-! ### Folds that build a row -/

theorem size_foldl {β : Type} {f : Row → β → Row}
    (hf : ∀ (r : Row) (b : β), (f r b).size = r.size) :
    ∀ (l : List β) (row : Row), (l.foldl f row).size = row.size
  | [], _ => rfl
  | b :: l, row => by rw [List.foldl_cons, size_foldl hf l (f row b), hf row b]

end Linger.Core.Vt

namespace Linger.Core.Vt

/-! ### Renderable is preserved by every operation

Two shapes cover the emulator. An operation that leaves `grid`, `cols`, `rows`
and `altGrid` alone is discharged by its frame (`renderable_congr`) — that is
most of `csiDispatch`. An operation that writes cells goes
`GridOk → GridOkExcept y → write → mendRow`, which is why every row mutation
ends in `Row.mend`. -/

/-- Same grid, dimensions and stash ⇒ same verdict, whatever else moved. -/
theorem renderable_of_gridOk {v w : Vt} (h : Renderable v)
    (hc : w.cols = v.cols) (hr : w.rows = v.rows) (ha : w.altGrid = v.altGrid)
    (hg : GridOk w.cols w.rows w.grid) : Renderable w :=
  ⟨hg, fun g c p hs => by rw [hc, hr]; exact h.alt g c p (by rw [← ha]; exact hs)⟩

theorem gridOkExcept_putCell {v : Vt} {y : Nat}
    (h : GridOkExcept v.cols v.rows y v.grid) (x : Nat) (c : Cell) (hc : CellOk c) :
    GridOkExcept v.cols v.rows y (v.putCell x y c).grid := by
  unfold Vt.putCell Vt.getRow
  dsimp only
  exact gridOkExcept_set h x c hc _ (fun hb => getD_of_lt _ _ _ _ hb)

theorem gridOk_mendRow {v : Vt} {y : Nat}
    (h : GridOkExcept v.cols v.rows y v.grid) :
    GridOk v.cols v.rows (v.mendRow y).grid := by
  have hkey : (v.mendRow y).grid
      = v.grid.setIfInBounds y (Row.mend (v.grid.getD y (blankRow v.cols {}))) := by
    unfold Vt.mendRow Vt.getRow
    dsimp only
    by_cases hb : y < v.grid.size
    · rw [getD_of_lt v.grid y (blankRow v.cols v.pen) (blankRow v.cols {}) hb]
    · simp only [Array.setIfInBounds]
      rw [dite_eq_right hb, dite_eq_right hb]
  rw [hkey]
  exact gridOk_of_except h

/-- The write-then-repair sandwich, as one step. -/
theorem renderable_write_mend {v : Vt} (h : Renderable v) (y : Nat)
    (f : Vt → Vt) (hf : GridOkExcept v.cols v.rows y (f v).grid)
    (hc : (f v).cols = v.cols) (hr : (f v).rows = v.rows)
    (ha : (f v).altGrid = v.altGrid) :
    Renderable ((f v).mendRow y) := by
  refine renderable_of_gridOk h (by rw [Vt.mendRow]; exact hc) (by rw [Vt.mendRow]; exact hr)
    (by rw [Vt.mendRow]; exact ha) ?_
  have := gridOk_mendRow (v := f v) (y := y) (by rw [hc, hr]; exact hf)
  rw [hc, hr] at this
  show GridOk ((f v).mendRow y).cols ((f v).mendRow y).rows ((f v).mendRow y).grid
  rw [show ((f v).mendRow y).cols = v.cols from by rw [Vt.mendRow]; exact hc,
    show ((f v).mendRow y).rows = v.rows from by rw [Vt.mendRow]; exact hr]
  exact this

/-! #### Printing -/

theorem renderable_printPut {v : Vt} (h : Renderable v) (ch : Char) (w : Nat)
    (hpc : Emittable ch) (hw : charWidth ch = w) :
    Renderable (v.printPut ch w) := by
  have hbase : CellOk { base := ch, marks := [], width := w, pen := v.pen } :=
    ⟨hpc, fun _ => hw, Nat.zero_le _, fun _ hm => nomatch hm⟩
  have hblank : CellOk { base := ' ', marks := [], width := 1, pen := v.pen } :=
    ⟨emittable_space, fun _ => rfl, Nat.zero_le _, fun _ hm => nomatch hm⟩
  have hshadow : CellOk { base := ' ', marks := [], width := 0, pen := v.pen } :=
    ⟨emittable_space, fun hz => absurd rfl hz, Nat.zero_le _,
      fun _ hm => nomatch hm⟩
  unfold Vt.printPut
  dsimp only
  split
  · exact renderable_write_mend h _ (fun u => u.putCell v.cursor.x v.cursor.y _)
      (gridOkExcept_putCell (gridOkExcept_of_gridOk _ h.main) _ _ hblank) rfl rfl rfl
  · split
    · exact renderable_write_mend h _
        (fun u => (u.putCell v.cursor.x v.cursor.y _).putCell (v.cursor.x + 1) v.cursor.y _)
        (gridOkExcept_putCell (gridOkExcept_putCell
          (gridOkExcept_of_gridOk _ h.main) _ _ hbase) _ _ hshadow) rfl rfl rfl
    · exact renderable_write_mend h _ (fun u => u.putCell v.cursor.x v.cursor.y _)
        (gridOkExcept_putCell (gridOkExcept_of_gridOk _ h.main) _ _ hbase) rfl rfl rfl

/-- Every cell of a renderable emulator is reproducible, including the
out-of-range reads that `getCell` answers with a default. -/
theorem cellOk_getCell {v : Vt} (h : Renderable v) (x y : Nat) : CellOk (v.getCell x y) := by
  unfold Vt.getCell Vt.getRow
  by_cases hb : y < v.grid.size
  · rw [getD_of_lt v.grid y (blankRow v.cols v.pen) (blankRow v.cols {}) hb]
    exact (h.main.2 y).cells _
  · rw [show v.grid.getD y (blankRow v.cols v.pen) = blankRow v.cols v.pen from by
      simp [Array.getD, hb]]
    exact (rowOk_blankRow v.cols v.pen).cells _

/-- Appending one legal mark to a cell, then repairing the row. Stated over an
arbitrary column so `printMark`'s shadow redirect does not have to be unfolded
inside the proof. -/
theorem renderable_addMark {v : Vt} (h : Renderable v) (cx y : Nat) (ch : Char)
    (hpc : Emittable ch) (hw : charWidth ch = 0)
    (hcap : (v.getCell cx y).marks.length < 8) :
    Renderable ((v.putCell cx y { v.getCell cx y with
      marks := (v.getCell cx y).marks ++ [ch] }).mendRow y) := by
  have hold := cellOk_getCell h cx y
  refine renderable_write_mend h y (fun u => u.putCell cx y _)
    (gridOkExcept_putCell (gridOkExcept_of_gridOk y h.main) cx _ ?_) rfl rfl rfl
  refine ⟨hold.base, hold.width, ?_, ?_⟩
  · simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · intro m hm
    rcases List.mem_append.mp hm with hm' | hm'
    · exact hold.marks m hm'
    · rw [show m = ch from by simpa using hm']
      exact ⟨hw, hpc⟩

theorem renderable_printMark {v : Vt} (h : Renderable v) (ch : Char)
    (hpc : Emittable ch) (hw : charWidth ch = 0) :
    Renderable (v.printMark ch) := by
  unfold Vt.printMark
  dsimp only
  repeat' split
  all_goals first
    | exact h
    | exact renderable_addMark h _ _ _ hpc hw (by omega)

end Linger.Core.Vt

namespace Linger.Core.Vt

/-! #### Whole-row moves, and the stages around a write -/

theorem rowOk_getRow {v : Vt} (h : Renderable v) (y : Nat) : RowOk v.cols (v.getRow y) := by
  unfold Vt.getRow
  by_cases hb : y < v.grid.size
  · rw [getD_of_lt v.grid y (blankRow v.cols v.pen) (blankRow v.cols {}) hb]
    exact h.main.2 y
  · rw [show v.grid.getD y (blankRow v.cols v.pen) = blankRow v.cols v.pen from by
      simp [Array.getD, hb]]
    exact rowOk_blankRow v.cols v.pen

theorem gridOk_set_row {cols rows : Nat} {g : Array Row} (h : GridOk cols rows g)
    (y : Nat) (r : Row) (hr : RowOk cols r) : GridOk cols rows (g.setIfInBounds y r) := by
  refine ⟨by simp [h.1], fun y' => ?_⟩
  by_cases hy' : y' = y
  · subst hy'
    by_cases hb : y' < g.size
    · rw [getD_set_self _ _ _ _ hb]; exact hr
    · rw [show g.setIfInBounds y' r = g from by
        simp only [Array.setIfInBounds]; rw [dite_eq_right hb]]
      exact h.2 y'
  · rw [getD_set_ne _ _ _ _ _ hy']; exact h.2 y'

theorem gridOk_foldl {cols rows : Nat} {β : Type} {f : Array Row → β → Array Row}
    (hf : ∀ (g : Array Row) (b : β), GridOk cols rows g → GridOk cols rows (f g b)) :
    ∀ (l : List β) (g : Array Row), GridOk cols rows g → GridOk cols rows (l.foldl f g) :=
  invariant_foldl (GridOk cols rows) f hf

/-- Scrolling moves whole rows and blanks one, so it never breaks a pair. The
scrollback push is outside `Renderable`'s scope (a repaint paints the screen). -/
theorem renderable_scrollUpIn {v : Vt} (h : Renderable v) (t b : Nat) (a : Bool) :
    Renderable (v.scrollUpIn t b a) := by
  have hgrid : GridOk v.cols v.rows (v.scrollUpIn t b a).grid := by
    have hstep : GridOk v.cols v.rows
        ((List.range (b - t)).foldl
          (fun g i => g.setIfInBounds (t + i) (v.getRow (t + i + 1))) v.grid) :=
      gridOk_foldl (fun g i hg => gridOk_set_row hg _ _ (rowOk_getRow h _)) _ _ h.main
    have hblank := gridOk_set_row hstep b (blankRow v.cols v.pen) (rowOk_blankRow _ _)
    unfold Vt.scrollUpIn
    dsimp only
    split <;> exact hblank
  refine renderable_of_gridOk h ?_ ?_ ?_ ?_
  · rw [frame_scrollUpIn]
  · rw [frame_scrollUpIn]
  · rw [frame_scrollUpIn]
  · rw [show (v.scrollUpIn t b a).cols = v.cols from by rw [frame_scrollUpIn],
      show (v.scrollUpIn t b a).rows = v.rows from by rw [frame_scrollUpIn]]
    exact hgrid

theorem renderable_scrollDownIn {v : Vt} (h : Renderable v) (t b : Nat) :
    Renderable (v.scrollDownIn t b) := by
  have hgrid : GridOk v.cols v.rows (v.scrollDownIn t b).grid := by
    have hstep : GridOk v.cols v.rows
        ((List.range (b - t)).foldl
          (fun g i => g.setIfInBounds (b - i) (v.getRow (b - i - 1))) v.grid) :=
      gridOk_foldl (fun g i hg => gridOk_set_row hg _ _ (rowOk_getRow h _)) _ _ h.main
    exact gridOk_set_row hstep t (blankRow v.cols v.pen) (rowOk_blankRow _ _)
  refine renderable_of_gridOk h ?_ ?_ ?_ ?_
  · rw [frame_scrollDownIn]
  · rw [frame_scrollDownIn]
  · rw [frame_scrollDownIn]
  · rw [show (v.scrollDownIn t b).cols = v.cols from by rw [frame_scrollDownIn],
      show (v.scrollDownIn t b).rows = v.rows from by rw [frame_scrollDownIn]]
    exact hgrid

theorem renderable_scrollUp {v : Vt} (h : Renderable v) : Renderable v.scrollUp :=
  renderable_scrollUpIn h _ _ _

theorem renderable_scrollDown {v : Vt} (h : Renderable v) : Renderable v.scrollDown :=
  renderable_scrollDownIn h _ _

/-- Cursor-only motion: the frame says the grid, dimensions and stash are
untouched, so the verdict carries. -/
theorem renderable_clearPending {v : Vt} (h : Renderable v) : Renderable v.clearPending :=
  renderable_congr h rfl rfl rfl rfl

theorem renderable_carriageReturn {v : Vt} (h : Renderable v) : Renderable v.carriageReturn :=
  renderable_congr h rfl rfl rfl rfl

theorem renderable_printAdvance {v : Vt} (h : Renderable v) (w : Nat) :
    Renderable (v.printAdvance w) := by
  refine renderable_congr h ?_ ?_ ?_ ?_ <;> rw [frame_printAdvance]

theorem renderable_lineFeed {v : Vt} (h : Renderable v) : Renderable v.lineFeed := by
  have h' := renderable_clearPending h
  unfold Vt.lineFeed
  dsimp only
  split
  · exact renderable_scrollUp h'
  · split
    · exact renderable_congr h' rfl rfl rfl rfl
    · exact h'

theorem renderable_reverseIndex {v : Vt} (h : Renderable v) : Renderable v.reverseIndex := by
  have h' := renderable_clearPending h
  unfold Vt.reverseIndex
  dsimp only
  split
  · exact renderable_scrollDown h'
  · exact renderable_congr h' rfl rfl rfl rfl

theorem renderable_printWrap {v : Vt} (h : Renderable v) : Renderable v.printWrap := by
  unfold Vt.printWrap
  split
  · exact renderable_lineFeed (renderable_carriageReturn h)
  · exact renderable_clearPending h

theorem renderable_printWideWrap {v : Vt} (h : Renderable v) (w : Nat) :
    Renderable (v.printWideWrap w) := by
  unfold Vt.printWideWrap
  split
  · exact renderable_lineFeed (renderable_carriageReturn h)
  · exact h

/-- Insert mode shifts cells within a row and then repairs it. Every cell it
writes came from the same row, so `CellOk` carries; the width bookkeeping is
`Row.mend`'s. -/
theorem renderable_printShift {v : Vt} (h : Renderable v) (w : Nat) :
    Renderable (v.printShift w) := by
  unfold Vt.printShift
  dsimp only
  split
  · rename_i hins
    refine renderable_of_gridOk h rfl rfl rfl ?_
    show GridOk v.cols v.rows (v.grid.setIfInBounds v.cursor.y (Row.mend _))
    refine gridOk_set_row h.main _ _ (rowOk_mend ?_ ?_)
    · exact size_foldl (fun r b => by simp) _ _ |>.trans (rowOk_getRow h v.cursor.y).size
    · exact cells_foldl (fun r b hr =>
        cells_set _ _ hr ((rowOk_getRow h v.cursor.y).cells _)) _ _
        (rowOk_getRow h v.cursor.y).cells
  · exact h

/-- **Printing preserves `Renderable`.** The stored codepoint is
`printableChar`-stable by construction, which is what `CellOk.base` needs, and
its width is `charWidth` of exactly that codepoint. -/
theorem renderable_print {v : Vt} (h : Renderable v) (ch : Char) :
    Renderable (v.print ch) := by
  have hpc' : ∀ (u : Vt) (c : Char), Emittable (u.printChar c) := by
    intro u c
    unfold Vt.printChar
    exact printableChar_emittable _
  unfold Vt.print
  dsimp only
  split
  · rename_i h0
    exact renderable_printMark h _ (hpc' v ch) (by simpa using h0)
  · exact renderable_printAdvance (renderable_printPut
      (renderable_printShift (renderable_printWideWrap (renderable_printWrap h) _) _) _ _
        (hpc' v ch) rfl) _

end Linger.Core.Vt

namespace Linger.Core.Vt

/-! #### Erase, insert, delete -/

/-- Every row mutation has the same skeleton: fold writes over the row, mend it,
put it back. Only the written cells differ, and each is either copied from the
same row or an erased blank. -/
theorem renderable_row_mutation {v : Vt} (h : Renderable v) {β : Type}
    (y : Nat) (f : Row → β → Row) (l : List β)
    (hsz : ∀ (r : Row) (b : β), (f r b).size = r.size)
    (hc : ∀ (r : Row) (b : β), (∀ x, CellOk (r.at x)) → ∀ x, CellOk ((f r b).at x)) :
    GridOk v.cols v.rows
      (v.grid.setIfInBounds y (Row.mend (l.foldl f (v.getRow y)))) := by
  refine gridOk_set_row h.main _ _ (rowOk_mend ?_ ?_)
  · exact (size_foldl hsz l (v.getRow y)).trans (rowOk_getRow h y).size
  · exact cells_foldl hc l (v.getRow y) (rowOk_getRow h y).cells

theorem renderable_eraseRowSpan {v : Vt} (h : Renderable v) (y a b : Nat) :
    Renderable (v.eraseRowSpan y a b) := by
  refine renderable_of_gridOk h rfl rfl rfl ?_
  exact renderable_row_mutation h y _ _ (fun r b => by simp)
    (fun r b hr => cells_set _ _ hr (cellOk_erased _))

theorem renderable_eraseChars {v : Vt} (h : Renderable v) (n : Nat) :
    Renderable (v.eraseChars n) := renderable_eraseRowSpan h _ _ _

theorem renderable_eraseLine {v : Vt} (h : Renderable v) (m : Nat) :
    Renderable (v.eraseLine m) := by
  unfold Vt.eraseLine
  split <;> exact renderable_eraseRowSpan h _ _ _

theorem renderable_foldl {β : Type} {f : Vt → β → Vt}
    (hf : ∀ (u : Vt) (b : β), Renderable u → Renderable (f u b)) :
    ∀ (l : List β) (v : Vt), Renderable v → Renderable (l.foldl f v) :=
  invariant_foldl Renderable f hf

theorem renderable_eraseScreen {v : Vt} (h : Renderable v) (m : Nat) :
    Renderable (v.eraseScreen m) := by
  unfold Vt.eraseScreen
  split
  · exact renderable_foldl (fun u i hu => renderable_eraseRowSpan hu _ _ _) _ _
      (renderable_eraseLine h _)
  · exact renderable_foldl (fun u i hu => renderable_eraseRowSpan hu _ _ _) _ _
      (renderable_eraseLine h _)
  · -- ED 3 also drops scrollback, which `Renderable` does not watch
    exact renderable_congr
      (renderable_foldl (fun u i hu => renderable_eraseRowSpan hu _ _ _) _ _ h)
      rfl rfl rfl rfl
  · exact renderable_foldl (fun u i hu => renderable_eraseRowSpan hu _ _ _) _ _ h

theorem renderable_deleteChars {v : Vt} (h : Renderable v) (n : Nat) :
    Renderable (v.deleteChars n) := by
  refine renderable_of_gridOk h rfl rfl rfl ?_
  exact renderable_row_mutation h _ _ _ (fun r b => by simp)
    (fun r b hr => cells_set _ _ hr (by
      split
      · exact (rowOk_getRow h v.cursor.y).cells _
      · exact cellOk_erased _))

theorem renderable_insertChars {v : Vt} (h : Renderable v) (n : Nat) :
    Renderable (v.insertChars n) := by
  refine renderable_of_gridOk h rfl rfl rfl ?_
  exact renderable_row_mutation h _ _ _ (fun r b => by simp)
    (fun r b hr => cells_set _ _ hr (by
      split
      · exact (rowOk_getRow h v.cursor.y).cells _
      · exact cellOk_erased _))

theorem renderable_insertLines {v : Vt} (h : Renderable v) (n : Nat) :
    Renderable (v.insertLines n) := by
  unfold Vt.insertLines
  split
  · exact h
  · exact renderable_foldl (fun u i hu => renderable_scrollDownIn hu _ _) _ _ h

theorem renderable_deleteLines {v : Vt} (h : Renderable v) (n : Nat) :
    Renderable (v.deleteLines n) := by
  unfold Vt.deleteLines
  split
  · exact h
  · exact renderable_foldl (fun u i hu => renderable_scrollUpIn hu _ _ _) _ _ h

/-! #### Cursor, pen, modes, and the alt screen -/

theorem renderable_moveTo {v : Vt} (h : Renderable v) (x y : Nat) :
    Renderable (v.moveTo x y) := renderable_congr h rfl rfl rfl rfl

/-- Setting a field and then homing the cursor, as one step. Stated over the
*result* record so `csiDispatch`'s `DECSTBM` and `setMode`'s `DECOM` arms unify
with it instead of with the incoming state. -/
theorem renderable_moveTo_congr {v w : Vt} (h : Renderable v)
    (hg : w.grid = v.grid) (hc : w.cols = v.cols) (hr : w.rows = v.rows)
    (ha : w.altGrid = v.altGrid) (x y : Nat) : Renderable (w.moveTo x y) :=
  renderable_moveTo (renderable_congr h hg hc hr ha) x y

theorem renderable_moveRel {v : Vt} (h : Renderable v) (dx dy : Int) :
    Renderable (v.moveRel dx dy) := renderable_congr h rfl rfl rfl rfl

theorem renderable_setCol {v : Vt} (h : Renderable v) (x : Nat) :
    Renderable (v.setCol x) := renderable_congr h rfl rfl rfl rfl

theorem renderable_applySgr {v : Vt} (h : Renderable v) (ps : List (Nat × Bool)) :
    Renderable (v.applySgr ps) := renderable_congr h rfl rfl rfl rfl

theorem renderable_backspace {v : Vt} (h : Renderable v) : Renderable v.backspace := by
  refine renderable_congr h ?_ ?_ ?_ ?_ <;> rw [frame_backspace]

theorem renderable_tab {v : Vt} (h : Renderable v) : Renderable v.tab := by
  refine renderable_congr h ?_ ?_ ?_ ?_ <;> rw [frame_tab]

theorem renderable_backTab {v : Vt} (h : Renderable v) : Renderable v.backTab := by
  refine renderable_congr h ?_ ?_ ?_ ?_ <;> rw [frame_backTab]

theorem renderable_enterAlt {v : Vt} (h : Renderable v) (s : Bool) :
    Renderable (v.enterAlt s) := by
  unfold Vt.enterAlt
  split
  · exact h
  · refine ⟨gridOk_replicate _ _ _, fun g c p hs => ?_⟩
    -- the stash is the main grid we just left
    simp only [Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨hg, -, -⟩ := hs
    subst hg
    exact h.main

theorem renderable_leaveAlt {v : Vt} (h : Renderable v) (s : Bool) :
    Renderable (v.leaveAlt s) := by
  unfold Vt.leaveAlt
  split
  · exact h
  · rename_i g cur pen heq
    exact ⟨h.alt g cur pen heq, fun _ _ _ hs => nomatch hs⟩

theorem renderable_setMode {v : Vt} (h : Renderable v) (priv : Bool) (n : Nat) (on : Bool) :
    Renderable (v.setMode priv n on) := by
  unfold Vt.setMode
  split <;> split
  all_goals first
    | exact h
    | exact renderable_congr h rfl rfl rfl rfl
    | (refine renderable_moveTo_congr h ?_ ?_ ?_ ?_ 0 0 <;> rfl)
    | (split <;> first
        | exact renderable_enterAlt h _
        | exact renderable_leaveAlt h _
        | exact renderable_congr h rfl rfl rfl rfl)

theorem renderable_setModes {v : Vt} (h : Renderable v) (priv : Bool)
    (ps : List (Nat × Bool)) (on : Bool) : Renderable (v.setModes priv ps on) :=
  setModes_invariant Renderable priv on ps
    (fun _ p _ hh => renderable_setMode hh priv p.1 on) v h

/-! #### Dispatch, and the parser -/

theorem renderable_csiDispatch {v : Vt} (h : Renderable v) (s : CsiState) (final : UInt8) :
    Renderable (v.csiDispatch s final) := by
  unfold Vt.csiDispatch
  split
  · exact h
  · split
    all_goals first
      | exact h
      | exact renderable_congr h rfl rfl rfl rfl
      | exact renderable_insertChars h _
      | exact renderable_moveRel h _ _
      | exact renderable_carriageReturn (renderable_moveRel h _ _)
      | exact renderable_setCol h _
      | exact renderable_moveTo h _ _
      | exact renderable_eraseScreen h _
      | exact renderable_eraseLine h _
      | exact renderable_insertLines h _
      | exact renderable_deleteLines h _
      | exact renderable_deleteChars h _
      | exact renderable_eraseChars h _
      | exact renderable_setModes h _ _ _
      | exact renderable_foldl (fun u i hu => renderable_tab hu) _ _ h
      | exact renderable_foldl (fun u i hu => renderable_scrollUp hu) _ _ h
      | exact renderable_foldl (fun u i hu => renderable_scrollDown hu) _ _ h
      | exact renderable_foldl (fun u i hu => renderable_backTab hu) _ _ h
      | (split <;> first
          | exact renderable_applySgr h _
          | exact renderable_congr h rfl rfl rfl rfl
          | exact h
          | (dsimp only
             split <;> first
              | exact h
              | (refine renderable_moveTo_congr h ?_ ?_ ?_ ?_ 0 0 <;> rfl)))

theorem renderable_acceptChar {v : Vt} (h : Renderable v) (n : Nat) :
    Renderable (v.acceptChar n) := by
  unfold Vt.acceptChar
  split <;> exact renderable_print h _

theorem renderable_ctl {v : Vt} (h : Renderable v) (b : UInt8) : Renderable (v.ctl b) := by
  unfold Vt.ctl
  split
  all_goals first
    | exact renderable_congr h rfl rfl rfl rfl
    | exact renderable_backspace h
    | exact renderable_tab h
    | exact renderable_lineFeed h
    | exact renderable_carriageReturn h
    | exact h

theorem renderable_oscFinish {v : Vt} (h : Renderable v) (acc : Array UInt8) :
    Renderable (v.oscFinish acc) := by
  unfold Vt.oscFinish
  dsimp only
  repeat' split
  all_goals exact renderable_congr h rfl rfl rfl rfl

theorem renderable_csiFinish {v : Vt} (h : Renderable v) (s : CsiState) (final : UInt8) :
    Renderable (v.csiFinish s final) := by
  unfold Vt.csiFinish
  exact renderable_congr (renderable_csiDispatch h _ _) rfl rfl rfl rfl

/-- Setting the UTF-8 accumulator and then accepting a codepoint. Named for the
same reason as `renderable_moveTo_congr`: `stepGround`'s continuation-byte arm
applies `acceptChar` to a *record*, and an `exact` with `rfl` arguments would fix
the implicit state to the incoming one instead. -/
theorem renderable_acceptChar_congr {v w : Vt} (h : Renderable v)
    (hg : w.grid = v.grid) (hc : w.cols = v.cols) (hr : w.rows = v.rows)
    (ha : w.altGrid = v.altGrid) (n : Nat) : Renderable (w.acceptChar n) :=
  renderable_acceptChar (renderable_congr h hg hc hr ha) n

theorem renderable_stepGround {v : Vt} (h : Renderable v) (b : UInt8) :
    Renderable (v.stepGround b) := by
  unfold Vt.stepGround
  repeat' split
  all_goals
    grind [renderable_congr, renderable_ctl, renderable_acceptChar,
      renderable_acceptChar_congr]

theorem renderable_stepEsc {v : Vt} (h : Renderable v) (b : UInt8) :
    Renderable (v.stepEsc b) := by
  unfold Vt.stepEsc
  split
  all_goals first
    | exact h
    | exact renderable_congr h rfl rfl rfl rfl
    | exact renderable_congr (renderable_lineFeed h) rfl rfl rfl rfl
    | exact renderable_congr (renderable_lineFeed (renderable_carriageReturn h)) rfl rfl rfl rfl
    | exact renderable_congr (renderable_reverseIndex h) rfl rfl rfl rfl
    | -- RIS: a fresh screen of the same dimensions
      (dsimp only
       split <;> exact renderable_congr (renderable_init v.cols v.rows) rfl rfl rfl rfl)
    | (repeat' split
       all_goals exact renderable_congr h rfl rfl rfl rfl)

theorem renderable_stepEscInter {v : Vt} (h : Renderable v) (i b : UInt8) :
    Renderable (v.stepEscInter i b) := by
  unfold Vt.stepEscInter
  dsimp only
  repeat' split
  all_goals exact renderable_congr h rfl rfl rfl rfl

theorem renderable_stepCsi {v : Vt} (h : Renderable v) (s : CsiState) (b : UInt8) :
    Renderable (v.stepCsi s b) := by
  unfold Vt.stepCsi
  repeat' split
  all_goals first
    | exact renderable_congr h rfl rfl rfl rfl
    | exact renderable_csiFinish h _ _
    | exact renderable_ctl h _

theorem renderable_stepOsc {v : Vt} (h : Renderable v) (acc : Array UInt8) (e : Bool)
    (b : UInt8) : Renderable (v.stepOsc acc e b) := by
  unfold Vt.stepOsc
  repeat' split
  all_goals first
    | exact renderable_oscFinish h _
    | exact renderable_congr h rfl rfl rfl rfl

theorem renderable_stepStr {v : Vt} (h : Renderable v) (e : Bool) (b : UInt8) :
    Renderable (v.stepStr e b) := by
  unfold Vt.stepStr
  repeat' split
  all_goals exact renderable_congr h rfl rfl rfl rfl

/-- **§Renderable is preserved by every byte.** With `renderable_init` this
covers every state the daemon can hold: the emulator never stores a grid the row
painter cannot express, for any input at all. -/
theorem renderable_step {v : Vt} (h : Renderable v) (b : UInt8) : Renderable (v.step b) := by
  unfold Vt.step Vt.abortUtf8
  dsimp only
  have h' : Renderable (if v.u8need > 0 && (b < 0x80 || b ≥ 0xC0) then
      { v with u8need := 0, u8acc := 0 } else v) := by
    split
    · exact renderable_congr h rfl rfl rfl rfl
    · exact h
  split
  all_goals first
    | exact renderable_stepGround h' _
    | exact renderable_stepEsc h' _
    | exact renderable_stepEscInter h' _ _
    | exact renderable_stepCsi h' _ _
    | exact renderable_stepOsc h' _ _ _
    | exact renderable_stepStr h' _ _

/-- The stream form. -/
theorem renderable_feed {v : Vt} (h : Renderable v) (bytes : List UInt8) :
    Renderable (v.feed bytes) :=
  renderable_foldl (fun _ b hu => renderable_step hu b) bytes v h

/-- Forgetting partial parser state cannot change the screen. -/
theorem renderable_quiesce {v : Vt} (h : Renderable v) : Renderable v.quiesce :=
  renderable_congr h rfl rfl rfl rfl

end Linger.Core.Vt

namespace Linger.Core.Vt

/-! #### Resize

The last operation that writes cells. Both `resizeRow` and `Vt.resize`'s `fit`
are maps over their target range, so each needs one lemma about `getD` of a
mapped `Array.range` and nothing about array splicing. -/

/-- Reading a mapped `Array.range`: in range it is the function, out of range the
default. Generic in the element type, because `resizeRow` maps over cells and
`Vt.resize`'s `fit` maps over rows. -/
theorem getD_map_range {α : Type} (f : Nat → α) (n x : Nat) (d : α) :
    ((Array.range n).map f).getD x d = if x < n then f x else d := by
  by_cases hb : x < n
  · rw [ite_eq_left hb]
    have hsz : x < ((Array.range n).map f).size := by simp [hb]
    rw [Array.getD, dite_eq_left hsz]
    simp
  · rw [ite_eq_right hb]
    have hsz : ¬ x < ((Array.range n).map f).size := by simpa using hb
    rw [Array.getD, dite_eq_right hsz]

theorem cells_map_range (f : Nat → Cell) (n : Nat) (hf : ∀ i, CellOk (f i)) :
    ∀ x, CellOk (Row.at ((Array.range n).map f) x) := by
  intro x
  unfold Row.at
  rw [getD_map_range]
  split
  · exact hf x
  · exact cellOk_default

theorem rowOk_resizeRow (row : Row) (c : Nat) (p : Pen) (h : ∀ x, CellOk (row.at x)) :
    RowOk c (resizeRow row c p) := by
  unfold resizeRow
  refine rowOk_mend (by simp) (cells_map_range _ _ (fun i => ?_))
  by_cases hi : i < row.size
  · rw [ite_eq_left hi]
    exact h i
  · rw [ite_eq_right hi]
    exact cellOk_erased p

/-- A grid re-fitted to `c × r` is reproducible: each row is an old row at the
new width, or a blank. -/
theorem gridOk_fit {cols : Nat} {g : Array Row} (c r : Nat)
    (h : ∀ y, RowOk cols (g.getD y (blankRow cols {}))) :
    GridOk c r ((Array.range r).map (fun j =>
      let src := if g.size ≥ r then g.size - r + j else j
      if src < g.size then resizeRow (g.getD src #[]) c {} else blankRow c {})) := by
  -- a source row that exists is one of `g`'s, whatever default the read carries
  have hsrc : ∀ (j : Nat), j < g.size → ∀ x, CellOk (Row.at (g.getD j (#[] : Row)) x) := by
    intro j hj x
    have hc := (h j).cells x
    unfold Row.at at hc ⊢
    rw [getD_of_lt g j (blankRow cols {}) (#[] : Row) hj] at hc
    exact hc
  refine ⟨by simp, fun y => ?_⟩
  rw [getD_map_range]
  by_cases hy : y < r
  · rw [ite_eq_left hy]
    dsimp only
    by_cases hge : g.size ≥ r
    · rw [ite_eq_left hge]
      by_cases hb : g.size - r + y < g.size
      · rw [ite_eq_left hb]
        exact rowOk_resizeRow _ _ _ (hsrc _ hb)
      · rw [ite_eq_right hb]
        exact rowOk_blankRow c {}
    · rw [ite_eq_right hge]
      by_cases hb : y < g.size
      · rw [ite_eq_left hb]
        exact rowOk_resizeRow _ _ _ (hsrc _ hb)
      · rw [ite_eq_right hb]
        exact rowOk_blankRow c {}
  · rw [ite_eq_right hy]
    exact rowOk_blankRow c {}

theorem renderable_resize {v : Vt} (h : Renderable v) (cols rows : Nat) :
    Renderable (v.resize cols rows) := by
  unfold Vt.resize
  refine ⟨gridOk_fit _ _ h.main.2, fun g c p hs => ?_⟩
  dsimp only at hs
  rcases hv : v.altGrid with - | x
  · rw [hv] at hs; exact nomatch hs
  · obtain ⟨g0, c0, p0⟩ := x
    rw [hv] at hs
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨hg, -, -⟩ := hs
    subst hg
    exact gridOk_fit _ _ (h.alt g0 c0 p0 hv).2

/-! ### §LiveReachable — the states a running session can actually hold

The predicate a replay theorem may assume: the least set containing a fresh
emulator and closed under the things a live session does to one — feed pty
bytes, resize on attach, forget partial parser state (what a checkpoint
save/load does), **and come off disk through the decoder's door**.

**The fifth rung arrived after finding R2** (SCRATCHPAD.md), and the earlier prose
here — "fidelity is claimed for these and not for an arbitrary decoded checkpoint,
which no theorem can vouch for" — was true when the door only decided `Good`. It is
not any more: `Vt.ofDecoded` now decides `Renderable` and the ruler as well, so
`ofDecoded_good`/`ofDecoded_renderable`/`ofDecoded_tabsOk` vouch for exactly the
three components the relation supplies, and `ofDecoded_u8Ok` for the fourth because
the door *fixes* `u8need := 0` and `u8acc := 0`.

The premise is the door's own conclusion (`Vt.ofDecoded … = some v`) and that is
load-bearing rather than stylistic. Step 3 measured a rung premised on `Good v`
**unsound**: `Good` implies neither the grid's shape nor a zeroed UTF-8
accumulator, so that rung broke `renderable_of_liveReachable` and
`u8Ok_of_liveReachable` — the two lemmas the relation exists to supply. Do not
re-derive that; the error texts are in the Step 3 record.

What the rung widens, deliberately: all four `*_of_liveReachable` lemmas now speak
of decoded states too, so every `Render.restore_*_reachable` theorem — whose
statements are unchanged — covers a receiver or a subject that came off disk, and
`Session.LiveVt` becomes provable for a **resumed** daemon
(`Session.liveVt_boot_of_load`, via `Checkpoint.load_live`). That last one is why
the rung was added at all: without it the resumed session's shape invariant travels
through `renderable_feed`/`renderable_resize` one operation at a time instead of
through one daemon-level theorem.

What it does **not** widen: nothing here says a ring row is the screen's width.
`Vt.resize` leaves the scrollback at its old width by design, so
`Render.restore_sb_exact`'s `hrok` is immovable by any amount of reachability — Step
3's measurement, and the reason the decoder deliberately does not validate the ring
either. -/

inductive LiveReachableVt : Vt → Prop where
  | init (cols rows : Nat) : LiveReachableVt (Vt.init cols rows)
  | feed {v : Vt} (h : LiveReachableVt v) (bytes : List UInt8) : LiveReachableVt (v.feed bytes)
  | resize {v : Vt} (h : LiveReachableVt v) (cols rows : Nat) :
      LiveReachableVt (v.resize cols rows)
  | quiesce {v : Vt} (h : LiveReachableVt v) : LiveReachableVt v.quiesce
  /-- **The resume rung.** A `Vt` the decoder's door accepted is one a live session can
  hold — not because the record on disk was trustworthy, but because the door refuses
  every record that does not describe such a state. The premise is `Vt.ofDecoded`'s own
  `some`, never `Good v`; see this section's docstring for why that distinction is the
  difference between sound and unsound. -/
  | ofDecoded {cols rows : Nat} {grid : Array Row} {cursor : Cursor} {pen : Pen} {modes : Modes}
      {top bot : Nat} {tabs : Array Bool} {sb : Ring}
      {altGrid : Option (Array Row × Cursor × Pen)} {saved : Saved} {title : String}
      {g0Line g1Line shiftOut bell : Bool} {v : Vt}
      (h :
        Vt.ofDecoded cols rows grid cursor pen modes top bot tabs sb altGrid saved title g0Line
            g1Line shiftOut bell =
          some v) :
      LiveReachableVt v

/-- **The shape hypothesis, discharged.** Every state a live session can hold is
one the row painter can express — so the replay theorem needs no side condition
on the grid, and cannot be satisfied vacuously by excluding awkward states.

The `ofDecoded` arm is what widens this from "every state a fresh boot reaches" to
"every state the daemon can hold, resumed sessions included", and it is the arm a
`Good`-premised rung could not have closed (§LiveReachable's docstring). -/
theorem renderable_of_liveReachable {v : Vt} (h : LiveReachableVt v) : Renderable v := by
  induction h with
  | init c r => exact renderable_init c r
  | feed _ bytes ih => exact renderable_feed ih bytes
  | resize _ c r ih => exact renderable_resize ih c r
  | quiesce _ ih => exact renderable_quiesce ih
  | ofDecoded hd => exact ofDecoded_renderable hd

/-- …and `Good` likewise, so the two invariants travel together. -/
theorem good_of_liveReachable {v : Vt} (h : LiveReachableVt v) : Good v := by
  induction h with
  | init c r => exact good_init c r
  | feed _ bytes ih => exact Good.feed bytes ih
  | resize _ c r ih => exact Good.resize c r ih
  | quiesce _ ih => exact Good.set_ground (Good.set_u8 0 0 (by omega) ih)
  | ofDecoded hd => exact ofDecoded_good hd

/-- **The decoder invariant a live state carries.** Whenever no UTF-8 sequence is pending the
accumulator is zero — `stepGround` zeroes it on the byte that *completes* a sequence, and
`abortUtf8` zeroes it on the byte that abandons one. This is the precondition the grid claim
needs on its receiver and could not get from `Good` or `Renderable`: `Good` bounds `u8need`
but says nothing about `u8acc`. -/
def U8Ok (v : Vt) : Prop := v.u8need = 0 → v.u8acc = 0

theorem u8Ok_init (cols rows : Nat) : U8Ok (Vt.init cols rows) := fun _ => rfl

theorem u8Ok_stepGround {v : Vt} (b : UInt8) (h : U8Ok v) : U8Ok (v.stepGround b) := by
  intro hz
  unfold Vt.stepGround at hz ⊢
  by_cases h1 : (b == 0x1B) = true
  · rw [ite_eq_left h1] at hz ⊢; exact h hz
  rw [ite_eq_right h1] at hz ⊢
  by_cases h2 : b < 0x20
  · rw [ite_eq_left h2] at hz ⊢
    rw [ua_ctl]; rw [un_ctl] at hz; exact h hz
  rw [ite_eq_right h2] at hz ⊢
  by_cases h3 : b < 0x80
  · rw [ite_eq_left h3] at hz ⊢
    rw [ua_acceptChar]; rw [un_acceptChar] at hz; exact h hz
  rw [ite_eq_right h3] at hz ⊢
  by_cases h4 : b < 0xC0
  · rw [ite_eq_left h4] at hz ⊢
    dsimp only at hz ⊢
    by_cases h5 : (v.u8need == 0) = true
    · rw [ite_eq_left h5] at hz ⊢; exact h hz
    rw [ite_eq_right h5] at hz ⊢
    by_cases h6 : (v.u8need == 1) = true
    · rw [ite_eq_left h6] at hz ⊢
      rw [ua_acceptChar]
    · rw [ite_eq_right h6] at hz ⊢
      exfalso
      simp only [beq_iff_eq] at h5 h6
      simp only [] at hz
      omega
  rw [ite_eq_right h4] at hz ⊢
  by_cases h7 : b < 0xE0
  · rw [ite_eq_left h7] at hz ⊢; exact absurd hz (by simp)
  rw [ite_eq_right h7] at hz ⊢
  by_cases h8 : b < 0xF0
  · rw [ite_eq_left h8] at hz ⊢; exact absurd hz (by simp)
  rw [ite_eq_right h8] at hz ⊢
  by_cases h9 : b < 0xF8
  · rw [ite_eq_left h9] at hz ⊢; exact absurd hz (by simp)
  rw [ite_eq_right h9] at hz ⊢
  exact h hz

theorem u8Ok_step {v : Vt} (b : UInt8) (h : U8Ok v) : U8Ok (v.step b) := by
  have hab : U8Ok (v.abortUtf8 b) := by
    unfold Vt.abortUtf8
    split
    · intro _; rfl
    · exact h
  unfold Vt.step
  dsimp only
  split
  · exact u8Ok_stepGround _ hab
  all_goals
    (intro hz
     first
       | (rw [ua_stepEscInter]; rw [un_stepEscInter] at hz; exact hab hz)
       | (rw [ua_stepCsi]; rw [un_stepCsi] at hz; exact hab hz)
       | (rw [ua_stepOsc]; rw [un_stepOsc] at hz; exact hab hz)
       | (rw [ua_stepStr]; rw [un_stepStr] at hz; exact hab hz)
       | (rcases u8pair_stepEsc (v.abortUtf8 b) b with ⟨hn, ha⟩ | ⟨-, ha⟩
          · rw [ha]; exact hab (by rw [← hn]; exact hz)
          · exact ha))

theorem u8Ok_feed : ∀ (bs : List UInt8) {v : Vt}, U8Ok v → U8Ok (v.feed bs)
  | [], _, h => h
  | b :: bs, v, h => by
    rw [show v.feed (b :: bs) = (v.step b).feed bs from rfl]
    exact u8Ok_feed bs (u8Ok_step b h)

/-- **The fourth component the resume rung needs, and the only one the door does not
already claim.** `Vt.ofDecoded` *fixes* `u8need := 0` and `u8acc := 0` rather than
validating them — parser state is deliberately not persisted (`Checkpoint.wVt`), so there
is nothing on disk to check — which makes `U8Ok` immediate at the door.

This is also the component that makes the premise's shape matter. `Good` bounds `u8need`
and says nothing whatever about `u8acc`, so a rung premised on `Good v` cannot reach this
claim; Step 3 measured exactly that failure (`invalid ▸ notation, argument hg.u8Le has type
v.u8need ≤ 3, equality expected`). -/
theorem ofDecoded_u8Ok {cols rows : Nat} {grid : Array Row} {cursor : Cursor} {pen : Pen}
    {modes : Modes} {top bot : Nat} {tabs : Array Bool} {sb : Ring}
    {altGrid : Option (Array Row × Cursor × Pen)} {saved : Saved} {title : String}
    {g0Line g1Line shiftOut bell : Bool} {v : Vt}
    (h :
      Vt.ofDecoded cols rows grid cursor pen modes top bot tabs sb altGrid saved title g0Line g1Line
          shiftOut bell =
        some v) :
    U8Ok v := by
  unfold Vt.ofDecoded at h
  split at h
  · cases h
    intro _
    rfl
  · exact absurd h (by simp)

theorem u8Ok_of_liveReachable {v : Vt} (h : LiveReachableVt v) : U8Ok v := by
  induction h with
  | init c r => exact u8Ok_init c r
  | feed _ bytes ih => exact u8Ok_feed bytes ih
  | resize _ c r ih => intro hz; rw [show (Vt.resize _ c r).u8acc = _ from rfl] at *; exact ih hz
  | quiesce _ _ => intro _; rfl
  | ofDecoded hd => exact ofDecoded_u8Ok hd

/-- **…and the ruler, which is `specs/archive/vt-toolkit.md` Step 3's harvest.** The one
hypothesis `Render.restore_tabs_reachable` still had to ask for —
`v.tabs.size = v.cols` — is a fact about every state a live session can hold, so a
caller with reachability no longer has to supply it. Neither `Good` nor
`Renderable` implies it (the first bounds the dimensions, the second speaks of the
grid), which is why it needed the §Ruler layer of its own rather than a clause on
one of them.

Note the two rungs that could have broken it and do not: `resize` reinstalls
`defaultTabs` at the new width, and the `feed` rung covers `TBC 3`, which replaces
the whole array — the invariant is *re-established* there rather than preserved,
which is the shape `tabsOk_csiDispatch` records. The `ofDecoded` rung is a third
that could have: before finding R2 the door accepted a ruler of any length at all,
and `ofDecoded_tabsOk` is exactly the claim that closed it. -/
theorem tabsOk_of_liveReachable {v : Vt} (h : LiveReachableVt v) : TabsOk v := by
  induction h with
  | init c r => exact tabsOk_init c r
  | feed _ bytes ih => exact tabsOk_feed bytes ih
  | resize _ c r ih => exact tabsOk_resize _ c r
  | quiesce _ ih => exact tabsOk_quiesce ih
  | ofDecoded hd => exact ofDecoded_tabsOk hd

/-! ## Absolute vertical motion

VPA shares CUP's origin and clamp. Screen bounds alone would not catch a cursor
below `top` under DECOM; the exact result and region bounds below do. -/

theorem csiDispatch_vpa (v : Vt) (s : CsiState) :
    v.csiDispatch s 0x64 =
      if s.ignore then v else v.moveTo v.cursor.x (s.arg 0 1 - 1) := by
  rfl

/-- Only the cursor changes: its column is preserved, the row uses the current
origin, and pending wrap is cleared. No premise constrains the requested row. -/
theorem csiDispatch_vpa_exact {v : Vt} (h : Good v) (s : CsiState) (hi : s.ignore = false) :
    v.csiDispatch s 0x64 =
      { v with
        cursor :=
          { x := v.cursor.x,
            y := min ((if v.modes.origin then v.top else 0) + (s.arg 0 1 - 1))
              (if v.modes.origin then v.bot else v.rows - 1),
            pending := false } } := by
  rw [csiDispatch_vpa]
  have hx : min v.cursor.x (v.cols - 1) = v.cursor.x := Nat.min_eq_left (by
    have hc := h.curX
    omega)
  simp [hi, Vt.moveTo, hx]

/-- Even a source cursor outside the region is placed inside it by VPA under
DECOM. Requiring the source cursor to be inside would conceal the original bug. -/
theorem csiDispatch_vpa_in_region {v : Vt} (h : Good v) (s : CsiState)
    (hi : s.ignore = false) (ho : v.modes.origin = true) :
    v.top ≤ (v.csiDispatch s 0x64).cursor.y ∧
      (v.csiDispatch s 0x64).cursor.y ≤ v.bot := by
  rw [csiDispatch_vpa_exact h s hi]
  simp only [ho, ↓reduceIte]
  have ht := h.topLe
  constructor <;> omega

/-! ## CSI collection — bounds and omitted parameters

`Good.csiLe` bounds the parameter count. Numeric bounds and the empty accumulator
need their own invariant: without the latter, treating an omitted field as zero
would only be an assumption about the parser's caller. The private parser stages
and the reachability proof below establish it for every byte stream, including
after a decoded checkpoint. The exact collection contracts also distinguish a
missing parameter from a dropped one; a frame alone would not catch that bug. -/

/-- Closing a field below the cap appends exactly one slot, including when no
digits preceded the separator, and resets the accumulator for the next field. -/
theorem csiPush_of_lt (s : CsiState) (sub : Bool) (h : s.params.size < 16) :
    csiPush s sub =
      { s with
        params := s.params.push (min s.cur 65535, s.curSub), cur := 0, curSub := sub,
        haveCur := false } := by
  unfold csiPush
  rw [ite_eq_right (by omega)]

/-- Overflow retains the collected fields but ignores the entire sequence. -/
theorem csiPush_of_ge (s : CsiState) (sub : Bool) (h : 16 ≤ s.params.size) :
    csiPush s sub = { s with ignore := true, cur := 0, haveCur := false } := by
  unfold csiPush
  rw [ite_eq_left h]

/-- A trailing separator creates an omitted final field; it cannot silently
disappear at dispatch. This matters for SGR, whose omitted field is a reset. -/
theorem csiFinish_omitted (v : Vt) (s : CsiState) (final : UInt8)
    (hh : s.haveCur = false) (hp : 0 < s.params.size) :
    v.csiFinish s final = { v.csiDispatch (csiPush s false) final with pstate := .ground } := by
  unfold Vt.csiFinish
  rw [ite_eq_right (by simp [hh])]
  split
  · rename_i he
    have hz : s.params.size = 0 := by
      change s.params.toList.length = 0
      rw [he]
      rfl
    omega
  · rfl

/-- Sixteen closed fields leave no room for the final field, whether explicit
or omitted. Dispatching the overflowing sequence changes only the parser state. -/
theorem csiFinish_overflow (v : Vt) (s : CsiState) (final : UInt8)
    (hp : 16 ≤ s.params.size) :
    v.csiFinish s final = { v with pstate := .ground } := by
  unfold Vt.csiFinish
  split
  · simp [Vt.csiDispatch]
  · split
    · rename_i he
      have hz : s.params.size = 0 := by
        change s.params.toList.length = 0
        rw [he]
        rfl
      omega
    · simp [csiPush_of_ge s false hp, Vt.csiDispatch]

/-- Numeric and omitted-value invariants; `Good.csiLe` separately bounds the count. -/
structure CsiValuesOk (s : CsiState) : Prop where
  curLe : s.cur ≤ 65535
  paramsLe : ∀ p ∈ s.params.toList, p.1 ≤ 65535
  emptyCur : s.haveCur = false → s.cur = 0

theorem csiValuesOk_empty : CsiValuesOk {} := by
  constructor
  · simp
  · simp
  · intro _; rfl

theorem csiValuesOk_push {s : CsiState} (h : CsiValuesOk s) (sub : Bool) :
    CsiValuesOk (csiPush s sub) := by
  by_cases hp : s.params.size < 16
  · rw [csiPush_of_lt s sub hp]
    constructor
    · simp
    · intro p hm
      simp only [Array.toList_push, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false] at hm
      rcases hm with hm | rfl
      · exact h.paramsLe p hm
      · exact Nat.min_le_right _ _
    · intro _; rfl
  · rw [csiPush_of_ge s sub (by omega)]
    exact ⟨by simp, h.paramsLe, fun _ => rfl⟩

def CsiOk (v : Vt) : Prop := ∀ s, v.pstate = .csi s → CsiValuesOk s

theorem csiOk_of_pstate_eq {v w : Vt} (hp : v.pstate = w.pstate) (h : CsiOk w) : CsiOk v :=
  fun s hs => h s (hp.symm.trans hs)

theorem csiOk_set {v : Vt} {s : CsiState} (h : CsiValuesOk s) :
    CsiOk { v with pstate := .csi s } := by
  intro t ht
  cases ht
  exact h

theorem csiOk_init (cols rows : Nat) : CsiOk (Vt.init cols rows) := by
  simp [CsiOk, Vt.init]

theorem csiOk_stepGround {v : Vt} (h : CsiOk v) (b : UInt8) :
    CsiOk (v.stepGround b) := by
  by_cases hb : b = 0x1B
  · simp [CsiOk, Vt.stepGround, hb]
  · exact csiOk_of_pstate_eq (ps_stepGround v b hb) h

theorem csiOk_stepEsc {v : Vt} (h : CsiOk v) (b : UInt8) : CsiOk (v.stepEsc b) := by
  unfold Vt.stepEsc
  repeat' split
  all_goals
    first
    | exact h
    | exact csiOk_set csiValuesOk_empty
    | simp [CsiOk, Vt.init]

theorem csiOk_stepEscInter (v : Vt) (i b : UInt8) : CsiOk (v.stepEscInter i b) := by
  unfold Vt.stepEscInter
  repeat' split
  all_goals simp [CsiOk]

theorem csiOk_stepCsi {v : Vt} {s : CsiState} (h : CsiOk v) (hs : CsiValuesOk s) (b : UInt8) :
    CsiOk (v.stepCsi s b) := by
  unfold Vt.stepCsi
  split
  · exact csiOk_set ⟨Nat.min_le_right _ _, hs.paramsLe, by simp⟩
  split
  · exact csiOk_set (csiValuesOk_push hs false)
  split
  · exact csiOk_set (csiValuesOk_push hs true)
  split
  · exact csiOk_set ⟨hs.curLe, hs.paramsLe, hs.emptyCur⟩
  split
  · exact csiOk_set ⟨hs.curLe, hs.paramsLe, hs.emptyCur⟩
  split
  · split
    · simp [CsiOk]
    · simp [CsiOk, Vt.csiFinish]
  split
  · simp [CsiOk]
  split
  · exact h
  split
  · exact csiOk_of_pstate_eq (ps_ctl v b) h
  · simp [CsiOk]

theorem csiOk_stepOsc (v : Vt) (acc : Array UInt8) (esc : Bool) (b : UInt8) :
    CsiOk (v.stepOsc acc esc b) := by
  unfold Vt.stepOsc
  repeat' split
  all_goals try (unfold Vt.oscFinish; dsimp only; repeat' split)
  all_goals simp [CsiOk]

theorem csiOk_stepStr (v : Vt) (esc : Bool) (b : UInt8) : CsiOk (v.stepStr esc b) := by
  unfold Vt.stepStr
  repeat' split
  all_goals simp [CsiOk]

theorem csiOk_step {v : Vt} (h : CsiOk v) (b : UInt8) : CsiOk (v.step b) := by
  have hab : CsiOk (v.abortUtf8 b) := csiOk_of_pstate_eq (ps_abortUtf8 v b) h
  unfold Vt.step
  dsimp only
  split
  · exact csiOk_stepGround hab b
  · exact csiOk_stepEsc hab b
  · exact csiOk_stepEscInter _ _ _
  · rename_i s hp
    exact csiOk_stepCsi hab (hab s hp) b
  · exact csiOk_stepOsc _ _ _ _
  · exact csiOk_stepStr _ _ _

theorem csiOk_feed : ∀ (bs : List UInt8) {v : Vt}, CsiOk v → CsiOk (v.feed bs)
  | [], _, h => h
  | b :: bs, v, h => by
    rw [show v.feed (b :: bs) = (v.step b).feed bs from rfl]
    exact csiOk_feed bs (csiOk_step h b)

/-- The decoder starts in ground state, so it needs no new acceptance condition. -/
theorem ofDecoded_csiOk {cols rows : Nat} {grid : Array Row} {cursor : Cursor} {pen : Pen}
    {modes : Modes} {top bot : Nat} {tabs : Array Bool} {sb : Ring}
    {altGrid : Option (Array Row × Cursor × Pen)} {saved : Saved} {title : String}
    {g0Line g1Line shiftOut bell : Bool} {v : Vt}
    (h :
      Vt.ofDecoded cols rows grid cursor pen modes top bot tabs sb altGrid saved title g0Line
          g1Line shiftOut bell =
        some v) :
    CsiOk v := by
  unfold Vt.ofDecoded at h
  split at h
  · cases h
    simp [CsiOk]
  · exact absurd h (by simp)

/-- Every reachable CSI state has bounded values and a zero accumulator whenever
the current field is omitted. Arbitrary feeds, resize, quiesce and resume are covered. -/
theorem csiOk_of_liveReachable {v : Vt} (h : LiveReachableVt v) : CsiOk v := by
  induction h with
  | init c r => exact csiOk_init c r
  | feed _ bytes ih => exact csiOk_feed bytes ih
  | resize _ _ _ ih => exact ih
  | quiesce _ _ => simp [CsiOk, Vt.quiesce]
  | ofDecoded hd => exact ofDecoded_csiOk hd

/-- Omitted fields in a live parser contribute zero, rather than losing their
position or reusing the previous field's digits. -/
theorem csiPush_omitted_of_liveReachable {v : Vt} (h : LiveReachableVt v) {s : CsiState}
    (hp : v.pstate = .csi s) (hh : s.haveCur = false) (hs : s.params.size < 16) (sub : Bool) :
    (csiPush s sub).params = s.params.push (0, s.curSub) := by
  rw [csiPush_of_lt s sub hs]
  simp only [(csiOk_of_liveReachable h s hp).emptyCur hh, Nat.zero_min]

end Linger.Core.Vt

namespace Linger.Core.Vt

/-! ## §Restore — the sticky receiver state, as one bundled projection

This layer supplies `Render.restore`'s receiver-quantified value
claims: the state the stream **establishes and must then leave alone** outside
the grid, cursor, pen, modes and parser — the scroll region, the two charset
designations, the shift state, and which screen is current. Its preservation
claims use the frames and `off_print` above.

Bundling was the idea the frames note rejected ("fixes only the fields we
happened to need"), and the objection is answered rather than ignored: this
bundle is not a chosen subset but a *closed* one. `rows` rides along because two
of the transforms read it — `DECSTBM` clamps against it, and the alt switch
resets the region to it — so a bundle without `rows` would not be closed under
its own transforms. Everything else the stream writes already has a layer.

The transforms are named (`stAlt`, `stStbm`, `stCharset`, `stSetMode`) so the
`Render` ladder composes them the way `MMap` composes `Modes` transforms. -/

/-- The receiver fields `restore` establishes and then must not disturb. -/
structure Sticky where
  rows : Nat
  top : Nat
  bot : Nat
  g0 : Bool
  g1 : Bool
  so : Bool
  alt : Bool
  deriving DecidableEq, Repr

def stick (v : Vt) : Sticky :=
  { rows := v.rows, top := v.top, bot := v.bot, g0 := v.g0Line, g1 := v.g1Line,
    so := v.shiftOut, alt := v.altGrid.isSome }

/-! The projections, as rewrite rules. `rfl` for a *variable* receiver, which is
what keeps the field corollaries in `Render` from asking the elaborator to whnf a
whole restore stream. -/

theorem stick_rows (u : Vt) : (stick u).rows = u.rows := by rfl

theorem stick_top (u : Vt) : (stick u).top = u.top := by rfl

theorem stick_bot (u : Vt) : (stick u).bot = u.bot := by rfl

theorem stick_g0 (u : Vt) : (stick u).g0 = u.g0Line := by rfl

theorem stick_g1 (u : Vt) : (stick u).g1 = u.g1Line := by rfl

theorem stick_so (u : Vt) : (stick u).so = u.shiftOut := by rfl

theorem stick_alt (u : Vt) : (stick u).alt = u.altGrid.isSome := by rfl

/-! ### The framed operations: one `rw` each, every field at once -/

theorem stick_putCell (v : Vt) (x y : Nat) (c : Cell) :
    stick (v.putCell x y c) = stick v := by rw [frame_putCell]; rfl

theorem stick_moveTo (v : Vt) (x y : Nat) : stick (v.moveTo x y) = stick v := by rw [frame_moveTo]; rfl

theorem stick_moveRel (v : Vt) (dx dy : Int) : stick (v.moveRel dx dy) = stick v := by
  rw [frame_moveRel]; rfl

theorem stick_setCol (v : Vt) (x : Nat) : stick (v.setCol x) = stick v := by rw [frame_setCol]; rfl

theorem stick_clearPending (v : Vt) : stick v.clearPending = stick v := by rw [frame_clearPending]; rfl

theorem stick_carriageReturn (v : Vt) : stick v.carriageReturn = stick v := by
  rw [frame_carriageReturn]; rfl

theorem stick_backspace (v : Vt) : stick v.backspace = stick v := by rw [frame_backspace]; rfl

theorem stick_tab (v : Vt) : stick v.tab = stick v := by rw [frame_tab]; rfl

theorem stick_backTab (v : Vt) : stick v.backTab = stick v := by rw [frame_backTab]; rfl

theorem stick_lineFeed (v : Vt) : stick v.lineFeed = stick v := by rw [frame_lineFeed]; rfl

/-- **A line feed below the region bottom just moves the cursor down.** Its only scrolling
consumer is the `cursor.y == bot` branch, and `y < bot` rules that out — the grid, and every
row, is left exactly as it was. This is the no-scroll fact the grid walk turns each `CRLF`
on. -/
theorem lineFeed_interior (v : Vt) (hy : v.cursor.y < v.bot) (hlt : v.bot < v.rows) :
    v.lineFeed = { v with cursor := { v.cursor with y := v.cursor.y + 1, pending := false } } := by
  unfold Vt.lineFeed Vt.clearPending
  dsimp only
  rw [ite_eq_right (show ¬(v.cursor.y == v.bot) = true from by simp; omega),
    ite_eq_left (show v.cursor.y + 1 < v.rows from by omega)]

theorem grid_lineFeed_interior (v : Vt) (hy : v.cursor.y < v.bot) (hlt : v.bot < v.rows) :
    v.lineFeed.grid = v.grid := by rw [lineFeed_interior v hy hlt]

theorem getCell_lineFeed_interior (v : Vt) (x y : Nat) (hy : v.cursor.y < v.bot)
    (hlt : v.bot < v.rows) : v.lineFeed.getCell x y = v.getCell x y := by
  unfold Vt.getCell Vt.getRow
  rw [lineFeed_interior v hy hlt]

/-! ### The positive scroll specification

The frames above say what `scrollUpIn` leaves **alone**. These say what it **writes** —
the gap §Total names in its own words ("a frame says what an operation leaves alone,
never what the written fields *become*"), closed for the one operation the scrollback
story rests on.

The fold is tractable for exactly one reason: it reads `v.getRow`, never the accumulator
it is building (`Linger/Core/Vt.lean`, `Vt.scrollUpIn`), so the writes are independent and
one pointwise characterization covers all of them. `getD_foldl_setRange` is that
characterization, stated over an arbitrary source function so nothing in it depends on the
values being rows. Same shape as `foldl_setTab_mem`/`_not_mem` over the tab ruler. -/

theorem size_foldl_setRange {α} [Inhabited α] (f : Nat → α) (top : Nat) :
    ∀ (n : Nat) (a : Array α),
      ((List.range n).foldl (fun b i => b.setIfInBounds (top + i) (f i)) a).size = a.size
  | 0, _ => rfl
  | n + 1, a => by
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [Array.size_setIfInBounds, size_foldl_setRange f top n a]

/-- **The write lands**: index `top + i` holds the `i`-th source value. The later writes
are at strictly larger indices, so they cannot disturb it. -/
theorem getD_foldl_setRange {α} [Inhabited α] (f : Nat → α) (top : Nat) (d : α) :
    ∀ (n : Nat) (a : Array α) (i : Nat),
      i < n →
        top + i < a.size →
          ((List.range n).foldl (fun b k => b.setIfInBounds (top + k) (f k)) a).getD (top + i) d =
            f i
  | 0, _, _, hi, _ => absurd hi (by omega)
  | n + 1, a, i, hi, hlt => by
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rcases Nat.lt_or_ge i n with h | h
    · rw [getD_set_ne _ (top + n) (top + i) (f n) d (by omega)]
      exact getD_foldl_setRange f top d n a i h hlt
    · have hin : i = n := by omega
      subst hin
      exact
        getD_set_self _ (top + i) (f i) d
          (by
            rw [size_foldl_setRange]; exact hlt)

/-- …and every index the fold never writes keeps what it had. -/
theorem getD_foldl_setRange_of_ne {α} [Inhabited α] (f : Nat → α) (top : Nat) (d : α) :
    ∀ (n : Nat) (a : Array α) (j : Nat),
      (∀ i, i < n → j ≠ top + i) →
        ((List.range n).foldl (fun b k => b.setIfInBounds (top + k) (f k)) a).getD j d = a.getD j d
  | 0, _, _, _ => rfl
  | n + 1, a, j, h => by
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [getD_set_ne _ (top + n) j (f n) d (h n (by omega))]
    exact getD_foldl_setRange_of_ne f top d n a j fun i hi => h i (by omega)

/-- The two branches of `scrollUpIn` differ only in `sb`, so its grid is one term. -/
theorem grid_scrollUpIn (v : Vt) (top bot : Nat) (a : Bool) :
    (v.scrollUpIn top bot a).grid =
      ((List.range (bot - top)).foldl
            (fun g i => g.setIfInBounds (top + i) (v.getRow (top + i + 1)))
            v.grid).setIfInBounds bot (blankRow v.cols v.pen) := by
  unfold Vt.scrollUpIn
  dsimp only
  split <;> rfl

/-- **What a scroll writes.** Row `y'` inside the region becomes the row below it, the
vacated bottom row is blank **in the pen currently in effect** (stated, not hidden — a
coloured session scrolls up a coloured blank), and everything outside the region is
untouched.

`top ≤ bot` is load-bearing for the third conjunct and nothing else: with an inverted
region `bot - top` is `0`, so the fold is empty and the blank write at `bot` is the only
one — and it lands *outside* `[top, bot]`, which would make "outside is untouched" false
at `y' = bot`. `Good.topLe` is where every caller gets it. -/
theorem scrollUpIn_rows (v : Vt) (top bot : Nat) (a : Bool) (htb : top ≤ bot)
    (hbot : bot < v.grid.size) :
    (∀ y', top ≤ y' → y' < bot → (v.scrollUpIn top bot a).getRow y' = v.getRow (y' + 1)) ∧
      (v.scrollUpIn top bot a).getRow bot = blankRow v.cols v.pen ∧
        ∀ y', (y' < top ∨ bot < y') → (v.scrollUpIn top bot a).getRow y' = v.getRow y' := by
  have hrow :
    ∀ y',
      (v.scrollUpIn top bot a).getRow y' =
        (((List.range (bot - top)).foldl
                (fun g i => g.setIfInBounds (top + i) (v.getRow (top + i + 1)))
                v.grid).setIfInBounds bot (blankRow v.cols v.pen)).getD y'
          (blankRow v.cols v.pen) := by
    intro y'
    show
      (v.scrollUpIn top bot a).grid.getD y'
          (blankRow (v.scrollUpIn top bot a).cols (v.scrollUpIn top bot a).pen) = _
    rw [show (v.scrollUpIn top bot a).cols = v.cols from by rw [frame_scrollUpIn],
      show (v.scrollUpIn top bot a).pen = v.pen from by rw [frame_scrollUpIn], grid_scrollUpIn]
  refine ⟨fun y' hle hlt => ?_, ?_, fun y' hne => ?_⟩
  · rw [hrow y', getD_set_ne _ bot y' _ _ (by omega)]
    rw [show y' = top + (y' - top) from by omega]
    exact
      getD_foldl_setRange _ top _ (bot - top) v.grid (y' - top) (by omega)
        (by
          rw [show top + (y' - top) = y' from by omega]; omega)
  · rw [hrow bot,
      getD_set_self _ bot _ _
        (by
          rw [size_foldl_setRange]; exact hbot)]
  · rw [hrow y', getD_set_ne _ bot y' _ _ (by rcases hne with h | h <;> omega),
      getD_foldl_setRange_of_ne _ top _ (bot - top) v.grid y'
        (fun i hi => by rcases hne with h | h <;> omega)]
    unfold Vt.getRow
    rfl

/-- **What a scroll pushes**: the evicted top row, once, when the region is the whole
screen and the alt screen is not up. The `getRow 0` is the row the guard's `top = 0`
makes it. -/
theorem scrollUpIn_sb_push (v : Vt) (bot : Nat) (hbot : bot = v.rows - 1)
    (halt : v.altGrid = none) : (v.scrollUpIn 0 bot true).sb = v.sb.push (v.getRow 0) := by
  unfold Vt.scrollUpIn
  dsimp only
  rw [ite_eq_left
      (show (true && (0 : Nat) == 0 && bot == v.rows - 1 && v.altGrid.isNone) = true from by
        simp [hbot, halt])]

/-- …and a scroll that is not allowed to push does not touch scrollback. `frame_scrollUpIn`
cannot say this: `sb` is inside the footprint it declares, so this is the positive fact
about the branch not taken — what the `Fixes (·.sb)` tail needs of `DL`, `IL` and `SU`. -/
theorem scrollUpIn_sb_of_false (v : Vt) (top bot : Nat) :
    (v.scrollUpIn top bot false).sb = v.sb := by
  unfold Vt.scrollUpIn
  dsimp only
  rw [ite_eq_right (by simp)]

/-- **A line feed at the region bottom scrolls**: `lineFeed_interior`'s twin, and the
bridge Step 3's `crlf_scroll_step` composes with the two theorems above. -/
theorem lineFeed_scroll (v : Vt) (hy : v.cursor.y = v.bot) :
    v.lineFeed = v.clearPending.scrollUp := by
  unfold Vt.lineFeed
  dsimp only
  rw [ite_eq_left
      (show (v.clearPending.cursor.y == v.clearPending.bot) = true from by
        simp [Vt.clearPending, hy])]

/-! ### The ring, below the cap

The receiver's ring is empty when `restore` starts pushing (`ED 3`) and the pushed run is
capped by `sbTake`, so the wrap branch is unreachable on the replay path. These are the
three facts that let a push be read as an append. -/

/-- Below the cap a push is an append, and the oldest index does not move. -/
theorem ring_push_data {r : Ring} (row : Row) (h : r.data.size < sbCap) :
    (r.push row).data = r.data.push row ∧ (r.push row).start = r.start := by
  unfold Ring.push
  rw [ite_eq_left h]
  exact ⟨rfl, rfl⟩

/-- A ring that never wrapped reads back as its own array, oldest first. -/
theorem ring_toList_of_start_zero {r : Ring} (h : r.start = 0) : r.toList = r.data.toList := by
  unfold Ring.toList
  rw [h]
  simp

/-- One `take` step, which is how the walk grows the expected history by a row. -/
theorem take_succ_getD {α} [Inhabited α] (l : List α) (n : Nat) (h : n < l.length) :
    l.take (n + 1) = l.take n ++ [l.getD n default] := by
  rw [List.take_add_one, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

theorem stick_reverseIndex (v : Vt) : stick v.reverseIndex = stick v := by rw [frame_reverseIndex]; rfl

theorem stick_scrollUpIn (v : Vt) (t b : Nat) (a : Bool) :
    stick (v.scrollUpIn t b a) = stick v := by rw [frame_scrollUpIn]; rfl

theorem stick_scrollDownIn (v : Vt) (t b : Nat) : stick (v.scrollDownIn t b) = stick v := by
  rw [frame_scrollDownIn]; rfl

theorem stick_scrollUp (v : Vt) : stick v.scrollUp = stick v := stick_scrollUpIn _ _ _ _

theorem stick_scrollDown (v : Vt) : stick v.scrollDown = stick v := stick_scrollDownIn _ _ _

theorem stick_eraseRowSpan (v : Vt) (y a b : Nat) : stick (v.eraseRowSpan y a b) = stick v := by
  rw [frame_eraseRowSpan]; rfl

theorem stick_eraseLine (v : Vt) (m : Nat) : stick (v.eraseLine m) = stick v := by
  rw [frame_eraseLine]; rfl

theorem stick_eraseChars (v : Vt) (n : Nat) : stick (v.eraseChars n) = stick v := by
  rw [frame_eraseChars]; rfl

theorem stick_deleteChars (v : Vt) (n : Nat) : stick (v.deleteChars n) = stick v := by
  rw [frame_deleteChars]; rfl

theorem stick_insertChars (v : Vt) (n : Nat) : stick (v.insertChars n) = stick v := by
  rw [frame_insertChars]; rfl

theorem stick_applySgr (v : Vt) (ps : List (Nat × Bool)) : stick (v.applySgr ps) = stick v := by
  rw [frame_applySgr]; rfl

theorem stick_oscFinish (v : Vt) (acc : Array UInt8) : stick (v.oscFinish acc) = stick v := by
  rw [frame_oscFinish]; rfl

theorem stick_stepStr (v : Vt) (e : Bool) (b : UInt8) : stick (v.stepStr e b) = stick v := by
  rw [frame_stepStr]; rfl

theorem stick_abortUtf8 (v : Vt) (b : UInt8) : stick (v.abortUtf8 b) = stick v := by
  unfold Vt.abortUtf8; split <;> rfl

/-- Fold invariance for the bundle, used by repeat-count dispatches
(`CHT`, `SU`, `SD`, `CBT`). -/
theorem stick_foldl {α : Type} (f : Vt → α → Vt) (hf : ∀ (w : Vt) (a : α), stick (f w a) = stick w) :
    ∀ (l : List α) (v : Vt), stick (l.foldl f v) = stick v
  | [], _ => rfl
  | a :: as, v => (stick_foldl f hf as (f v a)).trans (hf v a)

theorem stick_eraseScreen (v : Vt) (m : Nat) : stick (v.eraseScreen m) = stick v := by
  rw [frame_eraseScreen]
  rfl

theorem stick_insertLines (v : Vt) (n : Nat) : stick (v.insertLines n) = stick v := by
  rw [frame_insertLines]
  rfl

theorem stick_deleteLines (v : Vt) (n : Nat) : stick (v.deleteLines n) = stick v := by
  rw [frame_deleteLines]
  rfl

/-- **The charset translation is stable across a print**, so a row induction proves
`printChar ch = ch` once instead of per column. `print_narrow_eq` and its siblings
each take that as a hypothesis. -/
theorem printChar_congr {u v : Vt} (h0 : u.g0Line = v.g0Line) (h1 : u.g1Line = v.g1Line)
    (hs : u.shiftOut = v.shiftOut) (c : Char) : u.printChar c = v.printChar c := by
  unfold Vt.printChar
  rw [h0, h1, hs]

theorem printChar_print (v : Vt) (ch c : Char) : (v.print ch).printChar c = v.printChar c :=
  printChar_congr (g0_print v ch) (g1_print v ch) (so_print v ch) c

/-- With both charsets ASCII, `printChar` is the identity on anything the painter
emits — `safeChar` and `printableChar` agree on a non-control codepoint. -/
theorem printChar_id_of_ascii {v : Vt} (hg0 : v.g0Line = false) (hg1 : v.g1Line = false)
    {c : Char} (h20 : 0x20 ≤ c.toNat) (h7 : c.toNat ≠ 0x7F) : v.printChar c = c := by
  unfold Vt.printChar printableChar
  rw [show ((v.shiftOut && v.g1Line) || (!v.shiftOut && v.g0Line)) = false from by
    rw [hg0, hg1]; cases v.shiftOut <;> rfl]
  rw [show (if (false : Bool) = true then decLine c else c) = c from rfl]
  rw [ite_eq_right (by
    simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq]
    omega)]

/-! #### Where the cursor goes

`print_narrow_eq` and its siblings say what a print *writes*; the row induction also
needs where it leaves the cursor, because `hpend : cursor.pending = false` is a
hypothesis of all three and has to be re-established for column `k+1`. The margin
case is the interesting one and it is why `pending` is in the invariant at all: at
the right margin `printAdvance` clamps the column and arms wrap-pending, so the last
cell of a row leaves a state no absolute cursor move can express. -/

theorem off_putCell' (v : Vt) (x y : Nat) (c : Cell) :
    offScreen (v.putCell x y c) = offScreen v := by rw [frame_putCell]; rfl

theorem off_mendRow (v : Vt) (y : Nat) : offScreen (v.mendRow y) = offScreen v := by
  rw [frame_mendRow]; rfl

theorem off_clearPending (v : Vt) : offScreen v.clearPending = offScreen v := by
  rw [frame_clearPending]; rfl

theorem cursor_putCell (v : Vt) (x y : Nat) (c : Cell) :
    (v.putCell x y c).cursor = v.cursor := by rw [frame_putCell]

theorem cursor_mendRow (v : Vt) (y : Nat) : (v.mendRow y).cursor = v.cursor := by
  rw [frame_mendRow]

theorem cursor_clearPending (v : Vt) :
    v.clearPending.cursor = { v.cursor with pending := false } := by rfl

theorem cursor_printAdvance_lt (v : Vt) (n : Nat) (h : v.cursor.x + n < v.cols) :
    (v.printAdvance n).cursor = { v.cursor with x := v.cursor.x + n, pending := false } := by
  unfold Vt.printAdvance
  rw [ite_eq_right (by omega)]

theorem cursor_printAdvance_ge (v : Vt) (n : Nat) (h : v.cols ≤ v.cursor.x + n) :
    (v.printAdvance n).cursor
      = { v.cursor with x := v.cols - 1, pending := v.modes.wrap } := by
  unfold Vt.printAdvance
  rw [ite_eq_left (by omega)]

/-- The three facts `printAdvance` needs about the state a cell write leaves, as one
lemma: a write touches only the grid, so the cursor is the `clearPending` one and the
columns and modes are `v`'s. -/
private theorem write_frame (v : Vt) (f : Vt → Vt)
    (hf : ∀ u : Vt, offScreen (f u) = offScreen u ∧ (f u).cursor = u.cursor) :
    (f v.clearPending).cursor = { v.cursor with pending := false }
      ∧ (f v.clearPending).cols = v.cols ∧ (f v.clearPending).modes = v.modes := by
  obtain ⟨ho, hc⟩ := hf v.clearPending
  exact ⟨by rw [hc]; rfl, congrArg OffScreen.cols ho, congrArg OffScreen.modes ho⟩

theorem cursor_print_narrow_fits {v : Vt} {ch : Char}
    (hpc : v.printChar ch = ch) (hw : charWidth ch = 1) (hins : v.modes.insert = false)
    (hpend : v.cursor.pending = false) (hfit : v.cursor.x + 1 < v.cols) :
    (v.print ch).cursor = { v.cursor with x := v.cursor.x + 1, pending := false } := by
  rw [print_narrow_eq hpc hw hins hpend]
  obtain ⟨hcur, hcol, -⟩ := write_frame v
    (fun u => (u.putCell v.cursor.x v.cursor.y
      { base := ch, marks := [], width := 1, pen := v.pen }).mendRow v.cursor.y)
    (fun u => ⟨(off_mendRow _ _).trans (off_putCell' _ _ _ _),
      (cursor_mendRow _ _).trans (cursor_putCell _ _ _ _)⟩)
  rw [cursor_printAdvance_lt _ 1 (by rw [hcur, hcol]; exact hfit), hcur]

theorem cursor_print_narrow_margin {v : Vt} {ch : Char}
    (hpc : v.printChar ch = ch) (hw : charWidth ch = 1) (hins : v.modes.insert = false)
    (hpend : v.cursor.pending = false) (hmar : v.cols ≤ v.cursor.x + 1) :
    (v.print ch).cursor
      = { v.cursor with x := v.cols - 1, pending := v.modes.wrap } := by
  rw [print_narrow_eq hpc hw hins hpend]
  obtain ⟨hcur, hcol, hmod⟩ := write_frame v
    (fun u => (u.putCell v.cursor.x v.cursor.y
      { base := ch, marks := [], width := 1, pen := v.pen }).mendRow v.cursor.y)
    (fun u => ⟨(off_mendRow _ _).trans (off_putCell' _ _ _ _),
      (cursor_mendRow _ _).trans (cursor_putCell _ _ _ _)⟩)
  rw [cursor_printAdvance_ge _ 1 (by rw [hcur, hcol]; exact hmar), hcur, hcol, hmod]

theorem cursor_print_wide_fits {v : Vt} {ch : Char}
    (hpc : v.printChar ch = ch) (hw : charWidth ch = 2) (hins : v.modes.insert = false)
    (hpend : v.cursor.pending = false) (hfit : v.cursor.x + 1 < v.cols)
    (hfit2 : v.cursor.x + 2 < v.cols) :
    (v.print ch).cursor = { v.cursor with x := v.cursor.x + 2, pending := false } := by
  rw [print_wide_eq hpc hw hins hpend hfit]
  obtain ⟨hcur, hcol, -⟩ := write_frame v
    (fun u => ((u.putCell v.cursor.x v.cursor.y
        { base := ch, marks := [], width := 2, pen := v.pen }).putCell
          (v.cursor.x + 1) v.cursor.y
          (Cell.shadow { base := ch, marks := [], width := 2, pen := v.pen })).mendRow
            v.cursor.y)
    (fun u => ⟨((off_mendRow _ _).trans (off_putCell' _ _ _ _)).trans (off_putCell' _ _ _ _),
      ((cursor_mendRow _ _).trans (cursor_putCell _ _ _ _)).trans (cursor_putCell _ _ _ _)⟩)
  rw [cursor_printAdvance_lt _ 2 (by rw [hcur, hcol]; exact hfit2), hcur]

/-- The pair that ends exactly at the margin: the shadow occupies the last column, so
the advance clamps and arms wrap-pending — the state the spec's negative result says
is load-bearing. -/
theorem cursor_print_wide_margin {v : Vt} {ch : Char}
    (hpc : v.printChar ch = ch) (hw : charWidth ch = 2) (hins : v.modes.insert = false)
    (hpend : v.cursor.pending = false) (hfit : v.cursor.x + 1 < v.cols)
    (hmar : v.cols ≤ v.cursor.x + 2) :
    (v.print ch).cursor = { v.cursor with x := v.cols - 1, pending := v.modes.wrap } := by
  rw [print_wide_eq hpc hw hins hpend hfit]
  obtain ⟨hcur, hcol, hmod⟩ := write_frame v
    (fun u => ((u.putCell v.cursor.x v.cursor.y
        { base := ch, marks := [], width := 2, pen := v.pen }).putCell
          (v.cursor.x + 1) v.cursor.y
          (Cell.shadow { base := ch, marks := [], width := 2, pen := v.pen })).mendRow
            v.cursor.y)
    (fun u => ⟨((off_mendRow _ _).trans (off_putCell' _ _ _ _)).trans (off_putCell' _ _ _ _),
      ((cursor_mendRow _ _).trans (cursor_putCell _ _ _ _)).trans (cursor_putCell _ _ _ _)⟩)
  rw [cursor_printAdvance_ge _ 2 (by rw [hcur, hcol]; exact hmar), hcur, hcol, hmod]

/-- A combining mark moves nothing: `print_mark_eq` is a write and a mend. -/
theorem cursor_print_mark {v : Vt} {m : Char}
    (hpc : v.printChar m = m) (hw : charWidth m = 0) (hpend : v.cursor.pending = false)
    (hnw : (v.getCell (v.cursor.x - 1) v.cursor.y).width ≠ 0)
    (hcap : (v.getCell (v.cursor.x - 1) v.cursor.y).marks.length < 8) :
    (v.print m).cursor = v.cursor := by
  rw [print_mark_eq hpc hw hpend hnw hcap, cursor_mendRow, cursor_putCell]

/-- …and it does not *disarm* wrap-pending either, which is what lets a run of marks on
a final-column glyph all land on the same cell. -/
theorem cursor_print_mark_pending {v : Vt} {m : Char}
    (hpc : v.printChar m = m) (hw : charWidth m = 0) (hpend : v.cursor.pending = true)
    (hnw : (v.getCell v.cursor.x v.cursor.y).width ≠ 0)
    (hcap : (v.getCell v.cursor.x v.cursor.y).marks.length < 8) :
    (v.print m).cursor = v.cursor := by
  rw [print_mark_pending_eq hpc hw hpend hnw hcap, cursor_mendRow, cursor_putCell]

/-! ### Sticky projections of the print stages

The stage claims follow their frames; the complete print projects `off_print`. -/

theorem stick_printWrap (v : Vt) : stick v.printWrap = stick v := by rw [frame_printWrap]; rfl

theorem stick_printWideWrap (v : Vt) (w : Nat) : stick (v.printWideWrap w) = stick v := by
  rw [frame_printWideWrap]; rfl

theorem stick_printShift (v : Vt) (w : Nat) : stick (v.printShift w) = stick v := by
  rw [frame_printShift]; rfl

theorem stick_printPut (v : Vt) (ch : Char) (w : Nat) : stick (v.printPut ch w) = stick v := by
  rw [frame_printPut]; rfl

theorem stick_printAdvance (v : Vt) (w : Nat) : stick (v.printAdvance w) = stick v := by
  rw [frame_printAdvance]; rfl

theorem stick_printMark (v : Vt) (ch : Char) : stick (v.printMark ch) = stick v := by
  rw [frame_printMark]; rfl

/-- Printing a glyph cannot move the region, the charsets, the shift state or the
screen selection — it *reads* the charsets (`printChar` translates) and reads the
screen selection (a full-screen scroll goes to scrollback only on main), and
writes neither. -/
theorem stick_print (v : Vt) (ch : Char) : stick (v.print ch) = stick v :=
  congrArg (fun s => Sticky.mk s.rows s.top s.bot s.g0 s.g1 s.so s.alt.isSome) (off_print v ch)

theorem stick_acceptChar (v : Vt) (n : Nat) : stick (v.acceptChar n) = stick v := by
  unfold Vt.acceptChar; split <;> exact stick_print _ _

/-- `SO`/`SI` are the two C0 bytes that write a sticky field, so they are the two
excluded here — the reason `Render.charsetAnsi`'s shift state needs a claim of
its own and the rest of the stream can be transparent to it. -/
theorem stick_ctl (v : Vt) (b : UInt8) (h1 : b ≠ 0x0E) (h2 : b ≠ 0x0F) :
    stick (v.ctl b) = stick v := by
  unfold Vt.ctl
  split
  all_goals first
    | rfl
    | exact stick_backspace _
    | exact stick_tab _
    | exact stick_lineFeed _
    | exact stick_carriageReturn _
    | exact absurd rfl h1
    | exact absurd rfl h2

theorem stick_stepGround (v : Vt) (b : UInt8) (h1 : b ≠ 0x0E) (h2 : b ≠ 0x0F) :
    stick (v.stepGround b) = stick v := by
  unfold Vt.stepGround
  split
  · rfl                                       -- ESC: parser state only
  split
  · exact stick_ctl _ _ h1 h2                 -- C0
  split
  · exact stick_acceptChar _ _                -- ASCII
  split
  · -- a continuation byte: dropped, accumulated, or completes a codepoint
    split
    · rfl
    · split
      · exact stick_acceptChar _ _
      · rfl
  repeat' split
  all_goals rfl

/-! ### The transforms — the four things in a restore stream that DO write a
sticky field. Named, so the `Render` ladder composes them the way `MMap`
composes `Modes` transforms, and so "what can move this field" is a list. -/

/-- `?1049 h`/`l` (also `?47`, `?1047`): the screen switch, which resets the
region as a side effect. Mirrors `enterAlt`/`leaveAlt` including their
idempotence — which is why `alt` has to be *in* the bundle and not just an
output of it. -/
def stAlt (on : Bool) (s : Sticky) : Sticky :=
  match on with
  | true => if s.alt then s else { s with alt := true, top := 0, bot := s.rows - 1 }
  | false => if s.alt then { s with alt := false, top := 0, bot := s.rows - 1 } else s

/-- `CSI t ; b r` (DECSTBM), on the arguments after defaults and the 1-based
decrement — including the receiver-side refusal of a region of fewer than two
lines or one that does not fit, which is why `rows` is in the bundle. -/
def stStbm (t bo : Nat) (s : Sticky) : Sticky :=
  if t < bo && bo < s.rows then { s with top := t, bot := bo } else s

/-- `ESC ( x` / `ESC ) x`: a charset designation. -/
def stCharset (i x : UInt8) (s : Sticky) : Sticky :=
  if i == 0x28 then { s with g0 := x == 0x30 }
  else if i == 0x29 then { s with g1 := x == 0x30 }
  else s

/-- `SM`/`RM`: of the fourteen modes `setMode` knows, only the three
screen-switch numbers reach a sticky field. -/
def stSetMode (n : Nat) (on : Bool) (s : Sticky) : Sticky :=
  if n == 47 || n == 1047 || n == 1049 then stAlt on s else s

/-! The transforms' own arithmetic, so the value chain in `Render` can be a
sequence of rewrites rather than one giant `rfl`. -/

theorem stAlt_rows (on : Bool) (s : Sticky) : (stAlt on s).rows = s.rows := by
  unfold stAlt; cases on <;> (dsimp only; split <;> rfl)

theorem stAlt_alt (on : Bool) (s : Sticky) : (stAlt on s).alt = on := by
  unfold stAlt
  cases on
  · dsimp only
    split
    · rfl
    · rename_i h; simpa using h
  · dsimp only
    split
    · rename_i h; exact h
    · rfl

/-- `DECSTBM` accepted: the receiver-side guard is exactly "at least two rows and
it fits". -/
theorem stStbm_of {t bo : Nat} {s : Sticky} (h1 : t < bo) (h2 : bo < s.rows) :
    stStbm t bo s = { s with top := t, bot := bo } := by
  unfold stStbm; rw [ite_eq_left (by simp [h1, h2])]

theorem stStbm_rows (t bo : Nat) (s : Sticky) : (stStbm t bo s).rows = s.rows := by
  unfold stStbm; split <;> rfl

theorem stick_enterAlt (v : Vt) (b : Bool) : stick (v.enterAlt b) = stAlt true (stick v) := by
  unfold Vt.enterAlt stAlt
  dsimp only
  by_cases h : v.altGrid.isSome = true
  · rw [ite_eq_left h, ite_eq_left (show (stick v).alt = true from h)]
  · rw [ite_eq_right h, ite_eq_right (show ¬((stick v).alt = true) from h)]
    rfl

theorem stick_leaveAlt (v : Vt) (b : Bool) : stick (v.leaveAlt b) = stAlt false (stick v) := by
  unfold Vt.leaveAlt stAlt
  dsimp only
  rcases hv : v.altGrid with - | x
  · rw [ite_eq_right (show ¬((stick v).alt = true) from by
      show ¬(v.altGrid.isSome = true); rw [hv]; simp)]
  · rw [ite_eq_left (show (stick v).alt = true from by
      show v.altGrid.isSome = true; rw [hv]; simp)]
    rfl

theorem stick_stepEscInter (v : Vt) (i x : UInt8) (hlo : 0x30 ≤ x) (hhi : x ≤ 0x7E) :
    stick (v.stepEscInter i x) = stCharset i x (stick v) := by
  rw [stepEscInter_final v i x hlo hhi]
  unfold stCharset
  by_cases h28 : (i == 0x28) = true
  · rw [ite_eq_left h28, ite_eq_left h28]; rfl
  · rw [ite_eq_right h28, ite_eq_right h28]
    by_cases h29 : (i == 0x29) = true
    · rw [ite_eq_left h29, ite_eq_left h29]; rfl
    · rw [ite_eq_right h29, ite_eq_right h29]
      rfl

theorem stick_setMode (v : Vt) (n : Nat) (on : Bool) :
    stick (v.setMode true n on) = stSetMode n on (stick v) := by
  have halt : ∀ (u : Vt) (sv : Bool),
      stick (if on then u.enterAlt sv else u.leaveAlt sv) = stAlt on (stick u) := by
    intro u sv
    cases on
    · rw [ite_eq_right (by decide)]; exact stick_leaveAlt u sv
    · rw [ite_eq_left rfl]; exact stick_enterAlt u sv
  by_cases h47 : n = 47
  · subst h47
    show stick (if on then v.enterAlt false else v.leaveAlt false) = _
    rw [halt v false]
    unfold stSetMode
    rw [ite_eq_left (by decide)]
  by_cases h1047 : n = 1047
  · subst h1047
    show stick (if on then v.enterAlt false else v.leaveAlt false) = _
    rw [halt v false]
    unfold stSetMode
    rw [ite_eq_left (by decide)]
  by_cases h1049 : n = 1049
  · subst h1049
    show stick (if on then v.enterAlt true else v.leaveAlt true) = _
    rw [halt v true]
    unfold stSetMode
    rw [ite_eq_left (by decide)]
  -- every remaining arm writes `modes`, the cursor or the saved slot only
  unfold stSetMode
  rw [ite_eq_right (by
    intro h
    simp only [Bool.or_eq_true, beq_iff_eq] at h
    rcases h with (h | h) | h
    · exact h47 h
    · exact h1047 h
    · exact h1049 h)]
  unfold Vt.setMode
  split <;> rename_i hpv
  · split
    all_goals first
      | rfl
      | exact stick_moveTo _ _ _
      | (split <;> rfl)
      | (exfalso; simp_all)
  · exact absurd rfl hpv

/-- IRM is the only non-private mode we parse, and it is `modes`-only. -/
theorem stick_setMode_plain (v : Vt) (n : Nat) (on : Bool) :
    stick (v.setMode false n on) = stick v := by
  unfold Vt.setMode
  split <;> rename_i hpv
  · exact absurd hpv (by decide)
  · split <;> rfl

/-! ### Conditional sticky preservation through `csiDispatch`

One case-bash over every final byte, so that a new sequence in the emitter cannot
quietly acquire a sticky effect: the three finals that *can* have one are
hypotheses, not omissions. -/

/-- `SM` applies all parameters in order, as a state equation including every
mode's side effects. A first-parameter equation would discard requested modes. -/
theorem csiDispatch_sm (v : Vt) (s : CsiState) (hi : s.ignore = false) :
    v.csiDispatch s 0x68 = v.setModes (s.priv == 0x3F) s.params.toList true := by
  unfold Vt.csiDispatch; rw [ite_eq_right (by rw [hi]; simp)]; rfl

theorem csiDispatch_rm (v : Vt) (s : CsiState) (hi : s.ignore = false) :
    v.csiDispatch s 0x6C = v.setModes (s.priv == 0x3F) s.params.toList false := by
  unfold Vt.csiDispatch; rw [ite_eq_right (by rw [hi]; simp)]; rfl

/-- Single-mode emitters recover their exact old state equation from the full
parameter list, not just from a fact about its first element. -/
theorem csiDispatch_sm_one (v : Vt) (s : CsiState) (n : Nat) (sub : Bool)
    (hi : s.ignore = false) (hp : s.params = #[(n, sub)]) :
    v.csiDispatch s 0x68 = v.setMode (s.priv == 0x3F) n true := by
  rw [csiDispatch_sm v s hi, hp]
  exact setModes_one v _ n sub true

theorem csiDispatch_rm_one (v : Vt) (s : CsiState) (n : Nat) (sub : Bool)
    (hi : s.ignore = false) (hp : s.params = #[(n, sub)]) :
    v.csiDispatch s 0x6C = v.setMode (s.priv == 0x3F) n false := by
  rw [csiDispatch_rm v s hi, hp]
  exact setModes_one v _ n sub false

/-- `DECSTBM`, likewise as a state equation. -/
theorem csiDispatch_stbm (v : Vt) (s : CsiState) (hi : s.ignore = false) (hp : s.priv = 0) :
    v.csiDispatch s 0x72 =
      (if s.arg 0 1 - 1 < s.arg 1 v.rows - 1 && s.arg 1 v.rows - 1 < v.rows
       then ({ v with top := s.arg 0 1 - 1, bot := s.arg 1 v.rows - 1 }).moveTo 0 0 else v) := by
  unfold Vt.csiDispatch
  rw [ite_eq_right (by rw [hi]; simp)]
  show (if s.priv != 0 then v else
      if s.arg 0 1 - 1 < s.arg 1 v.rows - 1 && s.arg 1 v.rows - 1 < v.rows
      then ({ v with top := s.arg 0 1 - 1, bot := s.arg 1 v.rows - 1 }).moveTo 0 0 else v) = _
  rw [ite_eq_right (by rw [hp]; simp)]

theorem stick_csiDispatch_stbm (v : Vt) (s : CsiState) (hi : s.ignore = false) (hp : s.priv = 0) :
    stick (v.csiDispatch s 0x72)
      = stStbm (s.arg 0 1 - 1) (s.arg 1 v.rows - 1) (stick v) := by
  have hst : stStbm (s.arg 0 1 - 1) (s.arg 1 v.rows - 1) (stick v)
      = (if s.arg 0 1 - 1 < s.arg 1 v.rows - 1 && s.arg 1 v.rows - 1 < v.rows
         then { stick v with top := s.arg 0 1 - 1, bot := s.arg 1 v.rows - 1 } else stick v) := by rfl
  rw [csiDispatch_stbm v s hi hp, hst]
  split
  · exact stick_moveTo _ 0 0
  · rfl

/-! #### The preservers, one per final byte the emitters use

Per-final rather than one bash over all thirty: the tail walk
(`Render.csi_tail_proj`) takes the dispatch fact as a *hypothesis*, and every
sequence linger emits has a concrete final byte, so a 30-way case split with a
variable scrutinee would be work nobody needs. The same shape as
`modes_csiDispatch_{cup,sgr,stbm}`. -/

theorem stick_csiDispatch_cup (v : Vt) (s : CsiState) :
    stick (v.csiDispatch s 0x48) = stick v := by
  by_cases hi : s.ignore = true
  · simp [Vt.csiDispatch, hi]
  · unfold Vt.csiDispatch; rw [ite_eq_right (by simp [hi])]; exact stick_moveTo _ _ _

theorem stick_csiDispatch_cha (v : Vt) (s : CsiState) :
    stick (v.csiDispatch s 0x47) = stick v := by
  by_cases hi : s.ignore = true
  · simp [Vt.csiDispatch, hi]
  · unfold Vt.csiDispatch; rw [ite_eq_right (by simp [hi])]; exact stick_setCol _ _

theorem stick_csiDispatch_sgr (v : Vt) (s : CsiState) :
    stick (v.csiDispatch s 0x6D) = stick v := by
  by_cases hi : s.ignore = true
  · simp [Vt.csiDispatch, hi]
  · unfold Vt.csiDispatch
    rw [ite_eq_right (by simp [hi])]
    show stick (if s.priv == 0 then v.applySgr s.sgrParams else v) = _
    split
    · exact stick_applySgr _ _
    · rfl

theorem stick_csiDispatch_ed (v : Vt) (s : CsiState) :
    stick (v.csiDispatch s 0x4A) = stick v := by
  by_cases hi : s.ignore = true
  · simp [Vt.csiDispatch, hi]
  · unfold Vt.csiDispatch; rw [ite_eq_right (by simp [hi])]; exact stick_eraseScreen _ _

theorem stick_csiDispatch_tbc (v : Vt) (s : CsiState) :
    stick (v.csiDispatch s 0x67) = stick v := by
  by_cases hi : s.ignore = true
  · simp [Vt.csiDispatch, hi]
  · unfold Vt.csiDispatch
    rw [ite_eq_right (by simp [hi])]
    show stick (match s.arg 0 0 with
      | 0 => { v with tabs := v.tabs.setIfInBounds v.cursor.x false }
      | 3 => { v with tabs := Array.replicate v.cols false }
      | _ => v) = _
    split <;> rfl

/-! ### The remaining parser states -/

theorem stick_stepOsc (v : Vt) (acc : Array UInt8) (e : Bool) (b : UInt8) :
    stick (v.stepOsc acc e b) = stick v := by
  unfold Vt.stepOsc
  repeat' split
  all_goals first | exact stick_oscFinish _ _ | rfl

/-- `RIS` (`ESC c`) is the one escape that resets everything, and no linger
stream emits it. -/
theorem stick_stepEsc (v : Vt) (b : UInt8) (h : b ≠ 0x63) :
    stick (v.stepEsc b) = stick v := by
  unfold Vt.stepEsc
  split
  all_goals first
    | rfl
    | exact stick_lineFeed _
    | exact (stick_lineFeed _).trans (stick_carriageReturn _)
    | exact stick_reverseIndex _
    | exact absurd rfl h
    | (repeat' split
       all_goals rfl)

/-! ### `step`, one lemma per incoming parser state

Each is the `stick` analog of `ground_step` / `org_step_of_*`: `abortUtf8` cannot
move a sticky field (it drops pending UTF-8 and nothing else), so the incoming
state selects the arm and the arm's lemma finishes it. -/

theorem stick_step_of_ground {v : Vt} (b : UInt8) (hg : v.pstate = .ground)
    (h1 : b ≠ 0x0E) (h2 : b ≠ 0x0F) : stick (v.step b) = stick v := by
  have hw : (v.abortUtf8 b).pstate = PState.ground := by rw [ps_abortUtf8]; exact hg
  unfold Vt.step
  dsimp only
  rw [hw]
  exact (stick_stepGround _ b h1 h2).trans (stick_abortUtf8 v b)

theorem stick_step_of_esc {v : Vt} (b : UInt8) (hg : v.pstate = .esc) (h : b ≠ 0x63) :
    stick (v.step b) = stick v := by
  have hw : (v.abortUtf8 b).pstate = PState.esc := by rw [ps_abortUtf8]; exact hg
  unfold Vt.step
  dsimp only
  rw [hw]
  exact (stick_stepEsc _ b h).trans (stick_abortUtf8 v b)

theorem stick_step_of_osc {v : Vt} {acc : Array UInt8} {e : Bool} (b : UInt8)
    (hg : v.pstate = .osc acc e) : stick (v.step b) = stick v := by
  have hw : (v.abortUtf8 b).pstate = PState.osc acc e := by rw [ps_abortUtf8]; exact hg
  unfold Vt.step
  dsimp only
  rw [hw]
  exact (stick_stepOsc _ acc e b).trans (stick_abortUtf8 v b)

theorem stick_step_of_str {v : Vt} {e : Bool} (b : UInt8) (hg : v.pstate = .str e) :
    stick (v.step b) = stick v := by
  have hw : (v.abortUtf8 b).pstate = PState.str e := by rw [ps_abortUtf8]; exact hg
  unfold Vt.step
  dsimp only
  rw [hw]
  exact (stick_stepStr _ e b).trans (stick_abortUtf8 v b)

theorem stick_step_of_escInter {v : Vt} {i : UInt8} (x : UInt8) (hg : v.pstate = .escInter i)
    (hlo : 0x30 ≤ x) (hhi : x ≤ 0x7E) :
    stick (v.step x) = stCharset i x (stick v) := by
  have hw : (v.abortUtf8 x).pstate = PState.escInter i := by rw [ps_abortUtf8]; exact hg
  unfold Vt.step
  dsimp only
  rw [hw]
  rw [stick_stepEscInter _ i x hlo hhi, stick_abortUtf8]

/-- `SO` and `SI` from ground, the two bytes `stick_ctl` excludes. -/
theorem stick_step_si {v : Vt} (hg : v.pstate = .ground) :
    stick (v.step 0x0F) = { stick v with so := false } := by
  have hw : (v.abortUtf8 0x0F).pstate = PState.ground := by rw [ps_abortUtf8]; exact hg
  unfold Vt.step
  dsimp only
  rw [hw]
  unfold Vt.stepGround
  rw [ite_eq_right (by decide), ite_eq_left (by decide)]
  rw [show (v.abortUtf8 0x0F).ctl 0x0F = { (v.abortUtf8 0x0F) with shiftOut := false } from rfl,
    show stick { (v.abortUtf8 0x0F) with shiftOut := false }
      = { stick (v.abortUtf8 0x0F) with so := false } from rfl,
    stick_abortUtf8]

theorem stick_step_so {v : Vt} (hg : v.pstate = .ground) :
    stick (v.step 0x0E) = { stick v with so := true } := by
  have hw : (v.abortUtf8 0x0E).pstate = PState.ground := by rw [ps_abortUtf8]; exact hg
  unfold Vt.step
  dsimp only
  rw [hw]
  unfold Vt.stepGround
  rw [ite_eq_right (by decide), ite_eq_left (by decide)]
  rw [show (v.abortUtf8 0x0E).ctl 0x0E = { (v.abortUtf8 0x0E) with shiftOut := true } from rfl,
    show stick { (v.abortUtf8 0x0E) with shiftOut := true }
      = { stick (v.abortUtf8 0x0E) with so := true } from rfl,
    stick_abortUtf8]

/-! ## The clamp and the two tables, said out loud

Three pure-core values the tree *used* everywhere and *stated* nowhere: every proof that
needed them re-derived them inline, which is why the old source scanner counted
them as unclaimed. `Theorems/Coverage.lean` now checks exact constants in theorem
types. Each theorem below is the postcondition its callers were already assuming. -/

/-- **A clamped dimension is a legal dimension, and above the cap it *is* the cap.** The
second half is what makes `clampDim n + 1` the smallest value a caller must reject. -/
theorem clampDim_range (n : Nat) :
    1 ≤ clampDim n ∧ clampDim n ≤ 1000 ∧ (1000 ≤ n → clampDim n = 1000) := by
  unfold clampDim
  omega

/-- …and it touches nothing already legal. The **iff** matters: the reverse direction is
what four proofs re-derive by hand, and the forward one falsifies a clamp whose range
slipped — `max n 1` alone satisfies the reverse and fails this. -/
theorem clampDim_eq_self (n : Nat) : clampDim n = n ↔ 1 ≤ n ∧ n ≤ 1000 := by
  unfold clampDim
  omega

/-- **Both constructors apply the clamp, and the grid they build is the clamped height.**
`Good.resize` bounds the `rows` *field*; the grid proofs take `grid.size = rows` as a
hypothesis. This is what connects the two. -/
theorem init_shape (cols rows : Nat) :
    (Vt.init cols rows).cols = clampDim cols ∧ (Vt.init cols rows).rows = clampDim rows ∧
      (Vt.init cols rows).grid.size = clampDim rows :=
  ⟨rfl, rfl, by simp [Vt.init]⟩

/-- A resize clears deferred wrap in every cursor slot, including the main
screen cursor stashed while the alternate screen is active. -/
theorem resize_clears_pending (v : Vt) (cols rows : Nat) :
    (v.resize cols rows).cursor.pending = false ∧
      (v.resize cols rows).saved.cur.pending = false ∧
      ∀ g cur pen, (v.resize cols rows).altGrid = some (g, cur, pen) → cur.pending = false := by
  refine ⟨rfl, rfl, ?_⟩
  intro g cur pen h
  cases hAlt : v.altGrid with
  | none => simp [Vt.resize, hAlt] at h
  | some value =>
    obtain ⟨oldGrid, oldCur, oldPen⟩ := value
    simp only [Vt.resize, hAlt, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨_, hcur, _⟩
    rw [← hcur]

/-- **A 256-colour parameter cannot escape the palette.** -/
theorem color256_idx (n : Nat) : color256 n = Color.idx (UInt8.ofNat (min n 255)) := by rfl

/-- …and it **saturates rather than wraps**, which is the whole reason the `min` is there:
`UInt8.ofNat 256` is `0`, so without it `SGR 38;5;256` would silently select colour 0
instead of 255. -/
theorem color256_saturates : color256 256 = color256 255 := by rfl

/-- **Line drawing is geometry-neutral.** Every source is a one-column ASCII glyph and so
is every box character it maps to, so a charset designation cannot change a row's column
accounting — the thing `CellOk.width` ties stored cells to. A mapping added into the wide
or zero-width tables falsifies this. -/
theorem charWidth_decLine (c : Char) : charWidth (decLine c) = charWidth c := by
  unfold decLine
  repeat' split
  all_goals first
    | rfl
    | (subst_vars; decide)
    | decide

/-- **The `ByteArray` door is the same machine.** The daemon feeds the emulator
`ByteArray`s; `feedBytes` is the adapter, and this says it adds nothing — so every §Chunk
and §Bound theorem stated over `feed` covers the surface the runtime actually calls. -/
theorem feedBytes_eq (v : Vt) (bytes : ByteArray) : v.feedBytes bytes = v.feed bytes.toList := by
  rfl

/-- **The SGR parameter list is the parsed array, exactly.** `Good.csiLe` bounds
`params.size`; `sgrParams` is the list view `applySgr` consumes, so this is what carries the
CSI parameter cap across into the pen. -/
theorem sgrParams_length (s : CsiState) : s.sgrParams.length = s.params.size := by
  rfl

/-! ## Boundaries for injected titles

An ESC intermediate is pending until a final byte, even for sequences the emulator
does not interpret. DEL cannot publish a boundary in CSI, ESC or an intermediate
sequence. These claims allow any receiver title, screen, CSI parameters and UTF-8
state; only the parser state and the byte class select the transition.
-/

/-- Every byte in the full ESC intermediate range opens a pending sequence. -/
theorem stepEsc_intermediate (v : Vt) (b : UInt8)
    (hlo : 0x20 ≤ b) (hhi : b ≤ 0x2F) :
    v.stepEsc b = { v with pstate := .escInter b } := by
  unfold Vt.stepEsc
  split
  all_goals first
    | exact False.elim ((of_decide_eq_false rfl) hhi)
    | exact False.elim ((of_decide_eq_false rfl) hlo)
    | simp [hlo, hhi]

/-- The shared parser uses that transition even with a pending UTF-8 decoder. -/
theorem step_esc_intermediate {v : Vt} (b : UInt8) (hp : v.pstate = .esc)
    (hlo : 0x20 ≤ b) (hhi : b ≤ 0x2F) :
    v.step b = { (v.abortUtf8 b) with pstate := .escInter b } := by
  simp only [Vt.step, ps_abortUtf8, hp]
  exact stepEsc_intermediate _ b hlo hhi

/-- Further intermediates and ignored nonfinal bytes retain a pending parser
and the receiver's title. A new ESC has its own restart transition below. -/
theorem step_escInter_pending {v : Vt} {i : UInt8} (b : UInt8)
    (hp : v.pstate = .escInter i) (hf : ¬ (0x30 ≤ b ∧ b ≤ 0x7E))
    (he : b ≠ 0x1B) :
    (∃ j, (v.step b).pstate = .escInter j) ∧
      (v.step b).windowTitle = v.windowTitle := by
  simp only [Vt.step, ps_abortUtf8, hp]
  simp only [Vt.stepEscInter, Bool.and_eq_true, decide_eq_true_eq, hf, ite_false,
    beq_eq_false_iff_ne.mpr he, Bool.false_eq_true]
  split
  all_goals refine ⟨⟨_, rfl⟩, ?_⟩
  all_goals unfold Vt.windowTitle Vt.abortUtf8
  all_goals split <;> rfl

/-- An arbitrarily long unfinished sequence stays closed to injected output.
There is no length bound or assumption on the stored title. -/
theorem feed_escInter_pending (bytes : List UInt8) {v : Vt} {i : UInt8}
    (hp : v.pstate = .escInter i)
    (hb : ∀ b ∈ bytes, ¬ (0x30 ≤ b ∧ b ≤ 0x7E) ∧ b ≠ 0x1B) :
    (∃ j, (v.feed bytes).pstate = .escInter j) ∧
      (v.feed bytes).atBoundary = false ∧
      (v.feed bytes).windowTitle = v.windowTitle := by
  induction bytes generalizing v i with
  | nil => exact ⟨⟨i, hp⟩, by simp [Vt.feed, Vt.atBoundary, hp], rfl⟩
  | cons b bs ih =>
    obtain ⟨⟨j, hj⟩, ht⟩ := step_escInter_pending b hp (hb b (by simp)).1 (hb b (by simp)).2
    have hi := ih hj (fun c hc => hb c (by simp [hc]))
    exact ⟨hi.1, hi.2.1, hi.2.2.trans ht⟩

/-- Discarding scrollback after each byte cannot introduce a false boundary.
The observer waits through the whole unfinished sequence, preserving its title. -/
theorem observe_escInter_pending (bytes : List UInt8) {v : Vt} {i : UInt8}
    (hp : v.pstate = .escInter i)
    (hb : ∀ b ∈ bytes, ¬ (0x30 ≤ b ∧ b ≤ 0x7E) ∧ b ≠ 0x1B) :
    (∃ j, (v.observe bytes).pstate = .escInter j) ∧
      (v.observe bytes).atBoundary = false ∧
      (v.observe bytes).windowTitle = v.windowTitle := by
  induction bytes generalizing v i with
  | nil => exact ⟨⟨i, hp⟩, by simp [Vt.observe, Vt.atBoundary, hp], rfl⟩
  | cons b bs ih =>
    obtain ⟨⟨j, hj⟩, ht⟩ := step_escInter_pending b hp (hb b (by simp)).1 (hb b (by simp)).2
    have hi := ih (v := { (v.step b) with sb := {} }) hj (fun c hc => hb c (by simp [hc]))
    exact ⟨hi.1, hi.2.1, hi.2.2.trans ht⟩

/-- Starting after ESC, any intermediate followed by any unfinished suffix
keeps the public title observer away from a write boundary. -/
theorem observe_esc_intermediates (i : UInt8) (bytes : List UInt8) {v : Vt}
    (hp : v.pstate = .esc) (hlo : 0x20 ≤ i) (hhi : i ≤ 0x2F)
    (hb : ∀ b ∈ bytes, ¬ (0x30 ≤ b ∧ b ≤ 0x7E) ∧ b ≠ 0x1B) :
    (v.observe (i :: bytes)).atBoundary = false ∧
      (v.observe (i :: bytes)).windowTitle = v.windowTitle := by
  change ({ (v.step i) with sb := {} }.observe bytes).atBoundary = false ∧
    ({ (v.step i) with sb := {} }.observe bytes).windowTitle = _
  rw [step_esc_intermediate i hp hlo hhi]
  have h := observe_escInter_pending bytes
    (v := { (v.abortUtf8 i) with pstate := .escInter i, sb := {} }) rfl hb
  refine ⟨h.2.1, h.2.2.trans ?_⟩
  unfold Vt.windowTitle Vt.abortUtf8
  split <;> rfl

/-- A final completes both the control sequence and any stray partial UTF-8
decoder, so waiting for an intermediate sequence does not block forever. -/
theorem step_escInter_final_boundary {v : Vt} {i : UInt8} (b : UInt8)
    (hp : v.pstate = .escInter i) (hlo : 0x30 ≤ b) (hhi : b ≤ 0x7E) :
    (v.step b).atBoundary = true ∧ (v.step b).windowTitle = v.windowTitle := by
  have ha : b < 0x80 := by
    rw [UInt8.lt_iff_toNat_lt]
    rw [UInt8.le_iff_toNat_le] at hhi
    change b.toNat ≤ 126 at hhi
    change b.toNat < 128
    omega
  have hu : (v.abortUtf8 b).u8need = 0 := by
    unfold Vt.abortUtf8
    split
    · rfl
    · rename_i h
      simp [ha] at h
      omega
  simp only [Vt.step, ps_abortUtf8, hp]
  rw [stepEscInter_final _ i b hlo hhi]
  repeat' split
  all_goals constructor
  all_goals first
    | simpa [Vt.atBoundary] using hu
    | (unfold Vt.windowTitle Vt.abortUtf8
       split <;> rfl)

/-- ESC abandons an intermediate sequence by starting a new ESC sequence,
never by briefly reporting a boundary where an OSC title could be injected. -/
theorem step_escInter_restart {v : Vt} {i : UInt8} (hp : v.pstate = .escInter i) :
    (v.step 0x1B).pstate = .esc ∧ (v.step 0x1B).atBoundary = false ∧
      (v.step 0x1B).windowTitle = v.windowTitle := by
  simp only [Vt.step, ps_abortUtf8, hp]
  refine ⟨rfl, rfl, ?_⟩
  change (v.abortUtf8 0x1B).title = v.title
  unfold Vt.abortUtf8
  split <;> rfl

/-- DEL leaves the entire parser state intact, including every CSI parameter
and the selected charset bank. Its only possible effect is UTF-8 neutralization. -/
theorem step_del_preserves_parser {v : Vt}
    (hp : v.pstate = .esc ∨ (∃ i, v.pstate = .escInter i) ∨ (∃ s, v.pstate = .csi s)) :
    v.step 0x7F = v.abortUtf8 0x7F := by
  rcases hp with hp | ⟨i, hp⟩ | ⟨s, hp⟩
  · simp only [Vt.step, ps_abortUtf8, hp]
    rfl
  · simp only [Vt.step, ps_abortUtf8, hp]
    change { (v.abortUtf8 0x7F) with pstate := .escInter i } = _
    rw [← hp, ← ps_abortUtf8 v 0x7F]
  · simp only [Vt.step, ps_abortUtf8, hp]
    rfl

/-- The public observer cannot permit title output after DEL in an incomplete
CSI, ESC or intermediate sequence; the application title remains unchanged. -/
theorem observe_del_boundary {v : Vt}
    (hp : v.pstate = .esc ∨ (∃ i, v.pstate = .escInter i) ∨ (∃ s, v.pstate = .csi s)) :
    (v.observe [0x7F]).pstate = v.pstate ∧
      (v.observe [0x7F]).atBoundary = false ∧
      (v.observe [0x7F]).windowTitle = v.windowTitle := by
  change (v.step 0x7F).pstate = _ ∧ (v.step 0x7F).atBoundary = false ∧
    (v.step 0x7F).windowTitle = _
  rw [step_del_preserves_parser hp]
  refine ⟨ps_abortUtf8 _ _, ?_, ?_⟩
  · rcases hp with hp | ⟨i, hp⟩ | ⟨s, hp⟩ <;>
      simp [Vt.atBoundary, ps_abortUtf8, hp]
  · unfold Vt.windowTitle Vt.abortUtf8
    split <;> rfl

@[simp]
theorem windowTitle_eq (v : Vt) : v.windowTitle = v.title := rfl

theorem atBoundary_iff (v : Vt) : v.atBoundary = true ↔ v.pstate = .ground ∧ v.u8need = 0 := by
  simp [Vt.atBoundary]

public theorem observe_append (v : Vt) (a b : List UInt8) :
    v.observe (a ++ b) = (v.observe a).observe b := by
  simp [Vt.observe, List.foldl_append]

/-- Every observer byte is the existing parser step, changing only discarded
history. In particular its title, parser state and partial UTF-8 agree exactly. -/
theorem observe_singleton (v : Vt) (b : UInt8) :
    v.observe [b] = { (v.step b) with sb := {} } := rfl

theorem observe_no_history (v : Vt) (bytes : List UInt8) (h : v.sb = {}) :
    (v.observe bytes).sb = {} :=
  invariant_foldl (·.sb = {}) _ (fun _ _ _ => rfl) bytes v h

theorem observe_good (v : Vt) (bytes : List UInt8) (h : Good v) : Good (v.observe bytes) :=
  invariant_foldl Good (fun w b => { (w.step b) with sb := {} })
    (fun _ b hw => { Good.step b hw with sbLe := by simp [Ring.size, sbCap] }) bytes v h

/-- Discarding history preserves every invariant required of a public VT
transformer; screen shape and parser state still come from the usual step. -/
theorem observe_invariants (v : Vt) (bytes : List UInt8) (hr : Renderable v) (hu : U8Ok v)
    (ht : TabsOk v) (hc : CsiOk v) :
    Renderable (v.observe bytes) ∧
      U8Ok (v.observe bytes) ∧ TabsOk (v.observe bytes) ∧ CsiOk (v.observe bytes) :=
  invariant_foldl (fun w => Renderable w ∧ U8Ok w ∧ TabsOk w ∧ CsiOk w)
    (fun w b => { (w.step b) with sb := {} })
    (fun _ b hw =>
      ⟨renderable_congr (renderable_step hw.1 b) rfl rfl rfl rfl, u8Ok_step b hw.2.1,
        tabsOk_step b hw.2.2.1, csiOk_step hw.2.2.2 b⟩)
    bytes v ⟨hr, hu, ht, hc⟩

theorem observe_dims (v : Vt) (bytes : List UInt8) (h : Good v) :
    (v.observe bytes).colCount = v.colCount ∧ (v.observe bytes).rowCount = v.rowCount := by
  have hi :=
    invariant_foldl (fun w => Good w ∧ dims w = dims v) (fun w b => { (w.step b) with sb := {} })
      (fun w b hw =>
        ⟨{ Good.step b hw.1 with sbLe := by simp [Ring.size, sbCap] },
          (dims_step b hw.1).trans hw.2⟩)
      bytes v ⟨h, rfl⟩
  exact Prod.mk.inj hi.2

end Linger.Core.Vt
