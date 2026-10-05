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
  `Linger/Core`" (checked by grep in e2e), this establishes pure totality
  and state bounds. It does not prove that runtime IO succeeds or memory
  allocation cannot fail.

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

/-- **A ruler as wide as the screen.** The invariant `Render.restore_tabs_any`
needs of the session it replays: `Render.tabsAnsi` walks `v.cols` columns and
reads `v.tabs`, so a ruler of any other length makes the walk and the array
disagree. `Good` and `Renderable` both say nothing about it — `Good` bounds the
dimensions and `Renderable` speaks of the grid — which is why it is a predicate
of its own rather than a clause of either. -/
def TabsOk (v : Vt) : Prop := v.tabs.size = v.cols

end Linger.Core.Vt
