module

public import Linger.Core.Checkpoint
public import Theorems.Vt
import all Linger.Core.Checkpoint
import all Linger.Core.Vt
-- `Theorems.Vt` for `Good`, and for the three claims about the decoder's door
-- (`ofDecoded_good`, `ofDecoded_of_good`, `ofDecoded_none_of_cols_zero`) — the codec's
-- theorems are stated in terms of it now that `rVt` validates rather than forges
-- (`specs/archive/vt-toolkit.md` Step 2). `import all` because those declarations are
-- module-private, as the `Vt` seal forces.
import all Theorems.Vt

-- Converted from a legacy (non-`module`) file by the `Vt` seal
-- (`specs/archive/vt-toolkit.md` Step 1). Legacy files make every declaration public, and
-- a public statement may not mention a private field — `load_save_exact` mentions
-- three (`pstate`, `u8need`, `u8acc`) and `cases vt` needs the constructor. As a
-- `module` with no `public section`, the declarations are module-private and both
-- are allowed. `Theorems/Resume.lean` reaches in with `import all`.

/-! # §Restore — the reboot-resume codec theorems

THEOREMS.md row: `load (save s) = some s` — exactly, for every state
whose parser is quiescent (which is what checkpoints hold, since the
codec deliberately forgets partial escape sequences); the general form
round-trips modulo `Vt.quiesce`. Totality of `load` on arbitrary bytes
is by construction (`R α = List UInt8 → Option _`, structural
recursion only) — the second half of §Restore needs no theorem.

Every combinator round-trip is unconditional: `wNat` is LEB128, so
there is no "fits in N bits" side condition anywhere in the format.

**The `Vt` round trip is not.** `rVt` hands its decoded fields to
`Vt.ofDecoded`, which returns `none` unless they describe a `Good` **and** `Renderable`
state with a ruler the width of the screen (`specs/archive/vt-toolkit.md` Step 2 for the first,
finding R2 for the other two), so `rt_vt` and everything above it carries those three
hypotheses — satisfied by every live session (`load_save_live`), and false of exactly the
records the validation exists to refuse. The two directions are `rVt_good`/`rVt_shape` and
`load_good`/`load_renderable`/`load_tabsOk` (nothing bad is ever decoded, for **any** byte
string) and `load_save_none_of_cols_zero` (the canonical junk record is refused rather than
clamped).
-/

namespace Linger.Core.Checkpoint

open Linger.Core.Vt

/-- "Reader `r` inverts writer `w`, leaving the rest untouched." -/
abbrev RT {α : Type} (w : α → List UInt8) (r : R α) : Prop :=
  ∀ (a : α) (rest : List UInt8), r (w a ++ rest) = some (a, rest)

theorem rt_u8 : RT wU8 rU8 := fun _ _ => rfl

theorem rt_nat : RT wNat rNat := by
  intro n rest
  induction n using wNat.induct with
  | case1 n h =>
    rw [wNat, dite_eq_left h]
    have hb : (UInt8.ofNat n) < 128 := by
      simp only [UInt8.lt_iff_toNat_lt, UInt8.toNat_ofNat', show (128 : UInt8).toNat = 128 from rfl]
      omega
    simp [rNat, hb, UInt8.toNat_ofNat']
    clear hb
    omega
  | case2 n h ih =>
    rw [wNat, dite_eq_right h]
    have hmod : n % 128 < 128 := Nat.mod_lt _ (by omega)
    have hb : ¬(UInt8.ofNat (128 + n % 128)) < 128 := by
      simp only [UInt8.lt_iff_toNat_lt, UInt8.toNat_ofNat', show (128 : UInt8).toNat = 128 from rfl]
      omega
    simp only [rNat, List.cons_append, hb, ite_false, ih]
    clear hb
    simp only [UInt8.toNat_ofNat']
    have h1 : (128 + n % 128) % 256 = 128 + n % 128 := by omega
    rw [h1]
    have h2 : 128 + n % 128 - 128 + 128 * (n / 128) = n := by omega
    rw [h2]

theorem rt_bool : RT wBool rBool := by
  intro b rest
  cases b <;> rfl

theorem rt_char : RT wChar rChar := by
  intro c rest
  unfold wChar rChar
  rw [rt_nat c.toNat rest]
  have hv : c.toNat.isValidChar := c.valid
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [dite_eq_left hv]
  exact congrArg (fun x => some (x, rest)) (Char.ext rfl)

theorem rt_pair {α β : Type} {wa : α → List UInt8} {ra : R α} {wb : β → List UInt8} {rb : R β}
    (ha : RT wa ra) (hb : RT wb rb) : RT (wPair wa wb) (rPair ra rb) := by
  intro p rest
  unfold wPair rPair
  simp only [List.append_assoc, ha, hb, Option.bind_eq_bind, Option.bind_some]

theorem rt_opt {α : Type} {w : α → List UInt8} {r : R α} (h : RT w r) : RT (wOpt w) (rOpt r) := by
  intro o rest
  cases o with
  | none => rfl
  | some a =>
    unfold wOpt rOpt
    simp only [List.cons_append, h, Option.bind_eq_bind, Option.bind_some]

theorem rt_listAux {α : Type} {w : α → List UInt8} {r : R α} (h : RT w r) :
    ∀ (l : List α) (rest : List UInt8),
      rListAux r l.length (l.flatMap w ++ rest) = some (l, rest) := by
  intro l
  induction l with
  | nil =>
    intro rest; rfl
  | cons x xs ih =>
    intro rest
    simp only [List.flatMap_cons, List.length_cons, rListAux, List.append_assoc, h, ih,
      Option.bind_eq_bind, Option.bind_some]

theorem rt_list {α : Type} {w : α → List UInt8} {r : R α} (h : RT w r) :
    RT (wList w) (rList r) := by
  intro l rest
  unfold wList rList
  simp only [List.append_assoc, rt_nat, Option.bind_eq_bind, Option.bind_some]
  exact rt_listAux h l rest

theorem rt_str : RT wStr rStr := by
  intro s rest
  unfold wStr rStr
  simp only [rt_list rt_char, Option.bind_eq_bind, Option.bind_some, String.ofList_toList]

theorem rt_color : RT wColor rColor := by
  intro c rest
  cases c <;> rfl

theorem rt_pen : RT wPen rPen := by
  intro p rest
  unfold wPen rPen
  simp only [List.append_assoc, rt_color, rt_bool, Option.bind_eq_bind, Option.bind_some]

theorem rt_cell : RT wCell rCell := by
  intro c rest
  unfold wCell rCell
  simp only [List.append_assoc, rt_char, rt_list rt_char, rt_nat, rt_pen, Option.bind_eq_bind,
    Option.bind_some]

/-- Expanding the run-length groups of a list recovers the list. -/
theorem expand_runs {α : Type} [DecidableEq α] (l : List α) : expand (runs l) = l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [runs]
    cases hrt : runs t with
    | nil =>
      rw [hrt] at ih
      simp only [expand] at ih
      -- ih : [] = t, so t is empty and the run is just [a]
      simp only [← ih, expand, List.replicate, List.append_nil]
    | cons hd tl =>
      obtain ⟨n, b⟩ := hd
      rw [hrt] at ih
      simp only [expand] at ih
      by_cases hab : a = b
      · subst hab
        simp only [reduceIte, expand, List.replicate_succ, List.cons_append, ih]
      · simp only [hab, reduceIte, expand, List.replicate, List.singleton_append, ih]

theorem rt_rle {α : Type} [DecidableEq α] {w : α → List UInt8} {r : R α} (h : RT w r) :
    RT (wRLE w) (rRLE r) := by
  intro l rest
  unfold wRLE rRLE
  simp only [rt_list (rt_pair rt_nat h), Option.bind_eq_bind, Option.bind_some, expand_runs]

theorem rt_row : RT wRow rRow := by
  intro r rest
  unfold wRow rRow
  simp only [rt_rle rt_cell, Option.bind_eq_bind, Option.bind_some]

theorem rt_cursor : RT wCursor rCursor := by
  intro c rest
  unfold wCursor rCursor
  simp only [List.append_assoc, rt_nat, rt_bool, Option.bind_eq_bind, Option.bind_some]

theorem rt_modes : RT wModes rModes := by
  intro m rest
  unfold wModes rModes
  simp only [List.append_assoc, rt_bool, rt_nat, Option.bind_eq_bind, Option.bind_some]

theorem rt_saved : RT wSaved rSaved := by
  intro s rest
  unfold wSaved rSaved
  simp only [List.append_assoc, rt_cursor, rt_pen, Option.bind_eq_bind, Option.bind_some]

theorem rt_ring : RT wRing rRing := by
  intro r rest
  unfold wRing rRing
  simp only [List.append_assoc, rt_nat, rt_list rt_row, Option.bind_eq_bind, Option.bind_some]

theorem rt_alt : RT wAlt rAlt := by
  unfold wAlt rAlt
  apply rt_opt
  intro x rest
  obtain ⟨g, c, p⟩ := x
  simp only [List.append_assoc, rt_list rt_row, rt_cursor, rt_pen, Option.bind_eq_bind,
    Option.bind_some]

/-- **The fields round-trip unconditionally; acceptance is exactly the smart
constructor's decision.** This is what `rt_vt` used to be, and splitting it out is what
makes the behaviour change legible: every combinator below is still an unconditional
inverse, so nothing about the *format* got weaker — what changed is that the seventeen
decoded values now go through `Vt.ofDecoded`, which is free to refuse them.

Both of the claims above it read off this one: `rt_vt` by `ofDecoded_of_good`, and
`load_save_none_of_cols_zero` by `ofDecoded_none_of_cols_zero`. -/
theorem rVt_fields (v : Vt) (rest : List UInt8) :
    rVt (wVt v ++ rest) =
      (Vt.ofDecoded v.cols v.rows v.grid v.cursor v.pen v.modes v.top v.bot v.tabs v.sb v.altGrid
            v.saved v.title v.g0Line v.g1Line v.shiftOut v.bell).map
        (fun w => (w, rest)) := by
  unfold wVt rVt
  simp only [List.append_assoc, rt_nat, rt_list rt_row, rt_cursor, rt_pen, rt_modes,
    rt_list rt_bool, rt_ring, rt_alt, rt_saved, rt_str, rt_bool, Option.bind_eq_bind,
    Option.bind_some, Array.toArray_toList, Option.map_eq_bind, Function.comp_def]

/-- The Vt round trip: exact modulo the deliberately-forgotten parser
state, for any state the emulator can actually be in.

`Good` is the hypothesis the smart constructor introduced, and it is not a weakening of
the format: `good_init` plus the `Pres` machinery says every live session satisfies it,
and a state that does not is precisely one a checkpoint must not restore. The old
unconditional statement was true of `cols := 0`, which is the bug.

**`hren` and `htabs` arrived with finding R2** (SCRATCHPAD.md), for the same reason and by
the same mirror: the door now also refuses a record whose grid is not the shape its
dimensions claim, so the round trip is conditional on the *input* being that shape. Same
answer to "is this a weakening" — the unconditional statement was true of a screen
`Render.restore` cannot repaint, which is what `resume_grid` was refuted at. Every live
session satisfies all three (`good_of_liveReachable`, `renderable_of_liveReachable`,
`tabsOk_of_liveReachable`), so `load_save_live` below is the honest reading of the cost. -/
theorem rt_vt (v : Vt) (h : Good v) (hren : Renderable v) (htabs : TabsOk v) (rest : List UInt8) :
    rVt (wVt v ++ rest) = some (v.quiesce, rest) := by
  rw [rVt_fields, ofDecoded_of_good h hren htabs, Option.map_some]

/-- **Nothing bad is ever decoded, from any bytes at all.** Not "from bytes `save`
wrote" — from an arbitrary `List UInt8`, which is what a checkpoint file is: the
attacker-controlled input the `Vt` seal could not reach. If `rVt` yields a `Vt`, that
`Vt` is `Good`.

This is the theorem the step is for, and it is the one that makes every
`Good`-hypothesised claim in `Theorems/Render/*` and `Theorems/Resume.lean` reachable
from the resume path rather than merely stated. -/
theorem rVt_good {l : List UInt8} {v : Vt} {rest : List UInt8} (h : rVt l = some (v, rest)) :
    Good v := by
  simp only [rVt, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  -- One flat `rcases` pattern rather than a `repeat'`: the seventeen readers nest to the
  -- right, so the pattern flattens, and `repeat'` cannot be used because the eighteenth
  -- attempt destructures a `Vt` and leaves a broken context behind when it fails.
  obtain
    ⟨_, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -,
      _, -, w, hw, he⟩ :=
    h
  simp only [Option.some.injEq, Prod.mk.injEq] at he
  exact he.1 ▸ ofDecoded_good hw

/-- **…and nothing the emitter cannot repaint, either — finding R2.** The other half of
"nothing bad is ever decoded", from an arbitrary `List UInt8`: if `rVt` yields a `Vt`, that
`Vt`'s grid has exactly `rows` rows of exactly `cols` cells, every cell holds an emittable
base of the width it claims, every wide glyph keeps its shadow, the stashed alt screen is
the same shape, and the tab ruler is the width of the screen.

`Good` implied none of that — `decodedOk` was never passed the grid — and the gap was
observable: a real checkpoint with its `rows` byte flipped decoded to a screen whose replay
is not the screen it came from. The bundled conjunction is deliberate: one destructuring of
the seventeen readers, projected by `load_renderable` and `load_tabsOk` below. -/
theorem rVt_shape {l : List UInt8} {v : Vt} {rest : List UInt8} (h : rVt l = some (v, rest)) :
    Renderable v ∧ TabsOk v := by
  simp only [rVt, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain
    ⟨_, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -,
      _, -, w, hw, he⟩ :=
    h
  simp only [Option.some.injEq, Prod.mk.injEq] at he
  exact ⟨he.1 ▸ ofDecoded_renderable hw, he.1 ▸ ofDecoded_tabsOk hw⟩

/-- **…and it is a state a live session can hold** — the third and strongest reading of
"nothing bad is ever decoded", from an arbitrary `List UInt8`. Not merely `Good` (Step 2),
not merely `Good ∧ Renderable ∧ TabsOk` (finding R2): a member of the *closure* the replay
theorems are stated over, so a decoded screen is admissible wherever a fed-and-resized one
is.

This is `LiveReachableVt`'s `ofDecoded` rung reached through the readers, and it is the
claim the rung exists for. Before it, `Theorems/Session.lean` could lift the shape
invariant to the daemon only for a session booted from `Vt.init`; `load_live` below carries
it to the resume path, where `Session.liveVt_boot_of_load` closes the gap in one step.

The rung is sound only because the *door* decides all four components — R2 is what made
this provable, and a rung premised on `Good v` instead was measured unsound (§LiveReachable
in `Theorems/Vt.lean`). -/
theorem rVt_live {l : List UInt8} {v : Vt} {rest : List UInt8} (h : rVt l = some (v, rest)) :
    LiveReachableVt v := by
  simp only [rVt, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain
    ⟨_, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -,
      _, -, w, hw, he⟩ :=
    h
  simp only [Option.some.injEq, Prod.mk.injEq] at he
  exact he.1 ▸ LiveReachableVt.ofDecoded hw

/-! ### The format tag, as a named stage

`stripMagic` is the tag check, named rather than inlined; `load_save` and `save_tag` both
go through it instead of unfolding the decision into the parser chain. -/

theorem stripMagic_magic (p : List UInt8) : stripMagic (magic ++ p) = some p := by
  unfold stripMagic
  rw [List.take_append_of_le_length (by simp [magic]), List.take_of_length_le (by simp [magic]),
    List.drop_append_of_le_length (by simp [magic]), List.drop_of_length_le (by simp [magic]),
    List.nil_append]
  rw [ite_eq_left (rfl : magic = magic)]

/-- **The top-level no-forge claim**, and the one the runtime is entitled to lean on: a
checkpoint that loads at all loads to a `Good` screen. `Linger/Runtime/Daemon.lean`'s
resume path cites this for why the `clampDim` it still calls before `spawnPty` cannot
change the value it is given. -/
theorem load_good {l : List UInt8} {c : Ckpt} (h : load l = some c) : Good c.vt := by
  simp only [load, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, -, ⟨vt, _⟩, hvt, _, -, _, -, h⟩ := h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    exact rVt_good hvt
  · exact absurd h (by simp)

/-- **The top-level shape claim, for any byte string — finding R2's payoff.** A checkpoint
that loads at all loads to a screen the emitter can reproduce and a ruler the width of that
screen. One destructuring of `load`, projected by the two claims below.

This is what makes the §Replay theorems reachable from the *resume path* rather than merely
stated over a hypothesis: `Theorems/Resume.lean`'s `resume_grid_of_load` /
`resume_tabs_of_load` / `resume_sb_of_load` need no hypothesis at all beyond
`load l = some c`, where their `save`-side twins must ask for `Renderable` because their
subject is `save`'s input. -/
theorem load_shape {l : List UInt8} {c : Ckpt} (h : load l = some c) :
    Renderable c.vt ∧ TabsOk c.vt := by
  simp only [load, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, -, ⟨vt, _⟩, hvt, _, -, _, -, h⟩ := h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    exact rVt_shape hvt
  · exact absurd h (by simp)

/-- **The twin of `load_good`**: every byte string `load` accepts decodes to a `Renderable`
screen. Named as its own claim because that is the property `Render.restore`'s theorems ask
for, and because before R2 it was false — refutably, from one flipped byte of a real
checkpoint. -/
theorem load_renderable {l : List UInt8} {c : Ckpt} (h : load l = some c) : Renderable c.vt :=
  (load_shape h).1

/-- …and the ruler, which `Renderable` does not carry (`Render.restore_tabs_any`'s
`hvtabs`, `Resume.resume_tabs`'s). Before R2 a checkpoint could name a ruler of any length
at all. -/
theorem load_tabsOk {l : List UInt8} {c : Ckpt} (h : load l = some c) : TabsOk c.vt :=
  (load_shape h).2

/-- **The top-level reachability claim: a checkpoint that loads loads to a state a live
session can hold.** Strictly stronger than `load_good`, `load_renderable` and `load_tabsOk`
together — those three are its projections (`good_of_liveReachable` and siblings), and it
additionally puts the decoded screen inside the closure every `Render.restore_*_reachable`
theorem quantifies over.

The one-line consequence worth naming: `Theorems/Session.lean`'s `LiveVt` is now provable
for a **resumed** daemon (`Session.liveVt_boot_of_load`), so `Session.run_vt_renderable` and
the shape claims beneath it stop being about fresh boots only. That is the whole reason the
`ofDecoded` rung was added; this theorem is the bridge.

`load_save_live` below still asks for `LiveReachableVt c.vt` rather than `load l = some c`
on purpose: its subject is `save`'s **input**, the state the daemon holds, which reaches
the decoder only through `load_save`'s own conclusion (the circularity SCRATCHPAD.md
measured). `load_live` is the tool for the other direction — `load`'s output. -/
theorem load_live {l : List UInt8} {c : Ckpt} (h : load l = some c) : LiveReachableVt c.vt := by
  simp only [load, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, -, ⟨vt, _⟩, hvt, _, -, _, -, h⟩ := h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    exact rVt_live hvt
  · exact absurd h (by simp)

/-- §Restore, top level: a checkpoint written by `save` loads back to
exactly what was saved (parser state quiesced — which the daemon's
checkpoints already are, being taken between poll rounds). Totality on
garbage is by construction, and `load_good`/`load_renderable` say what that totality now
delivers: garbage yields `none`, never a bad screen and never a screen the emitter cannot
repaint.

Three hypotheses, all of them the decoder's acceptance seen from this side (`rt_vt`):
`Good` since Step 2, `Renderable` and `TabsOk` since R2. `load_save_live` below is the same
claim with all three discharged from reachability, which is the answer to "what does this
cost a real session". -/
theorem load_save (c : Ckpt) (h : Good c.vt) (hren : Renderable c.vt) (htabs : TabsOk c.vt) :
    load (save c) = some { c with vt := c.vt.quiesce } := by
  unfold load save
  simp only [List.append_assoc]
  rw [stripMagic_magic]
  simp only [rt_vt _ h hren htabs, rt_str, Option.bind_eq_bind, Option.bind_some]
  have h := rt_list (rt_pair rt_str rt_str) c.labels []
  rw [List.append_nil] at h
  rw [h]
  rfl

/-- **What the three hypotheses cost a real session: nothing.** Every state a live session
can hold is `LiveReachableVt`, and that discharges `Good`, `Renderable` and `TabsOk` at
once. Stated because R2 added two binders to `load_save` and a reader is entitled to see,
in one place, that the checkpoint every daemon writes still loads — the alternative is
three lemma names in a docstring and a reader taking them on trust. -/
theorem load_save_live (c : Ckpt) (h : LiveReachableVt c.vt) :
    load (save c) = some { c with vt := c.vt.quiesce } :=
  load_save c (good_of_liveReachable h) (renderable_of_liveReachable h) (tabsOk_of_liveReachable h)

/-- **The tag `save` writes.** Pinned as its own claim because the tag is the one part
of a checkpoint another program reads before trusting the rest, and because a wrong
constant here is invisible to the round trip (`load_save` would still hold of a `save`
that wrote any tag `stripMagic` accepted).

The pre-rename `"LZMX"` reader was removed on 2026-08-19, one commit after it landed:
it existed to migrate files written before the rename, `save` had already been writing
`"LNGR"` for a commit, and there were no old-tag checkpoints left on disk to orphan.
Anyone who needs to read one can check out `e1ac562`, where the reader and its two
theorems (`load_legacy_save`, `save_no_legacy`) are green — that is the escape hatch,
and it is cheaper than carrying a branch for a file nobody has. -/
theorem save_tag (c : Ckpt) : (save c).take 5 = magic := by
  unfold save
  simp only [List.append_assoc]
  rw [List.take_append_of_le_length (by simp [magic]), List.take_of_length_le (by simp [magic])]

/-- And when the parser is already quiescent, the round-trip is exact
— the letter of the THEOREMS.md row. `hren`/`htabs` are `load_save`'s, hence
`ofDecoded_of_good`'s; see there for why they are not a weakening. -/
theorem load_save_exact (c : Ckpt) (hg : Good c.vt) (hren : Renderable c.vt) (htabs : TabsOk c.vt)
    (h : c.vt.pstate = .ground) (h8 : c.vt.u8need = 0) (ha : c.vt.u8acc = 0) :
    load (save c) = some c := by
  rw [load_save c hg hren htabs]
  congr 1
  cases c with
  | mk vt cwd labels =>
    simp only [Ckpt.mk.injEq, and_true]
    cases vt
    simp_all [Vt.quiesce]

/-- **Junk dimensions are refused, not clamped** — the behaviour change of
`specs/archive/vt-toolkit.md` Step 2, stated at the top level rather than only fixtured.
`cols = 0` is the canonical corrupt value: no live session can hold it, `Good` is false
of it, and a decoder that accepted it would hand `Render.restore` a screen every one of
its theorems is vacuous at.

The `Ckpt` here is a *forged* one — a `Vt` no `init`/`resize`/`feed` path produces, which
is reachable in this file only because the seal's friend import is. That is the point:
the record on disk is the one input an attacker controls, and `save` of such a state is
byte-for-byte what a hostile file looks like. -/
theorem load_save_none_of_cols_zero (c : Ckpt) (h : c.vt.cols = 0) : load (save c) = none := by
  unfold load save
  simp only [List.append_assoc]
  rw [stripMagic_magic]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [rVt_fields, h, ofDecoded_none_of_cols_zero]
  rfl

end Linger.Core.Checkpoint
