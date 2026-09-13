# vt-toolkit — seal `Vt`, then lift `Vt`+`Render`+`Terminal` as a standalone emulator

Status: **All four steps done. Step 3 landed 2026-09-13; nothing remains.** One of Step 3's
three decisions was **reversed on 2026-09-13** by the adversarial audit's finding R2 — the
decoder now establishes `Renderable` and the ruler's length as well as `Good`. See
"Amendment (2026-09-13)" below; the original decision is kept, marked, rather than rewritten.
Archive this with the completion record below.

## Where this stands

**Step 3 is COMPLETE (2026-09-13), and the harvest came out smaller than this spec assumed
in one direction and larger in another.** Three decisions, each measured:

* **`deriving Inhabited` is off `structure Vt`** — and off `Checkpoint.Ckpt` and
  `Session.State`, which only had it transitively. `(default : Vt)` was a **third public
  door**: `cols = 0, rows = 0, grid = #[]`, obtainable by any importer with no friend
  import and no forge, provably `¬Good` and `¬LiveReachableVt`, and the Step 1
  break-verify never thought to try it. Measured before choosing: exactly **one** site in
  the whole tree needed `Inhabited Vt` and it needed an arbitrary *carrier*, not a
  default — `Theorems/Render/Modes.lean`'s `smMod` (plus the `show` in `Grid.lean`'s
  `smMod_dom6`), now `Vt.init 1 1`. Removing the door beat re-pointing it at
  `⟨Vt.init 80 24⟩`, on the axis Step 2 used: **fewer public doors**, not safer ones.
* **No `ofDecoded` rung on `LiveReachableVt`.** A rung with premise `Good v` does not
  merely make the harvest buy less — it makes the relation **unsound**:
  `renderable_of_liveReachable` and `u8Ok_of_liveReachable` both stop closing, because
  `Good` implies neither. Measured by adding it. A *sound* rung needs the decoder to
  establish `Renderable`, i.e. decision 3, after which the relation is pinned between
  `Good ∧ Renderable ∧ ground` and `Good ∧ Renderable ∧ U8Ok` and buys nothing an
  induction principle is wanted for. The harvest is scoped to reachable states and the
  scope is written next to the seal.
* **`Renderable` is not established at the decoder's door, and it stays that way.**
  `Vt.decodedOk` and `ofDecoded_of_good` are one predicate seen from both sides — the
  door's acceptance and its non-rejection — so **every clause added to the check becomes a
  hypothesis on `rt_vt` → `load_save` → `load_save_exact`, hence on five `resume_*` claims
  that never read the grid**. That is the "hypothesis a proof does not use" anti-pattern
  this repo names in `restore_sticky_any`, and A1's anchor has already moved once for
  Step 2. The gain would be a *new* family (`resume_*_of_load`), not a discharged
  hypothesis on the existing one: `Theorems/Resume.lean`'s subject is `save`'s **input**,
  so `hren` cannot be recovered from `load (save c) = some c` when that equation is itself
  gated on it. Declined; both halves. The shape half alone does not escape the mirror.
  **REVERSED on 2026-09-13 — see the amendment below.**

## Amendment (2026-09-13): decision 3 reversed, both halves landed

The adversarial audit run in parallel with Step 3 (SCRATCHPAD.md, finding **R2**) showed
that decision 3 above weighed one side of the trade. Every sentence of it about *theorem
hypotheses* is correct, and beside the point: `Vt.decodedOk` was never passed the grid, so a
checkpoint with **one flipped byte** — the `rows` byte of a real 4×2 record, 2 → 3 — decoded
to a `Good ∧ ¬Renderable` screen, and

```
((Vt.init badVt.colCount badVt.rowCount).feed (Render.restore badVt)).grid == badVt.grid → false
```

which is `resume_grid`'s conclusion, refuted for a state that came off disk. An observable
defect outranks a hypothesis count.

Both halves landed. The shape half and the per-cell half are the **same** hypothesis, which
is the fact decision 3 missed: `Renderable`'s `GridOk` → `RowOk` carries `CellOk`/`PairOk`,
so checking cells costs nothing over checking sizes, and the predicate it mirrors onto the
five claims is `Renderable` — exactly what `resume_grid`/`resume_sb` already asked for. A
shape-only door would have needed a *new*, weaker predicate to state the same mirror.

What it cost, measured and counted rather than estimated: `Renderable` and `TabsOk` on
`ofDecoded_of_good` → `rt_vt` → `load_save` → `load_save_exact`, and from there on **eight**
`resume_*` claims rather than the five this decision predicted — `resume_grid`/`resume_sb`
gain `htabs` for the round-trip conjunct even though `hren` was already theirs, and
`resume_tabs` gains `hren` for the same reason. **Twelve claims, 21 new binders**: the four
in the chain at two each, and thirteen between the eight `resume_*`. Every one is named in
its own docstring and in THEOREMS.md's A1 / §Restore / §Resume rows. For a live session all
of them are discharged by `renderable_of_liveReachable` and `tabsOk_of_liveReachable`;
`Checkpoint.load_save_live` is that composition written out, so a reader sees in one place
that the checkpoint every daemon writes still loads.

What it bought: `load_renderable`/`load_tabsOk` (the twins of `load_good`, over arbitrary
bytes) and the new family this decision correctly predicted — `resume_grid_of_load`,
`resume_tabs_of_load`, `resume_sb_of_load`, hypothesis-free over an arbitrary byte string.
The circularity argument above was re-checked rather than assumed and it holds: the existing
family's `hren` cannot be discharged, because the only bridge is `load_save_exact`, which is
the very call that acquires the hypothesis.

Also settled: the ring's rows are **not** validated, and that is forced rather than chosen —
`Vt.resize` leaves them at their old width (this file's own measurement, one section down),
so demanding `RowOk cols` of them would refuse a checkpoint a live session can produce.
`Render.restore_sb_exact`'s `hrok` therefore stays unreachable from disk. `Tests/Checkpoint.lean`
carries that as a passing fixture, so the gap is visible rather than implied.

**And one thing R2 unlocks that was NOT done here**, named so it is a decision rather than an
oversight: the `ofDecoded` rung on `LiveReachableVt` that Step 3 measured as *unsound* is now
sound. Its four components were checked in a scratch file — `Good` (`load_good`),
`Renderable` (`load_renderable`), `TabsOk` (`load_tabsOk`) and `U8Ok`, the last because the
door fixes `u8need := 0` and `u8acc := 0`, so `U8Ok` is `rfl`. What it would buy is no longer
nothing: `Theorems/Session.lean`'s `LiveVt`/`run_vt_renderable` lifts the shape invariant to
the daemon only for sessions booted from `Vt.init`, so a **resumed** session's `Renderable`
travels through `renderable_feed`/`renderable_resize` individually rather than through one
daemon-level theorem. Adding the rung changes what four `*_of_liveReachable` lemmas mean and
touches the Session claims, so it is its own step, not a rider on this one.

**What the harvest actually was.** The `Good`/`Renderable` binders left in the toolkit's
public claims are load-bearing — verified by enumerating all 43 of them, not asserted; the
`*_reachable` family and commit `dbfd219` had already taken the derivable ones. What was
still open was named in the source: `Theorems/Render/Tabs.lean`'s `restore_tabs_reachable`
asked for `v.tabs.size = v.cols` and said "proving [it] an invariant of every reachable
state is a `tabs_*` frame family of its own — worth doing, not needed here". It is done:
`Theorems/Vt.lean` §Ruler, the **fifth** instance of the `dims`/`org` invariance-layer
recipe, and it needs **no `Good`** where `dims` does, because `RIS` re-clamps ruler and
width through the same `Vt.init`. `Vt.tabsOk_of_liveReachable` is the payoff and
`Render.restore_tabs_live` — the twin of `restore_grid_reachable`, every invariant
discharged — is the claim. `restore_tabs_reachable` **stays**, with a witness proving it is
not redundant: a 1×1 record the decoder accepts, whose ruler is right and whose grid is
empty, so it satisfies the old hypothesis and refutes reachability.

**And one hypothesis that reachability provably cannot discharge**, which is a finding
rather than a gap: `Render.restore_sb_exact`'s `hrok : ∀ r ∈ v.sb.toList, RowOk v.cols r`.
`Vt.resize` reinstalls the grid *and* the ruler at the new width and leaves the scrollback
rows at their old one — measured, `((Vt.init 80 3).feed 20×LF).resize 40 3` has `cols = 40`
and eighteen 80-wide ring rows. So no amount of proof work moves that binder.

**Step 4 is COMPLETE** — `lean_lib LingerVt` in `lakefile.lean` plus an **exact-set** import
grep in `tests/gates.sh`. Two files; no Lean source changed, because the closure was already
right and this only makes it *checked*. The Lake negative result was re-measured three ways and
holds: a `lean_lib` with restricted `roots` compiles an out-of-set import without a murmur even
under `warningAsError`, so the target is the positive half and the **grep is the whole of the
closure claim**. Break-verified with a control that is the point — both broken trees *build*, so
unlike the Step 1 seal (where the compiler refuses and a gate would be decoration) here the
compiler consents and the gate is the only oracle. A `git mv` of a toolkit file also fails it.
The optional job-count ratchet was **declined**: jobs = closure cardinality, which is blind to
identity, so a cap raised for a legitimate fourth module would thereafter license any one
out-of-set leaf import silently.

**Step 1 is COMPLETE.** All 20 `Vt` fields are `private`; the seal bites, break-verified in the
real tree with a compiling control at the same position. Read the Step 1 record below before
anything else — it corrects this spec's own census, which was measuring forges and under-counted
by 18 files.

**Step 2 is COMPLETE**, and the design came out the *other* way from the plan: the forge is
gone, and the friend import **stayed** — permanently, with its reason written at the import.
`rVt` decodes through `Vt.ofDecoded`, a **`private`** validating constructor in `Vt.lean` that
returns `none` unless the decoded fields describe a `Good` state. Dropping the friend import
would have forced that constructor to be *public*, i.e. a second public door admitting any
`Good` state — unreachable ones included — for every module forever, which is a **wider**
no-forge hole than one grep-gated file. Two greps hold it: the decoder calls `ofDecoded`, and no
`Vt` field is assigned anywhere in `Checkpoint.lean`.

**Step 2 is COMPLETE, and it went the other way from this spec's recommendation.** The forge is
gone — `rVt` decodes through `Vt.ofDecoded`, which **validates and returns `none`** rather than
clamping — but the friend import in `Checkpoint.lean` **stayed, permanently**, and that is the
better trade, measured:

* The two options this spec offered were "15 public accessors" and "`Vt.encode`/`decode` inside
  `Vt.lean`". The third is what landed: a **`private`** smart constructor, reached through the
  friend import. `import all` grants access to a private *def*, not only a private field — tested
  in the real tree, not assumed.
* `Vt.encode`/`decode` inside `Vt.lean` **does not typecheck** and it is not a near miss: the
  `R`/`w*` combinators live in `Checkpoint.lean`, so `Vt.lean` importing it is `error: build
  cycle detected` (`Linger.Core.Vt:importInfo` → `Linger.Core.Checkpoint:leanArts` → back).
  Avoiding the cycle means moving the whole codec into `Vt.lean`, which puts the on-disk format
  inside the toolkit closure Step 4 exists to bound. Dead, with evidence.
* Dropping the import would force `ofDecoded` to be **public** — a second public door admitting
  any `Good` state, unreachable ones included, for every module forever. That is a *wider*
  no-forge hole than one grep-gated file, so the accessor option loses on its own axis. Surface:
  option (a) 16 new public defs + 16 new claims + read-hiding gone on 15 of 20 fields; what
  landed, 2 private defs + 4 claims + 0 public surface.
* The forge cannot come back: `tests/gates.sh` asserts positively that the decoder calls
  `Vt.ofDecoded` and negatively that no `Vt` field is assigned anywhere in `Checkpoint.lean`.
  SHIM_CAP's species of oracle, break-verified.
* **Validate, not clamp**, and the reason is the grid: clamping `cols` into `[1,1000]` satisfies
  `Good` while leaving the decoded rows at their own width, so the screen would be `Good` and
  **not** `Renderable` — and `Renderable` is what every `Render.restore` theorem needs.
  Establishing it by clamping means `Vt.resize`, which the resume path refuses.
* **The cost, and it is real:** `rt_vt`, `load_save` and `load_save_exact` now carry a `Good`
  hypothesis, so `resume_quiesced`/`resume_quiesced_any`/`resume_exact` are no longer
  hypothesis-free. That is not a weakening — the old unconditional statement was *also* true of
  `cols = 0`, which is the bug — but THEOREMS.md's A1 anchor said "no hypotheses" and now says
  "any state a live session can be in".

**Two mechanism facts that cost the work, and are not re-derivable from the docs:**

1. Per-field `private` makes the **constructor** private as a side effect, so `{ v with … }`,
   `Vt.mk` and `⟨…⟩` all refuse even for fields that stayed public. Sealing *one* field would
   therefore buy the entire no-forge property; sealing all twenty additionally buys
   read-hiding, which is what the other 25 files paid for.
2. `import all` grants **access**, not permission to re-export: a **public** declaration's
   *type* may still not mention a private field. `Theorems/Vt.lean` already had the friend
   import and still failed 101 times. The fix is the *absence* of a line — dropping
   `public section` makes declarations module-private, which may name private fields, and a
   downstream `import all` still reaches them. The two error texts distinguish the two
   failures: `Unknown constant _private.…` means add `import all`; `Field `cols` … is private`
   means make the declaration module-private.

**Next:** nothing. Step 3 landed on 2026-09-13 and this spec is closed; its record is at the
top of this file.

## Goal

Make the emulator and its emitter usable, and provable, on their own: `Linger/Core/Vt.lean`
+ `Render.lean` + `Terminal.lean` as a library whose representation is sealed and whose
import closure contains nothing else. The product keeps working unchanged — this is a
boundary, not a behaviour.

## The ordering, which is the whole reason this is a spec and not a patch

**Seal first, harvest second.** The theorems worth having (`Reachable v → Good v`, and a
public API whose `Good`/`Renderable` hypotheses are *discharged* rather than assumed) are
provable today, and would be **decoration** today: with a public constructor an importer can
forge a `Vt` with `cols := 0`, so a predicate describing "reachable" states describes a
subset and proves nothing about what a client can hold. This is exactly what
`specs/archive/lean-modules.md` records for `Buf` — its `ReachableIn`/`ReachableOut` bounds
were deliberately **not written** until Step 2 sealed the representation, because pre-seal
they would have been true of a predicate that described nothing. Same trap, one layer up.

So: the seal is the load-bearing move, and the harvest is what pays for it.

## Measured facts — do not re-derive these

**The reachability harvest already exists.** `Theorems/Vt.lean:4438` has
`LiveReachableVt` with `init`/`feed`/`resize`/`quiesce`, plus `good_of_liveReachable`,
`renderable_of_liveReachable` and `u8Ok_of_liveReachable`. A new `Reachable` inductive would
be a strict sub-relation and a rename — **do not add one**; use `LiveReachableVt`.

**The seal's blast radius was measured wrong, and the corrected numbers are these.** The
original scan was brace-matched, so it counted **forges**; the seal blocks **reads** too, and
reads are the bulk. Measured by doing it:

| where | files | what was needed |
|---|---|---|
| `Theorems/**` | **19** of 24 | drop `public section` (12 already had `import all` and it was *not sufficient*); `Session`/`Resume`/`Listing` also needed `import all Theorems.*` for the rungs they compose |
| `Tests/**` | **6** | 5 legacy→`module`, each also needing `public meta import` for compiled evaluation |
| `Linger/Core/` | **5** | `Vt` (the seal + a read-only window), `Render`/`Terminal` (friends — the toolkit's own other modules, **omitted entirely by the original census**), `Session` (5 sites → accessors), `Checkpoint` (a temporary friend import) |
| `Linger/Runtime/` | **1** | `Daemon.lean` reads `vt0.cols`/`rows` to clamp a checkpoint-loaded size before `spawnPty` — the original census said zero, and **this is the corrupt-checkpoint path Step 2 is about**, so missing it mattered |
| `Main.lean`, `E2E/**`, `Posix.lean` | 0 | genuinely zero, as claimed |

`Vt.mk` and bare `⟨…⟩` forges: **zero hits anywhere** — the one original claim that survived
intact.

**`Linger/Core/Checkpoint.lean` is not 1 site but 18**: `rVt`'s one forge plus **`wVt`'s 17
reads**, which the census did not count and which Step 2 must also relocate.

**The import DAG still supports the split** (Steps 3 and 4 unaffected in substance): `Vt`
imports nothing, `Render` only `Vt`, `Terminal` only `Render`; the two friend imports added are
same-closure. `LiveReachableVt` is untouched.

**The one genuine obstacle is the checkpoint decoder**, and it is the site the seal most
wants to bite: `rVt` builds a `Vt` field-by-field out of decoded bytes, so a corrupt
on-disk record is precisely how `cols := 0` reaches the emulator. It already returns
`Option (Vt × …)`, so the fix is an honest smart constructor in `Vt.lean` (validate or
clamp, `none` on junk) — **not** an `import all` friend escape, which would keep the forge
and lose the point. Scope the seal to `structure Vt` only: a deep seal over `Ring`/`Cursor`/
`Pen`/`Modes`/`Saved`/`Cell` costs six more anonymous constructors in that same function.

**Lake cannot make "the toolkit does not import Posix" a build failure inside one package,
and this was tested rather than assumed.** Lake resolves imports through one package-wide
`LEAN_PATH`, so a `lean_lib` with restricted `roots` still compiles an out-of-set module
happily; a scratch two-lib package confirmed it. The failure only appears across a *package*
boundary, which would mean a sub-package with its own `srcDir` and a path `require` — and
that trips `gates.sh`'s existing no-`require` gate, which exists to keep README's
"no external Lean dependencies" honest. So the closure guarantee lands as:

* a `lean_lib LingerVt` with `roots := #[Linger.Core.Vt, Linger.Core.Render, Linger.Core.Terminal]`
  — the **positive** check: it elaborates the toolkit closure and nothing else;
* a **source grep** in `tests/gates.sh` asserting those three files import only each other
  (same species of oracle as `SHIM_CAP`: evadeable by deliberately editing the list, not by
  reverting a fix);
* optionally a job-count ratchet in `tests/e2e.sh` (job counts are stable across
  incremental runs — measured: `Linger.Core.Terminal` is 4 jobs, `Vt` 2, `Session` 7).

**The import DAG already supports the split.** `Vt.lean` imports **nothing**;
`Render.lean` imports only `Vt`; `Terminal.lean` only `Render`. Neither reaches `Posix` or
`Runtime` today.

## Steps

1. **Seal `structure Vt`** — DONE (2026-09-11). All 20 fields `private`, `Vt.init` the door,
   plus a **read-only window** (`Vt.colCount`/`rowCount`/`cursorPos`/`inAlt`, claimed by four
   `@[simp]` equations in `Theorems/Vt.lean`) because the seal blocks reads as well as writes
   and `Linger/Core/Session.lean` is a *client* of the emulator rather than part of it — a
   friend import there would have handed the daemon the power to forge a `Vt`, which is the one
   thing the seal exists to stop. `@[expose]` had to come off `Vt.applySgr`: an exposed body may
   not mention a private constructor. Break-verified from `Linger/Runtime/` against the `linger`
   exe target, with a control at the same position.
2. **The checkpoint smart constructor** — DONE (2026-09-13). `rVt` decodes through
   `Vt.ofDecoded`, a **`private`** validating constructor in `Vt.lean` (with the guard as a
   named stage, `Vt.decodedOk`); a record that does not describe a `Good` state decodes to
   `none`. Claimed by `Vt.decodedOk_iff` / `ofDecoded_good` / `ofDecoded_of_good` /
   `ofDecoded_none_of_cols_zero` and, on the real path, `Checkpoint.rVt_good` / `load_good`
   (any byte string) and `load_save_none_of_cols_zero` (the canonical junk record). Six
   fixtures in `Tests/Checkpoint.lean`, two of them a real checkpoint with **one byte
   flipped**. The friend import stayed and is now permanent — see the record above for why
   that beats 15 public accessors, and `tests/gates.sh` for the two greps that stop the forge
   growing back. `Daemon.lean`'s `clampDim` stayed too, with a comment that now cites
   `load_good` for why it cannot change the value it is given.
3. **Harvest** — DONE (2026-09-13). The exhaustiveness is prose, in the `structure Vt`
   docstring, under "Every door, and why the list is prose and not a theorem": three doors
   (`Vt.init`, the private validating `Vt.ofDecoded`, and the transformers), the four
   invariants each establishes or preserves, and why `∀ v : Vt, Good v` is not provable and
   would not mean what it looks like — this module's friends can `cases v`, so the
   proposition is false *inside* the seal and the seal is not a statement about
   propositions. `deriving Inhabited` went with it (it was the third door). The
   `Good`/`Renderable` binders that remain are load-bearing; the ruler hypothesis this spec
   did not anticipate is the one that fell, via `Theorems/Vt.lean` §Ruler +
   `tabsOk_of_liveReachable` + `Render.restore_tabs_live`. The `ofDecoded` rung was measured
   to be **unsound**, not merely weak, and `Renderable`-at-the-door was declined with the
   mirror argument — **and un-declined on 2026-09-13, finding R2; see the amendment at the
   top of this file.** With the door now establishing `Renderable`, the sound `ofDecoded`
   rung this decision described is available and still not worth adding, for the reason
   given there (the relation would become a conjunction nobody needs an induction principle
   for). See the completion record above and SCRATCHPAD.md.
4. **The extraction target and its gate** — `lean_lib LingerVt` + the closure grep above.

## Non-goals

- **A theorem asserting "no importer can forge a `Vt`".** That is what `private` means; a
  theorem shaped like it would be decoration. The honest artefacts are the compile-time seal
  and a recorded break-verify.
- **A sub-package split** to get a build-level closure failure, unless the no-`require` gate
  is deliberately amended.
- **Renaming or moving the three files.** The library boundary is the target; the paths are
  not part of it.
