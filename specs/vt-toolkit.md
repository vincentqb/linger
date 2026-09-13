# vt-toolkit — seal `Vt`, then lift `Vt`+`Render`+`Terminal` as a standalone emulator

Status: **Steps 1, 2 and 4 done (2026-09-11). Step 3 is the only one left.**
`specs/scrollback-fidelity.md` is complete on its critical path, so this is the item in flight.

## Where this stands

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

**Next:** Step 3, the harvest — and read the Step 2 record in SCRATCHPAD.md first, because
`ofDecoded` adds a second constructor that `LiveReachableVt` does not model.

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
3. **Harvest** — drop `Good`/`Renderable` hypotheses from the toolkit's public claims where
   reachability now discharges them, and state the exhaustiveness in prose next to the seal
   (it is a compile-time property, not a theorem — do not fake it as one).
   **Step 2 changed this step's input:** `LiveReachableVt` has `init`/`feed`/`resize`/`quiesce`
   and no `ofDecoded` rung, so it no longer characterises every `Vt` a client can hold. Either
   add the rung (its premise is `Good`, which is *weaker* than reachable, so the relation
   collapses toward `Good` and the harvest buys less than the spec assumed) or scope the
   harvest to states reached through `init` and say so. Decide that before writing lemmas.
4. **The extraction target and its gate** — `lean_lib LingerVt` + the closure grep above.

## Non-goals

- **A theorem asserting "no importer can forge a `Vt`".** That is what `private` means; a
  theorem shaped like it would be decoration. The honest artefacts are the compile-time seal
  and a recorded break-verify.
- **A sub-package split** to get a build-level closure failure, unless the no-`require` gate
  is deliberately amended.
- **Renaming or moving the three files.** The library boundary is the target; the paths are
  not part of it.
