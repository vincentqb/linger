# vt-toolkit — seal `Vt`, then lift `Vt`+`Render`+`Terminal` as a standalone emulator

Status: **queued, not started** (2026-09-11). `specs/scrollback-fidelity.md` Step 4 is the
item in flight; this spec exists so its measured facts are not re-derived, and so the
ordering argument below is on the record before anyone starts.

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

**The seal's blast radius is 211 sites, and 210 of them are free.** Measured by
brace-matched scan over every tracked `.lean`:

| where | sites | class |
|---|---|---|
| `Theorems/**` (10 files) | 204 | already `module` files — one `import all Linger.Core.Vt` line each |
| `Tests/Render.lean`, `Tests/Terminal.lean` | 6 | legacy files; need the `module` + `public import` + `import all` conversion Step 5a rehearsed (Render also needs `public meta import` for its compiled-evaluation fixtures) |
| `Linger/Core/Checkpoint.lean:296-299` | **1** | **the only real-code forge** |
| `Linger/Runtime/**`, `Main.lean`, `E2E/**`, `Linger/Posix.lean` | **0** | they touch a `Vt` only through `Vt.init`/`resize`/`Terminal.feed` |

`Vt.mk` and `⟨…⟩` forges: zero hits anywhere. **The seal costs the shipping runtime
nothing**, which is the result that makes this cheap.

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

1. **Seal `structure Vt`** — `private` fields, `Vt.init` the door, `import all` in the ten
   `Theorems/` files and the two `Tests/` files. Break-verify from `Linger/Runtime/`: a read,
   a `{ v with … }` and a forge must each fail to compile (against the `linger` exe target —
   `lake build Linger` does **not** compile `Linger/Runtime/**`, the step-2 lesson).
2. **The checkpoint smart constructor** — `rVt` goes through it; a forged record with junk
   dimensions must decode to `none` rather than to a `Vt` that violates `Good`. This is a
   behaviour change at the boundary and wants a fixture.
3. **Harvest** — drop `Good`/`Renderable` hypotheses from the toolkit's public claims where
   reachability now discharges them, and state the exhaustiveness in prose next to the seal
   (it is a compile-time property, not a theorem — do not fake it as one).
4. **The extraction target and its gate** — `lean_lib LingerVt` + the closure grep above.

## Non-goals

- **A theorem asserting "no importer can forge a `Vt`".** That is what `private` means; a
  theorem shaped like it would be decoration. The honest artefacts are the compile-time seal
  and a recorded break-verify.
- **A sub-package split** to get a build-level closure failure, unless the no-`require` gate
  is deliberately amended.
- **Renaming or moving the three files.** The library boundary is the target; the paths are
  not part of it.
