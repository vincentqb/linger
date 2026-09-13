# vt-toolkit — seal `Vt`, then lift `Vt`+`Render`+`Terminal` as a standalone emulator

Status: **Step 1 done (2026-09-11). Steps 2-4 next.** `specs/scrollback-fidelity.md` is
complete on its critical path, so this is now the item in flight.

## Where this stands

**Step 1 is COMPLETE.** All 20 `Vt` fields are `private`; the seal bites, break-verified in the
real tree with a compiling control at the same position. Read the Step 1 record below before
Step 2 — it corrects this spec's own census, which was measuring forges and under-counted by
18 files.

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

**Next:** Step 2, the checkpoint smart constructor, and it is bigger than this spec assumed —
see the corrected numbers below.

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
2. **The checkpoint smart constructor** — `rVt` goes through it; a forged record with junk
   dimensions must decode to `none` rather than to a `Vt` that violates `Good`. This is a
   behaviour change at the boundary and wants a fixture. **Bigger than first assumed:**
   `wVt`'s 17 field *reads* need a home too, or the temporary friend import cannot come out.
   Two options, and the second is better — a per-field public accessor surface (which reopens
   read-hiding, though the constructor stays private so no-forge survives), or a
   `Vt.encode`/`decode` pair inside `Vt.lean` where the fields are visible, putting the wire
   format next to the representation it serialises. Also: `Daemon.lean`'s `clampDim` on the
   resume path becomes belt-and-braces once `rVt` clamps — its comment is the clearest statement
   of the bug this step fixes, so rewrite it rather than deleting the call silently.
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
