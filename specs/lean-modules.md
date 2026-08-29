# lean-modules — adopt the module system; seal Buf as the first compiler-enforced gate

Status: active
Updated: 2026-08-19

## Where this stands — read this first

**Next step: Steps 3–4 are optional — judge against the one-item-in-flight
rule before starting either; `scrollback-fidelity` Step 2 has been queued
longer.** Steps 0–2 landed 2026-08-19: the migration cost was two
`@[expose]`s (type-level defs, and `let rec` auxiliaries that proofs name —
see SCRATCHPAD "lean-modules step 1"), and `Buf` is sealed with its proofs in
the first friend module (SCRATCHPAD "step 2" carries the false-green
break-verify lesson: `lake build Linger` does not compile `Linger/Runtime/**`;
verify runtime breaks against the `linger` exe target). Step 0's probe facts
are in SCRATCHPAD 2026-08-19 ("Lean module system on v4.32.0") and are NOT to
be re-derived. The two that shape everything: interop is
legacy-imports-module only (so migration walks the import DAG bottom-up), and
`import all` lets proofs stay in `Theorems/` while internals go private — the
exact pair of blockers that killed the 2026-08-18 per-field-`private`
experiment (runtime-invariants Open decision 1, measured "no" then; the module
system flips it to yes).

- Step 0 ✓ probe (SCRATCHPAD 2026-08-19)
- Step 1 ✓ whole `Linger` lib + exe roots are `module` files (blanket
  `public section`); two `@[expose]`s were the entire friction (the
  type-level `Checkpoint.R`, and `Vt.applySgr` whose `let rec` auxiliary the
  Pen proofs induct on); gate regexes hardened, every count bit-identical
- Step 2 ✓ `Buf` sealed: `private bytes`, `Buf.empty` the one door in,
  `writeFrom` the one window out, `Theorems/Buf.lean` the first friend module
  (`import all`, theorems deliberately module-private — public `:= rfl`
  proofs elaborate against the body-hidden view and fail). Open decision 1
  of runtime-invariants flipped; all three representation attacks refuse
  from inside the daemon (break-verified against the `linger` exe target —
  `lake build Linger` does NOT compile `Linger/Runtime/**`; see SCRATCHPAD)
- Step 3 (optional) → sealed `SessionName` (sanitize-at-construction)
- Step 4 (optional) → `@[expose]`/`public` tightening beyond the blanket
- Step 5 (in flight) → seal `Session.State`: `boot` + `step` as the only
  doors, `run_wf`'s WF hypothesis made structural; boot caps restored labels
  (the Bounded-at-boot gap). Carries the 15-file mechanical migration of the
  theorem tree Session's friend conversion forces.

## Harvest — 2026-08-19 (after Step 2)

The seal's theorem dividend, applied by the decoration test (a claim whose
canonical break nothing catches is not written): `ReachableIn`/`ReachableOut`
in Core + `reachableIn_bound`/`reachableOut_bound` in the friend module — §Bound
over each queue's whole life, exhaustive over what an importer can possess
*because* the constructor is private. Break 1 re-admits a one-line `forge`
constructor (the pre-seal world) and the bound becomes unprovable; break 2
drops the enqueue guard and the bound is refuted. Docs made literal in the
same pass (`Posix.writeBuf`, the two Daemon queue fields, THEOREMS §Bound).
Weighed and declined: lifetime FIFO content equation, name-pair collapses —
reasons in SCRATCHPAD.

## Goal

Move the tree onto the module system in a semantics-preserving way, then spend
the new visibility machinery on the one place a measured decision is already
waiting for it: `Buf`'s representation. The point is compound engineering —
turning conventions and grep gates into compiler-enforced structure where the
compiler can now hold them — not novelty. The greps this repo runs are the
right oracle for source-tree properties; where a property becomes a *type*
property, the compiler is the stronger oracle, and the grep stays as
belt-and-braces for the half the type system cannot see.

## Decisions (made, with reasons)

1. **Blanket `public section`, not per-decl `public`.** Two inserted lines per
   file plus `import` → `public import` preserves today's visibility exactly,
   keeps decl text as `def …` (so `coverage.py`'s scans keep matching), and
   makes Step 1 mechanical. Tightening is separate, later, per-boundary work
   (Steps 2/4) — the same split as agent-cli's "mechanical step, then
   semantics".
2. **`Theorems/` and `Tests/` stay legacy files.** Measured: a legacy importer
   of a module file keeps body visibility (`unfold`/`decide`/`native_decide`
   work) while privacy still binds it. A proof library's entire job is seeing
   internals, and nothing imports it — module-izing it is `import all`
   boilerplate for zero boundary. Only files that must *state* facts about
   sealed internals convert, one at a time, as things get sealed
   (`Theorems/Buf.lean` in Step 2).
3. **Gates get hardened, never traded.** Sealing `Buf` does NOT retire the
   three runtime byte-queue greps: privacy seals `Buf`'s representation, but
   only the greps ban the runtime declaring a *parallel* `ByteArray` queue of
   its own. Different halves of the same discipline; both stay.
4. **The ratchet counts must come through Step 1 bit-identical.** Any regex
   hardening lands in the same commit as the migration, and the exit criterion
   is the before/after equality of every gate's measured number (coverage
   19-cap counts, SHIM_CAP 27, HEARTBEAT_CAP 1, RUNTIME_PARTIAL_CAP 2).

## Definition of done

1. Every file under `Linger/`, plus `Linger.lean`, `Main.lean`,
   `LingerTest.lean`, is a `module` file with `public import`s and a blanket
   `public section`; `./lake build` / `Theorems` / `Tests` / `tests/e2e.sh`
   green and warning-free.
2. `coverage.py` regexes also match `public def` / `@[expose] public def` and
   `public theorem`; all measured counts identical before/after Step 1.
3. Step 2: `Buf.bytes` and `Buf.off` are `private`; `Linger/Posix.lean`'s
   `writeBuf` (the one representation reader outside Core) moves behind the
   boundary or gets an `import all`; `Theorems/Buf.lean` converts to a module
   with `public import` + `import all`; every theorem and fixture still
   green; the three greps unchanged. Attack fixtures: a read, a write
   (`{ b with … }`), and a forge of `Buf` from `Linger/Runtime/` each fail to
   compile (break-verified, recorded).
4. `specs/archive/runtime-invariants.md` is a closed record and stays
   unedited; the flip of its Open decision 1 is recorded here and in
   SCRATCHPAD, with a pointer from THEOREMS.md's §Bound prose if it mentions
   the grep-only status.
5. SCRATCHPAD records the migration's surprises (lint strictness hits, any
   proof that had to change) and the break records.

## Steps

### Step 1 — the mechanical migration

Bottom-up over the import DAG: `Buf Wire Vt Name Status` → `Render Remote
Checkpoint Terminal` → `Listing Session` → `Posix` → `Paths` → `Daemon
Client` → `Cli` → `Resume` → roots (`Linger.lean`, `Main.lean`,
`LingerTest.lean`). Each file: `module` first line, imports become
`public import`, one `public section` after the imports (unclosed to EOF —
measured legal). Fix what the stricter lints surface; nothing else changes.

**Exit:** all three builds + e2e green; `python3 tests/coverage.py` prints the
same two counts as on the previous commit; the e2e ratchet numbers unchanged;
`git diff --stat` shows only header-line insertions and import keyword changes
outside the lint fixes.

### Step 2 — seal Buf

`private` on both fields. `mkBuf`-style constructors already exist
(`Buf := {}` default — check: an importer writing `{}` needs the constructor;
if `Daemon`/`Cli` build fresh `Buf`s via `{}`, add a tiny public `Buf.empty`
so the representation stays sealed). `Posix.writeBuf` reads `b.bytes`/`b.off`
by design ("the only place outside Core that reads a Buf's representation" —
its docstring); it keeps that role via `import all Linger.Core.Buf`, which
makes the friend relationship explicit and unique. `Theorems/Buf.lean`
converts (Decision 2). Break-verify with the three attacks from Runtime.

**Exit:** builds + e2e green; the attacks refuse to compile; greps still pass
and still find their historical hits on the pre-Buf commit (`9ea62b0` — the
gate must keep measuring the past correctly); SCRATCHPAD + this spec record
the open-decision flip.

### Step 3 (optional) — sealed SessionName

`Name.sanitize` becomes the only constructor of an opaque `SessionName`;
`Paths.socketPath`/`ckptPath`/`logPath` take it instead of `String`, making
AGENTS.md's "never interpolate raw names into paths" a type error instead of a
convention. Bigger surface (CLI argv handling, remote rows, tests); judge
against the one-item-in-flight rule when its turn comes. Kill if the
`name@host` split or the listing's socket-filename identity (§Row) forces
`SessionName` to grow String-like public accessors everywhere — a sealed type
that leaks everywhere is worse than the convention.

### Step 4 (optional) — tighten beyond the blanket

Replace blanket `public section` with per-decl `public` on the files whose
boundaries carry weight (Core API vs helpers), add `@[expose]` only where a
downstream module needs kernel reduction. Do it file-by-file with the
coverage counts watched; it is the compile-perf bet (hidden bodies mean
downstream re-elaboration can be skipped) and should be MEASURED (time a
touch-rebuild of a hot proof file before/after) rather than assumed.

### Step 5 — seal `Session.State`: boot + step become the only doors

The `Buf` story one layer up, and the A2 anchor upgraded: with the constructor
private, every `State` the daemon can possess is `State.boot …` moved forward
by `step` — so `run_wf`'s WF hypothesis stops being "holds if the runtime is
polite" and becomes structural. Field split: `vt`/`labels`/`metaKv` stay
public (the checkpoint save-hook reads exactly these three); the bookkeeping
WF protects — `clients`, `exited`, `scan`, `dirty`, `lastCkptMs`, `attachSeq`,
`outSeq`, `lookSeq`, `tickOutSeq`, `freshFlag` — goes private, which makes the
anonymous constructor (and every `{ s with … }` outside friends) refuse.

`State.boot vt labels metaKv` caps restored labels at `maxLabels` — closing
the gap this step's sizing surfaced: `.labelSet` enforces the cap per message,
but a corrupt checkpoint's label list had no cap at boot, so `Bounded` was
unprovable for a resumed daemon. Behaviour change, deliberate and tiny: a
forged >64-label checkpoint truncates instead of booting an over-cap store.

Consequences carried, not fought: `Theorems/Session.lean` and
`Tests/Session.lean` become friend modules (their statements name sealed
fields; their roster-forging fixtures are legitimate rigging) — which forces
the 15 theorem files they import (`Wire`, `Vt`, `Terminal`, `Render` + the
11-rung ladder) through the same mechanical `module` + blanket-public
migration as Step 1, since a module cannot import a legacy file. The rest of
`Theorems/`/`Tests/` stays legacy (Decision 2 holds where nothing names sealed
internals; measured: mixed public/private fields read fine downstream,
`native_decide` works inside a friend module, and a public-field `{ s with … }`
is still refused — the ctor is the gate).

**Exit:** gates green, every ratchet number unchanged except the def census
(+1, `boot`, arriving claimed); `boot_wf` (`Good vt → WF (boot …)`) and the
headline corollary `run_boot_wf` (every state reachable from any boot is WF)
proved; the boot-labels cap pinned by a fixture; break-verified: a `State`
forge/update from the daemon refuses to compile (against the `linger` exe
target — the step-2 lesson), and `boot` without the `take` refutes `boot_wf`.
The resume-path `Good vt` hypothesis is discharged where the checkpoint
theorems put it, or recorded honestly as carried by them — check
`Theorems/Checkpoint.lean` before claiming either way.

## Non-goals

- **Module-izing `Theorems/`/`Tests/` wholesale** (Decision 2's reason) —
  amended by Step 5: files whose statements name sealed `State` internals
  convert (Session's theorem and fixture files), and the theorem files they
  import migrate mechanically because a module cannot import a legacy file.
  Conversion follows the boundary, never runs ahead of it.
- **A toolchain bump.** Everything here is measured on the pinned v4.32.0;
  chasing newer module-system refinements is a separate risk (this host's
  glibc constraints make toolchain moves non-trivial — see `./lake`).
- **Retiring greps that still measure something** (Decision 3).
