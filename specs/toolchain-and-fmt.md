# toolchain-and-fmt — bump to v4.34.0-rc2 and adopt lean-fmt

Status: active
Updated: 2026-08-29

## Why this re-opens a settled non-goal

`specs/lean-modules.md` lists "a toolchain bump" as a non-goal: *"Everything here is
measured on the pinned v4.32.0; chasing newer module-system refinements is a separate
risk (this host's glibc constraints make toolchain moves non-trivial)."*

AGENTS.md allows re-opening a non-goal on a **new reason, not a fresh pair of eyes**.
The new reason is `lean-fmt`, the only Lean 4 formatter that exists: there is no
official one (the pretty-printer RFC, leanprover/lean4#369 and #1488, is still open)
and `lean-fmt` ships **one release per toolchain, tagged exactly as the toolchain**.
Measured: every one of its releases — including the old `v0.x` line — requires
`v4.34.0-rc1` or `v4.34.0-rc2`. There is no build of it for any stable Lean.

## The cost, stated up front

**We are pinning a 1467-theorem proof library to a Lean release candidate.**
`v4.34.0` stable does not exist yet (rc2 is the tip). That is the trade, and it is
the whole trade: formatting is worth it or it is not.

Three specific exposures, each of which must be MEASURED and not assumed:

1. **`warningAsError := true` makes every new deprecation a build error.** Two Lean
   minor versions of deprecations land at once. `String.splitOn` is already marked
   legacy ("will be deprecated in the future") and has ~50 call sites.
2. **`HEARTBEAT_CAP` is 1 with zero headroom.** Proof elaboration cost moves between
   versions. If v4.34 makes a proof more expensive, the gate fails — and AGENTS.md is
   explicit that a raise is a measurement to read, not a number to silence.
3. **The module system is two minor versions younger than our migration.** `private`
   fields, `import all` friend modules and `public section` are all load-bearing here
   (`Buf`'s seal, `Session.State`'s seal, `Theorems/Buf.lean`).

## Definition of done

1. `lean-toolchain` is `leanprover/lean4:v4.34.0-rc2`; `./lake build`,
   `./lake build Theorems Tests`, `./tests/e2e.sh` green and **warning-free**.
2. Every ratchet either unchanged or moved with a recorded measurement — especially
   `HEARTBEAT_CAP`. A raise is allowed only with the proof named and the cost read.
3. `lean-fmt` installed **standalone on PATH**, not as a Lake dependency: the
   `require`-free lakefile and `"packages":[]` manifest are gates in
   `tests/gates.sh`, and README promises no external Lean dependencies. Its own docs
   support this (`make install`).
4. The reformat lands as **its own commit**, separate from the bump — lean-fmt's own
   guidance, and the only way either diff is reviewable.
5. `lean-fmt check` wired into `.pre-commit-config.yaml` (it has `--staged`, exit
   codes 0/1/2, and does not compile the project — so it fits the ~1 s commit tier).
6. The pin's RC status is recorded in `AGENTS.md` with the trigger to move it:
   `v4.34.0` stable, plus a lean-fmt tag for it.

## Steps

- **Step 1 — the bump alone.** Nothing else changes. Measure the fallout, fix it,
  record every ratchet number before and after.
- **Step 2 — install lean-fmt, look before leaping.** `format --check` and `check`
  to size the diff before any file is rewritten.
- **Step 3 — the reformat**, its own commit, with the before/after of the gate.
- **Step 4 — the hook**, plus a `.lean-fmt.toml` if the defaults fight the house
  style.

## Kill criteria

Abandon and revert if: the bump needs more than a couple of new `maxHeartbeats`
raises (that is the proofs getting worse, which no formatter is worth), or if
lean-fmt's canonical style fights the deliberate layout the proofs rely on — the
named-stage style and `repeat' split` + `all_goals first | …` shapes are
design-for-provability decisions, not accidents. A formatter that reflows those into
one line is a formatter this repo cannot use.
