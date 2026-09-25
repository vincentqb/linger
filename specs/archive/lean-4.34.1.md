# Lean 4.34.1

Status: complete (2026-09-25) — archived record, do not edit
Updated: 2026-09-25
Predecessor: `specs/archive/codebase-audit.md`

## Goal

Upgrade linger to Lean `v4.34.1` as explicitly requested. The request
supersedes the previous requirement to wait for a matching lean-fmt tag.
Keep the formatter standalone and preserve every existing verification gate.

## Step 1

- Change the compiler pin and current setup instructions.
- Pin compatible formatter source independently and verify its build and
  checks against the upgraded project.
- Fix any compiler or proof compatibility issues without weakening contracts
  or raising resource allowances.
- Run `./lake build`, `./lake build Theorems Tests`, and the complete
  foreground `./tests/e2e.sh` verifier, including the generated C ABI check.
- Record evidence, archive this spec, commit the verified upgrade on main,
  push, and request the platform CI workflow.

## Evidence

- Starting main is clean at `3cf3cff`. The compiler reports
  `4.34.0-rc2`; the requested `4.34.1` version assertion fails before
  changing the pin. Receipt:
  `/tmp/linger-lean-4.34.1-20260925/version-before.log`.
- The parent owns compiler, proof and runtime validation. The formatter
  worker has an isolated worktree and writes only the CI workflow.
- `./lake env lean --version` now reports `4.34.1` and the version
  assertion passes. Both `./lake build` and `./lake build Theorems Tests`
  pass without changing any program or proof source. Receipts:
  `version-after.log`, `build.log` and `proofs-tests.log` in the same
  directory.
- The first complete verifier passes its clean build, generated C ABI and
  source gates, then the installed rc2 formatter refuses the new toolchain.
  Its log is retained as `formatter-version-refusal.log`.
- The formatter failure handler filtered only layout-drift lines. Under
  `set -e`, a toolchain error therefore exited before showing either the
  original diagnostic or the verifier's failure message. It now prints
  the captured diagnostic before failing. Running the actual formatter
  stage extracted from `tests/e2e.sh` rejects the old binary both before
  and after; diagnostic assertions fail before and pass after. Receipts:
  `formatter-diagnostic-{red,green}.log`.
- The standalone formatter source at
  `9e8704afb1ed88a935cbdbf10d735e826b0034b8` builds with the project
  compiler without source changes. Its release label remains rc2, while
  `--version` identifies its compiler as `Lean 4.34.1`. Both installed
  binaries are available in the usual local tool directory.
- CI now fetches that exact source commit, copies the project compiler pin
  and wrapper into a fresh checkout, and asserts the compiled Lean version
  on both cache hits and misses. The cache key includes source, compiler,
  OS and architecture. Lint and layout checks remain enabled.
- Worker lint and layout checks pass without using their caches. The
  workflow cache-hit assertion rejects the old binary and accepts the
  rebuilt binary. The worker handoff and build receipts are under
  `/tmp/linger-lean-fmt-4.34.1.mAVGFd/`. Parent `actionlint` and diff
  whitespace checks pass after integrating the workflow change.
- The complete foreground verifier passes on `4.34.1`: clean rebuild,
  generated C ABI, source and layout gates, semantic theorem coverage,
  CI runner selection, fuzz corpus, POSIX smoke tests and every live suite.
  Receipt: `/tmp/linger-lean-4.34.1-20260925/verifier.log`.
- Current formatter setup links now point to README and the workflow's
  installation instructions; the earlier archived recipe is unchanged.
- A separate cache-hit fixture excludes the helper executable from both
  the formatter's directory and PATH. Uncached lint and layout still pass
  on every Lean source file, so the workflow retains its single-binary
  cache.

## Completion record

The compiler pin, current setup instructions, standalone formatter
provisioning and formatter failure diagnostics are updated. Program and
proof source files need no compatibility changes. The complete Linux
verifier passes with the rebuilt formatter; final program and proof/test
builds, source gates, shell syntax, workflow validation and diff checks
also pass. Receipts include `final-{build,proofs-tests,gates}.log`.

All worker changes are integrated on main. Hosted platform checks remain
unverified at this checkpoint: the previous workflow was blocked before
execution by GitHub's billing/spending limit. A manual platform workflow
will be requested after pushing the verified upgrade.
