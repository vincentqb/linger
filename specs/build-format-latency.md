# Build and formatting latency

## Status

Active, 2026-10-02. Baseline `a8c40c0`, clean and published before this
spec opened. The preceding source-changing hosted run spent 225.592 seconds
building and 123.766 in source gates plus layout. Its live suites took
66.240 seconds. Measure the causes before attributing these costs.

Step 1 is measured. Step 2 has two independently reviewed renderer changes:
explicit list rewrites preserve the complete original proof contract, and
consolidated compile-time fixtures preserve every distinct assertion.
Interleaved local module checks improve from 19.339 to 13.853 seconds and
17.055 to 10.132 seconds respectively. Both deliberate core mutations are
rejected by the consolidated assertion. The renderer checkpoint passes the
complete foreground verifier in 103.277 seconds with unchanged source bytes
and all fifteen live suites passing their exact counts. Publication follows
the required checkpoint builds and hooks. VT factorization remains under
investigation.

## Intent and constraints

Explain and reduce the cost of formatting and compilation, both locally
and in CI. Keep every current theorem statement, semantic coverage
obligation, compiler warning check, formatter validation, ABI check and
test assertion unless a stronger reviewed replacement is established.
Use the existing minimal-code, verifier-in-the-loop, spec-driven-build
and compound-engineering skills. Preserve meaningful failures as durable
checks and document rejected performance candidates.

Out of scope: product behavior, new C, additional dependencies, weakened
formatting, compiler upgrades without evidence, machine-specific benchmark
thresholds, and new general-purpose build frameworks.

## Ownership

One writer per worktree. Each worker reads AGENTS.md, this spec,
SCRATCHPAD.md and the actual implementation and callers. The coordinator
owns shared records, integration and publication. Worker reports and
profiling probes live outside the tracked tree at
`/tmp/linger-build-format-20261002-iLuMec/`.

- **Formatter worker:** `.lean-fmt.toml`, `.pre-commit-config.yaml`,
  `.github/workflows/ci.yml`, and a focused Lean regression module under
  `E2E/` if needed. Investigate the pinned standalone formatter and apply
  a measured, supported invocation/configuration or pin fix. External
  formatter source is evidence; do not publish changes to its repository.
- **Proof worker:** `Theorems/Vt.lean` and `Theorems/Vt/*.lean`.
  Factor only along real proof dependencies, preserving declaration names,
  types, universe parameters and axiom sets. Avoid speculative abstractions.
- **Coordinator:** `lakefile.lean`, `tests/e2e.sh`, `tests/gates.sh`,
  `E2E/Ci.lean`, `E2ETest.lean`, `Theorems/Render/Grid.lean`,
  `Tests/Render.lean`, README.md, THEOREMS.md, AGENTS.md, this spec and
  append-only SCRATCHPAD.md. Inspect build scheduling, native compilation,
  dependency invalidation and cache behavior locally. The renderer paths
  are added after profiling found costly definitional equality in
  `restore_cons` and repeated evaluation of the large history fixtures.
  Integrate any workflow changes only after the formatter worker stops.

Timed experiments share an exclusive lock under the task directory.
Correctness runs may overlap only when their times are not presented as
controlled measurements.

## Steps

1. **Measure and isolate.** Read build logs, dependency graphs, formatter
   implementation and caches. Write fixed-source receipts, stage and
   per-module timings, and bounded candidate plans under the task directory.
   Exit: costs are attributed to observed operations, with warm and
   source-changing runs distinguished.
2. **Publish the renderer checkpoint.** Apply the measured proof and fixture
   changes with targeted failure controls and declaration equality checks.
   An independent reviewer reads the actual sources and receipts. Run the
   required builds, complete foreground verifier and hooks; commit and push.
   Exit: the measured improvements retain the full contract, independent
   review has no blockers, and the checkpoint is verified and published.
3. **Evaluate and publish VT factorization.** Complete the isolated proof
   worker's bounded candidate and inspect its declaration and dependency
   receipts. Measure compilation and cold formatting using fixed inputs.
   Integrate only a justified improvement, preserve the standalone boundary,
   and independently review the contract. Run the assembled verifier and
   hooks before committing and pushing. Exit: accepted changes retain the
   guarantees and hosted CI passes, or the rejected candidate and evidence
   are recorded without speculative code. Measurements identify host, cache
   and source context; review remains bounded to two review/revise rounds.
4. **Close.** Preserve unique worker evidence, retire merged branches and
   worktrees, archive this spec, and update AGENTS.md. Exit: clean main
   matches the remote and the completion record states remaining costs.
