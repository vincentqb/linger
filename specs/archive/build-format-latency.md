# Build and formatting latency

## Status

Closed, 2026-10-02. All four steps are complete. The measured renderer
and VT changes are published in `9294e98` and `74bb34e`; both checkpoints
pass the full local verifier and hosted Linux CI. Both worker worktrees
and branches are retired after audited recovery copies.

Baseline `a8c40c0` was clean and published before this spec opened. The
preceding source-changing hosted run spent 225.592 seconds building and
123.766 in source gates plus layout. Its live suites took 66.240 seconds.
These observations motivated measurement; they are not controlled baseline
comparisons for the changes below.

Step 1 is measured. Step 2 has two independently reviewed renderer changes:
explicit list rewrites preserve the complete original proof contract, and
consolidated compile-time fixtures preserve every distinct assertion.
Interleaved local module checks improve from 19.339 to 13.853 seconds and
17.055 to 10.132 seconds respectively. Both deliberate core mutations are
rejected by the consolidated assertion. The renderer checkpoint passes the
complete foreground verifier in 103.277 seconds with unchanged source bytes
and all fifteen live suites passing their exact counts. Commit `9294e98`
publishes that checkpoint after required builds and hooks pass; hosted run
36952028070 succeeds in 250 seconds for the Linux job, including 177.287
seconds for the full verifier. VT factorization passes independent source,
declaration and import-boundary review. The final formatted split preserves
all compiled declaration contracts and passes four matched no-cache formatter
checks. Cold layout falls from 30.574 to 19.626 seconds, a 35.8% reduction.
The final bounded review accepts the compiled layout contract without blockers.
The assembled foreground verifier passes in 173.412 seconds, with all fifteen
live suites matching their exact counts and unchanged source manifests.
Required checkpoint builds and all-file hooks pass with the same verified
source inventory. Commit `74bb34e` publishes the VT factorization; hosted
run 36953792910 succeeds. Both worker worktrees and branches are retired
after publication, with verified recovery copies and no unique commits lost.

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
  Factor only along real proof dependencies, preserving authored qualified
  names, types, universe parameters and axiom sets. Record exact mappings
  for compiler-generated private names when their owning module moves;
  compare every original declaration through that mapping without aliases
  or compiler escapes. Avoid speculative abstractions.
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

## Completion record

The formatter's large-file cost is parsing, rendering and exact validation;
its compiled skeleton already skips most proof bodies. Factoring VT along
State and independent Parser/Renderable dependencies reduces that cost and
allows independent module rebuilds. Explicit list rewrites avoid expensive
definitional reduction in the renderer proof. Consolidating large renderer
fixtures avoids repeated evaluation while retaining every distinct assertion.

Matched local baseline/candidate/candidate/baseline trials use the same
compiler, formatter, host and fixed source inputs:

| Operation | Baseline mean | Final mean | Reduction |
| --- | ---: | ---: | ---: |
| Cold formatter result cache, warm imports and OS cache | 30.574 s | 19.626 s | 35.8% |
| Renderer grid proof module | 19.339 s | 13.853 s | 28.4% |
| Renderer unit-test module | 17.055 s | 10.132 s | 40.6% |

The separate VT rebuild trial improves from 30.234 to 24.723 seconds
(18.2%); it precedes the final umbrella layout patch. It is not a complete
clean-build measurement. The warm formatter baseline is 1.172 seconds.
Increasing formatter concurrency regresses the measured cold check and is
rejected. No formatter pin or dependency change is justified by the evidence.

Independent review and compiled declaration comparison preserve all 1,373
original logical VT declarations, including every one of the 1,148 theorem
statements, their universe parameters and individual axiom sets. Recorded
private-name mappings account for module ownership. The final layout patch
also preserves all 1,650 split declaration instances exactly, excluding only
source line positions. The import-boundary gate now checks every VT child;
nine controls exercise its accepted imports and deliberately broken boundary.
Two real renderer mutations are caught by the consolidated assertions.

The assembled foreground verifier passes with unchanged source bytes and
modes, generated C ABI and standalone checks, semantic coverage, formatter
validation, CI negative controls, shim smoke, fuzz and all fifteen live suites
with their exact counts. Required checkpoint builds and hooks pass.
Hosted run [36953792910](https://github.com/vincentqb/linger/actions/runs/36953792910)
passes for `74bb34e`, following the successful renderer run
[36952028070](https://github.com/vincentqb/linger/actions/runs/36952028070).

Remaining cost is explicit: the broad VT refactor's hosted Linux job takes
414 seconds, including 347.997 for the verifier: 193.457 building,
58.935 source gates plus layout and 66.370 live suites. Toolchain restoration
takes 22 seconds and final hooks 18. This run rebuilds changed proof modules
and their consumers; it is not comparable to the earlier warm CI run or a
controlled before/after total. The audit establishes the component speedups
above, not a sub-five-minute bound for all source changes.

Recovery copies preserve worker sources, patches, untracked files, modes and
links. Both retired branches have no unique commits; worker code matches the
published tree. All agents are closed and main is the sole worktree. Detailed
receipts and both bounded independent reviews remain under
`/tmp/linger-build-format-20261002-iLuMec/`. Closure changes only these records;
its required builds and hooks are recorded in the append-only worklog.
