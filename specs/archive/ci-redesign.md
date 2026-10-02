# CI redesign

## Status

Closed, 2026-10-02. The published source checkpoint `419f2df` passes final
independent review, complete foreground verification and hosted Linux run
37008938692. All product theorem contracts and live assertions are retained.
The three worker branches and worktrees are retired after containment and
recovery checks. Closure changes only records; its non-record source manifest
matches the complete verifier. The completion evidence and limits are below.

## Intent and constraints

Give each verification obligation one execution per CI run. Remove the
Python hook dependency, keep local and CI checks on the same implementation,
and make logs distinguish compilation, product checks and verifier regression
checks. Reuse a successful verification only when every relevant input is
identical; an artifact cache or a documentation-only diff is not evidence
that a previous verification succeeded. Scheduled, manual and release runs
retain clean verification and macOS coverage.

Keep all product theorem contracts and live assertions. Reduce waiting only
where an observed condition replaces it; negative observation windows retain
their meaning. New regression tests must reject deliberately broken behavior.
Shell remains the build/CI boundary; tests of that boundary are Lean. No
Python, new C, generic workflow framework, or product feature changes.

## Ownership

One writer per worktree. Shared records, workflow, verifier orchestration,
entry points, gates, README and publication belong to the coordinator.
Workers read this spec, AGENTS.md, SCRATCHPAD.md and their implementation.
Evidence and temporary scripts live under
`/tmp/linger-ci-redesign-20261002-nuJuA0/`. Controlled timing runs take its
exclusive `measure.lock`; ordinary correctness runs must not be described
as isolated timing measurements.

- Hygiene worker: `tests/hygiene.sh` and `E2E/Hygiene.lean`. Replace generic
  hook checks with small native boundary checks and exercise their failures.
  The coordinator owns hook installation, workflow lint, and integration.
- Coverage worker: `Theorems/Coverage.lean` and `E2E/Coverage.lean`. Consolidate
  source census and semantic checking without losing fresh-source detection
  or the existing parser/reference regression fixtures.
- Selector-test worker: `E2E/Manager.lean` only. Reduce its measured latency
  while preserving every assertion and isolation/signal/timeout contract.

## Steps

1. **Design and measure.** Read the actual workflow and hosted phase receipts,
   inventory the obligations, and make regression fixtures for the proposed
   boundaries. Reads: workflow, verifier, hooks, coverage, selector tests and
   prior records. Writes: this spec, append-only SCRATCHPAD, worker evidence.
   Exit: duplicate work and remaining costs have measured owners, and the
   execution/reuse design fails closed.
2. **Implement the shared path.** Integrate native hygiene, consolidated
   coverage, successful-verification reuse and the simplified workflow.
   Reads: Step 1 evidence and actual callers. Writes: workflow, verifier
   scripts, hooks, E2E entry point/CI checks, gates, README and owned worker
   files. Exit: each obligation has one owner, no Python hook setup remains,
   and focused controls catch stale reuse, skipped checks and real failures.
   Run required builds and the full verifier; commit and push the checkpoint.
3. **Reduce live-test latency and verify the assembly.** Integrate justified
   selector-test changes after a separate review; measure fixed inputs and
   keep exact check counts. Writes: selector test, any required integration
   and records. Exit: every live assertion still runs, the assembled foreground
   verifier passes, and hosted CI confirms the new execution path. Review is
   bounded to two review/revise rounds; unresolved correctness issues require
   revisiting the design.
4. **Close and publish.** Record actual warm/source-changing/records-only
   timings without conflating them, preserve worker evidence, retire owned
   branches/worktrees after containment checks, archive this spec and update
   AGENTS.md. Exit: verified main is committed and pushed, remote matches,
   and the completion record states any remaining costs or limitations.

## Completion record

The two CI jobs have distinct responsibilities. Hygiene and standalone
workflow lint run first; the full verifier performs build, ABI, source gates,
formatting, semantic coverage, verifier regressions, fuzz and live checks
once. The Python hook framework and final duplicate hook pass are removed.
Local hooks use the same native hygiene and source gates. Their staged-content
guard prevents working-tree corrections from hiding invalid staged content.
Sixteen input-key regressions and three hook regressions join the existing
fixtures. Deliberate mutations exercise failed checks rather than merely
showing successful execution.

An exact successful-verification receipt covers all non-record contents,
paths, modes and runner OS/architecture/image. It is saved only after the
complete verifier succeeds. Current records still receive source gates and
hygiene on a hit. Scheduled, manual and tag runs bypass receipt reuse and
start without build or formatter-result caches. Compiled artifacts retain
their separate content checks. The final records-only publication exercises
receipt reuse; that post-publication observation belongs with the external
run evidence rather than a later edit to this archived record.

Coverage shares one exact-constant census and still rereads current source
on its direct invocation. Fixed parser/reference fixtures move unchanged into
the compiled theorem module. Manager overlaps two independent check groups;
complete PTY acquisition and other parent-side launches share an
exception-safe mutex. Explicit waits and observations remain outside it.
No product code, C shim, toolchain or theorem statement changes.

| Measurement | Before | After |
| --- | ---: | ---: |
| Controlled local warm coverage | 9.373 s | 5.033 s |
| Corrected local Manager pair, fixed CLI/picker | 64.882 s | 32.835 s |
| Hosted shared redesign, `b0f4bd0` | — | Linux 166 s; full verifier 128 s |
| Hosted final source, `419f2df` | — | Linux 154 s; full verifier 117 s |

The controlled coverage reduction is 46.3%; the corrected Manager pair
saves 49.39%. The final hosted hygiene job takes 9 seconds. Its Linux
verifier reports build 22, ABI 1, source gates 3, formatting/lint 8,
coverage 5, verifier regressions 8, shim smoke 7 and live suites 62 seconds;
phase reporting is whole-second resolution. Manager takes 32.542 seconds.
The earlier user-quoted run 36954511812 was a warm records-only checkpoint:
Linux 168 seconds, full verifier 101.511, build 1.393 and live suites 66.682.
Those different inputs do not constitute a controlled full-CI comparison.
Broad source changes still require rebuilding affected proofs; toolchain
cache restoration takes 19 seconds in the final source run. No universal
runtime bound is claimed.

The assembled local verifier takes 101.385 seconds, including 59 seconds
for live suites, and retains all 470 live assertions, 45 CI checks,
48 hygiene checks and 63 shim checks. Semantic coverage retains 355 pure
definitions and every runtime backing entry. Source bytes, modes and inventory
match before and after. Both required checkpoint builds pass. Independent
review accepts coverage, the corrected native hook, the reuse boundary and
the corrected Manager scheduler. The first Manager revision was rejected
for concurrent PTY acquisition and never reached main.

Each worker has zero unique commits outside main. Four worker source files
are integrated byte-for-byte; the original hygiene fixtures remain with
three additional staged-content checks. Before retirement, complete source
snapshots, manifests, Git state and patches are preserved and compared.
Only reproducible build/formatter caches and Git worktree pointers are
excluded. Main is the only remaining branch and worktree.

All detailed evidence is under
`/tmp/linger-ci-redesign-20261002-nuJuA0/`: `assembled-full/`,
`hosted-37008938692/`, `reviews/`, `hook-controls/`, `gate-controls/`,
`selector-evidence/round2/`, `evidence-coverage/` and `worker-recovery/`.
`SCRATCHPAD.md` records the failed probes, corrected measurements,
publication and closure checks.
