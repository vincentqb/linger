# Shared display convention

## Status

Active, 2026-10-02. Starting from clean, published `1fe50a5`.
Step 1 implementation, negative controls, assembled verification and both
independent review passes are complete. The corrected title budget and
isolated Manager log repair have no remaining review blockers. Publication
is in progress.

## Intent and constraints

Use `session · application title · attention` consistently. Optional empty
parts disappear, and attention remains the last displayed segment. Preserve
the shared status vocabulary, native terminal palette, bounded OSC encoding,
application-stream boundaries and default title handback. Align the optional
fish prompt recipe without changing the user's left prompt or command status.

Keep one Lean composition policy and the existing `linger status` sampler.
No additional public command or option, dependency, C, monitor bar, title stack,
or changes to sampling intervals. Shell remains native prompt configuration;
tests and status policy remain Lean. Historical records stay untouched.

## Steps

1. **Implement and verify the convention.** Read the current title composer,
   runtime caller, fish recipe, proof contracts and live checks. First reproduce
   the wrong order with a failing check. Update the shared policy, meaningful
   ordering/omission proofs, callers, native recipe, source ties and user docs.
   Writes: `Linger/Core/Title.lean`, `Linger/Core/Terminal.lean`,
   `Theorems/Title.lean`, `Theorems/TerminalTitle.lean`, `Tests/Title.lean`,
   `Linger/Runtime/Client.lean`, `E2E/Title.lean`, `E2E/Recipes.lean`,
   `E2E/Manager.lean` and any necessary bounded `E2E/Ci.lean` regression,
   `recipes/fish_prompt.fish`, `recipes/README.md`, `tests/gates.sh`,
   `tests/e2e.sh`, `README.md`, `THEOREMS.md`, `AGENTS.md`, this spec and
   append-only `SCRATCHPAD.md`. Exit: deliberately reversed order fails,
   empty segments have no stray separator, native prompt checks preserve
   status and sampling behavior, independent review finds no correctness
   blockers, both required builds and the full foreground verifier pass.
   Commit and push that verified checkpoint.
2. **Close and publish.** Record actual verification and hosted results,
   archive this spec and restore the no-live-spec pointer. Exit: verified
   main is pushed, remote matches, and the completion record states what the
   shared policy proves and what the native recipe tests observe. Review is
   bounded to two passes; no unrelated features.

## Review findings

The first independent review finds that placing attention last exposes the
encoder's existing character limit: a long application title can hide the
suffix. Reserve its space in the pure composition policy, using the encoder's
budget, and prove that fitting session/attention content survives encoding.
Add an encoded regression before fixing this case.

The first complete verifier also exposes an existing Manager test-log race:
group timing on stderr interrupts concurrent PASS lines on stdout. The strict
runner rejects 110/111 lines despite a successful suite verdict. Repair this
in an isolated worktree without relaxing the runner, assertion inventory,
concurrency, launch serialization, observation windows or child joining.

## Verification so far

The encoded regression fails before the budget fix. The repaired composer
reserves the session and attention suffix, then clips application text to
the generic encoder's shared character budget. A generic payload append
theorem and the session composition theorem prove suffix preservation at
the actual encoding boundary, conditional on session and attention fitting.
All 19 live title checks pass, including a maximum-length Unicode title.
Removing the suffix reservation fails both proof/unit checks and precisely
the new live title assertion. Restoring it passes the proof/test build and
source gates. Reversing only the runtime arguments still fails its gate.

The Manager worker joins all assertion writers and flushes stdout before
printing collected timing/exception diagnostics. Actual Runner checks pass
111/111 for Manager and 45/45 for CI. Deterministic controls reject the original
scheduler, a missing final flush and an early flush; a throwing group retains
its complete assertion, diagnostic and failure verdict. The complete
assembled verifier remains required; focused results do not replace it.

The assembled foreground verifier passes in 106.132 seconds, including all
474 live assertions, 45 CI, 48 hygiene and 63 shim checks. All 356 explicit
pure definitions have semantic theorem coverage. Required program and
proof/test builds pass separately. The complete 144-file non-record
inventory, modes and bytes match before and after verification. Manager
retains its worker-verified source and passes 111/111 in 32.259 seconds.
Logs, counts and manifests: `final-full/` under
`/tmp/linger-display-convention-20261002-CMHm3y/`.

The second independent review accepts the final sources and retained
negative-control evidence, including the actual encoded-suffix theorem.
It confirms the fish hook boundaries and unchanged Manager assertions,
waits and concurrency. Review is source/evidence inspection, not an
additional execution; observed Manager stream behavior is Linux-specific.
