# Smaller recipes and a proved import plan

Status: complete — local Linux verifier green; hosted checks pending
Updated: 2026-09-26
Next: none
Predecessor: `specs/archive/ghostty-recipe.md`

## Goal

Implement the user's approved per-recipe recommendations. Share one fish picker
between one-shot attach and detach-to-picker looping. Keep reconnect, status
refresh, terminal launch and native configuration at their existing boundaries.
Move the foreign-save parser and import policy into a standalone Lean tool.

The previous fish-only importer decision is reopened for a concrete reason:
the importer now performs whole-file parsing, parallel-record bookkeeping,
validation, existing-session planning and command eligibility. Typed records
and a pure plan can replace that bookkeeping and carry meaningful proofs.
Neither the main linger CLI nor its daemon, VT or checkpoint codec needs the
foreign format.

## Requirements and evidence

| Decision | Required support |
|---|---|
| One `lz` function, with `--loop [NAME[@HOST]]` | Existing §Detach and §Handback guarantees support returning to the caller. Shared Lean IO checks exercise the real function's argument handling, failure status and loop ordering. |
| Keep `lza` and `lzs` in fish | §Detach supports sessions surviving a client; §Status and §Row support the displayed observations. IO checks cover the actual retry/refresh policy. |
| Keep `lzo` in fish | §Name and §Remote support canonical session identities; IO checks validate the whole remote listing and exact launch arguments. |
| Keep Ghostty and SSH settings native | Their tools own configuration semantics. Check documented Ghostty launch syntax and parse the SSH setting; make no GUI or network-liveness proof claim. |
| Standalone Lean `lzr` | Prove successful parsing gives nonempty, valid, distinct names and representable directory/command fields; prove plan provenance, existing-name exclusion, command opt-in and eligibility, and sequential idempotence. |
| Keep the importer outside `Linger/` | Source gates check the import boundary and connect the IO executor to the proved parser and plan. No C, raw OS binding, runtime or checkpoint extension. |

Theorems state semantic contracts, not a claim that one source language is
intrinsically preferable. An import uses a successful initial listing snapshot.
Sequential idempotence does not imply an atomic create-only operation or safe
concurrent imports: `linger run` remains an upsert.

Preserve the save-path defaults, directory decoding, command text, skipped
live/resumable names, and fail-before-creation preflight. Resolve the executable
and relative state paths from the invocation directory, following symlinks
before parent components and retaining a missing state-directory suffix.
Saved directory paths use physical OS traversal. Use one effective home for
save defaults, tilde expansion and child environments, including the account
home when HOME is absent or empty. Reject NUL before strings cross a POSIX boundary.

## Steps

### Step 1 — consolidate picker composition

Complete. `lz --loop [NAME[@HOST]]` shares one picker and attach path with
one-shot `lz`; `lzh.fish` is removed. Ghostty passes the quoted command through
its documented `shell:` mode. The new loop and argument assertions fail on
the predecessor and pass on the final implementation. The complete foreground
verifier passes, including the existing importer and all other live suites.

### Step 2 — type and prove the importer

Complete. The optional `lzr`
executable consumes the pure parser and plan. All seven pure definitions have
substantive theorem coverage; six compiled implementation mutations fail both
proofs and fixtures. Nine compiled call-site or boundary mutations fail source
gates, and an unclaimed pure definition fails the theorem census.

The executable passes the existing importer behavior checks, including the new
NUL preflight rejection that fails against the fish predecessor. The fish
importer is removed. An independent IO review found exported-function lookup,
missing-home and long-relative-state-path regressions in the initial Lean draft.
The fixes pass all comparison probes. Six permanent Lean regressions fail on
the initial draft and pass on the final executable. The complete foreground
verifier passes with the final recipe assertion roster, followed by both
required warm builds.

## Verification

Every checkpoint runs both required Lean builds. Deletions additionally run
the complete foreground verifier. New proofs and runtime ties are deliberately
broken to confirm they detect the motivating failure, then restored. Keep the
exact recipe assertion roster in `tests/e2e.sh`. Format the changed Lean files,
run the source gates, and retain receipts under
`/tmp/linger-recipe-boundaries-20260926/`.

Workers use separate worktrees with disjoint file ownership. Integrate their
reviewed changes into main and push ordinary commits; do not rewrite history.
Append verification and completion evidence to SCRATCHPAD.md and archive this
spec when the approved changes are complete.

## Completion

Both approved steps are implemented and verified on Linux with Lean v4.34.1.
There are four fish helpers and two native configuration examples. The optional
importer is built separately; it adds no C, raw OS bindings, Lean dependencies
or changes to the session program or VT toolkit.

The new pure module has seven definitions, sixteen authored proofs and twenty
unit fixtures. Six compiled policy mutations fail both proofs and fixtures;
nine compiled executor or import-boundary mutations fail the source gates.
A compiled unclaimed definition also fails the expanded theorem census.
The final verifier includes the clean build, generated C ABI, purity and
boundary gates, formatter, theorem census, CI runner checks, fuzz corpus, POSIX
smoke tests, all twelve live suites and the unrelated-session sentinel.

Receipts are retained in `/tmp/linger-recipe-boundaries-20260926/`, particularly
`importer-full-verifier.log`, `importer-clean-build.log`, `step2-build.log` and
`step2-proofs-tests.log`. Detailed mutation and review receipts are recorded in
SCRATCHPAD.md. Workers were reviewed, integrated and closed before this
checkpoint. Hosted platform checks remain pending at closure; no macOS or
live Ghostty GUI result is claimed.
