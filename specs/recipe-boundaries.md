# Smaller recipes and a proved import plan

Status: in progress
Updated: 2026-09-26
Next: Step 2 — type and prove the standalone importer
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
live/resumable names, and fail-before-creation preflight. Freeze relative state
paths and the executable in the invocation directory without collapsing
symlink/parent components. Reject NUL before strings cross a POSIX boundary.

## Steps

### Step 1 — consolidate picker composition

Complete. `lz --loop [NAME[@HOST]]` shares one picker and attach path with
one-shot `lz`; `lzh.fish` is removed. Ghostty passes the quoted command through
its documented `shell:` mode. The new loop and argument assertions fail on
the predecessor and pass on the final implementation. The complete foreground
verifier passes, including the existing importer and all other live suites.

### Step 2 — type and prove the importer

Pending. Add the pure parser/planner, theorem and unit-test modules, optional
`lzr` executable, and direct executable checks against real daemons. Delete the
fish importer only after equivalent behavior passes. Extend semantic coverage
and source gates to the new pure module and executor. Document the per-decision
proof/test boundary and finish with a full verified checkpoint.

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
