# Keep only useful imported data

Status: Active — implementation verified; publication and closure pending
Updated: 2026-10-01

## Intent

The user wants Linger to carry only data it actually uses, even when discarding
foreign metadata prevents reconstructing a tmux save. Imported identity names
the session and its working directory starts the shell. Native checkpoints
already retain the terminal state and labels used by Linger.

Stop persisting or consulting opaque foreign source data. Export the current
native names and directories through the existing checked serializer.
Shared layouts, focus, grouping, titles and saved commands have no new native
consumer in this change. Exact foreign reconstruction is deliberately retired.
Keep native LNGR v1 files, import naming, directory handling, validation and
command nonexecution intact. Existing user files are not automatically deleted.

Out of scope: new metadata fields or checkpoint versions, grouping or display
features, input recording, process restoration, and rewriting archived records.

## Step 1 — simplify and verify

Reads: `Tools/Resurrect.lean`, `Theorems/Resurrect.lean`,
`Tests/Resurrect.lean`, `Manager/Resurrect.lean`, `E2E/Interop.lean`,
the native checkpoint/path/listing code, existing gates and interchange docs,
`SCRATCHPAD.md`, and `specs/archive/tmux-roundtrip.md`.

Writes: those three pure-policy/proof/test files (isolated worker);
`Manager/Resurrect.lean`, `E2E/Interop.lean`, `tests/{gates,e2e}.sh`,
`THEOREMS.md`, `recipes/README.md`, `README.md`, `AGENTS.md`, this spec,
and append-only `SCRATCHPAD.md` (coordinator).

The coordinator implements the IO deletion and executable regressions while
the worker removes the pure retention branch and generalizes metadata
irrelevance. A separate reviewer checks the assembled diff during verification.
Allow at most two review/revision rounds before revisiting an unresolved choice.

Exit: a new check fails on the original binary and passes on the implementation.
Imports do not create provenance; stale provenance cannot influence or block
export; current live and resumable names/directories round trip. Native state,
path-context behavior, command nonexecution, incomplete-observation rejection
and exclusive private publication remain covered. Discarded row metadata has
a general irrelevance theorem. The full foreground Linux verifier, required
builds, semantic coverage and commit hooks pass. Mutation checks demonstrate
that the new proof/IO bindings catch regressions. Commit the verified step.

Outcome: the assembled Linux verifier passes all 470 live assertions, including
33 interchange checks, all 63 shim checks and semantic coverage of all 354 pure
definitions. The independent assembled review finds no blockers. The original
binary fails eight new assertions; a well-typed metadata mutation fails the
generalized proof and ten unit guards. Evidence, limits and the source-gate
bookkeeping correction are recorded in `SCRATCHPAD.md`.

## Step 2 — publish and close

Publish to main, inspect hosted checks, and remove worker worktrees/branches
after checking all accepted changes are integrated and no unique work remains.
Append the completion record, archive this spec, and commit/push closure.

Exit: intended changes are committed and pushed, the checkout is clean, and
the report distinguishes proved guarantees, exercised behavior and limitations.
