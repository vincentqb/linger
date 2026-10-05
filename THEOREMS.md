# Verification guarantees

Lean checks the pure session model, terminal model and command policies.
The statements below are an index; each linked declaration gives its exact
hypotheses. Runtime behavior is covered by IO suites and source gates.

## Core contracts

| Area | Guarantee | Proofs |
|---|---|---|
| Checkpoints | Saving a live state and loading it restores its quiesced state. Accepted checkpoints can be saved and loaded again exactly. | [Checkpoint](Theorems/Checkpoint.lean): `load_save_live`, `load_resave` |
| Session events | Arbitrary event traces preserve state invariants; input from one client leaves other clients' records unchanged. | [Session](Theorems/Session.lean): `run_wf`, `run_bytes_isolates` |
| Terminal input | Arbitrary byte streams preserve cursor and parser bounds and renderable grid structure. | [State](Theorems/Vt/State.lean): `Good.feed`; [Renderable](Theorems/Vt/Renderable.lean): `renderable_feed` |
| Transport | Arbitrary chunking of a well-formed encoded stream preserves messages and order. | [Wire](Theorems/Wire.lean): `decode_encode_chunked` |
| Ownership | At most one daemon owns a session name, assuming exclusive kernel locking and the guarded claim protocol. | [Claim](Theorems/Claim.lean): `at_most_one_owner` |
| Buffers | Reachable input and output buffers stay within their retained-byte caps. | [Buf](Theorems/Buf.lean): `reachableIn_bound`, `reachableOut_bound` |
| Screen restoration | Replay reconstructs the selected grid, tab ruler and retained scrollback in the terminal model under the stated receiver conditions. | [Grid](Theorems/Render/Grid.lean): `restore_grid_any`; [Tabs](Theorems/Render/Tabs.lean): `restore_tabs_any`; [Scrollback](Theorems/Render/Scrollback.lean): `restore_sb_any` |
| Incremental replay | Each step preserves the complete repaint stream and respects its byte budget; positive budgets make progress and terminate. | [Replay](Theorems/Replay.lean): `start_faithful`, `next_faithful`, `next_bounded`, `next_progress`, `drain_start` |
| Terminal handback | Cleanup establishes canonical parser, modes, character sets, screen selection, pen and empty title for receivers at least two rows tall. | [Sticky](Theorems/Render/Sticky.lean): `leave_canonical_all` |
| Status and titles | Classification matches the status predicates, summaries count attention exactly, and attention is the final title segment. | [Status](Theorems/Status.lean): `classify_iff`, `summary_exact`; [Title](Theorems/Title.lean): `compose_attention_last` |

## Command policies

| Area | Guarantee | Proofs |
|---|---|---|
| Entry point | Empty arguments show help; session commands retain their arguments. | [Entry](Theorems/Entry.lean): `route_bare_help`, `route_session_argv` |
| Remote hosts | Validation accepts exactly clean, duplicate-free host lists and preserves their contents. | [Remote](Theorems/Remote.lean): `checkHosts_ok_iff` |
| Selection | Attach choices come from the listing, creation choices are valid, and refresh preserves a still-available selection. | [Picker](Theorems/Picker.lean): `step_attach_mem`, `step_create_valid`, `refresh_selected` |
| Fuzzy matching | Successful matches maximize the configured score; ties choose the earliest alignment. | [Fuzzy](Theorems/Fuzzy.lean): `alignWith_score_max`, `alignWith_earliest` |
| Input | Bracketed paste emits text only, without control keys. | [Input](Theorems/Input.lean): `feed_paste_only_text`, `feed_paste_no_controls` |
| Saved sessions | Parsing yields valid panes; sequential import is idempotent; generated saves round-trip names and directories. Listing and selection use the same catalog. | [Resurrect](Theorems/Resurrect.lean): `parseSave_valid`, `plan_sequential_idempotent`, `renderSave_roundtrip`, `catalogRows_common`, `selectedPane_exact` |

## Scope

These proofs establish properties of pure functions. They do not prove syscalls,
filesystem durability, scheduling or the runtime's IO execution. Source gates
tie runtime consumers to proved policies; [E2E](E2E/) exercises the executable.
Ownership relies on local kernel locking. Buffer bounds count retained logical
bytes, not allocator or operating-system memory. No theorem guarantees that the
whole process cannot crash: allocation failure, OS termination and failures in
the compiler, runtime or C shim are outside these proofs.

Terminal fidelity is relative to linger's terminal model and each theorem's
receiver assumptions. Cursor restoration requires origin mode to be off.
Incoming title content and the saved cursor slot are covered by fixtures.
Cleanup clears the title rather than restoring a prior title. Recovery preserves
screen state, not running processes or images.

## Checks

`./lake build Theorems Tests` checks proofs and unit fixtures. The
[declaration census](Theorems/Coverage.lean) requires semantic coverage of every
pure definition; [renderer coverage](E2E/Coverage.lean) checks resolved references.
Run `./tests/e2e.sh` for the complete verifier, including generated C ABI,
source gates, formatting, semantic lint, fuzz fixtures and live suites.
