# Verification guarantees

Lean checks the session model, shared event driver, terminal model and command policies.
The statements below are an index; each linked declaration gives its exact
hypotheses. Runtime behavior is covered by IO suites and source gates.

## Core contracts

| Area | Guarantee | Proofs |
|---|---|---|
| Checkpoints | Saving a live state and loading it restores its quiesced state. Accepted checkpoints can be saved and loaded again exactly. | [Checkpoint](Theorems/Checkpoint.lean): `load_save_live`, `load_resave` |
| Session events | Arbitrary event traces preserve state invariants; input from one client leaves other clients' records unchanged. | [Session](Theorems/Session.lean): `run_wf`, `run_bytes_isolates` |
| Event driver | Every finite batch completes with session bounds and renderable terminal structure preserved, assuming each external operation returns a typed result without an uncaught exception. Disconnects and checkpoint failures are permitted outcomes. | [Driver](Theorems/Driver.lean): `run_total_safe` |
| Failure feedback | Effects execute in order; feedback precedes queued input and strictly decreases in depth. Failure feedback cannot request exit, and no events execute after exit. | [Driver](Theorems/Driver.lean): `effects_in_order`, `run_execution`, `feedback_strictly_decreases`, `handle_feedback_keeps_alive`, `run_exited` |
| Terminal input | Arbitrary byte streams preserve cursor and parser bounds and renderable grid structure. | [State](Theorems/Vt/State.lean): `Good.feed`; [Renderable](Theorems/Vt/Renderable.lean): `renderable_feed` |
| Transport | Arbitrary chunking of a well-formed encoded stream preserves messages and order. | [Wire](Theorems/Wire.lean): `decode_encode_chunked` |
| Ownership | Every active daemon or offline reader holds both resource locks. Sharing either resource excludes simultaneous ownership across arbitrary acquisition, release and reuse. | [Claim](Theorems/Claim.lean): `reachable_protected`, `at_most_one_owner`, `claim_free` |
| Buffers | Reachable input and output buffers stay within their retained-byte caps. | [Buf](Theorems/Buf.lean): `reachableIn_bound`, `reachableOut_bound` |
| Screen restoration | Replay reconstructs the selected grid, tab ruler and retained scrollback in the terminal model under the stated receiver conditions. | [Grid](Theorems/Render/Grid.lean): `restore_grid_any`; [Tabs](Theorems/Render/Tabs.lean): `restore_tabs_any`; [Scrollback](Theorems/Render/Scrollback.lean): `restore_sb_any` |
| Incremental replay | Each step preserves the complete repaint stream and respects its byte budget; positive budgets make progress and terminate. | [Replay](Theorems/Replay.lean): `start_faithful`, `next_faithful`, `next_bounded`, `next_progress`, `drain_start` |
| Terminal handback | Cleanup establishes canonical parser, modes, character sets, screen selection, pen and empty title for receivers at least two rows tall. | [Sticky](Theorems/Render/Sticky.lean): `leave_canonical_all` |
| Status and titles | Classification matches the status predicates, summaries count attention exactly, and attention is the final title segment. | [Status](Theorems/Status.lean): `classify_iff`, `summary_exact`; [Title](Theorems/Title.lean): `compose_attention_last` |

## Command policies

| Area | Guarantee | Proofs |
|---|---|---|
| Entry point | Empty arguments show help; session commands retain their arguments. | [Entry](Theorems/Entry.lean): `route_bare_help`, `route_session_argv` |
| Session targets | Validation preserves exact names and SSH destinations; distinct accepted names cannot alias through validation. | [Name](Theorems/Name.lean): `check_eq_some_iff`, `check_no_alias`; [Remote](Theorems/Remote.lean): `parseTarget_exact`, `parseTarget_name_valid` |
| Remote commands | Quoting preserves every argument, including empty strings and shell metacharacters, in the literal POSIX shell model. | [Remote](Theorems/Remote.lean): `command_argv`, `shellQuote_roundtrip` |
| Remote hosts | Validation accepts exactly clean, duplicate-free host lists and preserves their contents. | [Remote](Theorems/Remote.lean): `checkHosts_ok_iff` |
| Selection | Attach choices come from the listing, creation choices are valid, and refresh preserves a still-available selection. | [Picker](Theorems/Picker.lean): `step_attach_mem`, `step_create_valid`, `refresh_selected` |
| Interactive fuzzy matching | Successful matches maximize the configured score; ties choose the earliest alignment. | [Fuzzy](Theorems/Fuzzy.lean): `alignWith_score_max`, `alignWith_earliest` |
| Input | Bracketed paste emits text only, without control keys. | [Input](Theorems/Input.lean): `feed_paste_only_text`, `feed_paste_no_controls` |
| Saved sessions | Parsing yields valid panes; sequential import is idempotent; generated saves round-trip names and directories. Listing and selection use the same catalog. | [Resurrect](Theorems/Resurrect.lean): `parseSave_valid`, `plan_sequential_idempotent`, `renderSave_roundtrip`, `catalogRows_common`, `selectedPane_exact` |

## Scope

The daemon uses the proved driver with an IO interpreter. Its total-correctness
theorem models external operations with `Except`: each must return, honor its
typed reply and avoid unreported exceptions. No assumption about the frequency
of disconnects or failed saves is needed. This covers finite event batches,
not scheduling or filesystem durability.

Source gates tie the IO adapter to the shared driver; [E2E](E2E/) exercises the
executable. Ownership assumes cooperating processes, stable lock inodes that are
never unlinked or replaced, and a filesystem honoring exclusive locking. Both
the socket namespace and checkpoint namespace stay locked from before recovery
through final cleanup. A socket pathname alone does not establish this invariant.
Buffer bounds count retained logical bytes, not allocator or operating-system memory. Allocation
failure, OS termination and failures in the compiler, runtime or C shim remain
outside these proofs.

Terminal fidelity is relative to linger's terminal model and each theorem's
receiver assumptions. Cursor restoration requires origin mode to be off.
Incoming title content and the saved cursor slot are covered by fixtures.
Cleanup clears the title rather than restoring a prior title. Recovery preserves
screen state, not running processes or images.

## Checks

`./lake build Theorems Tests` checks proofs and unit fixtures. The
[declaration census](Theorems/Coverage.lean) requires semantic coverage of every
pure definition; [renderer coverage](E2E/Coverage.lean) checks resolved references.
Run `./scripts/e2e.sh` for the complete verifier, including generated C ABI,
source gates, formatting, semantic lint, fuzz fixtures and live suites.
