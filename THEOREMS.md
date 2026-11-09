# Verification guarantees

Lean checks the session model, shared event driver, terminal model and command policies.
The statements below are an index; each linked declaration gives its exact
hypotheses. Runtime behavior is covered by IO suites and source gates.
[Manifest.lean](Manifest.lean) states the headline theorems over `Spec` definitions and
holes for the program's parts, [Claims](Theorems/Claims.lean) proves them of the program, and
`./lake test` runs `lake comparator` to check that the proofs match the statements.

## Core contracts

| Area | Guarantee | Proofs |
|---|---|---|
| Checkpoints | Saving a live state and loading it restores its quiesced state. Accepted checkpoints can be saved and loaded again exactly. | [Checkpoint](Linger/Session/Proofs/Checkpoint.lean): `loadBytes_saveBytes_live`, `loadBytes_resave` |
| Resume | A daemon resumed from any bytes on disk boots a terminal a live session can hold; after any event trace its screen stays repaintable, its tab ruler fits, and its next checkpoint loads back with the parser quiesced. | [Session](Linger/Session/Proofs/Session.lean): `liveReachableVt_resumeVt`, `run_resume_vt_shape`, `run_resume_load_save` |
| Session events | Arbitrary event traces preserve state invariants, and input from one client leaves other clients' records unchanged. A read-only client's keystrokes change neither the state nor the pty, and whatever bytes it sends, however chunked, leave the terminal and the labels unchanged and cause only messages to it, its own disconnection or a checkpoint. | [Session](Linger/Session/Proofs/Session.lean): `run_wf`, `run_bytes_isolates`, `onMsg_input_readonly`, `run_readonly` |
| Listing rows | A listing row is named by its socket file; the daemon's reply cannot rename it. A saved session whose end record says its program ended shows `✓` for status 0 and `!` otherwise, as does one a peer lists that way; any other status a peer reports for a saved session shows as resumable. | [Listing](Linger/Display/Proofs/Listing.lean): `rowFields_name`, `rowStatus_ended`, `rowStatus_remote_saved` |
| Event driver | Every finite batch completes with session bounds and renderable terminal structure preserved, assuming each external operation returns a typed result without an uncaught exception. Disconnects and checkpoint failures are permitted outcomes. | [Driver](Linger/Session/Proofs/Driver.lean): `run_total_safe` |
| Failure feedback | Effects execute in order; feedback precedes queued input and strictly decreases in depth. Failure feedback cannot request exit, and no events execute after exit. | [Driver](Linger/Session/Proofs/Driver.lean): `effects_in_order`, `run_execution`, `feedback_strictly_decreases`, `handle_feedback_keeps_alive`, `run_exited` |
| Terminal input | Arbitrary byte streams preserve cursor and parser bounds and renderable grid structure. | [State](Linger/Terminal/Proofs/Vt/State.lean): `Good.feed`; [Renderable](Linger/Terminal/Proofs/Vt/Renderable.lean): `renderable_feed` |
| Terminal controls | Outside a pending UTF-8 sequence, DEL and the C0 controls the model ignores leave the terminal unchanged, except as OSC payload data and just after ESC within a DCS, SOS, PM or APC body. | [Vt](Linger/Terminal/Proofs/Vt.lean): `step_del_inert`, `step_c0_inert` |
| Repeat counts | Scroll and tab counts saturate at the screen, and one SU adds at most the region's height to history; every CSI repeat applies its step at most a screen-measured number of times. | [Vt](Linger/Terminal/Proofs/Vt.lean): `csiDispatch_scroll_saturates`, `csiDispatch_tab_saturates`, `csiDispatch_su_history`; [State](Linger/Terminal/Proofs/Vt/State.lean): `repeatAtMost_eq_repeat` |
| Focus reports | A program that enabled focus reporting hears that it gained focus when a client that can type attaches to a session nobody could type into, and that it lost focus when the last such client leaves. A watcher's departure causes no report, nor does anything for a program that did not enable it. | [Session](Linger/Session/Proofs/Session.lean): `onMsg_attach_focus`, `closeClient_focus`, `closeClient_watcher`, `focusEffects_off` |
| Request replies | One read from a connection builds at most one info, history or screen reply, or control resize, however many requests it carries. A message the session does not know is refused and changes nothing; every `info` reply reports the protocol level and version. | [Session](Linger/Session/Proofs/Session.lean): `step_bytes_one_reply`, `onMsg_unknown`, `infoFields_protocol` |
| Program end | When the program ends, every attached or waiting client is told how it ended, then the status a shell would report, and the daemon exits last, after saving the last screen as the program left it and deleting nothing, so the session stays listed as a result until `kill` discards it. `info` reports an exit code, a signal and an unseen ending with distinct fields. A name's end record reads back as written, and once a session has taken the name a reader always hears an answer from it; a reader that does not hold the name hears the same answer whenever it hears one. | [Session](Linger/Session/Proofs/Session.lean): `step_ended_reports`, `step_childExited_keeps`, `outcomeFields_injective`; [Record](Linger/Session/Proofs/Record.lean): `decode_encode`, `answer_isSome`, `settled_answer` |
| Starting a session | `start` takes a name exactly when no live or saved session holds it, and its daemon's report of what it did reads back as written. | [Start](Linger/Session/Proofs/Start.lean): `plan_take_iff`, `decode_encode` |
| Transport | Arbitrary chunking of a well-formed encoded stream preserves messages and order. | [Wire](Linger/Session/Proofs/Wire.lean): `decode_encode_chunked` |
| Ownership | Every active daemon or offline reader holds both resource locks. Sharing either resource excludes simultaneous ownership across arbitrary acquisition, release and reuse. | [Claim](Linger/Session/Proofs/Claim.lean): `reachable_protected`, `at_most_one_owner`, `claim_free` |
| Buffers | Reachable input and output buffers stay within their retained-byte caps. | [Buf](Linger/Session/Proofs/Buf.lean): `reachableIn_bound`, `reachableOut_bound` |
| Screen restoration | Replay reconstructs the selected grid, tab ruler, retained scrollback, cursor, modes, pen, scroll region, character sets and screen selection, and leaves any receiver quiesced. | [Grid](Linger/Terminal/Proofs/Render/Grid.lean): `restore_grid_any`; [Tabs](Linger/Terminal/Proofs/Render/Tabs.lean): `restore_tabs_any`; [Scrollback](Linger/Terminal/Proofs/Render/Scrollback.lean): `restore_sb_any`; [PendingWrap](Linger/Terminal/Proofs/Render/PendingWrap.lean): `restore_cursor_any`; [Modes](Linger/Terminal/Proofs/Render/Modes.lean): `restore_modes_any`, `restore_pen_any`; [Sticky](Linger/Terminal/Proofs/Render/Sticky.lean): `restore_sticky_any`, `restore_quiesced_any` |
| Incremental replay | Each step preserves the complete repaint stream and respects its byte budget; positive budgets make progress and terminate. | [Replay](Linger/Terminal/Proofs/Replay.lean): `start_faithful`, `next_faithful`, `next_bounded`, `next_progress`, `drain_start` |
| Text output | Capture, history, `info` replies and plain listing rows encode no C0, DEL or C1 control character beyond their own line and field separators. | [History](Linger/Terminal/Proofs/Render/History.lean): `screenText_text`, `history_text`; [Session](Linger/Session/Proofs/Session.lean): `infoText_text`; [Listing](Linger/Display/Proofs/Listing.lean): `humanRow_text` |
| Terminal handback | Cleanup establishes canonical parser, modes, character sets, screen selection, pen and empty title for receivers at least two rows tall. | [Sticky](Linger/Terminal/Proofs/Render/Sticky.lean): `leave_canonical_all` |
| Status and titles | Classification matches the status predicates, summaries count attention exactly, and attention is the final title segment. | [Status](Linger/Display/Proofs/Status.lean): `classify_iff`, `summary_exact`; [Title](Linger/Display/Proofs/Title.lean): `compose_attention_last` |

## Command policies

| Area | Guarantee | Proofs |
|---|---|---|
| Entry point | Empty arguments show help; `attach`/`a` without a target opens the chooser in the requested read-only or writable mode; named commands retain their exact arguments. | [Entry](Linger/App/Proofs/Entry.lean): `route_bare_help`, `route_selector_iff`, `route_session_argv` |
| Session targets | Validation preserves exact names and SSH destinations; distinct accepted names cannot alias through validation. | [Name](Linger/Target/Proofs/Name.lean): `check_eq_some_iff`, `check_no_alias`; [Remote](Linger/Target/Proofs/Remote.lean): `parseTarget_exact`, `parseTarget_name_valid` |
| Remote commands | Quoting preserves every argument, including empty strings and shell metacharacters, in the literal POSIX shell model. | [Remote](Linger/Target/Proofs/Remote.lean): `command_argv`, `shellQuote_roundtrip` |
| Remote hosts | Validation accepts exactly clean, duplicate-free host lists and preserves their contents. | [Remote](Linger/Target/Proofs/Remote.lean): `checkHosts_ok_iff` |
| Command operands | Every attach or capture argv linger builds for itself reads back as its exact target; without `--`, no name starting with `-` reads back as itself, and every such name but `--` is refused. | [Remote](Linger/Target/Proofs/Remote.lean): `targetArgs_targetOperands`, `targetArgs_option_ne`, `targetArgs_option` |
| Environment | An unset or empty SHELL starts `sh` and a nonempty one runs unchanged; only a nonempty HOME configures remote hosts; a resume runs in its saved directory, else in a nonempty HOME, else nowhere; read-only views always keep the detach key, which LINGER_NO_DETACH_KEY, set to any value, disables for writable attach. | [Env](Linger/Os/Proofs/Env.lean): `shellOf_absent`, `shellOf_set`, `remotesFile_eq_none_iff`, `resumeDir_saved`, `resumeDir_home`, `resumeDir_absent`, `detachEnabled_readOnly`, `detachEnabled_writable` |
| Selection | Attach choices come from the listing, creation choices are valid, and refresh preserves a still-available selection. | [Picker](Linger/Selector/Proofs/Picker.lean): `step_attach_mem`, `step_create_valid`, `refresh_selected` |
| Interactive fuzzy matching | Successful matches maximize the configured score; ties choose the earliest alignment. | [Fuzzy](Linger/Selector/Proofs/Fuzzy.lean): `alignWith_score_max`, `alignWith_earliest` |
| Input | Bracketed paste emits text only, without control keys. | [Input](Linger/Selector/Proofs/Input.lean): `feed_paste_only_text`, `feed_paste_no_controls` |
| Saved sessions | Parsing yields valid panes; sequential import is idempotent; generated saves round-trip names and directories. Listing and selection share a catalog showing the saved foreground command. | [Resurrect](Linger/Import/Proofs/Resurrect.lean): `parseSave_valid`, `plan_sequential_idempotent`, `renderSave_roundtrip`, `catalogRows_common`, `catalogRows_command`, `selectedPane_exact` |
| Saved pane contents | Capture replay processes at most twice the eight MiB byte limit. A printable saved-command notice adds at most 43 framing bytes and four bytes per command character. Imported checkpoints are live terminal states and round-trip exactly, preserving cwd and command metadata; empty and missing captures remain distinguishable. | [Resurrect](Linger/Import/Proofs/Resurrect.lean): `captureLimit_eq`, `captureBytes_bounded`, `commandNotice_eq`, `commandNotice_bounded`, `checkpoint_notice`, `checkpoint_live`, `checkpoint_roundtrip`, `checkpoint_metadata` |

## Scope

The daemon uses the proved driver with an IO interpreter. Its total-correctness
theorem models external operations with `Except`: each must return, honor its
typed reply and avoid unreported exceptions. No assumption about the frequency
of disconnects or failed saves is needed. This covers finite event batches,
not scheduling or filesystem durability.

Source gates tie the IO adapter to the shared driver; the executable suites, under each
component's `Suites/`, exercise the executable. Ownership assumes cooperating processes,
stable lock inodes that are never unlinked or replaced, and a filesystem honoring
exclusive locking. Both the socket namespace and checkpoint namespace stay locked from
before recovery through final cleanup. A socket pathname alone does not establish this
invariant.
Buffer bounds count retained logical bytes, not allocator or operating-system memory. Allocation
failure, OS termination and failures in the compiler, runtime or C shim remain
outside these proofs.

Terminal fidelity is relative to linger's terminal model and each theorem's
receiver assumptions. Cursor restoration (`restore_cursor_any`) requires origin
mode to be off. Incoming title content and the saved cursor slot are covered by
fixtures. Cleanup clears the title rather than restoring a prior title. Recovery
preserves screen state, not running processes or images.
tmux imports read captured screen and scrollback when the latest save has a
capture archive. Each pane shows its saved foreground command above a fresh shell
prompt; the command is retained as metadata and is never executed.

## Checks

`./lake build Theorems Tests` checks proofs and unit fixtures.
[Contract pins](Theorems/Contracts.lean) restate every theorem cited above, so a
weakened statement fails the build. The [declaration census](Theorems/Coverage.lean)
requires semantic coverage of every definition in a pure module;
[renderer coverage](Verify/Coverage.lean) checks resolved references.
Run `./scripts/verify.sh` for the complete verifier, including generated C ABI,
source gates, formatting, semantic lint, fuzz fixtures and live suites.
