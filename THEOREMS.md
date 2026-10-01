# Theorems — the tension ledger

The anchors carry the product's promises; the § rungs name each tension
and the invariant that resolves it, listed before their first proof so
an open tension is on the record. The history behind every row — proof
recipes, break records, measurements, the audits — lives in
`SCRATCHPAD.md` and `specs/archive/`.

## The anchor set

| Anchor | Statement | Theorem |
|---|---|---|
| **A1. A session survives a crash** | a checkpoint round-trips exactly for any state a live session can hold (`Good ∧ Renderable ∧ TabsOk`; the decoder refuses the rest), and the rebuilt byte stream leaves **any** receiver quiesced; cursor position is restored when origin mode is off. A decoded screen is itself live-reachable, so the round trip holds across a second reboot, hypothesis-free, for arbitrary bytes on disk and an arbitrary event trace after | `Resume.resume_quiesced_any`, `Resume.resume_cursor`, `Session.run_resume_load_save` |
| **A2. The daemon cannot be broken by traffic** | no event trace of any length — adversarial clients, hostile pty bytes, any interleaving — breaks a buffer cap, the screen invariant, or one client's isolation from another; structural since the `State` seal (private constructor, capped boot), and covering a resumed daemon's screen from either `vt0` source | `Session.run_wf`, `Session.run_bytes_isolates`, `Session.boot_wf` / `run_boot_wf`, `Session.run_resume_vt_shape` |
| **A3. The transport is invisible** | any re-chunking of any well-formed encoded stream decodes to exactly that stream: same messages, same order, nothing retained, no error | `Wire.decode_encode_chunked` |
| **A4. A session name has one owner** | given the kernel grants at most one `flock` holder, at most one daemon ever unlinks or binds a given name | `Claim.at_most_one_owner` |
| **A5. session attachment is invisible to the terminal it borrows** | both directions receiver-quantified, under each theorem's stated premises. Inbound (`restore`): modes `restore_modes_any`; pen `restore_pen_any`; sticky fields `restore_sticky_any` (`restore_region_any`, `restore_charset_any`, `restore_alt_any` are its projections); screen cells `restore_grid_any` / `restore_grid_reachable` / `Resume.resume_grid` — the selected grid (main or alternate), every height, mid-character receivers included through the reachable wrapper; tab ruler `restore_tabs_any` / `Resume.resume_tabs`; scrollback `restore_sb_any` / `restore_sb_reachable` / `Linger.Core.resume_sb` (as `.toList` — same history, different ring records; `restore_sb_exact` when the budget kept everything, `restore_sb_keeps_of_empty` for the no-history branch, a user-facing decision). Outbound (hand-back): `leave_canonical_all`, including the empty title; `leave_boundary_title` gives the title and parser boundary without a height premise. Inbound title content and the **DECSC slot** remain fixture-carried. Handback establishes a default title; it does not recover the borrowed title. Attaching a session that has history erases the borrowed window's saved lines (`ED 3` — attachment uses the main screen and shares the user's scrollback; conformance entry 11, README §Notes) | see row |

## The rungs

| § | Tension | Invariant | Where |
|---|---------|-----------|-------|
| §Entry | discoverable commands vs implicit terminal behavior | `route_bare_help` sends empty argv to help; `route_selector_iff` selects exactly for `["select"]`; `route_session_argv` preserves other session commands and operands; `route_import_argv` and `route_export_argv` give interchange commands their complete trailing argv | Theorems/Entry.lean |
| §Frame | evolvable protocol vs simple daemon | `decode (encode m) = ([m], ∅)`; unknown tag skips exactly its frame | Theorems/Wire.lean |
| §Chunk | arbitrary TCP/pty chunking vs stateful parsers | `feed (a ++ b) = feed b ∘ feed a`; output framing is faithful and bounded (`outputMsgs_faithful`, `outputMsgs_bounded`, `outputMsgs_payloads`); accepted info replies preserve every byte in bounded frames, with overflow refused before any prefix (`infoMsgs_faithful`, `infoMsgs_bounded`, `infoMsgs_refused`) | Theorems/Wire.lean, Theorems/Vt.lean, Theorems/Session.lean |
| §Stream | fragmentation vs one parsed conversation | any re-chunking of a well-formed stream feeds back to exactly that stream (`decode_encode_chunked`; §Frame and §Chunk are its special cases) | Theorems/Wire.lean |
| §Bound | unbounded queues under load | every buffer has a structural cap preserved by `step`; nothing to fill | Theorems/Wire.lean, Theorems/Vt.lean, Theorems/Session.lean |
| §Total | adversarial bytes vs no crashes ever | `Vt.step`/`feed` total (no `partial`, grep-checked); `Good` preserved for any byte; dimensions preserved (`dims_feed`) | Theorems/Vt.lean |
| §Detach | sessions outlive clients | a zero-client session still advances; `.closed id` removes every record for that id (`step_closed_clients`) while preserving the screen and labels, and may checkpoint. Once any decoded prefix requests the sender's close or exit, every suffix preserves its exact state and effects (`feedMsgs_stopped_suffix`; `feedMsgs_after_close` and `feedMsgs_after_exit` are instances). The runtime handles an event's effect feedback before already queued events; after exit it consumes no queued events | Theorems/Session.lean, E2E/Attach.lean, E2E/Delivery.lean |
| §Restore | reboot-resume vs corrupt/stale state files | `load (save s) = some s` for every live state (`load_save_live`); `load` total on arbitrary bytes, and what it accepts is `Good`, `Renderable`, the ruler the width of the screen, and live-reachable (`load_good`, `load_renderable`, `load_tabsOk`, `load_live`) — refusals, not clamps. Scrollback row widths are deliberately unchecked (`Vt.resize` legitimately leaves old-width rows). On-disk tag pinned: `save_tag`, `"LNGR"` v1 only (the pre-rename reader is at `e1ac562`) | Theorems/Checkpoint.lean |
| §Name | user-chosen names vs filesystem paths | sanitized names can't escape the socket dir (no `/`, `..`-prefix, NUL, empty); `@` reserved for `name@host`; sanitization preserves exactly the valid names and is idempotent | Theorems/Name.lean |
| §Remote | trusting remote `ls` output vs local listing safety | parser total, garbage-tolerant; §Name carries through; display fields scrubbed of control bytes. Host validation accepts exactly clean, duplicate-free lists and returns them unchanged (`checkHosts_ok_iff`) | Theorems/Remote.lean |
| §Isolate | many clients on one session vs per-client framing | `.bytes id` leaves every *other* client's record (and decoder) bit-identical | Theorems/Session.lean |
| §Row | a list row's identity vs an unreliable `info` reply | a row's name is the sanitized socket filename alone; the reply can neither change it nor smuggle a second one in | Theorems/Listing.lean |
| §Claim | one session name vs many daemons racing for it | *given* the kernel grants ≤1 `flock` holder, ≤1 daemon ever unlinks or binds that name | Theorems/Claim.lean |
| §Replay | one saved byte stream must recreate the live screen | parser quiesced for any receiver (`restore_quiesced`, `restore_u8_zero`); cursor exact end to end (`restore_cursor`, given `Good` and DECOM off); the byte layer (`utf8_feed`, `cellText_feed`, `crlf_feed`); the pen (`penSgr_feed`, every sequence under the parser's 16-parameter cap, `penSgr_under_cap`); the cells closed via §Renderable plus the grid walk | Theorems/Render.lean, Tests/Render.lean |
| §Paint | simple replay proofs vs copying growing output prefixes | `rowAnsi_eq_rowAnsiLinear` proves exact function equality for the compiler substitution; `rowAnsiLinear_exact` preserves every emitted byte and the final pen for any row and starting pen. Existing replay and size guarantees therefore apply to the compiled painter | Linger/Core/Render.lean, Theorems/Render.lean |
| §Delivery | a complete repaint can exceed a client's output buffer | a cursor captured at attach denotes exactly `Render.restore`; each advance emits a bounded prefix and retains its exact suffix, with a strictly decreasing work measure for positive budgets. The complete walk preserves every byte in order while retaining shared rows and at most one rendered row or title chunk | Theorems/Replay.lean, Theorems/Session.lean, E2E/Delivery.lean |
| §Handback | the program owned the terminal vs the shell gets it back | `Render.leaveAnsi` is a **constant**, written in interactive cleanup. `leave_canonical_all`: any receiver at least two rows tall ends parser-ground, default modes, whole scroll region, ASCII charsets with G0 shifted in, main screen current, pen reset and title empty (`leave_canonical` is the hypothesis-free parser+modes half). The cursor position is the receiver's business (clamped park), pinned by `E2E/Attach.lean`. Clearing the title establishes a default without querying or stacking the borrowed title | Linger/Core/Render.lean, Linger/Runtime/Client.lean, E2E/Attach.lean |
| §Terminal | a child needs a terminal that answers, linger owns none | one bounded pure transducer owns a documented query profile: the VT projection, scanner and ordered reply stream are roster-independent (`Terminal.feed_vt`, `Session.ptyOut_reply_roster_independent`); an owned query is answered exactly once, everything else is byte-for-byte passthrough (`apc_passthrough`, `sixel_passthrough`); the scanner is capped and over-cap becomes passthrough (`feed_bounded`); no reply can commit a line into the child (`feed_replies_noNl` — terminal-reply command injection, closed); chunking-invariant (`feed_append`) | Theorems/Terminal.lean, Theorems/Session.lean |
| §Renderable | the painter expresses fewer grids than the emulator reaches | the emulator never stores a shape a repaint cannot reproduce (`renderable_step`/`renderable_feed`/`renderable_resize`/`renderable_quiesce`, from `renderable_init`); `LiveReachableVt` is the least predicate closed under those and containing every screen the decoder's door accepts (`LiveReachableVt.ofDecoded` — a `Good` premise is provably unsound, counterexample in SCRATCHPAD.md); the decoder establishes it from disk too (`Vt.ofDecoded_renderable`, `Checkpoint.load_renderable`); lifted to the daemon by `Session.run_vt_renderable` and `run_resume_vt_shape` | Linger/Core/Vt.lean, Theorems/Vt.lean |
| §Status | one glyph per listing row vs seven conditions | `classify_iff` equates classification with the independent legend predicates; `cover`, `disjoint`, `classify_sound` and `classify_unique` derive the partition. Every state is reachable; icons and names are injective and names are clean | Theorems/Status.lean |
| §Title | visible cross-session attention vs an uninterrupted terminal stream | composition omits empty parts; the title payload excludes terminal controls and fits the OSC parser cap (`compose_parts`, `payload_safe`, `ansi_payload_bound`, `ansi_ends`). Updates wait for parser-ground and complete UTF-8 (`update_waits`, `update_requires_boundary`). The existing VT observer is chunking-invariant, keeps no history, and preserves its dimensions and parser/screen invariants (`observe_append`, `observe_no_history`, `observe_dims`, `observe_invariants`) | Theorems/Title.lean, Theorems/TerminalTitle.lean, Theorems/Vt.lean, E2E/Title.lean |
| §Resume | the product's own promise: crash, reboot, reattach | §Restore ∘ §Replay, stated twice — over `save`'s input and over `load`'s output (`resume_grid_of_load`, `resume_tabs_of_load`, `resume_sb_of_load`: any byte string that loads, no other hypothesis) — and lifted to the daemon over its own `vt0` (`Session.run_resume_vt_shape`, `run_resume_load_save`) | Theorems/Resume.lean, Theorems/Session.lean |
| §Import | foreign save records vs distinct session identities, directory-only restoration and safe error display | successful parsing gives a nonempty list with canonical, distinct names and NUL-free directories (`parseSave_valid`); ignored pane metadata and valid saved commands cannot affect parsed panes (`parseRow_metadata_irrelevant`); planning preserves records and order and skips existing names (`mem_plan`, `plan_order`); adding planned names to the snapshot makes a sequential rerun empty (`plan_sequential_idempotent`); diagnostics exclude C0, DEL and C1 and preserve already printable text (`diagnostic_printable`, `diagnostic_eq_self`) | Theorems/Resurrect.lean, E2E/Recipes.lean |
| §Interchange | current native state vs discarded foreign metadata | valid native names have reversible encoding (`encodeName_reversible`); every successful generated save parses back to exactly its names and directories for any home (`renderSave_roundtrip`); the executor exports current native fields without retained foreign source | Theorems/Resurrect.lean, E2E/Interop.lean |
| §Select | fuzzy emphasis and explicit creation vs an exact session identity | alignment accepts exactly the filter language, maximizes score and chooses earliest ties (`align_isSome_iff_matches`, `align_score_max`, `align_earliest`); emphasis preserves shared text/status and marks the chosen target positions (`highlightedPresentation_projection`, `highlightedPresentation_existing_marked_iff`); matching preserves snapshot order (`visible_order`, `items_existing_prefix`); existing selections retain original targets (`step_attach_mem`); creation uses an exact valid target absent from the snapshot (`step_create_valid`); only acceptance acts on the highlighted row (`step_attach_iff`, `step_create_iff`); refresh retains query and surviving targets (`refresh_query`, `refresh_selected`) and bounds the cursor (`refresh_valid`) | Theorems/Fuzzy.lean, Theorems/Picker.lean, E2E/Manager.lean |
| §Input | split keyboard bytes and pasted commands vs deliberate selection | one byte produces at most one physical key (`feed_length`); UTF-8 prefixes retain at most three bytes (`stored_bound`, `feed_storage_bound`); delivered text excludes controls (`feed_text_valid`); paste emits only text and survives incomplete input (`feed_paste_only_text`, `feed_paste_sticky`, `flush_paste`); the separate binding preserves every byte's selector meaning (`Key.feed_byte_bindings`), and a timeout never accepts (`Key.flush_no_accept`) | Theorems/Input.lean, Theorems/Key.lean, E2E/Manager.lean |

The terminal libraries separate decoded keys from picker actions. Binding
contracts fix the original control-byte and navigation behavior, including
paste suppression and Escape timeout. Replay fidelity and progress belong
to the VT toolkit; following-frame capacity belongs to `Buf`, with
`followingCap_iff` identifying the largest safe allowance. Generic title safety
belongs to `Terminal.Title`; `update_nonempty_iff` permits emission exactly
at a complete parser and UTF-8 boundary. Sanitized session composition stays
in `Title`. Independent library and proof targets have no session or OS
imports, with source gates enforcing their complete import boundaries.
Verification record: `specs/archive/terminal-libraries.md`.

The reusable fuzzy library admits separate case and scoring policies.
`alignWith_isSome_iff_sublist`, `alignWith_marks_length` and `alignWith_spells`
characterize the language and original scalar positions for every
configuration. `alignWith_score_max` and `alignWith_earliest` quantify
over arbitrary integer weights, including zero and negative bonuses.
`alignWith_scoring_irrelevant` makes acceptance independent of scoring.
`alignWith_smart_sensitive` and `alignWith_smart_insensitive` establish exact
result equality with the selected case policy, chosen by ASCII capitals in
the query. `align_default` fixes the original insensitive policy and all
three weights explicitly, so changing record defaults cannot silently move
that contract. The existing default alignment contracts remain in force.
Verification and publication record: `specs/archive/fuzzy-library.md`.

The CSI collector preserves omitted parameters, saturates numeric parameters
and rejects overflow at the existing parameter cap. `csiPush_of_lt`,
`csiPush_of_ge`, `csiFinish_omitted` and `csiFinish_overflow` state those
transitions; `csiOk_of_liveReachable` connects their numeric preconditions to
every live or decoded terminal. Vertical absolute positioning shares the
origin-aware cursor operation (`csiDispatch_vpa_exact`,
`csiDispatch_vpa_in_region`). Ordinary importers can only use checked terminal
operations; `Tests.VtApi` checks that raw cell and parser mutators are hidden.

Mode-setting and mode-resetting sequences apply every collected parameter in
order. `setModes_append` specifies composition of batches; `setModes_one`
preserves each existing single-mode transition, and the mode-batch invariants
preserve `Good`, grid shape and tab shape. Footprint claims about origin and
screen selection inspect the whole parameter list, since a later parameter can
change either one. Receiver-quantified replay guarantees keep their existing
assumptions and conclusions.

Renderer stream predicates lift from fragments through rows, CRLF joining and
grids (`StreamPred.rowAnsi`, `StreamPred.joinCRLF`, `StreamPred.gridAnsi`).
The existing parser-boundary, mode-preservation and quiescence proofs share
these traversals without adding receiver-shape premises.
`csi_digits_feed_eq` gives the exact collector state after any natural-number
digit stream, starting in CSI with a zero current parameter and no pending
UTF-8 continuation: only that parameter and its presence flag change, with
saturation at 65535. `csi_digits_tail_eq` carries that equation through a final
byte in 0x40–0x7E, with no intermediate byte and fewer than 16 prior parameters.
Private, ignore and subparameter flags remain explicit. Mode changes, cursor
placement, tab clearing and history clearing use the same contract, while
their original endpoint assumptions remain unchanged.

Checkpoint acceptance also establishes parser quiescence (`load_accepted`,
`load_quiescent`). `load_save_append` rejects every nonempty suffix, and
`load_resave` gives exact state and metadata equality after resaving any
accepted input. These claims do not imply that decoding hostile lengths uses
bounded memory or time.

The checkpoint reader validates dimensions before reading screen rows.
Length-prefixed collections check their declared count before decoding elements;
screen rows check the sum of encoded run counts before expanding them. The
guarded decoder equals the original reader chain on every byte list, including
accepted noncanonical encodings and unread suffixes (`rVt_unbounded`).
`rList_bounded`, `rRLE_bounded` and `ofDecoded_bounds` connect the early guards
to the existing acceptance contract. Source gates pin rejection before
allocation, because equal mathematical results alone cannot establish execution
order. Historical row widths, encoded payload size and overall decoding time
remain outside these bounds.

The grid theorems cover the active grid with either main or alternate screen
selected. They do not state equality of both buffers and every saved field at
once. The cursor-position guarantee assumes origin mode off. The title and saved
cursor slot have fixture coverage; accepted checkpoint titles may contain
controls that replay deliberately sanitizes. Matching the active grid alone
does not establish that the next glyph behaves identically: pending wrap needs
its own continuation check.

Deferred wrap is reconstructed at the active, DECSC-saved and
alternate-screen-stashed positions by reprinting a representable margin glyph.
`pendingAnsi_feed_eq`, `savedPendingAnsi_feed_eq` and
`cursorPendingAnsi_feed_eq` give the complete state effects of those bytes;
`pending_tail_frames` proves that the reprints preserve painted cells and
history. `Replay.start_faithful` includes all three stages in the captured
stream before following application bytes. Socket checks compare the next-glyph
screen with uninterrupted output for narrow and wide cells with combining marks.
Decoded pending cursors away from the margin remain a representability limit.
Resizing clears deferred wrap in all three cursor slots
(`Vt.resize_clears_pending`), so leaving the alternate screen cannot resurrect
a wrap associated with the old geometry.

The existing receiver-quantified endpoint guarantees retain their original
premises and conclusions. The internal `restore_grid_of_paint` and
`restore_sb_of_paint` helpers now require the canonical paint context needed
for existing-cell reprints; their callers establish it from the original
endpoint assumptions.

`Render.reprint_margin` supplies the character-level frame for restoring pending
wrap. On a Good, Renderable receiver with ASCII charsets, wrapping enabled,
insertion disabled and no wrap already pending, reprinting the canonical margin
glyph with its own pen and all stored marks changes only the cursor to the last
column with wrap pending. The equality preserves the entire remaining state,
including both grids, saved fields, parser state and scrollback. It covers
single- and double-width glyphs. `Render.reprintAnsi_feed_eq` connects the
complete CUP/SGR/glyph/SGR byte sequence to that frame. Equivalence under
arbitrary future input remains outside these contracts.

`Render.cellText_cursor_margin_any_acc` connects a cell's actual UTF-8 bytes to the
pending cursor. For a positive-width canonical cell ending at the margin,
feeding its base and marks sets the last-column cursor with pending wrap,
preserving its other fields. The receiver needs a ground parser, no pending
UTF-8 bytes and the painting modes, but no grid invariant or initial accumulator
value: missing cells, saturated mark lists and stale accumulators cannot
invalidate this cursor claim. `Render.cellText_ground_need_any_acc` separately
proves that every cell's emitted bytes finish in ground with no pending bytes.
ASCII retains a stale accumulator; a fresh multibyte lead overwrites it.
These statements let the existing cursor guarantees retain their original
receiver scope while grid preservation uses the stronger frame above.

## Reading a row

Each § is proved for *all* inputs, not sampled. Proofs use compiled
evaluation nowhere; the unit tests in `Tests/` do, because they pin
concrete behavior where evaluation is the point. Each row was
**break-verified** — the code deliberately broken once to watch the
theorem catch — with the break recorded in `SCRATCHPAD.md`. The
machine-layer rows hold over whole event *traces*: `run_eq_foldl` identifies the
state/effect fold over the events the runtime actually consumes, and
`run_wf` / `run_bytes_isolates` lift §Bound + §Total + §Isolate to the
daemon's whole life. `run_preserves` supplies the general state-invariant
lift. This trace algebra does not imply that the runtime processes queued
events after exit or meets a wall-clock deadline.

`feedMsgs_induct` lifts predicates of the entire state/effect accumulator,
with handler obligations only after the sender lookup and stop guards
succeed. `feedMsgs_append` preserves the exact accumulator across batch
boundaries, including ordered effects and pending stops.
`onMsg_vt_preserves` and `step_vt_preserves` lift terminal predicates closed
under the resize and feed operations the session actually performs. Existing
`Good` and live-reachability proofs instantiate these contracts.

## Frames

`frame_X : v.op = { v with field := … }` states an operation's whole
footprint once, so field invariance follows by projection. `frame_grid_foldl`
lifts exact grid-only updates through a fold; `frame_insertLines` and
`frame_deleteLines` cover the complete operations without shape premises.
`frame_eraseScreen` also specifies that mode 3 clears history and all other
modes retain it. Printing's existing `off_print` observation supplies its
unchanged-field projections. Conditional dispatch retains operation-specific
claims because reset, mode and screen transitions have different footprints.

Bundling selected fields would omit the rest of the state; splitting `Vt`
would not express these per-operation footprints. Those bounded negative
results remain recorded in the worklog. A frame whose right-hand side projects
the operation's own updated grid does not specify that grid's contents.
Positive specifications such as `scrollUpIn_rows`, `scrollUpIn_sb_push` and
`lineFeed_scroll` remain separate.

## Coverage

Every user-facing README promise maps to a theorem, a named test, a
stated limitation, or a settled non-goal — never to nothing; a new
promise (or § / anchor) lands with its mapping. That is a review
discipline. `Theorems/Coverage.lean` resolves every explicit `def` in
`Linger/Core/` and `Tools/` to its fully qualified environment
constant and requires that exact constant in a theorem type. Lean's parser
handles layout, escaped names, strings and nested comments; the census tracks
namespace and section scopes and rejects unsupported scope commands. Standard
private-name resolution and expression traversal connect source definitions
to theorem types. Quoted commands do not change its scope or declare names.
Comments, proof bodies and colliding basenames cannot satisfy it.

After the program builds, `E2E/Coverage.lean` classifies renderer and replay
definitions referenced outside their own module in the compiled `Main`
module closure. Resolved references cover qualified, relative, opened and
renamed names without mistaking strings, quotations or local names for calls.
Target module provenance excludes private helpers with a renderer's logical
name. Compiled fixtures check these cases and the declaration census.
This inventories definition bodies in the program's modules; it does not
claim every inventoried call executes. Each referenced operation has an
explicit backing entry:

| stream | backing |
|---|---|
| `Replay.start`, `Replay.next` | `start_faithful`, `next_faithful`, `next_bounded`, `next_progress`, `drain_start`: exactly the renderer stream (see A5 for receiver scope) |
| renderer stages used by `Replay.start` | components of `start_faithful` / `drain_start`; no additional standalone receiver claim |
| `Render.rowAnsi`, `Render.scrollbackAnsi` | `rowAnsi_len_add_crlf_le_cost`, `scrollbackAnsi_le`; `rowAnsi_eq_rowAnsiLinear` certifies the compiled row implementation; cursor storage is bounded by `next_storage` / `steps_storage` |
| `Render.leaveAnsi` | `leave_canonical`, `leave_canonical_all` |
| `Render.history` | `history_framing`, `history_lines`, `history_records`, `history_screenText_suffix` |
| `Render.screenText` | `screenText_framing`, `screenText_lines`, `screenText_records` |
| `Render.utf8s` | `utf8s_no_ctl`, `utf8s_no_esc`, `utf8s_no_esc_bel`, `Session.utf8s_no_frame` |
| `Render.digits` | `digits_range`, `Terminal.noNl_digits` |
| `Render.dropTrailingBlanks` | `dropTrailingBlanks_subset`, used by `Listing.humanRow_printable` |

A newly referenced definition fails the gate until classified; an entry for a
definition no longer referenced fails too.

The shared queue allowance is `Buf.followingCap`, outside the VT toolkit.
`followingCap_front` and `followingCap_frame` bound both uses.
`followingCap_iff` proves that, when the front queue and one frame each fit,
the allowance admits exactly the debts that fit alongside both. A source gate
ties the daemon's following queue to this buffer policy.

`Session.onMsg_attach_snapshot` captures the immutable snapshot at the pure attach
event. `Replay.start_faithful` and `drain_start` equate the cursor's full
denotation to `Render.restore` for every snapshot. `next_faithful` gives an exact
prefix/suffix equality; `next_progress` proves termination for positive budgets,
including empty stage transitions. `steps_storage` bounds serialized literal
and pending bytes after any finite prefix, without summing the rendered sizes of
the screen grids. The shared snapshot, allocator capacity and object overhead
are outside that serialized-byte measure.

The runtime holds one optional cursor per connection. Previously queued bytes
precede it; subsequent live output and exit notifications follow it. Its two
socket buffers share `outbufCap`, reserving a frame using the actual wire
encoder's overhead. Active and retired transports together use `maxClients`.
Logical close feeds `.closed` immediately and gives any retained transport a
fixed Nat deadline that repeated closes cannot extend. Polling expires retired
transports; shutdown makes a final bounded drain attempt and releases leftovers.
Source gates and real socket/PTY regressions connect these IO operations to the
pure claims. Delivery requires the peer to finish draining before its applicable
deadline and remain within the live-output allowance. The deadline is enforced
by a cooperative poll loop, without a hard real-time guarantee.

## Entry-point boundaries

`Name.sanitize_eq_self_iff` identifies the canonical names with `Name.Valid`.
`sanitize_eq_self_of_valid` preserves every valid name, and
`sanitize_idempotent` means separate entry paths can sanitize independently
without changing the target on a second pass. Output safety alone would permit
renaming an already-valid session.

§Entry defines the dispatch contract for the unified executable.
`route_bare_help` sends empty argv to help. `route_selector_iff` selects exactly
for `["select"]`; `route_select_operands` forwards extra operands to the session
backend, which rejects them. `route_session_argv` preserves every other
session command and operand; `route_ls_argv` and
`route_daemon_argv` state the listing and internal re-exec cases. Import keeps
all trailing arguments for its executor to validate (`route_import_argv`);
export does the same (`route_export_argv`).
Routing takes only argv; `Main` consumes this pure decision without inspecting
terminal streams. Source gates pin all four dispatch branches and the running
executable's path. The selector's executor requires terminal input and output.
`E2E.Manager` checks bare help and explicit selection with all four stream
combinations, explicit listing in a terminal, help and invalid operands. Both
manager suites exercise absolute invocation with no `linger` on PATH and with
a PATH impostor. These contracts state behavior, not a proof of a UI preference.

§Select supports the manager's pure selection model.
`align_isSome_iff_matches` proves that an alignment exists exactly for a query
accepted by the filter. `align_marks_length` gives one mark per original Unicode
scalar; `align_spells` proves that the marked characters spell the folded query.
The independent `Walk` semantics assigns four points at a word boundary,
eight for adjacency and minus one for each skipped character before completion.
`align_score_max` bounds every legal alignment's score, and `align_earliest`
chooses the true-first lexicographically earliest mask among every equally
scoring legal alignment. One suffix-table certificate proves both adjacency
contexts, including completeness on failure. These are semantic guarantees;
the work bound is established by the recurrence and performance checks.

`rowPieces_nameSpan` locates the name inside the shared row.
`highlightedPresentation_existing_marked_iff` connects each displayed scalar
to the chosen alignment for the actual query and exact target, excluding badge,
padding and metadata. `highlightedPresentation_projection` preserves every
plain character and status; `highlightedPresentation_existing_humanRow` retains
the listing's bytes. `highlightedPresentation_creation` leaves the creation
choice unmarked. `emphasizeCells_at` sets each scalar's emphasis from its own
match or any following zero-width mark attached to its cell. This propagates
an accent-only match back to the base before the terminal prints it;
`emphasizeCells_projection` preserves all characters and status styles.
Source gates tie the executor to these stages, the query, displayed rows,
ANSI underline, selection reverse, status palette and viewport clipping.
Live terminal checks inspect the resulting cells. Scores never enter the
list-order or attachment paths.
`matches_iff_sublist` specifies ASCII-case-insensitive subsequence matching;
other Unicode characters remain exact. `visible_order` and `mem_visible`
retain the listing's order and original targets. `parseListing_valid` rejects
noncanonical names, duplicate targets and control characters across the entire
snapshot; `parseListing_records` preserves every complete original name record.
`parseSnapshot_complete` retains that validated name list together with its
complete metadata. `presentation_existing_humanRow` proves that each existing
selector row has exactly the listing's plain bytes, before selection markers
and viewport clipping. Both renderers consume the same `rowPieces`, whose
`rowPieces_styles` theorem limits status styling to the badge. `style_palette`
restricts that styling to the terminal's basic foreground palette and dim
default foreground; `terminalListing_plain` preserves plain listing output.
Metadata changes cause a repaint even when the target list stays unchanged.
The selectable `Item` distinguishes an existing target from a labelled creation
choice. `items_existing_prefix` keeps all matching existing rows first.
`mem_items_create` characterizes creation exactly: the query (or the shared
attach default for an empty query) must be canonical and printable, with a
nonempty remote suffix if present, and absent from the snapshot. An exact
existing target therefore has no duplicate creation row. `step_create_valid`
carries name safety and the unchanged target through acceptance;
`step_init_empty` positively establishes creation of the default session from
an empty listing.

`validTarget_iff` connects the internal target check to `Name.Valid`,
printable characters and the optional nonempty remote suffix in both
directions. `Listing.nameWidth_le_iff` makes the shared name column the least
width sufficient for every name in the snapshot. It measures Unicode scalar
count; terminal-cell clipping remains the executor's separate width operation.

`init_valid` and `step_stay_valid` bound the cursor and query through keyboard
transitions. `refresh_query` and `refresh_candidates` keep the query while
replacing the validated snapshot. `refresh_selected` preserves the exact target
when it remains available, even if rows move or a creation choice becomes an
existing session. `refresh_missing` clamps the former row when the target
vanishes; `refresh_valid` establishes cursor bounds even from a forged cursor.
`step_attach_iff`, `step_create_iff` and `step_attach_mem`
require Enter on the corresponding highlighted row; existing attachment still
requires an original candidate, even for a forged out-of-range state. When
there are no selectable rows, Enter stays editable. `step_cancel` produces only
cancellation. Snapshot absence is not an atomic creation claim: a session
can appear or disappear before the existing attach upsert runs. These theorems
specify the choices; they do not prove that a UI preference is desirable.

§Input supports the finite keyboard decoder. Its modes store only bounded
UTF-8 prefixes and a finite CSI parameter recognizer. `feed_text_valid`
restricts text to printable scalar characters; `feed_ascii`, `feed_special`
and `feed_control` specify physical keys. Unnamed C0 controls retain their
byte identity. `feed_paste_only_text` suppresses non-text keys in bracketed
paste, while `feed_paste_sticky` and `flush_paste` preserve paste suppression
across malformed or incomplete sequences. `flush_emits` limits timeout
output to Escape after a lone escape outside paste; `flush_no_enter`
excludes Enter. UTF-8 decoding is connected to Lean's native `String.fromUTF8?`
validator and a single-scalar result; the validator itself is not proved here.
The internal `deliver_mem` contract preserves the recognized key's identity
and characterizes exactly which keys the paste/printability filter permits.

`Tools.Key.ofInput` owns selector bindings. `Key.feed_byte_bindings` fixes the
meaning of all possible idle bytes against the original concrete defaults.
`Key.ofInput_control_iff` characterizes the complete control binding set;
`Key.feed_ctrl_r` keeps Ctrl-R inert. `Key.feed_paste_no_commands` and
`Key.flush_no_accept` carry the decoder's paste and timeout guarantees through
the adapter to selector actions. Generic input and its proofs import no
application bindings; ordinary-import API checks and exact import gates
enforce this boundary.

`Manager.Picker` consumes these models. Source gates pin the parser, selectable
rows, their displayed order, labels and cursor positions, initial states,
keyboard and refresh transitions, decoder, character widths, fixed poll
descriptors and unchanged attach argv for both row kinds. They also pin input
handling before snapshot replacement, drawing before the next poll, and the
listing's process and reader ownership. Decoder ties preserve byte traversal
order and carry both returned state and emitted keys through the adapter,
including timeout handling, to dispatch. The CLI consumes the same pure default
session name as the picker. `E2E.Manager` checks the creation
label, terminal restoration, resize, subprocess handoff, paste, exact selection,
creation and refresh scheduling through real ptys. A cleanup exception still
restores termios; attachment begins after leaving the picker screen.
These are IO observations, not theorem statements.

`Remote.checkHosts_ok_iff` specifies validation after the CLI's intended
trimming and comment filtering. It preserves the complete normalized list,
including order, and accepts every duplicate-free list whose hosts exclude
C0 and DEL. Source gates tie its success/error result to `resolveRemotes`,
the overview command and ordered `listRemote` traversal. These contracts do
not establish hostname resolution or SSH liveness.

The same status vocabulary drives prompt and title summaries.
`attentionCounts_mem` characterizes each displayed group as its exact positive
count, restricted to unread output, reported failed exits and unknown sessions.
`summary_exact`, `summary_omits_zero` and `summary_alphabet` fix group order,
omit zero counts and restrict the output to decimal counts, shared glyphs and
spaces. `linger status` observes local info without acknowledging unread output.
Its IO executor uses nonblocking connection attempts and one shared reply
deadline; incomplete replies and busy sockets remain unknown. These timing
and socket-lifetime claims are exercised by `E2E.Status`, not proved by the
pure counting theorems. The fish recipe delegates to that command and preserves
the preceding command's exit status.

The title observer shares the session's VT parser. `observe_esc_intermediates`
and `observe_escInter_pending` keep every unfinished ESC intermediate sequence
closed to injected titles, without a length bound. `observe_del_boundary`
preserves pending ESC/CSI sequences across DEL, including accumulated parameters.
`step_escInter_final_boundary` proves that a final byte completes the sequence;
it does not assume the application will eventually send one.

§Detach preserves a session when its client leaves; §Handback specifies the
terminal state returned to the caller. The selector temporarily uses an alternate
screen, restoring it before session attachment. It returns to selection after every attach
exit. `E2E.Manager` checks that default across successful attachment, failure
and real detach, with terminal restoration before each attachment.
Synthetic failure and handoff checks invoke the same executor through an
isolated recorder; public dispatch and live attach/detach use the actual binary.

The native configurations for Ghostty, kitty and WezTerm each launch
`linger select`. `E2E.Recipes` inspects the three native configuration
settings; documented launch syntax supports them. SSH keepalives remain native
transport configuration. These observations do not prove GUI behavior, network
recovery time or a preference for a configuration format.

§Import supports `linger import`. `parseSave_valid` gives
nonempty, distinct names that already satisfy `Name.Valid`, plus NUL-free
decoded directories. `parseRow_command_valid` requires the saved command's
sentinel and absence of NUL. `parseRow_metadata_irrelevant` proves that replacing
the ignored pane metadata and any valid saved command leaves the complete row
result unchanged. The parser discards those fields: neither `Pane` nor the plan
retains them. `parseRow_other` proves that non-pane records contribute no pane,
regardless of their remaining fields.
`mem_plan` preserves each original pane and requires its name to be absent from
the snapshot. `plan_order` preserves their order, and `plan_names_unique` carries
parsing's distinctness through filtering.

`plan_sequential_idempotent` says a later snapshot containing the old names and
all planned names produces no actions. It does not prove atomic name claiming,
concurrent imports or successful IO. `Manager.Resurrect` preflights every saved
directory and obtains a successful listing before executing the plan.
Source gates pin its parser, plan, supplied executable and constant shell-creation argv,
`linger run NAME true`; the saved directory supplies the child's cwd.
`E2E.Recipes` checks those actual arguments, ignored saved commands, failure
ordering, executable identity, home fallback, relative paths, and untouched
existing shells on reruns against real daemons.

§Interchange supports `linger export SAVE`. `common` projects panes to session
names and directories. Source line numbers, commands, window composition and
native terminal state are outside this projection. `encodeName_reversible`
covers the complete valid native name alphabet. The reserved `linger=` prefix
and dot-to-tilde encoding survive tmux session naming; `projectName_native`
recovers the name at window zero, pane zero. `projectName_reserved_topology`
rejects other indices in this namespace, while `projectName_foreign` preserves
the established projection for ordinary imported names.

`renderSave_roundtrip` concerns the actual serialized text returned by
`renderSave`, including its delimiters and fields. Successful generation
reparses that text and checks the resulting common fields. A NUL home in that
check prevents home expansion; `parseSave_home_independent` then supplies the
same result for every real home. `renderSave_valid` carries nonemptiness,
distinct names, name validity and NUL-free directories through this certificate.
`renderSave_directories` separately enforces the supported literal-directory
repertoire. These are guarantees about successful results, not a claim that
every input is encodable. Executable acceptance fixtures and an isolated
tmux-resurrect restore/save exercise useful successful cases.

Only names and directories cross the import boundary into
native session creation; discarded titles, window state and valid saved
commands cannot affect that projection. The import record's line number is
used only for diagnostics. Native terminal state remains in its existing codec.

The manager observes live process directories and decodes resumable checkpoints
in the caller's native path context. It exports only those current fields through
`renderSave`. Export does not normalize home or consult a foreign source file.
Source gates and `E2E.Interop` bind the IO implementation to this policy.
The suite checks the absence of persisted source, independence from obsolete
provenance, common-field round trips, incomplete observations, failed imports,
home/path resolution and exclusive file publication. These
checks cover IO behavior; the pure theorems do not establish filesystem
durability, an atomic snapshot across daemons, or the behavior of another
program. Native checkpoint data and companion pane-content archives are outside
the interchange guarantee.

`diagnostic_printable` excludes C0, DEL and C1 from displayed importer errors;
`diagnostic_eq_self` preserves already printable text, including spaces and
Unicode. `Manager.Resurrect` applies that function only when displaying an
error, leaving the original names, paths and arguments intact. It captures both
creation-child streams and includes their failure text in that same diagnostic.
Source gates tie the executor to these boundaries; `E2E.Recipes` checks controls
in rejected names, missing directories, missing save paths and failed child
output, along with silent successful imports and stop-on-failure ordering.
These laws do not claim visual unambiguity for arbitrary Unicode or prove
filesystem IO.

The source gates constrain each manager executor's imports. Interchange uses
the session listing and checkpoint reader plus standard account/environment IO;
the selector uses its pure policies and terminal interface.
They keep the manager out of the session library and VT toolkit; only `Main`
composes those library commands with selection and interchange.
Theorems cannot inspect IO call sites or prove a preference for
a source language; each decision is supported by its semantic contract and the
checks at the boundary where that contract is used.

## Concurrency

The daemon's session state has one application-level owner: its `poll` loop.
No signal handler mutates that state. Lean and libuv may still run worker
threads, so the post-fork shim paths avoid allocation and stdio formatting;
a source gate checks their call boundary. What remains in the session machine
is interleaving — §Chunk per connection, §Isolate across
clients — and two processes meeting at a file: §Restore, with atomic
tmp+`rename` writes and a `load` that is total and accepts only `Good ∧
Renderable` screens, so a racing reader sees the old file or the new
one. Two clients typing at once interleave into the pty — inherent, and
no theorem claims otherwise. The pty size is owned by the newest
attached real terminal (`resizeOwned_owner_only`); a control `linger
resize` never overrides an attached sizer (`controlResize_never_overrides`),
applies exactly once with nobody attached (`controlResize_applies`), is
inert at the same size (`controlResize_same_size`), and always answers
(`controlResize_replies`). Every emitted pty resize uses the resulting emulator
dimensions (`onMsg_resizePty_agrees`), and a repeated effective size preserves
the complete emulator (`resize_same_effective`). The shared resize transition
and successful label edits mark persistent state dirty, so quiet edits reach
the periodic checkpoint (`resize_changed_dirty`, `onMsg_labels_changed_dirty`).

Disconnects caused by malformed input use the same save decision as EOF:
the old roster determines whether removing a client needs a checkpoint
(`closeClient_last_dirty`, `step_bytes_malformed_close`).
A failed save marks that state dirty again without producing an immediate
retry (`step_checkpointFailed`); the next periodic attempt still obeys the
checkpoint cadence. `E2E.Resume.checkpointRetry` exercises that feedback through
the real effect interpreter with no intervening output.

Periodic checkpoint time uses natural-number milliseconds from Lean's monotonic
clock. Less than one interval of elapsed time emits no save and preserves dirty
state and the previous attempt clock (`step_tick_before_interval`); any periodic
save implies at least that interval elapsed (`step_tick_checkpoint_elapsed`).
Both claims quantify over arbitrary clocks, including a tick older than the
previous attempt. Source gates tie the direct Nat clock and daemon tick to these
proofs. Detach and explicit-save events retain their separate behavior.

## The agent verbs

A capture cannot be forged and parses positionally: `screenText_framing`
/ `screenText_lines` / `screenText_records` (line *k* IS `rowText` of
row *k*), `history_records`, and `history_screenText_suffix` (a capture
is exactly the transcript's tail). A capture is a look — deliberately:
`onMsg_screen` is `rfl` (any smuggled side effect breaks it), with
`screen_marks_seen` / `screen_behind_zero` the user-facing halves;
`info` and `history` deliberately do not mark seen. `behind` is honest
over the daemon's whole life: `onMsg_outSeq` (traffic cannot forge
activity) and `run_lookSeq_le` (the read mark never overtakes). The
runtime half is pinned by `E2E/Agent.lean`.

An `info` prefix is not a completed answer. The CLI accepts fields only after
`done`; disconnects, timeouts, malformed frames or records, invalid UTF-8,
explicit refusal and excess reply bytes return an error. A connected peer with
a failed answer still has a live listing row, so querying it cannot unlink its
socket. These IO contracts are checked by `E2E.Agent`, separately from the pure
listing identity theorem. Remote attach sanitizes the session name before SSH
joins the remote command for shell execution (`E2E.Remote`).

The info producer and CLI share the whole-answer byte policy. An accepted
answer emits bounded frames followed by exactly one `done`; concatenating
their payloads recovers every serialized field and label
(`onMsg_info_faithful`, `onMsg_info_bounded`). Exceeding the policy emits only
a bounded refusal, without a partial answer or completion (`infoMsgs_refused`).
A source gate ties the CLI accumulator to the proved producer's cap. Individual
records and UTF-8 characters may span frames, so text decoding follows payload
concatenation.

## Session identity: the kernel plus a proof

`Daemon.serve` takes an exclusive `flock` on `<name>.lock` *before*
probing and holds it for the process's life. No staleness timeout exists
anywhere, because the kernel drops a dead holder's lock; the lock file
is deliberately never unlinked. §Claim states the exclusion the only way
an OS primitive admits — conditionally: `Exclusive` (≤1 holder) names
exactly what the kernel is trusted for, `Guarded` (only the holder
unlinks or binds) is proved. `E2E/Robust.lean` pins the correspondence:
a stale socket plus eight concurrent starts yields exactly one daemon.

## Network filesystems: where the guarantees stop

Local storage is assumed. Unix sockets don't bind on NFS and a shared
socket directory would cross-delete live sockets — the defaults
(`$XDG_RUNTIME_DIR` or `/tmp/linger-$UID`) avoid it; a network
`LINGER_DIR` is unsupported. `flock` is unreliable over NFS, so §Claim
does not hold there. Checkpoints default under `$HOME`, so the state
directory is namespaced by hostname — also the right semantics, since
machine B's process world is not on machine A. Writes are safe anywhere
(atomic rename; `load` yields `none` on a torn or foreign file, never a
screen the emitter cannot repaint). An explicit `LINGER_DIR` is taken
verbatim.

## The conformance profile — what `restore`/`leave` assume of the receiver

Emitter/parser self-consistency theorems: the model receiver is our own
`Vt`, so each entry is a behaviour the stream depends on and a place a
nonconforming terminal would diverge from the proof — the honest
boundary of the claim. The pty suites remain the only evidence about
real terminals.

1. Absolute cursor addressing with origin mode off (`?6l`; `CSI H`,
   `CHA` from the screen origin).
2. Deferred wrap at the right margin with autowrap on (`?7h`); a margin
   cell's combining mark attaches to that cell.
3. An SGR parameter cap of at least sixteen; `penSgr` emits ≤8 per
   sequence (`penSgr_under_cap`) so none is dropped.
4. `ED 2` clears the screen and touches nothing else.
5. Charset designations are honoured (`ESC ( B`, `ESC ) B`, `SI`).
6. DECSTBM sets the scroll region and refuses a region of fewer than
   two lines.
7. The alt-screen switch (`?1049`) stashes and blanks at the current
   size, and resets the region.
8. The final cursor address is clamped by the receiver
   (`CSI 999 ; 1 H`), which is why the stream carries no dimensions
   for it.
9. A leading `ST` (`ESC \`) resynchronises a receiver caught in a
   string state.
10. UTF-8 decoding returns to a clean state after each complete glyph;
    the stream ends ESC-initiated.
11. `CSI 3 J` — a divergence, not an assumption. xterm's `ED 3` erases
    saved lines only; ours clears the screen too, which is unobservable
    where we emit it (an `ED 2` is four bytes earlier). `E3=\E[3J` is
    declared by xterm, tmux, alacritty, foot, vte and the linux
    console, and ncurses' `clear(1)` sends `CSI H CSI 2 J CSI 3 J` —
    our order. Emitted **only when there is history to put there**; a
    terminal without it keeps the previous occupant's history — benign.
    (`E2E/Attach.lean` step 11 pins the order; `Tests/Render.lean`'s
    guard fixtures pin both branches.)
12. A printed line that scrolls off the top of a whole-screen region
    enters the terminal's own scrollback — the only way to put one
    there, and how the history stage works. No scrollback means no
    history: the same benign failure as 11.

## What these theorems do not settle

- **§Total covers the emulator, not the runtime.** `Linger/Runtime/*`
  is `IO`; its definitions no longer need `partial def`, but the explicit
  event loop has no termination theorem.
  Runtime correctness rests on the live suites in `E2E/`; the
  pure/impure line is enforced by `tests/gates.sh`.
- **§Bound measures retained logical bytes.** The socket output buffers share
  `outbufCap`, and the child's input queue has `ptyInCap`. Each allowance is
  4 MiB; excessive live output disconnects that client, while excessive input
  drops the newest whole frame. `Theorems/Buf.lean` proves that the stored byte
  sequence is exactly the debt (`bufNoRetain`), with content claims and
  whole-lifetime bounds via `reachableIn_bound`/`reachableOut_bound`.
  `bufOffer_rejected` preserves the entire queue on refusal, so keeping its
  size while discarding or reordering its contents cannot satisfy the contract.
  This does not measure ByteArray allocator capacity, list/object overhead, the shared
  terminal snapshot or OS buffers. Private representations and source gates
  connect the proved operations to their IO consumers.
- **§Restore restores the codec's state, not the shell's world**:
  screen, scrollback, modes, labels, cwd — not the process tree.
  Scrollback replays to the byte budget (`sbReplayBytes = 262144`, about
  three thousand plain 80-column lines); the counted-cost bounds are
  proved (`sbRows_budget`, `rowAnsi_len_le_cost`). The complete emitted history
  stage is bounded by `sbReplayBytes + 2 * rows + 19`
  (`scrollbackAnsi_le_cost`, `scrollbackAnsi_le`), including its framing and
  control sequences. The screen paint is a separate term.
- **A screen paint can exceed the output allowance.** Replay advances under
  backpressure from shared screen rows, retaining one rendered row or bounded
  title chunk at a time. `E2E.Delivery` exercises accepted paints exceeding the
  allowance, FIFO live output and child-exit tails. A closing peer that does not
  finish within its drain grace can lose its remaining transport tail.
- **Images are passed through, not modelled**: the emulator parks in
  the string state and accumulates nothing, so §Bound holds for
  megabytes of base64; nothing is stored, so `restore` cannot replay
  them — the application's redraw does (pinned by `E2E/Graphics.lean`;
  reasons in README Graphics and the AGENTS.md non-goal).
