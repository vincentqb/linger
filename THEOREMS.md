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
| **A5. linger is invisible to the terminal it borrows** | both directions receiver-quantified, no hypothesis on the receiver. Inbound (`restore`): modes `restore_modes_any`; pen `restore_pen_any`; sticky fields `restore_sticky_any` (`restore_region_any`, `restore_charset_any`, `restore_alt_any` are its projections); screen cells `restore_grid_any` / `restore_grid_reachable` / `Resume.resume_grid` — the selected grid (main or alternate), every height, mid-character receivers included; tab ruler `restore_tabs_any` / `Resume.resume_tabs`; scrollback `restore_sb_any` / `restore_sb_reachable` / `Linger.Core.resume_sb` (as `.toList` — same history, different ring records; `restore_sb_exact` when the budget kept everything, `restore_sb_keeps_of_empty` for the no-history branch, a user-facing decision). Outbound (hand-back): `leave_canonical_all`. Still fixture-carried, named so the list is not "just the cells": the window **title** and the **DECSC slot**. The one thing linger does that it cannot undo: attaching a session that has history erases the borrowed window's saved lines (`ED 3` — linger shares the user's scrollback and never enters the alt screen; conformance entry 11, README §Notes) | see row |

## The rungs

| § | Tension | Invariant | Where |
|---|---------|-----------|-------|
| §Frame | evolvable protocol vs simple daemon | `decode (encode m) = ([m], ∅)`; unknown tag skips exactly its frame | Theorems/Wire.lean |
| §Chunk | arbitrary TCP/pty chunking vs stateful parsers | `feed (a ++ b) = feed b ∘ feed a`; output framing is faithful and bounded (`outputMsgs_faithful`, `outputMsgs_bounded`, `outputMsgs_payloads`); accepted info replies preserve every byte in bounded frames, with overflow refused before any prefix (`infoMsgs_faithful`, `infoMsgs_bounded`, `infoMsgs_refused`) | Theorems/Wire.lean, Theorems/Vt.lean, Theorems/Session.lean |
| §Stream | fragmentation vs one parsed conversation | any re-chunking of a well-formed stream feeds back to exactly that stream (`decode_encode_chunked`; §Frame and §Chunk are its special cases) | Theorems/Wire.lean |
| §Bound | unbounded queues under load | every buffer has a structural cap preserved by `step`; nothing to fill | Theorems/Wire.lean, Theorems/Vt.lean, Theorems/Session.lean |
| §Total | adversarial bytes vs no crashes ever | `Vt.step`/`feed` total (no `partial`, grep-checked); `Good` preserved for any byte; dimensions preserved (`dims_feed`) | Theorems/Vt.lean |
| §Detach | sessions outlive clients | a zero-client session still advances; `.closed id` removes every record for that id (`step_closed_clients`) while preserving the screen and labels, and may checkpoint. The runtime feeds intentional closes back too; after exit it consumes no queued events (`E2E.Attach.closeFeedback`) | Theorems/Session.lean, E2E/Attach.lean |
| §Restore | reboot-resume vs corrupt/stale state files | `load (save s) = some s` for every live state (`load_save_live`); `load` total on arbitrary bytes, and what it accepts is `Good`, `Renderable`, the ruler the width of the screen, and live-reachable (`load_good`, `load_renderable`, `load_tabsOk`, `load_live`) — refusals, not clamps. Scrollback row widths are deliberately unchecked (`Vt.resize` legitimately leaves old-width rows). On-disk tag pinned: `save_tag`, `"LNGR"` v1 only (the pre-rename reader is at `e1ac562`) | Theorems/Checkpoint.lean |
| §Name | user-chosen names vs filesystem paths | sanitized names can't escape the socket dir (no `/`, `..`-prefix, NUL, empty); `@` reserved for `name@host` | Theorems/Name.lean |
| §Remote | trusting remote `ls` output vs local listing safety | parser total, garbage-tolerant; §Name carries through; display fields scrubbed of control bytes | Theorems/Remote.lean |
| §Isolate | many clients on one session vs per-client framing | `.bytes id` leaves every *other* client's record (and decoder) bit-identical | Theorems/Session.lean |
| §Row | a list row's identity vs an unreliable `info` reply | a row's name is the sanitized socket filename alone; the reply can neither change it nor smuggle a second one in | Theorems/Listing.lean |
| §Claim | one session name vs many daemons racing for it | *given* the kernel grants ≤1 `flock` holder, ≤1 daemon ever unlinks or binds that name | Theorems/Claim.lean |
| §Replay | one saved byte stream must recreate the live screen | parser quiesced for any receiver (`restore_quiesced`, `restore_u8_zero`); cursor exact end to end (`restore_cursor`, given `Good` and DECOM off); the byte layer (`utf8_feed`, `cellText_feed`, `crlf_feed`); the pen (`penSgr_feed`, every sequence under the parser's 16-parameter cap, `penSgr_under_cap`); the cells closed via §Renderable plus the grid walk | Theorems/Render.lean, Tests/Render.lean |
| §Handback | the program owned the terminal vs the shell gets it back | `Render.leaveAnsi` is a **constant**, written in `Client.attach`'s `finally` so every exit path emits it. `leave_canonical_all`: any receiver at least two rows tall ends parser-ground, default modes, whole scroll region, ASCII charsets with G0 shifted in, main screen current, pen reset (`leave_canonical` is the hypothesis-free parser+modes half). The cursor position is the receiver's business (clamped park), pinned by `E2E/Attach.lean`. Still leaked outbound: the window title | Linger/Core/Render.lean, Linger/Runtime/Client.lean, E2E/Attach.lean |
| §Terminal | a child needs a terminal that answers, linger owns none | one bounded pure transducer owns a documented query profile: the VT projection, scanner and ordered reply stream are roster-independent (`Terminal.feed_vt`, `Session.ptyOut_reply_roster_independent`); an owned query is answered exactly once, everything else is byte-for-byte passthrough (`apc_passthrough`, `sixel_passthrough`); the scanner is capped and over-cap becomes passthrough (`feed_bounded`); no reply can commit a line into the child (`feed_replies_noNl` — terminal-reply command injection, closed); chunking-invariant (`feed_append`) | Theorems/Terminal.lean, Theorems/Session.lean |
| §Renderable | the painter expresses fewer grids than the emulator reaches | the emulator never stores a shape a repaint cannot reproduce (`renderable_step`/`renderable_feed`/`renderable_resize`/`renderable_quiesce`, from `renderable_init`); `LiveReachableVt` is the least predicate closed under those and containing every screen the decoder's door accepts (`LiveReachableVt.ofDecoded` — a `Good` premise is provably unsound, counterexample in SCRATCHPAD.md); the decoder establishes it from disk too (`Vt.ofDecoded_renderable`, `Checkpoint.load_renderable`); lifted to the daemon by `Session.run_vt_renderable` and `run_resume_vt_shape` | Linger/Core/Vt.lean, Theorems/Vt.lean |
| §Status | one glyph per listing row vs seven conditions | the seven states partition the observation space: `cover`, `disjoint`, `classify_sound` + `classify_unique`, `reachable`, `icon_injective` / `name_injective`, `name_clean` | Theorems/Status.lean |
| §Resume | the product's own promise: crash, reboot, reattach | §Restore ∘ §Replay, stated twice — over `save`'s input and over `load`'s output (`resume_grid_of_load`, `resume_tabs_of_load`, `resume_sb_of_load`: any byte string that loads, no other hypothesis) — and lifted to the daemon over its own `vt0` (`Session.run_resume_vt_shape`, `run_resume_load_save`) | Theorems/Resume.lean, Theorems/Session.lean |

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
once. Cursor equality currently assumes origin mode off. The title and saved
cursor slot have fixture coverage; accepted checkpoint titles may contain
controls that replay deliberately sanitizes. Matching the active grid alone
does not establish that the next glyph behaves identically: pending wrap needs
its own continuation check.

`Render.reprint_margin` supplies the character-level frame for restoring pending
wrap. On a Good, Renderable receiver with ASCII charsets, wrapping enabled,
insertion disabled and no wrap already pending, reprinting the canonical margin
glyph with its own pen and all stored marks changes only the cursor to the last
column with wrap pending. The equality preserves the entire remaining state,
including both grids, saved fields, parser state and scrollback. It covers
single- and double-width glyphs. Connecting the emitted restoration bytes to this
frame is a separate obligation; this helper alone does not prove end-to-end
continuation.

`Render.cellText_cursor_margin` connects a cell's actual UTF-8 bytes to the
pending cursor. For a positive-width canonical cell ending at the margin,
feeding its base and marks sets the last-column cursor with pending wrap,
preserving its other fields. The receiver needs a quiesced parser and the
painting modes, but no grid invariant: missing cells and saturated mark lists
cannot invalidate this cursor claim. This allows the existing cursor guarantees
to retain their original receiver scope while grid preservation uses the
stronger frame above.

## Reading a row

Each § is proved for *all* inputs, not sampled. Proofs use compiled
evaluation nowhere; the unit tests in `Tests/` do, because they pin
concrete behavior where evaluation is the point. Each row was
**break-verified** — the code deliberately broken once to watch the
theorem catch — with the break recorded in `SCRATCHPAD.md`. The
machine-layer rows hold over whole event *traces*: `run` names the fold
the runtime's poll loop performs (`run_eq_foldl` pins it exactly), and
`run_wf` / `run_bytes_isolates` lift §Bound + §Total + §Isolate to the
daemon's whole life.

## Frames

`frame_X : v.op = { v with field := … }` states an operation's whole
footprint once, so any field invariance is one rewrite — in force for
the thirty leaf operations whose result is a syntactic record update.
Compositions (`print`) and folds (`csiDispatch`, the erase/insert/delete
family) keep per-field lemmas; both limits were measured, not assumed.
Two rejected alternatives, recorded: *bundling* fields fixes only the
fields we happened to need where a frame is complete, and *splitting*
`Vt` cannot capture invariance that is per-operation. A frame says what
an operation leaves alone, never what the written fields become — the
positive specifications (`scrollUpIn_rows`, `scrollUpIn_sb_push`,
`lineFeed_scroll`) are separate content.

## Coverage

Every user-facing README promise maps to a theorem, a named test, a
stated limitation, or a settled non-goal — never to nothing; a new
promise (or § / anchor) lands with its mapping. That is a review
discipline. `Theorems/Coverage.lean` resolves every explicit pure-core
`def` to its fully qualified environment constant and requires that exact
constant in a theorem type; comments, proof bodies, formatting and colliding
basenames cannot satisfy it. `E2E/Coverage.lean` independently classifies
every byte stream the runtime emits:

| stream | backing |
|---|---|
| `Render.restore` | proved receiver-quantified (see A5) — not the title or the DECSC slot |
| `Render.leaveAnsi` | `leave_canonical`, `leave_canonical_all` |
| `Render.history` | `history_framing`, `history_lines`, `history_records`, `history_screenText_suffix` |
| `Render.screenText` | `screenText_framing`, `screenText_lines`, `screenText_records` |
| `Render.utf8s` | `utf8s_no_ctl`, `utf8s_no_esc`, `utf8s_no_esc_bel`, `Session.utf8s_no_frame` |

A new emitter fails the gate until classified; an entry for a stream the
runtime no longer emits fails too.

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
- **§Bound bounds our buffers, not the OS's.** Both runtime byte queues
  are `Linger.Core.Buf`, capped at 4 MiB: `outbufCap` disconnects a slow
  client, `ptyInCap` drops the newest whole frame. `Theorems/Buf.lean`
  proves the arithmetic — caps bound what is owed, memory equals the
  debt (`bufNoRetain`), each bound paired with a content claim, and
  whole-lifetime via `reachableIn_bound`/`reachableOut_bound`. That the
  daemon *uses* `Buf` is the `private` seal plus a grep gate, not a
  theorem.
- **§Restore restores the codec's state, not the shell's world**:
  screen, scrollback, modes, labels, cwd — not the process tree.
  Scrollback replays to the byte budget (`sbReplayBytes = 262144`, about
  three thousand plain 80-column lines); the counted-cost bounds are
  proved (`sbRows_budget`, `rowAnsi_len_le_cost`). The complete emitted history
  stage is bounded by `sbReplayBytes + 2 * rows + 19`
  (`scrollbackAnsi_le_cost`, `scrollbackAnsi_le`), including its framing and
  control sequences. The screen paint is a separate term.
- **The screen paint is the unbudgeted term**: worst-case pens at
  400×100 emit ~4.5 MB, past `outbufCap` before any scrollback.
  Delivery must advance under backpressure while retaining the complete
  screen; dropping paint bytes would give up replay fidelity.
- **Images are passed through, not modelled**: the emulator parks in
  the string state and accumulates nothing, so §Bound holds for
  megabytes of base64; nothing is stored, so `restore` cannot replay
  them — the application's redraw does (pinned by `E2E/Graphics.lean`;
  reasons in README Graphics and the AGENTS.md non-goal).
