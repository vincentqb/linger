# restore-conformance — restore works into any client, and the proofs say so

Status: active
Updated: 2026-08-17
Predecessor: `specs/terminal-contract.md` (Steps 1–3 complete; its Step 4 is carried
here in a different shape, and its Step 5 archival gate is carried unchanged)

## Where this stands — read this first

**Next step:** the **alt-screen branch** of `restore_grid_any`, and it is now narrow.
`alt_switch_entry` + `modeSet_feed_eq` are its hard half (the switch fires and hands the
second paint a blank grid of the receiver's shape, region reset, cursor homed). What is
missing is only the **modes** at the switch — `insert`/`wrap`/`origin`, which sit between the
prologue that sets them and the switch that inherits them, across the main paint. **Do it by
adding an `org` field to `Matches`** (one line per rung via `modes_print'`/`frame_setCol`, ten
rungs), threading it through `paint_range`/`paint_rows`/`gridAnsi_writes_grid`; then the alt
branch composes exactly like the main one. The alternative (`MMap id (gridAnsi …)`) is worse:
`MMap` carries no `u8acc`, which `utf8_feed` needs for a multi-byte glyph. Then `rows = 1`
(weaken `Walking.bot` to `rows ≤ 1 ∨ bot = rows - 1`; a one-row grid cannot scroll) and
`resume_grid`. Details in SCRATCHPAD 2026-08-18 and in a note above
`restore_grid_reachable`.

**Definition-of-done item 5 is proved for the main screen** (2026-08-18):
`restore_grid_any_main` and `restore_grid_reachable` — feeding `restore v` to any
**live-reachable** client of the session's dimensions leaves its grid equal to `v.grid`, array
for array, cell for cell. Non-vacuity checked at a real 80×24 `Vt.init`.

**The `u8acc` precondition flagged last round is solved twice over**, and the honest summary
is that it was a limit only on paper: `uaz_feed` (an all-ASCII stream leaves the decoder
quiesced, with the composable `Ascii` family for the side condition) and `U8Ok`
(`u8need = 0 → u8acc = 0`, proved for **every live-reachable state** — so no real client
violates it). `Good` bounds `u8need` but says nothing about `u8acc`, which is why it needed
its own invariant. `u8pair_stepEsc` records the shape that *is* true: unchanged **or** both
cleared — the backwards direction is false, because `RIS` rebuilds through `Vt.init`.

Also landed: `paint_entry` (the establishing prefix leaves the receiver ready — every
hypothesis `gridAnsi_writes_grid` asks for), `modeSet_feed_eq` (a private mode set as a
*state* equation; `modeSet_modes` saw only the `Modes` field, and `?1049h`'s real work is
stashing the grid), `setMode_pstate`, `csi_priv_open_eq`, `modes_eraseScreen`,
`grid_eq_of_cells`.

**Step 4's grid-painting core is COMPLETE** (2026-08-18), the mathematically hard part:
* `OffRow` — a row's paint touches no other row (the cross-row scroll `RowOk` guards
  against, stated positively; the half `Matches`, being about one row, could not carry).
  `paint_range`/`rowAnsi_writes_row` now also conclude it.
* `crlf_step` / `lineFeed_interior` — the inter-row `CRLF` is one clean cursor move; below
  `bot` the line feed does not scroll. The no-scroll argument.
* `paint_rows` — the grid row walk (over `rowsAnsi`/`joinCRLF`); no line feed scrolls
  because `joinCRLF` emits no trailing separator, so the last row's LF never fires.
* `gridAnsi_writes_grid` — **the whole grid, painted into any client of matching
  dimensions with reproducible rows, reproduces `v.grid` exactly**, array for array.
* `prologue_sticky` / `prologue_modes` — the prologue's canonical mid-stream entry state
  (region whole, no alt, ASCII charsets; insert off, wrap on, origin off). `rows ≥ 2` is
  `DECSTBM`'s own constraint; the one-row grid needs no region fact (it cannot scroll).

**Step 3 is COMPLETE** (2026-08-17). `rowAnsi_writes_row`: feeding `rowAnsi g startPen` into
any receiver matching `g` at frontier 0 paints the whole row, ending matched at every column
with `rowAnsi`'s returned pen in effect. Built bottom-up: the mark loop (`withMarks`,
`mark_step`/`marks_fold` over a write column `wcol < kf` so one loop serves narrow and wide,
`step_narrow_marks`); the wide-with-marks `CHA`/`CHA` dance (`cha_feed_eq :
feed (CHA n) = setCol (n-1)`, `cha_matches`/`_lt`, `step_wide_marks`); the eight cell rungs
(narrow/wide × marks/no-marks × interior/margin) plus `step_pen` and `shadow_emits_nothing`;
and the fold (`rowSlot` extracted from the lambda; `rowSlot_eq_*` output equations;
`rowSlot_fold_split` peel; `paint_range` — strong induction peeling a cell or a pair, with
`Matches.frontier` making a shadow at a recursion point a *type error*). `STATEMENT_CAP` back
to 21 (`rowSlot` now named by a theorem). Break-verified emitter-side (`rowSlot`) and
emulator-side (`printMark`, `setCol`).

`hcb : k + 3 < 65535` (per rung) / `w.cols < 65533` (row) is the column analogue of
`restore_sticky_any`'s row bound — `CHA` clamps its parameter to 65535, so the emitted column
must stay under it; the ≤1000 dim clamp supplies it downstream.

**Definition-of-done items 4 (mostly done — `rowAnsi_writes_row` landed, the grid walk
remains) and 5 are all that remain.** Items 1, 2, 2b and 3 are done — three restated on
contact, recorded in each — and item 6 (gates green, every theorem break-verified) is
standing. `restore_tabs_any` is an optional warm-up, not on the critical path.

**Done:** Step 0 — two bugs fixed. **Step 1 is complete**: A5 is proved at the
value level in both directions for the modes, the pen and the sticky bundle
(region, both charsets, shift state, screen selection). Four restored fields are
*not* covered and are named here so the list is not mistaken for "just the cells":
the screen **cells** (Steps 3–4), the window **title**, the **tab ruler** and the
**DECSC slot**; `restore_cursor` also still quantifies over `Vt.init` rather than
any receiver. The tab ruler was worse than unproved until ledger item 0 was fixed
in the same session — a theorem would have found it *false* — which is the clearest
argument this spec has produced for naming the uncovered fields instead of writing
"only the cells".
* outbound: `leave_canonical` (parser ground + modes default, any receiver) and
  `leave_canonical_all` (+ region, charsets, shift state, screen, pen — for a
  receiver at least two rows tall, which is `DECSTBM`'s own constraint).
* inbound modes: `restore_modes_any` (given the mouse allowlist).
* inbound pen: `restore_pen_any`.
* inbound sticky fields: `restore_sticky_any` — the scroll region, both charset
  designations, the shift state and the screen selection, for any receiver of the
  same height, given `Good v` and `v.top < v.bot` (the region `DECSTBM` accepts;
  a one-row region is the excluded degenerate case). Its three projections are
  `restore_region_any`, `restore_charset_any`, `restore_alt_any`.

The reusable layer: `modeSet_modes` (dispatch bridge), `MMap` + `MMap.ite`,
`uz_titleAnsi`, and — from the sticky round — `Vt.stick` (one **bundled**
projection, so `print` and `csiDispatch`, the two operations frames could not
cover, are paid for once instead of per field), `csi_tail_proj` (the CSI walk with
the projection as a parameter; `csi_tail_modes` and `csi_tail_pen` are now its
instances), `smap_csi_one_arg` (the digit-run-and-dispatch walk, once for both
markers), and `SMap` (the `Quiet` shape at the bundle, with no `u8need` side
condition — an `ESC` clears a half-decoded character and nothing sticky rides on
it, which is what lets the *repaint* be a chunk).

Step 2 — **done** (`restore_grounds` + `restore_u8_zero`, composed as
`restore_quiesced_any` / `resume_quiesced_any`). Steps 3–5 — not started.

**Two long-range dependencies are now visible in the theorems rather than left to
inspection.** `charsetAnsi` is set-only for the shift state and `regionAnsi` emits
nothing for a whole-screen region, so both claims run back through the entire
repaint to the prologue's `SI` and `CSI 1 ; rows r`. They hold — but the transform
in `smap_charsetAnsi` now *says* that it rests on the prologue, which is the same
set-only shape `87f64b3` fixed in `modesAnsi`. Recorded, not fixed: making them
absolute would change emitted bytes for no behavioural gain now that the
dependency is proved rather than assumed.

**The inbound proof needed no paint ladder** — a discovery that corrected the plan.
Because every `modesAnsi` chunk is `ESC`-initiated and `ESC` clears `u8need`, the
prefix (prologue through the title) only has to reach `pstate = ground` — the
already-proven `Ends` ladder — so `gridAnsi` is never dragged into a modes proof.
`restore_modes_any` carries one hypothesis, `v.modes.mouse ∈ {0,1000,1002,1003}`:
the emulator's own mouse allowlist (`setMode` stores only those), and the reason
`modesAnsi` normalizes a foreign checkpoint's garbage mouse to off rather than
replaying it.

**The dispatch-exposing edit is done, and it generalized.** Step 1 named one
prerequisite: factor the CSI walk to expose the dispatch, not just the grid fact.
That is `modeSet_modes` — feeding `modeSet n on` from ground has modes exactly
`setMode true n on`, for *any* `n` (alt-screen modes included, unlike `keeps_modeSet`).
On top of it, `MMap` (the modes-from-ground analog of `Keeps`) composes per-chunk
transforms, and `leave_modes` folds the hand-back's chunks to the default record for
any receiver. `restore_modes_any` is the same machinery pointed inbound, and needed
no `MMap id (gridAnsi)` after all — see the paint-ladder note above.

**Step 0 changed the shape of the goal.** The bug family was not exhausted, and the
question that keeps paying is the §Replay one asked in *both directions and at both
ends*: *what does this byte stream assume about, or leave behind in, the stateful
thing it writes to?* Two hits:

- **The hand-back (into the user's terminal).** A detaching client restored termios
  and nothing else, so leaving any full-screen program handed the user's shell a
  terminal still on the alt screen, mouse reporting on, no cursor, autowrap off, a
  stale scroll region, DEC line drawing selected. Fixed with `Render.leaveAnsi` — a
  constant, in `Client.attach`'s `finally`. Pinned by `tests/attach_test.py` step 9;
  theorem `leave_canonical` is folded into Step 1.
- **The XTGETTCAP reply (into the child's input).** A security bug — query replies
  are written into the child's own pty input, and the request is untrusted child
  output, so echoing its payload verbatim let a `cat` of a hostile file inject a CR
  and run a command. Fixed by filtering the echo, and **proved**: `feed_replies_noNl`
  says no reply linger writes to the child contains a line terminator, for any input.
  (SCRATCHPAD 2026-08-15T22:30.)

So the goal below is half of a pair, and the pair is what the product actually
promises: **linger borrows terminals — the user's and the child's — and must both
establish what it needs and give back what it took, at both ends.** The receiver-
facing halves are all one theorem shape (`Sets`/`Ends`, quantified over the
receiver), which is why the hand-back joins Step 1. The audit's other real findings
(none a security hole) are the ledger at the end of Step 0 — deliberately not fixed
this round, one item in flight.

**The diagnosis this spec is built on:** every §Replay bug had the same shape, and the
shape was in the quantifier. `Tests/Fuzz.lean`'s header calls it "an emitter stage
correct only under a precondition on the emulator state it is fed into" — and the
fidelity theorem quantifies over `Vt.init`, the one receiver state in which every such
precondition already holds. The theorem was structurally blind to the class.

Two live bugs came out of that reading, both fixed and break-verified:

- `87f64b3` — `modesAnsi` was set-only for eight modes and the repaint ran before any
  receiver state was established, so a client's leftover IRM, DECOM, mouse reporting,
  scroll region, charset or alt screen either corrupted the repaint or survived it.
- `cd7c17b` — a client mid-OSC or mid-DCS **swallowed the entire restore stream**,
  because `stepOsc` accumulates our `ESC` and then our `[`. Also `titleAnsi` was
  set-only, so an empty session title left the client's old one on display.

`906bf11` then closed the first of these *at the theorem level*: `restore_grounds`
holds for any receiver with no hypothesis at all. Step 1 then closed the modes, the
pen and the sticky bundle the same way. `restore_grid` still quantifies over
`Vt.init`, so the **cells** are fixture-and-fuzz-carried (Steps 3–4) — and so are
the **title**, the **tab ruler** and the **DECSC slot**, which have no
receiver-quantified theorem at all. Asking the same quantifier question of them is
what found ledger item 0.

## The bigger picture — what this ladder is for

Written down because two sessions of induction-grinding is exactly when it gets
lost. PLAN.md's instruction is "high quality theorems are how we resolve tensions",
not "prove everything": a theorem earns its place by carrying a product promise or
by naming what is trusted. THEOREMS.md's anchor set is the list that matters, and
this spec exists to finish one anchor and to add one.

**The promise this ladder serves.** linger is not a window manager — windows, tabs
and splits are settled non-goals — so it *borrows* a terminal you already had
instead of owning one. Everything about the borrow is one claim in two directions:

* **inbound**: whatever state the client's terminal is in, the restore stream
  establishes what the repaint needs (`restore_grounds` ✓, and every restored field
  but the cells ✓ — Step 1);
* **outbound**: whatever state the session's program left, the hand-back returns the
  terminal to a state the next program can use (`leaveAnsi`, Step 1).

That pair is the anchor to add (A5 in THEOREMS.md: *linger is invisible to the
terminal it borrows*), and it is what makes attach/detach compose with everything
else you run in that terminal. Note which half was missing: the one nobody had asked
a quantifier question about.

**What the fidelity half can and cannot claim.** `restore_grid` models the client
with our own `Vt`, so completing it proves *emitter/parser self-consistency*, not
that xterm renders the session. There is no route to a real-terminal claim by
grinding harder on this induction; the routes are:

1. *State the profile.* Write down, as prose in THEOREMS.md, the receiver behaviours
   the emitter depends on — absolute `CUP` with DECOM off, deferred wrap at the
   right margin (the 2026-08-15 negative result, discovered the hard way), SGR
   parameter limits, `ED 2` leaving modes alone, charset designation scope. Then the
   honest claim is "our emitter and parser agree, and here is the list a real
   terminal has to match". Cheap, reviewable against the DEC/xterm documentation,
   and it is a *product* artifact: it is the compatibility profile linger requires.
2. *Make the profile a law bundle in Lean* — a receiver structure with those laws,
   `restore` proved against any lawful receiver, `Vt` shown to be one instance. This
   is the §Claim move (`Exclusive` names in one reviewable line what the kernel is
   trusted for) applied to the terminal, and it is the only shape in which a
   conformance claim can be stated at all. It is also a large refactor of a 4 000-line
   proof file, and **no bug found so far would have been caught by it**: the bugs
   lived in the quantifier over *receiver state*, which `Sets`/`Ends`-over-any-`w`
   already fixes.

So: do (1) now, as part of Step 5's documentation half. Treat (2) as a deliberately
deferred option with its reason recorded, not as a road not noticed.

**Priority, argued from the evidence rather than from tidiness.** Bugs found by
asking "what does this stream assume about, or leave behind in, the thing it writes
to?": four, in two sessions (`87f64b3`, `cd7c17b`, the empty-title leak, the
hand-back). Bugs found by the fuzz corpus and the round-trip fixtures: the cell-level
ones, and its failure lists are currently empty with no held-out mutations. Bugs that
the remaining row induction would find that neither has: none identified. The
induction buys *universality* over the corpus, which is worth having and is worth
having **last**. Hence the order: Step 1 (both directions, cheap, certifies three
shipped fixes) → Step 2 → Step 3 → Step 4.

## Open questions

- **Self-consistency is not conformance.** `restore_grid` models the client with our
  own `Vt`, so it proves emitter/parser agreement, not that xterm renders it. The pty
  and e2e suites are the only evidence about real terminals. Belongs in THEOREMS.md as
  a stated limitation.
- **Was the bug family exhausted?** No — Step 0 found the hand-back (see above). The
  question that keeps paying is *"what does this stream assume about, or leave behind
  in, the thing it writes to?"*, asked in **both** directions. Ask it of any new
  emitter before proving anything about it.
- **Does the `u8need` half need a per-chunk predicate of its own**, or can `Keeps` be
  generalized to carry an arbitrary property? The latter would subsume `Sets`.
- **The window title is still leaked outbound.** `titleAnsi` sets the client's title
  on attach and the hand-back does not put it back, because we never read it. xterm's
  title stack (`CSI 22 ; 0 t` / `CSI 23 ; 0 t`) is the mechanism and is not universal.
  Open, recorded, small.

## Step 0 — audit for siblings of the receiver-state bug

Status: **done** (2026-08-15). Ran as a fanned-out read across five lenses (emitters,
runtime hygiene, the child's side, theorem quantifiers, dead surface) with an
adversarial verifier per candidate. **Two fixed this round; the rest recorded below.**

Fixed:
- **The hand-back** (`Render.leaveAnsi`, `tests/attach_test.py` step 9, SCRATCHPAD
  2026-08-15T20:10). Its theorem is folded into Step 1.
- **XTGETTCAP reply command injection** (`Terminal.xtgetcapReply`, SCRATCHPAD
  2026-08-15T22:30). The §Replay family aimed at the *child*: query replies are
  written into the child's own pty input, and an XTGETTCAP request is untrusted child
  output, so echoing its payload verbatim let a `cat` of a hostile file smuggle a CR
  and run a command. Fixed by filtering the echo to the hex+`;` alphabet; proved by
  `feed_replies_noNl` (no reply linger writes to the child contains a line
  terminator, over the whole stream). This is a security fix and outranked the
  remaining proof steps, which is why it was taken this round.

Checked and needing no emitter of its own (so a future session does not redo it):
`linger history` emits `rowText`, every character `safeChar`-scrubbed, so no escape
byte (and `withAnsi = true` is unreachable from the CLI — `Session.onMsg` passes
`false`); `Zmx/Core/Listing.lean` and `Status.lean` emit glyphs only; `resizeEffects`
carries no bytes.

Exit criterion, met: each emitter either establishes/handles what it depends on, or
is recorded below with a reason and a severity.

### Step 0 findings ledger — real, not yet fixed

Recorded so they are not lost; none is a security hole, and one-item-in-flight is why
they wait. Roughly by severity:

0. ~~**`tabsAnsi` is set-only: a client's leftover tab ruler survives the
   restore.**~~ **Fixed 2026-08-16, same session it was found.** Found by an
   adversarial review of the sticky-field claims, asking the spec's own question of
   a field no theorem covers. `tabsAnsi`
   (`Zmx/Core/Render.lean`) emits `[]` when `v.tabs == defaultTabs v.cols`, and
   nothing else in linger's output clears tab stops — no `TBC`, and no `RIS`
   anywhere — so a client whose previous occupant ran `CSI 3 g` plus its own `HTS`es
   keeps that ruler, and `\t` in the session lands on the wrong column. Exactly the
   shape `87f64b3` fixed in `modesAnsi`, and the reason ledger item 1's fix
   *un-deadened* this path: `tabsAnsi` is live on the attach path again.
   **Reproduced against the project's own oracle**, not argued: with `sess` on the
   default ruler and a receiver whose ruler was re-set every four columns,
   `roundtripsFrom` is `false` and `replayEq` fails on `.tabs` (it compares `r.tabs`,
   `Tests/Render.lean:35`); it passes today only because no fixture moves the
   *receiver's* ruler. **Fixed** by emitting the ruler unconditionally (`CSI 3 g`
   then one `CHA`+`HTS` per stop): ~70 bytes for an 80-column default ruler, against
   a field that was only right when the client happened to be pristine. Pinned by
   the `dirtyTabs` fixtures in `Tests/Render.lean` (including a non-vacuity case
   showing nothing *before* `tabsAnsi` clears a stop), break-verified by restoring
   the guard. `restore_tabs_any` is now **provable** and was not proved — as the code
   stood such a theorem would have been *false*, so this is the one place where the
   fix had to precede the theorem. It wants a `tabs` projection of its own (an
   `Array Bool`, so not a scalar to fold into `stick`) and the `TBC` + `HTS` fold;
   that is the natural next receiver-quantified field.

1. ~~**Reattach at an unchanged size wipes the scroll region and tab ruler.**~~
   **Fixed in `33b107e`**, and certified: `Session.onMsg .attach` now guards the
   `Vt.resize` on an actual dimension change, `Theorems/Session.lean`'s
   `onMsg_attach_same_size_vt` proves the same-size attach leaves `vt` untouched, and
   `Tests/Session.lean` pins it with a non-vacuity case. Kept here with its original
   diagnosis because it is what made item 0 reachable: with the guard in place a
   same-size reattach preserves the child's ruler, so `tabsAnsi` is no longer dead on
   the attach path — it is live and wrong.
2. ~~**Label values are not tab/newline-scrubbed.**~~ **Fixed 2026-08-17, and proved.**
   `infoText` framed fields as `k\tv\n` through a `String` interpolation, and
   `.labelSet`/`linger set` apply no filter — so a label value with a newline and a tab
   forged an extra record, including a `status`/`state` pair that the listing would
   display as the session's state. Fixed at the **emit site** rather than at
   `.labelSet`: `infoText` now builds `List UInt8` with `Render.utf8s`, which maps a C0
   control (tab and newline included) to U+FFFD, so a guard needs no invariant about
   where a field came from and covers fields nobody has added yet — the same argument
   `gridAnsi` makes for establishing its own pen. Proved by `infoText_framing` (every
   byte is a framing byte or printable content) and `infoText_records` (as many
   newlines and tabs as fields — the anti-forgery claim). Break-verified, and the
   fixture pins the *before* as well: the old shape emits one newline too many.
   The restructure is also what made it provable, which is the point — the old shape
   ended in `String.toUTF8`, and a `String` does not reduce in the kernel. That is now
   the recorded route for `Render.history`, the last emitter still in that shape.
   Still open, and much smaller: the local-listing `cmd` and `label.*` *display* lost
   the `Remote.scrub` the old `Tui.rowOfInfo` applied, so a control character shows raw
   in the human column. Cosmetic, not a forged record.
3. **The pty input buffer (`rt.ptyIn`) is uncapped**, unlike the per-client 4 MiB
   output queue — §Bound's runtime half is asymmetric. A child that stops reading plus
   a client that floods input grows it unboundedly. Runtime (`IO`), so not a core
   theorem, but the cap belongs next to the client one in `Daemon.lean`.
4. **Resume spawns the pty at a hardcoded 80×24** while the restored `Vt` keeps the
   checkpoint's dimensions, until the first sizing attach reconciles them. Narrow
   reach: `linger run`/`send`/`wait` on a checkpointed-but-not-live session.
5. **Modes the `Vt` does not model** (DECSCNM `?5`, `?1005`/`?1015` mouse encodings,
   DECSCUSR cursor shape) can be neither established by the prologue nor cleared by the
   hand-back, in either direction — a completeness limit of the emulator, not a leak
   the current model can even represent.
6. **`.err` is dropped by `Client.attach`** (only `drainReplies` prints it), so a
   "too many clients" refusal reads to the user as a clean detach. UX, easy fix.

## Goal

`restore` puts **any** conforming receiver of the right size into the session's
state, and the hand-back returns **any** receiver to a state the next program can
use — with the theorems quantified over that receiver rather than over one convenient
starting point.

Two things this deliberately does not claim. It is not conformance to xterm: the
model receiver is our own `Vt`, so these are emitter/parser self-consistency
theorems, and the pty and e2e suites remain the only evidence about real terminals.
And it is not scrollback: restore repaints the screen, not history.

## Definition of done

1. **Done, in a different shape.** `Sets` (a bare `∀ w` per chunk) is false for a
   lone chunk — a mid-OSC receiver swallows it — so the predicates that landed are
   `MMap` (modes-from-ground, with `comp`/`congr`/`ite`/`nil`) and `SMap` (the same
   at the sticky bundle, without `u8need`). Both mirror `Ends`/`Quiet`/`Keeps`.
2. **Done.** `restore_modes_any` (the ten `Modes` fields, certifying `87f64b3`),
   `restore_pen_any`, and `restore_sticky_any` — the charset designations and shift
   state, the scroll region, and the alt-screen flag, with `restore_charset_any` /
   `restore_region_any` / `restore_alt_any` as its named projections.
2b. **Done.** `leave_canonical` (parser `ground` + modes default, no hypothesis on
   the receiver) and `leave_canonical_all` (also the charset flags, the scroll
   region, the alt-screen flag and the pen, for a receiver at least two rows tall).
   Independent of any session state, since `leaveAnsi` takes no argument. What no
   theorem covers is the final cursor position: `CSI 999 ; 1 H` is clamped by the
   receiver, so where it lands is the receiver's business.
3. **Done, in a different shape** (see Step 2). The *predicates* keep their
   ground-parser assumption — they must, since a receiver mid-OSC swallows a lone
   chunk — and the receiver-quantification happens once, by peeling the lead-in
   (`st_grounds`). What the criterion was reaching for is the top-level claims, and
   those now carry no hypothesis on the receiver at all: `restore_grounds`,
   `restore_u8_zero`, `restore_quiesced_any`, `resume_quiesced_any`. The prologue's
   `ESC \` lead-in is what makes it true, exactly as this item said.
4. **Partly done, and "with `rowAnsi` threading it" is the wrong shape** — recorded
   rather than quietly dropped. `PaintState` (`x`, `y`, `pen`, `pending`) ✓ and
   `Matches` ✓ are in, along with every cell-shape rung but one. But `rowAnsi` must
   *not* thread `PaintState`: two of its four fields — `y` and `pending` — are
   **receiver** state that the emitter cannot see and must not carry. `rowAnsi` already
   threads the emitter's half (`(bytes, pen, x)`); `PaintState` is the receiver's, and
   `Matches` is what ties them. So the remaining work under this item is
   `rowAnsi_writes_row` folding the rungs over the row, not an emitter refactor.
   Landed rungs: `step_narrow` (interior), `step_narrow_margin` (the clamp-and-arm
   case), `step_wide` (the pair, one rung, `k` to `k+2`), `step_pen`, and
   `shadow_emits_nothing`. Remaining: the mark loop (narrow-with-marks, then the
   wide-with-marks `CHA`/`CHA` dance), then `rowAnsi_writes_row`.
5. `restore_grid_any`: for every `v` and every `w` of the same dimensions, the grid
   after `w.feed (restore v)` is `v.grid`, with cell and pen equality. Then
   `restore_grid_reachable` from `LiveReachableVt`, and `resume_grid` composing with
   checkpoint exactness.
6. `./lake build Theorems Tests` and `./tests/e2e.sh` warning-free and green; every
   new theorem break-verified and recorded in `SCRATCHPAD.md`.

Review/revise cap: two fresh-review rounds, as before.

## Step 1 — the receiver-quantified value claims, in both directions

Status: **done** (2026-08-16). Outbound `leave_canonical`; inbound
`restore_modes_any`, `restore_pen_any`, `restore_sticky_any` (+ its three named
projections). Every restored field except the screen cells is now a theorem
quantified over the receiver.

Purpose: make the shipped fixes theorems rather than tests — the hand-back
(anchor A5, done) and `87f64b3`'s both-ways modes (`restore_modes_any`, done).

Reads: `Zmx/Core/Render.lean`, `Theorems/Render.lean`, `SCRATCHPAD.md`.
Writes: `Theorems/Render.lean`, `THEOREMS.md`, `SCRATCHPAD.md`.

**What landed, and the layer it built** (SCRATCHPAD 2026-08-16). The predicate that
worked is not `Sets` (a bare `∀ w`, false for a lone chunk since a mid-OSC receiver
swallows it) but `MMap`, the modes-from-ground analog of `Keeps`: `∀ v, ground → u8
0 → ground ∧ u8 0 ∧ modes = f v.modes`, with a `comp` law. The lead-in is peeled by
`st_grounds` (grounds any `w`), then the tail composes from ground. The dispatch-
exposing bridge the spec named is `modeSet_modes`: feeding `modeSet n on` from ground
has modes exactly `setMode true n on`, for **any** `n` — alt-screen modes included,
where `keeps_modeSet` excludes 47/1047/1049 because they touch the grid, but the
parser and the modes projection do not. Per-chunk bridges: `mmap_modeSet`, `mmap_irm`
(non-private IRM), `mmap_keypad`, `mmap_id_csi_seq` (+ `modes_csiDispatch_{stbm,cup,
sgr}` for the CSI preservers), `mmap_id_charset`, `mmap_id_si`. `leave_modes` folds
them to the default record; break-verified (drop any `modeSet` from `leaveAnsi` and
the `rfl` that the composite equals `{}` fails).

**Inbound (`restore_modes_any`), as landed.** Same machinery, target `v.modes`
instead of `{}`. It needed **no** `MMap id (gridAnsi)` and no `eraseScreen`
modes-frame, which is where the plan was wrong: `modesAnsi` overwrites every mode
field absolutely, so the whole prefix (prologue, `SGR 0`, `ED 2`, the repaint,
region, tabs, DECSC, title) only has to reach `pstate = ground` — `prologue_grounds`
plus the `Ends` ladder plus `uz_titleAnsi` — and the suffix folds as
`mmap_modesAnsi ∘ mmap_id_charsetAnsi ∘ mmap_id_penSgr ∘ mmap_id_cursorAnsi`. The
paint never enters a modes proof. (It does enter the *sticky* proof, which is why
that one needed `smap_id_gridAnsi`.)

**Non-modes projections, as landed.** The `pen` repeated the `MMap` shape with its
own projection (`csi_tail_pen`). The rest did **not**, and the difference is worth
recording: the scroll region is emitted before the title and the screen switch in
the middle of the repaint, so those claims cannot step over `gridAnsi` the way the
modes proof could. They went through `Vt.stick`, one bundled projection with the
frames idiom underneath, plus `csi_tail_proj` (the walk with the projection as a
parameter — `csi_tail_modes` and `csi_tail_pen` are now instances, so the walk's
proof *script* is written once instead of three times — the file still grew, because
the new docstrings outweigh the saved script; the honest claim is that it paid for
itself at the third projection and keeps a fourth free) and `SMap`, a `u8need`-free
stream predicate.

Exit, met: `restore_modes_any` for the ten `Modes` fields; `restore_pen_any`;
`restore_sticky_any` for the other five. Break-verified (SCRATCHPAD 2026-08-16):
negating `charsetAnsi`'s shift-state condition fails **only** the new
`smap_charsetAnsi`, and putting `regionAnsi`'s `DECSTBM` top parameter off by one
fails **only** the new `smap_regionAnsi` — two isolating breaks; the alt-screen and
G0 breaks also trip the older parser ladder, which names the mode numbers.

## Step 2 — drop the ground-parser assumption

Status: **done** (2026-08-17). `restore_grounds (v w : Vt) :
(w.feed (restore v)).pstate = .ground` holds with no hypothesis on `w` — the first
receiver-quantified theorem in the file. Chain: `un_abortUtf8_esc`, `esc_lands` (one
case per `PState`), `st_finish`, `st_grounds`, `prologue_grounds`.

The abort turned out to be `ESC \` (ST) rather than `CAN`: our `stepOsc` treats a C0
byte as payload, so `CAN` would have needed a Core semantics change, while `ST` is
what both string states already listen for and `stepEsc` routes `0x5C` to its default
arm. No new parser surface.

**The `u8need` half needed no ladder at all**, and the reason is the mirror of the
lead-in: `restore` *ends* with `cursorAnsi`, one `CSI … H`, and `u8_zero_after_csi`
zeroes `u8need` whatever the incoming state was — a CSI's final byte cannot leave a
character half-decoded. So `restore_u8_zero (v w)` is fifteen lines and the whole
stream in front of it is irrelevant, where `restore_quiesced` had to assume a fresh
`Vt.init`. `restore_quiesced_any` and `resume_quiesced_any` compose the two ends.

Purpose: a client cut off mid-escape is a real state, and every existing stream
theorem assumed it away.

**The exit criterion as first written was wrong, and this is the same correction
item 1 needed.** It asked for "the three predicates carry no hypothesis on the
receiver's parser state" — but a per-chunk predicate *cannot* drop it: a receiver
mid-OSC swallows a lone chunk, which is exactly why `Sets` became `MMap`. The
achievable — and achieved — form is about the **top-level claims**, with `st_grounds`
peeling the lead-in once:

* `restore_grounds` — parser, any receiver, no hypothesis. ✓
* `restore_u8_zero` — decoder, any receiver, no hypothesis. ✓
* `restore_modes_any`, `restore_pen_any`, `restore_sticky_any` — the values. ✓
* `restore_quiesced_any`, `resume_quiesced_any` — the composition, replacing the
  `Vt.init`-quantified `restore_quiesced` / `resume_quiesced` (kept, since the
  fresh-terminal form is what `Tests/` exercises). ✓

`Quiet`'s origin half is **subsumed**, not carried: a receiver-quantified
"DECOM ends off" is the `origin` component of `restore_modes_any`. What is *not*
done, and belongs to Steps 3–4 rather than here, is generalizing `restore_cursor`
off `Vt.init`: where the cursor lands depends on where the paint left it, so it is a
grid-level claim, not a parser-level one.

Break-verified: ending `restore` with a dangling UTF-8 lead byte (`0xC3`) fails
`restore_u8_zero`; replacing the prologue's `ESC \` lead-in with `ESC 7` fails
`restore_grounds`. Both also fail `restore_sticky_any`, so the value claims are
sensitive to both ends of the stream. Witnessed in `Tests/Render.lean`: receivers
caught mid-UTF-8, mid-OSC and mid-CSI are each left quiesced.

## Step 3 — `PaintState`

Status: **the layer under it is in** (2026-08-17); the row induction itself is not
started.

What landed, and why this order: a fanned-out map of the existing machinery found
that the row induction's step lemmas were blocked on facts nobody had named, not on
the induction. Three clusters, all now closed:

* **`OffScreen`, the cut `print` induces.** `print` is one of the two operations a
  frame *equation* cannot cover (five composed stages). `Vt.offScreen` bundles
  everything outside `grid`/`cursor`/`sb` — the cut `print` actually makes — so
  `off_print` composes by transitivity, which a frame cannot, and every field
  invariance across a print is one `congrArg`. That is where `pen_print`,
  `ins_print`, `wrap_print`, `g0_print`/`g1_print`/`so_print` and `ua_print'` come
  from. The last one matters most: `Render.cellText_feed` carries `u8acc = 0` as a
  hypothesis, so a row induction has to *re-establish* it per cell, and nothing said
  a print preserves it.
* **Where the cursor goes.** `print_narrow_eq` and its siblings say what a print
  writes; all three take `cursor.pending = false` as a hypothesis, so the induction
  has to re-establish it for column `k+1`. `cursor_printAdvance_lt`/`_ge` and
  `cursor_print_narrow_fits`/`_margin`, `cursor_print_wide_fits`/`_margin`,
  `cursor_print_mark` do that — and the margin cases are where the spec's
  wrap-`pending` negative result shows up as a theorem: at the right margin the
  advance clamps the column and arms wrap-pending, a state no absolute cursor move
  can express.
* **The two byte→cursor bridges.** `cup_places_cursor` covered two-argument `CUP`
  only. The repaint uses two other forms and neither had a bridge, so the induction
  could not say where it was writing: `gridAnsi` homes with a bare `CSI H`
  (`home_places_cursor`) and `rowAnsi`'s wide-with-marks branch parks the cursor with
  `CHA` twice (`cha_places_cursor`). Same walk as `cup_places_cursor`, one parameter
  shorter.

**The invariant itself landed 2026-08-17**, with the frame that makes it usable:
* `PaintState` (`x`, `y`, `pen`, `pending`) and `Matches w P g k`. `Matches` carries the
  parser **triple** and the receiver-side context every rung needs (autowrap on, IRM off,
  ASCII charsets, a full-length row, `y` in the grid) so that one step lemma
  re-establishes everything the next needs, and it asserts **nothing** about columns
  `≥ k` — which is what lets the theorem quantify over an arbitrary client whose
  unpainted columns still hold the previous occupant's junk, half pairs included.
* `frontier : k = 0 ∨ (g.at (k-1)).width ≠ 2`, the recorded constraint, as a field.
* `prefix_kept` — **a write at or past the frontier leaves the painted prefix alone.**
  This is the delicate one and it is per column, not per row: `Vt.mendRow` sweeps the
  whole row and on a row with broken pairs `mendAt` may rewrite any column, which is
  exactly the mid-paint situation. So the case analysis is on the *source* row's shape at
  each column (which the induction knows, because the prefix already equals the source
  there) and `RowOk.pairs` turns "width 0 at `j`" into "a whole pair at `j-1`", so
  `mend_keeps_wide` applies to the pair rather than half of it.
* the within-row write frames it rests on, which did not exist:
  `at_putCell_ne`, `getCell_write_mendRow_keep_narrow`, `getCell_write_mendRow_keep_wide`.

`frontier` is **verified load-bearing**: replacing it with `True` collapses
`prefix_kept`'s width-2 case, which is the case where the shadow would sit at `k`,
unpainted, and the sweep would blank the base the previous rung had just painted.

**The first step lemma landed too**: `step_narrow` — one narrow, mark-free cell in the
interior of a row, `Matches … k → Matches … (k+1)`, re-establishing all fifteen fields.
Nothing in it is novel, which is the point of having built the layer first: the cell's
bytes become one `print` (`cellText_feed`), the print becomes a write plus an advance
(`print_narrow_eq`), and the invariant's fields fall to `cursor_print_narrow_fits`,
`off_print`'s corollaries, `write_shape` and `prefix_kept`. All three of its hypotheses
are verified load-bearing.

`write_shape` is worth noting: it is stated about the *composite*
`((u.putCell x y c).mendRow y).printAdvance n` rather than about `print`, because under
`print_narrow_eq`'s hypotheses that composite **is** the print — where a general
statement for `print` would have to reason through `printWrap`'s scroll, which those
hypotheses exist to rule out.

**Four more rungs landed** (2026-08-17): `step_narrow_margin` (the clamp-and-arm case
the interior rung cannot cover), `step_wide` (the pair in one rung, `k` to `k+2`),
`step_pen` (which is what makes the cell rungs' `hpen` dischargeable), and
`shadow_emits_nothing` (the pair's second slot emits nothing, which is *why* `step_wide`
has to advance by two). `prefix_kept` was refactored into `mend_keeps_prefix` on the way:
the original bundled "the writes missed the prefix" with "the sweep keeps it", which only
fits a single write, and the wide rung does two.

**The mark loop landed** (2026-08-17), closing item 1 below. `withMarks g k acc` (the
source row with column `k`'s marks truncated) is the reused invariant: `rowOk_withMarks`
shows it is still `RowOk` because column `k` is a glyph, never a shadow, and only a
shadow's content is pair-constrained. `mark_step` does one mark — interior and margin
unified by one `hdisj` disjunction, which is why the margin needed
`print_mark_pending_eq` (the cursor is *on* `k` with wrap-pending, so the mark attaches
there). `marks_fold` folds it; `step_narrow_marks` assembles base + marks, making
`step_narrow` its `marks = []` case. `matches_below`/`matches_row_congr` are the row
swaps at the loop's entry and exit.

**What remains of Step 3**, in order:
1. ~~the **mark loop**~~ — **done** (see above).
2. the **wide-with-marks** rung — `rowAnsi`'s `CHA`/`CHA` dance, which parks the cursor
   between glyph and shadow because `printMark` steps one left. `cha_places_cursor` is
   already in and now covers the final-column clamp (`min (n-1) (cols-1)`); what it needs
   is the two-jump bookkeeping and the `step_wide` base underneath it;
3. `rowAnsi_writes_row` — the fold over the row. Note it inducts over `rowAnsi`'s *byte*
   accumulator, so the invariant is `Matches (w.feed acc.1) …`, using
   `feed (a ++ b) = feed b ∘ feed a`. This is the theorem that will *name* `rowSlot` (the
   fold body extracted from `rowAnsi`'s lambda), bringing `STATEMENT_CAP` back to 21.

Also landed: `paint_grounds`, the first of `restore_grid_of_paint`'s three hypotheses,
for any receiver. The `u8need` one is *not* free the same way — the whole stream ends
in a `CSI … H` but this prefix ends in glyph bytes — so it belongs with the cell
induction, where UTF-8 completeness is in scope anyway.

Break-verified, both isolating: making `CHA` off by one in `Vt.csiDispatch` fails
**only** `cha_places_cursor`; making `printAdvance` not arm wrap-pending at the margin
fails **only** `cursor_printAdvance_ge`.

**What the map got wrong, recorded because it is the lesson.** The readers reported
`mend_of_pairOk`, `mendAt_of_pairOk` and `mend_blankRow` as non-existent — they are in
`Theorems/Render.lean`, not `Theorems/Vt.lean` — and reported `penSgr_feed` and
`sgrOf_feed` as gaps by quoting SCRATCHPAD entries that predate them landing. Verified
each disputed claim by grep before planning on it. A stale worklog entry reads exactly
like a current gap; the check is cheap and the plan built on it is not.

Purpose: replace the monolithic row induction with a named invariant, which is what
makes the exact claim affordable. `rowAnsi` already threads `(bytes, pen, x)`; the
missing piece is `pending`, which the 2026-08-15 negative result proved is
load-bearing rather than noise.

Remaining shape: a `PaintState` record; `rowAnsi` refactored to carry it; `Matches w P g k`
meaning "`w`'s row agrees with `g` on columns `< k`, and `w`'s cursor and pen are
`P`"; one step lemma per cell shape, with `mend_of_pairOk` as the stability argument
for the re-mend after each write.

**Constraints the hazard enumeration turned up** (2026-08-17). Each of these is a way
the obvious statement would be wrong, so they are recorded before the proof rather
than discovered during it:

1. **`PaintState` carries the parser *triple*, not a pair**: `pstate = .ground`,
   `u8need = 0` **and** `u8acc = 0`. `cellText_feed`/`utf8s_feed` all require the
   third, and inside the wide-with-marks rung the stream goes CSI → glyph, so it must
   be re-established rather than assumed once. (`ua_print'` is the print half; the
   CSI half comes from the walk's own record equation.)
2. **The wide pair is ONE induction step advancing `k` by two.** Not two steps of one.
   If `k` ever sat between a width-2 base and its shadow, `halfPair (k-1)` would be
   true at that moment and the re-mend would blank the base the previous rung just
   painted. The shadow slot is a no-op on the receiver — its column was written by the
   base's `printPut` — but it still advances the fold, which is exactly why the two
   must be consumed together.
3. **The row-exit `pending` is branch-dependent, so do not claim it unconditionally.**
   After a width-1 or unmarked width-2 last cell it is `w.modes.wrap`; after a
   *marked wide* last cell it is **false**, because the branch's trailing `CHA`
   cleared it. `rowAnsi_writes_row`'s conclusion should claim `x = cols - 1` and
   leave `pending` to be re-established by the following `carriageReturn` — which
   discards it unconditionally, so nothing downstream cares.
4. **`RowOk` is load-bearing for row *isolation*, not just for agreement.** A width-2
   base in the final column is a broken pair (its out-of-range neighbour reads as a
   width-1 default), and `RowOk.pairs` excludes it. Without that, the base would wrap
   and the joining CRLF would scroll the whole grid — a cross-row catastrophe, not a
   cell mismatch. Likewise `RowOk.size : row.size = cols` is what keeps `printWrap`
   from ever firing mid-row.
5. **`cols = 1` must not be excluded** — the fuzz corpus's `dims` includes `(1,1)`, so
   every seed exercises it. `cols = 0` needs no side condition (the claim is vacuous
   via `RowOk.size`, not via the receiver), so do not add `0 < w.cols`.

Exit: `rowAnsi_writes_row` for any `RowOk` row, from any receiver matching the
claimed `PaintState`. A same-shape value mutation in `rowAnsi` breaks it.

## Step 4 — the grid, and the end-to-end claim

Status: **item 5 proved for the main screen; the alt-screen branch remains** (2026-08-18).
The `joinCRLF` row walk with the no-scroll argument (`paint_rows`, `crlf_step`,
`lineFeed_interior`), the whole-grid paint (`gridAnsi_writes_grid`), the cross-row locality
(`OffRow` + companions), and the prologue's canonical entry state (`prologue_sticky`,
`prologue_modes`) are all proved and committed, and so are the composition
(`paint_entry`, `restore_grid_any_main`, `restore_grid_reachable`) and the decoder
preconditions (`uaz_feed`, `U8Ok`). Remaining: the **alt-screen** branch (blocked only on the
modes at the switch — add `org` to `Matches`; see "Where this stands"), the `rows = 1` corner,
and `resume_grid`.

Shape: `joinCRLF` row walk (including the argument that no line feed scrolls), the
alt switch, then composition through `restore_grid_of_paint` — which already exists,
already reduces `restore_grid` to the paint prefix, and whose first hypothesis is
now discharged for any receiver (`paint_grounds`).

**Correction to this step, from the same enumeration.** The line above used to say the
no-scroll argument "needs Step 1's scroll-region claim". **It does not, and citing
`restore_region_any` or `restore_alt_any` there would be a category error**: those are
*end-of-stream* conclusions, and `regionAnsi` is emitted **after** the paint. What the
paint needs are three **mid-stream** facts about the state the prologue leaves:

* `(w.feed (prologueAnsi v)).top = 0 ∧ .bot = w.rows - 1` — the accepted `DECSTBM`.
  It exists today only *inside* `restore_sticky_any`'s proof and has to be lifted out.
* `(w.feed (prologueAnsi v)).altGrid = none` — holds for **any** receiver with no
  hypothesis, both branches of `leaveAlt` ending there.
* `(w.feed (prologueAnsi v)).modes.origin = false` — without it the bare `CSI H`
  homes to `(0, top)` and every absolute address downstream shifts.

Then `cursor.y = y` plus `bot = rows - 1` is what rules the scroll out at each CRLF,
by the row induction's own cursor bookkeeping. Two traps to avoid:
`smap_id_gridAnsi` **looks** like a no-scroll theorem and is not one — it is
region-*persistence* only, and says nothing about the grid; and `stick_lineFeed` is an
unconditional theorem about the operation that *does* scroll, so it is not evidence
that a line feed is harmless.

A wrap-`pending` armed by the last cell of a row **cannot** cause a scroll at the
CRLF: `printWrap` is the only consumer that line-feeds and it fires only on a
printable byte, of which the separator has none — the `CR` discards `pending` before
the `LF` looks at anything.

**And one genuine new receiver hypothesis.** `ED 2` does *not* establish that the
receiver's rows are the right length: `Vt.eraseScreen 2` is a fold of `eraseRowSpan`,
which writes into *existing* cells, so a receiver whose rows are shorter than its
`cols` stays short and writes past the end vanish. So the grid claim needs
`GridOk w.cols w.rows w.grid` (equivalently `Renderable w`) on the **receiver**,
alongside `w.cols = v.cols` and `w.rows = v.rows`. That is a real limit on "any
receiver" and belongs in the statement, not in a comment.

Exit: criteria 5 of Definition of done.

## Step 5 — review, document, archive

Status: not started.

Write the **conformance profile** into THEOREMS.md (route 1 above): the receiver
behaviours the restore stream depends on, as a reviewable list — absolute `CUP` with
DECOM off, deferred wrap at the right margin, the SGR parameter cap, `ED 2` leaving
modes alone, charset designation scope, and the DECOM/DECSTBM cursor homing the
hand-back has to work around. Each entry is a place a nonconforming terminal would
diverge from a green proof, so the list is the honest boundary of the self-consistency
claim — and doubles as linger's stated compatibility requirement.

Archive `specs/terminal-contract.md` and `specs/grid-fidelity.md` with completion
records once their carried obligations land here. Neither may be archived while its
exit criteria are unmet; that is why both are still in `specs/`.

## Carried decisions

Recorded so they are not relitigated:

- **Autowrap stays on across the repaint.** `Vt.printMark` reads wrap-pending to
  attach a combining mark to the margin cell it just wrote, and no absolute cursor
  move can express that position. Two fuzz seeds catch the alternative
  (SCRATCHPAD 2026-08-15).
- **`ED 2`'s cell-level blanking is not on the critical path.** The paint writes every
  column, so only `eraseScreen_two_frame` is needed, and it is proved.
- **The exact-cell claim is not to be weakened.** Choosing test coverage over proof
  for the anchor claim was considered and rejected: the fuzzer's exclusion list was
  historically non-empty, so cell bugs here are real and recurring.
- **Explicit private-mode sets, not DECSTR.** We already parse the former, so the
  prologue costs no new parser surface, and `CSI ! p`'s reset list varies by
  terminal. The hand-back inherits this for the same reason.
- **The hand-back places the cursor rather than preserving it.** `?6l` and `CSI r`
  both home the cursor, here and on real terminals, so there is nothing to preserve
  by the time the resets are done; and DECSC/DECRC cannot be used to save it, because
  the bundle a real DECRC restores (pen, charset, origin, wrap) is exactly the state
  being reset. `CSI 999 ; 1 H` parks it bottom-left, clamped by the receiver so the
  stream needs no size. `SGR 0` comes last for the same DECRC-bundling reason.
- **The hand-back is a constant.** What linger gives back does not depend on what the
  session was doing — which is the whole claim, and is why it takes no `Vt`.
