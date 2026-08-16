# restore-conformance — restore works into any client, and the proofs say so

Status: active
Updated: 2026-08-16
Predecessor: `specs/terminal-contract.md` (Steps 1–3 complete; its Step 4 is carried
here in a different shape, and its Step 5 archival gate is carried unchanged)

## Where this stands — read this first

**Next step:** the **tab-ruler leak** an adversarial review of this round turned
up (Step 0 findings ledger, item 0) — `tabsAnsi` is set-only, so a client whose
previous occupant set a custom ruler keeps it. Same shape as `87f64b3`, reproduced
against `replayEq`, and it is a *behaviour* fix so it outranks the remaining proof
work. Then Step 2's `u8need` half (Definition-of-done item 3; the parser half is
done), then Steps 3–4 — `PaintState` and the grid *cells* induction (items 4–5).
Items 3, 4 and 5 are what remain of the Definition of done.

**Done:** Step 0 — two bugs fixed. **Step 1 is complete**: A5 is proved at the
value level in both directions for the modes, the pen and the sticky bundle
(region, both charsets, shift state, screen selection). Four restored fields are
*not* covered and are named here so the list is not mistaken for "just the cells":
the screen **cells** (Steps 3–4), the window **title**, the **tab ruler** (which a
theorem would find FALSE — ledger item 0) and the **DECSC slot**; `restore_cursor`
also still quantifies over `Vt.init` rather than any receiver.
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

Step 2 — first half (`restore_grounds`). Steps 3–5 — not started.

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

0. **`tabsAnsi` is set-only: a client's leftover tab ruler survives the restore.**
   *The next item.* Found 2026-08-16 by an adversarial review of the sticky-field
   claims, asking the spec's own question of a field no theorem covers. `tabsAnsi`
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
   *receiver's* ruler. Fix: emit the ruler unconditionally (`CSI 3 g` then one `HTS`
   per stop), which also makes `restore_tabs_any` provable — as things stand such a
   theorem would be **false**, not merely absent. Needs a `dirtyTabs` fixture and the
   five `ends_`/`quiet_`/`keeps_`/`mmap_id_`/`smap_id_` `tabsAnsi` proofs updated
   (they all `split` on the guard that would go away).

1. ~~**Reattach at an unchanged size wipes the scroll region and tab ruler.**~~
   **Fixed in `33b107e`**, and certified: `Session.onMsg .attach` now guards the
   `Vt.resize` on an actual dimension change, `Theorems/Session.lean`'s
   `onMsg_attach_same_size_vt` proves the same-size attach leaves `vt` untouched, and
   `Tests/Session.lean` pins it with a non-vacuity case. Kept here with its original
   diagnosis because it is what made item 0 reachable: with the guard in place a
   same-size reattach preserves the child's ruler, so `tabsAnsi` is no longer dead on
   the attach path — it is live and wrong.
2. **Label values are not tab/newline-scrubbed.** `infoText` frames fields as
   `k\tv\n`; `.labelSet`/`linger set` apply no filter, so a label value with a newline
   and tab forges an extra row — including a `status`/`state` pair — in the listing.
   `name_clean` proves the status column is clean; labels bypass it. The local-listing
   `cmd` and `label.*` display also lost the `Remote.scrub` that the old `Tui.rowOfInfo`
   applied, in a refactor. **§Row/§Status integrity**; fix is to scrub or reject the
   two framing bytes at `.labelSet`.
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
3. `Ends`, `Quiet` and `Keeps` re-stated without the ground-parser assumption, which
   requires the prologue to lead with a sequence abort so a client caught
   mid-escape resynchronises.
4. `PaintState` — the painter's abstract state (`x`, `y`, `pen`, `pending`) as a
   named record, with `rowAnsi` threading it, and a `Matches` relation tying it to a
   `Vt` and a row prefix.
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

Status: **first half done** (2026-08-15). `restore_grounds (v w : Vt) :
(w.feed (restore v)).pstate = .ground` holds with no hypothesis on `w` — the first
receiver-quantified theorem in the file. Chain: `un_abortUtf8_esc`, `esc_lands` (one
case per `PState`), `st_finish`, `st_grounds`, `prologue_grounds`.

The abort turned out to be `ESC \` (ST) rather than `CAN`: our `stepOsc` treats a C0
byte as payload, so `CAN` would have needed a Core semantics change, while `ST` is
what both string states already listen for and `stepEsc` routes `0x5C` to its default
arm. No new parser surface.

Remaining: the `u8need` half, and the same treatment for `Quiet`'s origin half. Both
need each chunk to preserve its property from an arbitrary start — the per-chunk work
`Keeps` already does for the grid.

Purpose: a client cut off mid-escape is a real state, and every existing stream
theorem assumed it away.

Exit: the three predicates carry no hypothesis on the receiver's parser state.
`restore_quiesced` and `resume_quiesced` follow with their hypotheses removed.

## Step 3 — `PaintState`

Status: not started.

Purpose: replace the monolithic row induction with a named invariant, which is what
makes the exact claim affordable. `rowAnsi` already threads `(bytes, pen, x)`; the
missing piece is `pending`, which the 2026-08-15 negative result proved is
load-bearing rather than noise.

Shape: a `PaintState` record; `rowAnsi` refactored to carry it; `Matches w P g k`
meaning "`w`'s row agrees with `g` on columns `< k`, and `w`'s cursor and pen are
`P`"; one step lemma per cell shape (width 1, width 2 with room, width 0), with
`mend_of_pairOk` as the stability argument for the re-mend after each write.

Exit: `rowAnsi_writes_row` for any `RowOk` row, from any receiver matching the
claimed `PaintState`. A same-shape value mutation in `rowAnsi` breaks it.

## Step 4 — the grid, and the end-to-end claim

Status: not started. Depends on Steps 1–3.

Shape: `joinCRLF` row walk (including the argument that no line feed scrolls, which
needs Step 1's scroll-region claim), the alt switch, then composition through
`restore_grid_of_paint` — which already exists and already reduces `restore_grid` to
the paint prefix.

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
