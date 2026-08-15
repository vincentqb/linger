# restore-conformance — restore works into any client, and the proofs say so

Status: active
Updated: 2026-08-15
Predecessor: `specs/terminal-contract.md` (Steps 1–3 complete; its Step 4 is carried
here in a different shape, and its Step 5 archival gate is carried unchanged)

## Where this stands — read this first

**Next step:** Step 1, built on the hand-back first (`sets_leaveAnsi_*`) and then
reused for `modesAnsi` — see Step 1, which now names the one prerequisite edit.

**Done:** Step 0 — done, **one finding, fixed and pinned by a test, theorem
pending** (the hand-back; see below and SCRATCHPAD 2026-08-15T20:10). Step 1 —
predicate and laws only, no instances. Step 2 — first half (`restore_grounds`).
Steps 3–5 — not started.

**Step 0's finding, because it changes the shape of the goal.** The bug family was
not exhausted, and the miss was one of *direction*: every fix so far concerned what
`restore` assumes about the client it writes **into**, and nothing asked what linger
**leaves behind**. A detaching client restored termios and nothing else, so
detaching out of any full-screen program handed the user's shell a terminal still on
the alt screen, with mouse reporting on, no cursor, autowrap off, a stale scroll
region and DEC line drawing selected. Fixed with `Render.leaveAnsi` — a constant, in
`Client.attach`'s `finally` — and pinned by `tests/attach_test.py` step 9.

So the goal below is half of a pair, and the pair is what the product actually
promises: **linger borrows your terminal and must both establish what it needs and
give back what it took.** Both halves are the same theorem shape (`Sets`, quantified
over the receiver), which is why the hand-back joins Step 1 rather than opening its
own spec.

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
holds for any receiver with no hypothesis at all. The rest of the layers
(`Ends`/`Quiet`/`Keeps`, `restore_grid`) still assume a pristine, ground receiver, so
for everything except the parser state the tests are still the only guard.

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
  establishes what the repaint needs (`restore_grounds` ✓; the modes are Step 1);
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

Status: **done** (2026-08-15). One finding, fixed: the hand-back (`Render.leaveAnsi`,
`tests/attach_test.py` step 9, SCRATCHPAD 2026-08-15T20:10). Its theorem is folded
into Step 1.

What was checked and needs no emitter of its own, so a future session does not redo
it: `linger history` emits `rowText`, whose every character passes `safeChar`, so it
carries no escape byte and cannot dirty the terminal it prints to (`withAnsi = true`
is unreachable from the CLI — `Session.onMsg` passes `false`); `Zmx/Core/Listing.lean`
and `Status.lean` emit no escape sequences at all, glyphs only; `resizeEffects`
carries no bytes, only a `resizePty` effect.

Exit criterion, met: each emitter either establishes what it depends on, or has a
recorded reason it need not.

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

1. `Sets`, a predicate for "this chunk leaves property `P` at value `x` regardless of
   the receiver's incoming state", with `nil`/`append`/`ite` composition laws
   mirroring `Ends`/`Quiet`/`Keeps`.
2. `restore_modes_any`: for every `v` and every `w`, the modes after
   `w.feed (restore v)` are `v`'s — the theorem that certifies `87f64b3` instead of
   the tests carrying it alone. Likewise the charset flags, the scroll region, and
   the alt-screen flag.
2b. `leave_canonical`: for every `w`, the modes, charset flags, scroll region,
   alt-screen flag and pen after `w.feed leaveAnsi` are the canonical ones and the
   parser is `ground` — the outbound half, and anchor A5. Independent of any session
   state, since `leaveAnsi` takes no argument.
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

## Step 1 — `Sets`, in both directions

Status: predicate and laws in; no instances yet.

Purpose: make three shipped fixes theorems rather than tests — `87f64b3`'s both-ways
modes, `cd7c17b`'s lead-in, and the hand-back. This is the cheapest step and the one
that pays first, because it is a frame-shaped claim — the kind that has caught every
real bug in this project — with the quantifier corrected.

Reads: `Zmx/Core/Render.lean`, `Theorems/Render.lean`, `SCRATCHPAD.md`.
Writes: `Theorems/Render.lean`, `THEOREMS.md`, `SCRATCHPAD.md`.

Shape: `Sets (P : Vt → α) (x : α) (bs : Bytes) : Prop := ∀ w, P (w.feed bs) = x`.
The composition law that matters is *left*-absorbing: `Sets P x b → Sets P x (a ++ b)`
for any `a`, which is what lets a later chunk overwrite an earlier one and is why
both-ways emission is provable at all.

**Do the hand-back first.** `leaveAnsi` is the same claim with every complication
removed: a constant, no `ite`, canonical values as literals. Prove the ladder there,
then `modesAnsi`'s session-dependent version is that ladder plus `Sets.ite`. The
reverse order pays the hardest case first for no reason.

**The one prerequisite edit**, unchanged from the last session's reading: factor the
CSI walk so it exposes the **dispatch**, not just the grid fact.
`keeps_csi_digits_tail` performs the walk and then discards everything except
`pstate`/`u8need`/`grid`; a mode claim needs the same walk to hand back "this is
`csiDispatch t final` for a `t` whose only parameter is `n`, with `priv` and `ignore`
as they were". `csi_digits_run_eq` already carries `ignore` and `priv` through the
digit run, and `org_setMode_decom_off` → `org_csiFinish_decom_off` is the template
for one field. Consumers stay in the `∀ w` shape, so no pstate-congruence lemma for
`csiDispatch` is needed: the dispatch fact applies to the walked state directly.

Exit: `leave_canonical` for the ten `Modes` fields, `g0Line`, `g1Line`, `shiftOut`,
`top`, `bot`, `altGrid.isNone`, `pen` and `pstate`; then `restore_modes_any` for the
same fields with the session's values. Deleting any one both-ways emit from
`modesAnsi`, or any one line of `leaveAnsi`, breaks the corresponding claim.

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
