# scrollback-fidelity — the ring reaches the terminal, and the scroll gets its positive spec

Status: active
Updated: 2026-08-18
Predecessors: `specs/restore-conformance.md` (complete — the screen, on both
screens at every height), `specs/ledger-cleanup.md` (complete). This opens the
successor both parked: `restore` repaints the screen and drops the history above
it (`THEOREMS.md:45`, `Tests/Render.lean:22`).

## Where this stands — read this first

**Next step:** Step 1 — the emitter and the oracle. Nothing else. Step 1 must
leave `restore_grid_any` / `restore_grid_reachable` / `resume_grid` green with
their statements unchanged; if it cannot, stop and read the kill criteria rather
than weakening them.

**Precondition:** the working tree must be clean. `git status` at the time of
writing shows uncommitted edits in `Theorems/Render/{Grid,Modes,Row}.lean` and
`Theorems/Vt.lean` (-18 lines, post-split cleanup). Step 1 edits `Grid.lean`
heavily; commit or stash that first.

**Stale reads to distrust:** any line number for `Theorems/Render.lean` — it is a
38-line façade since `56eedda`; the ladder is in `Theorems/Render/*.lean`.
`restore_tabs_any` landed (`Tabs.lean:652`); nothing is in flight there.

## Goal

Put the session's scrollback into the **receiver's own** scrollback buffer, so
that wheel-scroll, search and selection see the history above the screen — and
prove it, for any client, with the same receiver-quantified shape the screen
already has.

There is exactly one way to put a line into a terminal's native scrollback: print
it inside a whole-screen scroll region and let it scroll off. So the ring must be
painted and then pushed. The design question is only *where* that happens relative
to the screen paint, and `paint_rows` (`Theorems/Render/Grid.lean:794`) decides it:
its no-scroll argument is `Y + rs.length = rows` plus `crlf_step` (`:653`) under
`hy : v.cursor.y < v.bot`. **Painting `sbRows v ++ v.grid` as one tall array makes
the painted-row count exceed the screen height and deletes that argument** — and
with it `restore_grid_any_main` (`:1345`), `restore_grid_any` (`:1648`),
`restore_grid_reachable`, `Resume.resume_grid`. So the history push is its own
stage, *before* the screen paint, and the screen paint is byte-for-byte unchanged.

Scope, named so it is a decision and not a side effect: **text rows only**. A
sixel or kitty placement that was in the ring stays gone — consistent with the
settled non-goal on images. Sold as "scrollback fidelity" without that sentence,
this reads as re-opening it.

## Definition of done

1. `restore` repaints the session's ring into the receiver's ring: the history
   rows, oldest first, each fitted to the session's width, trimmed to a byte
   budget from the oldest end. `Vt.resize` (`Zmx/Core/Vt.lean:673-698`) does not
   touch `sb`, so the fit is mandatory, not hygiene.
2. `Tests/Render.lean`'s `replayEq` (`:27`) compares `sb` against `sbRows v`, and
   its docstring loses "Deliberately excluded: `sb`" (`:22`). The suite carries a
   `dirtySb` receiver (its own history, non-empty, different from the session's —
   the analogue of `dirtyTabs` at `:330`) and `roundtripsFrom (midOsc …)` on a
   scrolling session, because the push now sits inside the region a swallowed
   stream would eat (commit `cd7c17b`).
3. **The byte-budget gate.** `sbTake_budget`/`sbRows_budget` bound the *counted*
   cost `sbRowCost`; only fixtures bound the *emitted* bytes. So the suite carries
   a `native_decide` bound on `(restore heavyRing).length` **and** a non-vacuity
   fixture `(sbRows heavyRing).size < heavyRing.sb.size`, plus a pty assertion on
   the reattach burst length with the measured number in the failure message. This
   asymmetry is stated in the spec and in `THEOREMS.md`, not glossed: the proofs
   are self-consistent about their own cost function and would survive changing
   `sbRowCost`'s `+ 6` to `+ 0`. The fixtures are the oracle until item 8 lands.
4. `restore_grid_any`, `restore_grid_reachable` and `Resume.resume_grid` compile
   with their **statements unchanged** — no new hypothesis, in particular none
   about `v.sb`. This is what `fitRow`'s unconditional `RowOk` buys, and it is the
   item that fails if anyone substitutes a bare `Vt.resizeRow`.
5. The **positive scroll specification**: `scrollUpIn_rows` (what a full-screen
   scroll *writes* — row `y'` becomes row `y'+1`, the vacated bottom row is
   `blankRow v.cols v.pen`, the pen **in effect**), `scrollUpIn_sb` (it pushes
   `v.getRow 0`, exactly once, iff the guard holds), `lineFeed_scroll`. This
   closes the gap `THEOREMS.md:358-361` names in its own words: "a frame says what
   an operation leaves alone, never what the written fields *become*."
6. `restore_sb_any` (any `Good`/`Renderable` receiver of the session's dims),
   `restore_sb_reachable` (hypotheses discharged from `LiveReachableVt`), and
   `Resume.resume_sb` — mirroring `restore_tabs_any` (`Tabs.lean:652`),
   `restore_tabs_reachable` (`:700`), `Resume.resume_tabs`.
7. `THEOREMS.md`: a conformance-profile entry for `CSI 3 J` recorded as a
   **divergence** (ours clears the screen too — `Zmx/Core/Vt.lean:529-531`; xterm's
   erases saved lines only); the A5 sentence at `:45` amended (scrollback leaves
   the fixture-carried list); the §Restore bullet at `:538` made true, with the
   budget named as its limit. `README.md` gains the note that attaching discards
   the user's own terminal scrollback in that window, next to the graphics limits.
8. `./lake build`, `./lake build Theorems Tests`, `./tests/e2e.sh` green and
   warning-free at every step boundary; `python3 tests/coverage.py` still reports
   `20 (cap 20)` — every new `Zmx/Core/*` def named in a theorem **statement**,
   the cap **not** bumped; every theorem and fixture break-verified with the break
   in `SCRATCHPAD.md`.

## Steps

### Step 1 — the emitter and the oracle: the whole capability, no new induction

Status: → next.

New in `Zmx/Core/Render.lean`, after `gridAnsi`:

- `crlfB : Bytes := [0x0D, 0x0A]` — one syntactic unit for the flush to rewrite.
- `cellFit (c : Cell) : Cell` — `base := printableChar c.base`,
  `width := if c.width == 0 then 0 else charWidth base` (**the zero branch is
  load-bearing**: collapsing a wide glyph's shadow to width 1 shifts every pair
  after it), `marks` filtered to zero-width printables and `.take 8`, pen kept.
  Every clause is one field of `CellOk` (`Theorems/Vt.lean:3198-3202`), so
  `cellOk_cellFit` is unconditional. Same discipline as `printableChar` on store.
- `fitRow (row : Row) (cols : Nat) : Row := Row.mend ((Array.range cols).map (fun i => cellFit (row.at i)))`.
  **Not** `Vt.resizeRow`: that copies cells verbatim, and `sb` rows are the one
  place no stated invariant covers.
- `sbReplayBytes : Nat := 262144` — the budget, **in emitted bytes, not rows**. A
  blank 80-column row costs 82 (`Cell.erased` emits one space, no SGR, `+2` CRLF);
  a truecolour-per-cell row costs ~43 B/column, so a full `sbCap = 10000` ring of
  those is ~86 MB against a 4 MiB `outbufCap` that *disconnects*. A row cap bounds
  nothing that matters.
- `sbRowCost (row : Row) : Nat := (rowAnsi row {}).1.length + 6` — paint, `+2` for
  the pushing CRLF, `+4` slack for the one `SGR 0` a row can emit that a
  default-seeded count does not (`penSgr {}` is four bytes; bounded because the
  fit's `mend` rules out a width-0 first cell).
- `sbTake (cols budget : Nat) : List Row → List Row` — structural on the list,
  fit fused in so the per-cell work touches only the rows kept; **stops** at the
  first row that does not fit rather than skipping it, so the result is always
  "the newest N lines".
- `sbRows (v : Vt) : Array Row := (sbTake v.cols sbReplayBytes v.sb.toList.reverse).reverse.toArray`
  — `Ring.toList` is oldest-first (`Zmx/Core/Vt.lean:196`, docstring and `push`
  agree) and oldest-first is the push order. The double reverse is where the
  order bug will actually live.
- `scrollbackAnsi (v : Vt) : Bytes := csiNum 3 0x4A ++ (if (sbRows v).isEmpty then [] else gridAnsi (sbRows v) ++ (List.replicate v.rows crlfB).flatten) ++ csiNum 4 0x6C ++ modeSet 6 false ++ modeSet 7 true`.
  - `ED 3` first: a client is not a reset terminal, and a second attach would
    otherwise stack another copy. The set-only lesson of `tabsAnsi`/`titleAnsi`,
    one field further out.
  - `gridAnsi (sbRows v)` homes and paints `m` rows with `m-1` separators; `v.rows`
    more CRLFs push exactly `m` (pushes `= C - (rows-1)` where `C = (m-1)+rows`).
    `F = v.rows` is the unique correct count.
  - The empty guard is load-bearing — the `broadcast_empty` defect one module over.
  - The three mode re-establishments: `paint_entry` needs
    `insert = false, wrap = true, origin = false` and gets them through an `MMap`,
    which cannot be pushed across the ring's **glyph** bytes (no
    `mmap_id_gridAnsi`; `Modes.lean` explains the asymmetry). Twelve ASCII bytes
    move the obligation to where `mmap_irm`/`mmap_modeSet` already close it, and
    zero `u8need` for free through `abortUtf8`.

`screensAnsi` (`Zmx/Core/Render.lean:341`) gains `scrollbackAnsi v ++` at the
front, **before** the `match v.altGrid`. Not a new top-level stage in
`restoreBody`: 55 occurrences of the literal `prologueAnsi v ++ csiNum 0 0x6D`
prefix exist across `Theorems/Render/{Keeps,Tabs,Sticky,Modes,Grid}.lean`, and
`restore_split`, `restore_grid_of_paint`, `keeps_restoreTail`,
`restore_tabs_split` and the `Modes.lean` chains all name `screensAnsi v`
*opaquely* — so this placement touches four unfold sites instead of fifty-five
rewrites. It also means the flush's evicted rows `m…rows-1` are the **blanks the
preceding `ED 2` left**, not the receiver's junk, which is strictly more forgiving
than pushing before the clean slate.

Naming theorems (the coverage gate is at 20/20, so each base name must appear in
a theorem *statement* — a docstring does not count, `coverage.py` strips comments):

- `sbTake_budget : ((sbTake cols budget l).map sbRowCost).sum ≤ budget` — names
  `sbTake`, `sbRowCost`. Induction on the list; `dsimp only` then `split`; `omega`.
- `sbRows_budget (v) : ((sbRows v).toList.map sbRowCost).sum ≤ sbReplayBytes` —
  names `sbRows`, `sbReplayBytes`. If `List.sum_reverse` is absent in 4.32 core,
  go via `(List.reverse_perm _).sum_eq` or state the first over `foldr`.
- `sbTake_prefix` — the kept rows are a contiguous **newest** run, `map fitRow` of
  a `take`. This is what licenses "oldest dropped first" in the docs and is the
  shape Step 3 consumes.
- `cellOk_cellFit (c) : CellOk (cellFit c)` — unconditional; four clauses,
  `printableChar_emittable` (`Theorems/Vt.lean:3186`) for the first.
- `rowOk_fitRow (row cols) : RowOk cols (fitRow row cols)` — `rowOk_mend`
  (`:3318`) ∘ `cells_map_range` (`:4025`). **No hypothesis.** Names `fitRow`.
- `fitRow_id_of_rowOk` — the fit is the identity on rows a live session stores, so
  comparing against `sbRows` is not a weakened target. Names nothing new; earns
  its keep as the anti-vacuity receipt.
- `ends_scrollbackAnsi`, `quiet_scrollbackAnsi`, `smap_id_scrollbackAnsi`, plus
  `ends_crlfRun`/`smap_id_crlfRun` — names `scrollbackAnsi`, `crlfB`. Two to six
  lines each: `ends_gridAnsi` (`Ends.lean:~820`), `quiet_gridAnsi`
  (`Quiet.lean:~698`) and `smap_id_gridAnsi` (`Sticky.lean:~493`) are already
  generic in the array, which is the single fact that makes this step cheap.
- `scrollback_entry (v w)` — the bridge. Feeding `scrollbackAnsi v` after
  `paint_entry`'s prefix preserves all sixteen of `paint_entry`'s conjuncts:
  dims by `dims_feed`, `gsz`/`rlens` by `renderable_feed`, sticky by
  `smap_id_ed 3` + `smap_id_scrollbackAnsi`, modes by `MMap` over the trailing
  `4l ?6l ?7h`, `u8need`/`u8acc` because the stage ends in ASCII, `altGrid = none`
  because nothing here emits `?1049h`. The four unfold repairs
  (`Quiet.lean:722`, `Sticky.lean:619`, `Ends.lean:852`, `Grid.lean:1355,1630`)
  then each gain one `.append` / one longer `hscreens`.

Tests (`native_decide` is allowed in `Tests/`, banned in `Theorems/` by
`tests/e2e.sh`): `replayEq`'s new conjunct; `scrolled := screen 6 2 "aa\r\nbb\r\ncc\r\ndd\r\nee"`
with a non-vacuity check that its ring has three rows; `dirtySb`; the **headline**
fixture `String.fromUTF8! ⟨(history r false).toArray⟩ == "aa\nbb\ncc\ndd\nee\n"`
after restoring into `dirtySb` (a length check would not catch an off-by-one
flush); `roundtripsFrom (midOsc 6 2) scrolled`; a wide glyph and a combining mark
**in the ring**; the shrink case `(screen 8 2 "abcdefgh\r\n22\r\n33\r\n44").resize 4 2`
with both `(sbRows v).all (·.size == 4)` and `!(v.sb.toList.all (·.size == 4))`;
`heavyRing` (300 lines of per-cell truecolour through 40 columns) with the
non-vacuity, cost and emitted-length bounds.

Python: `tests/attach_test.py` step 11 — `\x1b[3J` present, `ED 3` before `ED 2`,
a line that scrolled off the screen reappears, burst inside budget, client still
alive after both the plain and the truecolour burst. `tests/resume_test.py` —
push `survives-the-reboot-42` (`:42`) off the screen with a 60-line loop before
the detach, so the existing assertion at `:79` is *strengthened* to prove the ring
survived the checkpoint **and** reached the terminal. It fails today.

Docs: conformance-profile entry (a divergence), README note, `SCRATCHPAD.md` step
notes with the breaks.

**Exit:** all three build gates green and warning-free; `coverage.py` at 20/20;
`restore_grid_any` / `restore_grid_reachable` / `resume_grid` **statements
byte-identical to today** and green; the leak reproduced and closed under breaks
B1 (delete the paint branch → `history` gives the screen only), B2 (drop `ED 3` →
`roundtrips` from a fresh `Vt.init` still passes while `dirtySb` fails — the exact
blind spot that hid the ruler bug), B3 (`ED 3` after the push → our model wipes
what we just filled), B4 (flush `rows-1` loses the newest history row; `rows+1`
leads with a blank), B5 (drop the outer `.reverse` → history reads backwards), B6
(bare `resizeRow` → the shrink fixtures fail; record which fixtures *don't*
notice), B7 (budget to `1 <<< 30` → emitted-length fixture fails; budget to `0` →
the `scrolled` fixtures fail, proving the trim is not silently eating everything),
B8 (`cellFit` without the width-0 guard → `fitRow_id_of_rowOk` and the wide-glyph
fixture fail while `cellOk_cellFit` still proves — the honest warning that `CellOk`
does not measure the sanitizer's correctness), B11/B12 (the two Python halves).

### Step 2 — the positive scroll specification, zero emitter change

Status: pending.

In `Theorems/Vt.lean`, beside `lineFeed_interior`:

- `getD_foldl_set_range` — a fold of `setIfInBounds` at distinct indices from a
  **fixed source**. This is why `scrollUpIn` is tractable at all: its fold reads
  `v.getRow`, never the accumulator (`Zmx/Core/Vt.lean:314`). Model:
  `foldl_setTab_mem`/`_not_mem` in `Theorems/Render/Tabs.lean`, the same shape over
  `Array Bool`, so the recipe is proved in-repo.
- `scrollUpIn_rows`, `scrollUpIn_sb`, `lineFeed_scroll` — as in Definition-of-done
  item 5. State the vacated row's pen (`blankRow v.cols v.pen`); do **not** hide it.
- `ring_push_data` (non-wrap branch is `data.push`, `start` untouched),
  `ring_toList_of_start_zero`, `take_succ_getD`.
- `write_shape`/`write_shape2` (`Theorems/Vt.lean:2903,2920`) gain a `.sb = u.sb`
  conjunct — the same `rw [frame_printAdvance, frame_mendRow, frame_putCell]` line
  their `cols` conjunct already uses.
- `OffRow` (`Theorems/Render/Grid.lean:25`) gains a fifth field `sb : u'.sb = u.sb`.
  Its `cells` clause **cannot** supply this: at `rows = 1` a scroll rewrites only
  row `y`, so `cells` is vacuous while the ring grows. `refl`/`trans` are trivial;
  the ~8 cell rungs read it off `write_shape` or the state equation they already
  rewrite with; `rowAnsi_writes_row`'s statement is unchanged.
- `paint_rows` gains one conclusion conjunct `(w.feed …).sb = w.sb` — never a
  weakening, and it is what carries the ring across the alt screen's second paint.

**Exit:** gates green; `THEOREMS.md:358-361` gains the receipt that the positive
specification now exists for the one operation the scrollback story rests on.
Break-verified by changing `Zmx/Core/Vt.lean:314` to read the accumulator
(`scrollUpIn_rows`' first conjunct stops closing) and `:315` to `blankRow v.cols {}`
(the pen conjunct fails; a coloured-history fixture goes false while a plain one
still passes). Deleting `OffRow.sb` and attempting Step 3 must fail on the
`rows = 1` fixture — run that once to see the vacuity.

### Step 3 — the scroll walk and the `Fixes (·.sb)` tail

Status: pending.

- `crlf_scroll_step` — `crlf_step`'s twin at `cursor.y = bot`, as a **full state
  equation**: `crlf_feed` → `lineFeed_scroll` → `frame_scrollUpIn`
  (`Theorems/Vt.lean:812`) → `frame_carriageReturn` for `getRow 0`/`cols`/`pen`.
  Its guard `top = 0 ∧ bot = rows-1 ∧ altGrid = none` is exactly what
  `paint_entry` (`Grid.lean:1267`, fifteenth conjunct) and `scrollback_entry`
  establish.
- `push_walk` — the walk over the history rows with a ring accumulator. Invariant
  `(off, Y)`: `off` rows evicted, cursor on screen row `Y`. Two phases, uniform:
  step-down is today's `crlf_step`; scroll shifts `done` by one with **no index
  arithmetic** (`T.getD (off+1+y')` is old `done` at `y'+1`) and the ring by one
  `List.take` step. `rows = 1` needs no special case and no `rows ≥ 2` hypothesis
  — re-introducing that restriction would make this theorem disagree with
  `restore_grid_any` about which heights it covers, which commit `8dc61a4` fought
  to remove.
- The flush: `rows` CRLFs from `(0, rows-1)` push exactly `m` — repeated
  `crlf_scroll_step` from a known-blank screen, which is the easier half.
- `sbRoom`: the receiver's ring is empty at entry (`ED 3`) and
  `(sbRows v).size ≤ v.sb.size ≤ sbCap` via `Good.sbLe` (`Theorems/Vt.lean:35`) and
  `sbTake_prefix`, so `Ring.push` never rotates and the wrap law is never needed.
- `Theorems/Render/Scrollback.lean` (new file, so `Tabs.lean` is not disturbed):
  `psBlind_sb`, `sb_setMode` (**every** mode number — `enterAlt`/`leaveAlt` keep
  `sb`, `Zmx/Core/Vt.lean:643-659`), the `sb_csiDispatch_*` family, `fixes_sb_tail`.
  A mechanical clone of `fixes_tabs_tail` (`Tabs.lean:375`) with `π := (·.sb)`: the
  `Fixes π` layer (`Tabs.lean:32-95`) is already generic given `PsBlind π`. No `J`
  appears in the tail, so `ED 3` never has to be excused. This is a third of the
  proof lines and the least interesting third.

**Exit:** gates green; the walk's heartbeat number recorded in `SCRATCHPAD.md`
(`paint_rows` already needs `maxHeartbeats 1000000`, `Grid.lean:792`). Break: add
`csiNum 3 0x4A` to `modesAnsi` and confirm `fixes_sb_modesAnsi` fails — the check
that the tail family is not vacuous over `ED`.

### Step 4 — the claim

Status: pending.

`restore_sb_any` → `restore_sb_reachable` → `Resume.resume_sb`, plus
`restore_sb_exact` (`= v.sb.toList` when the history is short enough and its rows
are already the session's width, via `fitRow_id_of_rowOk`). `.toList`, not `.sb`,
is deliberate and honest: the session's ring may have wrapped (`start ≠ 0`) while
the receiver's is built from index 0, so the two records differ in representation
and agree as histories. `THEOREMS.md` A5 gains the row; the fixture-carried list
at `:45` loses scrollback.

**Exit:** gates green; `Zmx/Core/Checkpoint.lean`'s `wRing` dropped from `save`
must break `resume_sb`'s first conjunct (via `load_save_exact`), confirming the
end-to-end claim depends on the checkpoint carrying history.

### Step 5 — optional

Status: pending, off critical path.
`rowAnsi_len_seed` (the `+4` slack made honest) and `scrollbackAnsi_le`, which
retire Definition-of-done item 3's fixtures in favour of a theorem. And a
decision about `Render.history`'s `withAnsi` branch (`Zmx/Core/Render.lean:548-558`):
**it is dead** — the only call site is `Session.lean:250` at `false`,
`history_framing`/`history_lines` are both stated at `false`, and `Cli.lean` has
no flag. Either wire it up as `linger history --color` with its own framing
theorem or delete the argument; unreachable unproved code in the emitter is the
state `tests/coverage.py` exists to prevent.

## Open decisions the implementer must not make alone

1. **`ED 3` discards the user's own terminal scrollback.** `linger` never enters
   the alt screen (`prologueAnsi` emits `?1049l`; the client writes payloads
   straight to `stdoutFd`), so the session and the user's shell share one buffer.
   My recommendation: emit it unconditionally and document it — guarding it
   reintroduces exactly the set-only pattern `tabsAnsi` and `titleAnsi` were fixed
   to eliminate, and without it a second attach stacks a second copy of the ring.
   A `LINGER_NO_SB_REPLAY=1` opt-out is a legitimate alternative (a `Client` env
   read, not a core change) and is not costed here.
2. **Is 262144 the right budget?** Derived (≈3200 blank 80-column rows, more than
   tmux's default 2000-line history, one sixteenth of `outbufCap`), but the binding
   constraint is time on a slow link: 256 KiB over 1 MB/s ssh is a quarter-second
   stall on every attach. Measure one real reattach over the actual ssh path
   before freezing it; 131072 is the safer number if attach latency wins.
3. **`CSI 3 J` in real terminals.** Unverified from this host and unverifiable from
   a pty (a pty has no scrollback). Failure mode is benign — the previous
   occupant's history survives above ours and repeated attaches stack copies — but
   "benign" should be checked for at least the user's own terminal.
4. **The checkpoint has no budget either.** `wRing v.sb` writes the whole ring, so
   a truecolour ring is already a multi-megabyte file on the checkpoint cadence.
   Pre-existing, not added here, and unmeasured — but the same reasoning applies to
   disk.

## Kill criteria and fallback (from the design review)

**Bet A — kill criteria.**

*Step 1 (the emitter).* Kill if **either**: (a) `restore_grid_any` /
`restore_grid_reachable` / `resume_grid` cannot be made green without adding a
hypothesis or weakening a statement — the temptation will be to add something
about `v.sb`, and `fitRow`'s unconditional `rowOk_fitRow` exists precisely so that
is never necessary; if it still is, the definition is wrong, not the theorem; or
(b) the `MMap`-across-glyphs obstacle turns out to be unavoidable *and* the twelve
bytes of mode re-establishment do not clear it — i.e. `scrollback_entry`'s modes
conjunct will not close. Run the experiment either way: drop
`csiNum 4 0x6C ++ modeSet 6 false ++ modeSet 7 true` from `scrollbackAnsi` and
confirm the modes obligation fails. **If it still closes, `mmap_id_gridAnsi` is
reachable after all and the stage should shed those bytes.**
*Fallback that still ships:* `linger scrollback` / `linger history --color` — wire
up `Render.history`'s existing-but-dead `withAnsi` branch
(`Zmx/Core/Render.lean:548-558`; the only call site is `Session.lean:250` at
`false`, and `history_framing`/`history_lines` are both stated at `false`) behind
a CLI flag with its own framing theorem. The user gets coloured history on demand,
no `ED 3`, no destruction of their own scrollback, no touch to `restore`. Strictly
smaller than the goal, but it is a shipped capability and it deletes unproved dead
code either way.

*Steps 2-4 (the ladder).* Kill Step 3 if `push_walk` blows past ~4,000,000
heartbeats, **or** if its scroll branch needs a hypothesis the bundle does not
carry — per house doctrine that means the *bundle* is wrong, so try the flat
structure once before declaring. Do **not** buy a `rows ≥ 2` restriction to make it
go: commit `8dc61a4` fought to remove exactly that, and re-introducing it for a
new claim would make two neighbouring theorems disagree about which heights they
cover.
*Fallback that still ships:* Step 1 and Step 2 already stand. Step 1 leaves the
capability shipped with a decidable oracle — `replayEq` on `sb`, the `dirtySb`
receiver, the byte fixtures, two pty assertions, a strengthened `resume_test` —
which fails the build the moment any of it regresses. That is the same posture
`Tests/Render.lean`'s header documents for the grid before stage 3d landed, and it
is a defensible place to stop. Step 2 stands entirely alone as §Replay's positive
scroll specification, closing the gap `THEOREMS.md:358-361` names. Then A5's
inbound list reads "history: repainted and fixture-carried; the receiver-quantified
claim is future work with the scroll spec already in hand", and
`specs/scrollback-fidelity.md` records `push_walk` as the single blocking rung with
the *measured* reason it stalled.

*The kill criterion nobody will remember to check:* if the product decision on
`ED 3` goes the other way — the user decides discarding their own terminal
scrollback on every attach is unacceptable — Step 1's emitter is dead as designed,
because without `ED 3` a second attach stacks a second copy of the ring. The
fallback is the same `linger scrollback` command. Get that decision before writing
`scrollbackAnsi`, not after the pty test.

**Bet B — kill criteria.**

*Step 1.* Cannot fail; the compile was already demonstrated. If a function turns
out to need `partial` after all, leave it and put the reason in a comment — that is
the outcome `lakefile.lean` asks for.

*Step 2 (`Buf` + the gate).* Kill if the gate cannot be made to pass without
hollowing it out — specifically, if bounding `Cli.queryInfo` through `Buf` turns
into a rewrite of the reply loop, or if the whole-`Zmx/Runtime` scope turns up a
fourth long-lived buffer that does not fit the `Buf` shape. Do **not** narrow the
gate's scope to `Daemon.lean` to make it pass: that leaves `Cli.lean:122`'s
unbounded accumulator alive and puts the next buffer in `Client.lean` where the
gate is not looking, which is a gate measuring nothing.
Also kill if the answer to "does this theorem bite the shipped code?" comes out
honestly *no* — i.e. if the grep turns out to be evadeable by ordinary refactoring
rather than by deliberately writing something novel. The `SHIM_CAP` and
`coverage.py` precedents say it is not, and `coverage.py:116-134` already scans
`Zmx/**`, so there is precedent for a Runtime-side gate — but check, don't assume.
*Fallback that still ships:* Step 1, plus `Buf` and `Theorems/Buf.lean` **without**
the runtime rewiring — a proved, claimed, unreferenced Core module is not much, so
prefer instead: keep the two `Daemon.lean` buffers on `Buf` (the rewiring is 45
lines and closes the sharp-oracle gap for the compaction fix) and drop only the
`Cli.lean` conversion and the `.extract` grep, shipping the two *structural* greps
(no `ByteArray` field, no `mut ByteArray` local) with `Cli.lean`'s accumulator
tracked as a separate one-line item. That keeps the ratchet real and the diff
honest.

*Steps 3-4 (roster, two-pass `pump`).* Both are already optional. Kill Step 3 the
moment `Rt` holds a shadow copy of anything in `Loop`; kill Step 4 if the
`IO.eprintln "BUG —"` alarm cannot be asserted-absent in a live suite, because an
alarm nobody hears is not a mitigation and the two-pass schedule then rests
entirely on a reading of an `IO` file with no gate.
*Fallback:* leave `pump` `partial` with a comment citing `step_closed`. That is the
honest state and it costs nothing.
