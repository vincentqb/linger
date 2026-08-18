# ledger-cleanup — close the parked findings, and make the listing's own output safe

Status: active
Updated: 2026-08-18
Predecessor: `specs/restore-conformance.md` (complete; this picks up the optional
leftovers it parked — `restore_tabs_any` and Step 0 ledger items 3, 4, 6 — plus the
cosmetic display gap recorded under its ledger item 2)

## Where this stands — read this first

**Next step:** nothing required. All five items are done; what remains is the parked ssh-argv
host validation (a security follow-up, not a visual) and, optionally, proving
`tabs.size = cols` a reachability invariant so `restore_tabs_any`'s `hvtabs` hypothesis could
be discharged rather than assumed (a `tabs_*` frame family, recon's "F2").

**Done (2026-08-18):** item 1 (`restore_tabs_any` / `restore_tabs_reachable` / `resume_tabs`,
on the generic `Fixes π` stream-predicate layer — see SCRATCHPAD for why that replaced a fourth
hand-rolled copy of `Keeps`; `STATEMENT_CAP` tightened 21 → 20), items 2 (`ptyIn` cap + the twin `flushConn`/`flushPty` partial-drain
compaction), 3 (resume at the checkpoint's dimensions, `clampDim`-guarded), 4 (`.err` on the
attach path via an `Outcome` sum), and 5 (the human listing rendered in the pure core —
`Listing.humanRow`/`humanListing` through `utf8s`, `humanRow_printable`/`humanListing_printable`
in `Theorems/Listing.lean`; the resumable-row and `-r`-host display leaks closed; columns
aligned, `(busy)`-on-remote and trailing-whitespace fixed). Tested (`Tests/Listing.lean`
fixtures, `overview_test` hostile-ckpt guard, `robust_test`/`resume_test`), break-verified, full
`e2e.sh` green. SCRATCHPAD 2026-08-18.

## Goal

Close the four parked findings from `specs/restore-conformance.md`, and make the
human-readable listing provably safe to print:

1. **`restore_tabs_any`** — the tab ruler as a receiver-quantified theorem. The *fix*
   landed (ledger item 0: `tabsAnsi` emits unconditionally, pinned by `dirtyTabs`);
   what is missing is the proof. It needs a `tabs` projection of its own — an
   `Array Bool`, so not a scalar that folds into `stick` — and the `TBC` + `HTS` fold.
   This is the last restored field with no theorem except the title and the DECSC slot.
2. **`rt.ptyIn` is uncapped** (ledger item 3) — the per-client *output* queue caps at
   4 MiB and disconnects, but the pty *input* buffer has no bound, so §Bound's runtime
   half is asymmetric. A child that stops reading plus a client that floods input grows
   it without limit.
3. **Resume spawns the pty at a hardcoded 80×24** (ledger item 4) while the restored
   `Vt` keeps the checkpoint's dimensions, until the first sizing attach reconciles
   them. Reach: `linger run`/`send`/`wait` on a checkpointed-but-not-live session.
4. **`.err` is dropped by `Client.attach`** (ledger item 6) — only `drainReplies`
   prints it, so a "too many clients" refusal reads to the user as a clean detach.
5. **The listing's human column** — the display path lost the `Remote.scrub` the old
   `Tui.rowOfInfo` applied. Remote rows are scrubbed in `Remote.parseRecord` and our
   own daemon scrubs at the emit site (`infoText`, via `Render.utf8s`), so the question
   is whether any path still reaches the terminal unscrubbed, and the answer should be
   a *theorem about the printed row*, not an audit that has to be redone.

Non-goal: item 5 of the old ledger (modes the `Vt` does not model — DECSCNM `?5`,
`?1005`/`?1015`, DECSCUSR). That is an emulator completeness limit, not a leak the
current model can represent, and widening `Modes` is a different project.

## Definition of done

1. `restore_tabs_any` green in `Theorems/Render.lean`, receiver-quantified, no `sorry`
   and no `native_decide`, break-verified with the break in `SCRATCHPAD.md`.
2. `rt.ptyIn` capped with the same shape as the client output queue, and the cap named
   in one place rather than inlined.
3. Resume spawns the pty at the checkpoint's dimensions.
4. A refusal (`.err`) reaches the user on the attach path.
5. The human-readable listing row is provably free of control bytes, for any `info` a
   reply could carry — a theorem, not an inspection.
6. `./lake build`, `./lake build Theorems Tests` and `./tests/e2e.sh` green and
   warning-free; every new theorem and test break-verified and recorded.

## Steps

Filled in as each round starts; one item in flight at a time.
