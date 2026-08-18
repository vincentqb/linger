# FINDINGS — 2026-08-18 — factoring audit

Left for whoever picks this repo up next: **resolve and commit here.** From a
cross-repo audit of six Lean projects run while distilling the "restructure code
for provability rather than weakening a theorem" rule (this repo's `AGENTS.md`)
into a portable skill (`~/notes/skills/design-for-provability`). Tagged VERIFIED
(command shown) or CANDIDATE (not reproduced — check first).

This repo came out of the audit as the strongest instance of the discipline
working: zero `sorry`, zero `axiom`, zero `native_decide` in `Theorems/`, the ban
enforced by `tests/e2e.sh` with its reason written at the gate, and the
`mendRow` funnel + "Bytes, not Strings" rewrite are both now worked examples in
the skill. The items below are the two open threads.

## 1. RESOLVED (2026-08-18) — split done; the acceptance criterion's hypothesis is REFUTED

```
$ wc -l Theorems/Render.lean          # 9167
$ grep -c '^namespace' Theorems/Render.lean   # 13
$ grep -rn maxHeartbeats Theorems/ | wc -l    # 20
```

9,167 lines with 13 namespace open/close cycles is accretion from
one-commit-per-step, and it is splittable **at the ladder boundaries the file
already names, at zero logical cost.** Do that first, because it is free and it
makes the real question legible.

The real question is what the 20 heartbeat raises are paying for.
`THEOREMS.md:349-355` already records the diagnosis and the priced-and-declined
refactor: the elaborator cost is a tax on **record width** (an invariant over a
20-field flat record is a defeq check per field per unification), and splitting
the invariant would move the cost to every call site. The deferred alternative —
moving read-only fields into parameter position — is the actual owner.

**Acceptance criterion for the split: the bumps that survive it are the record-width
tax, and the ones that disappear were file size.** Treat deletion of a bump as the
success signal, not the split itself.

### Resolution

**The split landed** (`56eedda`): `Theorems/Render.lean` is now a 38-line façade over
`Theorems/Render/{Ends,Quiet,Pen,Keeps,Modes,Sticky,History,Row,Grid,Tabs}.lean`
(1017/840/931/987/1048/1270/111/1367/1690/711 lines), cut at the boundaries the file's own
`/-! ## …` headers named. Verbatim move: the 607-name declaration set diffs empty and each
part's body is byte-identical to its original slice. Two incidental fixes it forced —
`u8_bounds` and `print_quiet` lost `private` (it does not cross a module boundary, and they
are used by 4 and 2 rungs respectively), and `tests/coverage.py` globbed `Theorems/*.lean`
non-recursively so it stopped seeing the statements (`rglob`, as it already does for `Zmx`).

**The heartbeat re-measure: 18 of the 20 raises are deletable.** Survivors:
`Checkpoint.load_save` (needs its 2,000,000 — fails at 1,000,000) and
`Vt.renderable_stepGround` (needs between 600,000 and 1,000,000; its 2,000,000 is generous
but not misleading, so it was left alone rather than tightened into fragility).

**But the acceptance criterion above is wrong about the mechanism, and the control says so.**
Re-running the same deletions at the pre-split commit (`1f68e42`, in a throwaway worktree):

```
PRE-SPLIT  step_narrow                  delete -> PASS
PRE-SPLIT  mark_step                    delete -> PASS
PRE-SPLIT  paint_range (4000000)        delete -> PASS
PRE-SPLIT  paint_rows                   delete -> PASS
PRE-SPLIT  restore_modes_any (800000)   delete -> PASS
PRE-SPLIT  renderable_csiDispatch       delete -> PASS
```

All six were **already** deletable before the split, so the split gets no credit for the 18.
They were not paying for file size and not paying for record width — they were paying for
nothing: budget added when the proofs were in an earlier shape (rougher scripts, less
factored surrounding lemmas) and never re-measured once the shape improved. **A
`maxHeartbeats` raise is a measurement with an expiry date, and nothing in the repo expires
it.** The sweep that finds them is cheap and mechanical: delete the line, build the module,
restore. Worth repeating after any large refactor.

The record-width diagnosis at `THEOREMS.md:349-355` survives, but as a statement about
*where* the remaining cost sits rather than as the explanation for the 18. Capping each
affected file at half the default budget (100,000) isolates exactly three tight declarations:
`Render.Grid.paint_range` (the `Matches` strong induction), `Vt.csiDispatch` and
`Vt.renderable_csiDispatch` (dispatch-table case splits under `Good`/`Renderable`) — all
three invariant-over-wide-record work, and `Vt.csiDispatch` never had a raise at all.
`Row.lean` and `Modes.lean` pass at 50,000, a quarter of the default.

So the honest scoreboard: 20 raises → 2, of which 1 is correctly priced and 1 is generous;
plus 3 declarations that run under the default with less than 2× margin, which is where the
record-width tax actually shows up.

## 2. MEASURED (2026-08-18) — hard core: bookkeeping is ~22% of proof lines

9,167 theorem lines against a ~560-line emitter is the corpus's widest ratio. The
case for *hard core*: it is the only **inverse** claim in the repo (emitter ∘
parser = identity; every other rung is forward preservation), mean 17 lines per
theorem, and the combinators were factored out once and then measured as "not a
line win … the value is in what the *next* layer costs."

The diagnostic that would settle it, and the one the skill generalizes from this
case: **classify the proof lines as *field bookkeeping* vs *the inverse
argument*.** That ratio, not the file size, is the diagnosis — cost in the
plumbing is a factoring signal, cost in the mathematics is not.

### Measurement

Metric, applied to the 12 rungs whose proofs discharge an invariant record (`step_*`,
`mark_step`, `marks_fold`, `offRow_*`, `paint_*` in `Theorems/Render/{Row,Grid}.lean`): lines
inside the `refine ⟨?_, …, ?_⟩` field-discharge block (plus `h*.field` re-establishments)
count as **field bookkeeping**; everything before it is **the inverse argument**.

```
  step_narrow                fields=15 lines=  83 bookkeeping≈ 24 argument≈ 59
  step_narrow_margin         fields=15 lines=  80 bookkeeping≈ 24 argument≈ 56
  step_wide                  fields=15 lines= 100 bookkeeping≈ 26 argument≈ 74
  step_pen                   fields=15 lines=  34 bookkeeping≈ 16 argument≈ 18
  mark_step                  fields=14 lines= 106 bookkeeping≈ 19 argument≈ 87
  step_wide_margin           fields=15 lines=  97 bookkeeping≈ 26 argument≈ 71
  offRow_narrow              fields= 4 lines=  29 bookkeeping≈  5 argument≈ 24
  offRow_wide                fields= 4 lines=  32 bookkeeping≈  5 argument≈ 27
  offRow_mark                fields= 3 lines=  44 bookkeeping≈  3 argument≈ 41
  paint_range                fields= 1 lines= 157 bookkeeping≈ 13 argument≈144
  paint_rows                 fields= 3 lines= 117 bookkeeping≈ 36 argument≈ 81
  paint_entry                fields= 4 lines=  67 bookkeeping≈  7 argument≈ 60
  TOTAL: bookkeeping≈204  argument≈742  => bookkeeping is 22% of proof lines
```

**Verdict: hard core.** 22% plumbing against 78% argument is not a factoring signal, and the
distribution is the tell — the *small* rungs are bookkeeping-heavy (`step_pen`, a 34-line
lemma that changes one field, is ~47% discharge) while the *large* ones are dominated by the
argument (`paint_range` 8%, `mark_step` 18%). Bad factoring would show the opposite shape:
cost growing with the number of fields rather than with the difficulty of the step. The
15-field `Matches` discharge costs a flat ~24 lines per rung, which is the record-width tax
priced in lines rather than in heartbeats — real, bounded, and not what makes these proofs
long.

Caveat: the classifier is a heuristic over line prefixes, so treat the 22% as ±5, not exact.
The per-rung shape is the finding, not the single number. The deferred alternative (moving
read-only fields into parameter position) would attack the ~204 bookkeeping lines and none of
the 742 — which prices it: it is a legibility change, not a way to make this ladder shorter.

## 3. Note on the coverage floor

`tests/coverage.py` (`STATEMENT_CAP = 21`, comments stripped so "neither check can
be satisfied by writing prose") is the mechanism the skill now recommends
generally. Keep the ratchet monotone; it is doing work no review pass can.

Still true, and the ratchet has since moved the right way: the cap is **20** as of
2026-08-18 (`restore_tabs_any` claimed `size_defaultTabs`). The split forced one fix to the
gate itself — it globbed `Theorems/*.lean` non-recursively, so moving statements into
`Theorems/Render/` made 58 core defs read as unclaimed; `rglob` restores it. A gate that
silently stops seeing its input is the failure mode to watch for in this mechanism.
