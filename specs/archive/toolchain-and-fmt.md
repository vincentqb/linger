# toolchain-and-fmt — bump to v4.34.0-rc2 and adopt lean-fmt

Status: **complete (2026-08-29)** — archived record, do not edit
Predecessor: `specs/archive/lean-suites.md`.

## Completion record

Both steps landed. `./lake build`, `./lake build Theorems Tests` and
`./tests/e2e.sh` green and warning-free; `gates OK`; coverage `259 defs, 16
unclaimed, cap 16`; all ten pty floors exact. **Every ratchet came through the bump
unchanged** — `SHIM_CAP` 27, `HEARTBEAT_CAP` 1, `RUNTIME_PARTIAL_CAP` 2,
`E2E_PARTIAL_CAP` 5.

**The linter is adopted. The formatter is declined.** That split was not the plan;
it is what the measurements forced, and it is the useful part of this record.

### Step 1 — the bump

152 errors, all deprecations, zero real breakage — errors rather than warnings only
because `warningAsError` was installed one commit earlier for exactly this:

| count | from | to |
|---|---|---|
| 74 | `if_neg` | `ite_eq_right` |
| 54 | `if_pos` | `ite_eq_left` |
| 11 | `dif_neg` | `dite_eq_right` |
| 6 | `if_false` | `ite_false` |
| 3 | `dif_pos` | `dite_eq_left` |
| 2 | `if_true` | `ite_true` |

Safe to rename mechanically because the replacements are **definitionally
identical**, checked in the new toolchain's `Init/Core` before touching anything:
`if_pos` is literally *defined as* `ite_eq_left hc`, same signature and argument
order. A blind rename of a proof lemma can change meaning; this one could not.

`HEARTBEAT_CAP` holding at 1 was the load-bearing result — two minor versions of
elaborator changes made no proof here more expensive, and the kill criterion was
"more than a couple of new raises". The `./lake` wrapper needed no edit at all: it
derives its toolchain directory from `lean-toolchain` since the previous commit, so
the bump was picked up automatically.

### Step 2 — lean-fmt, and why only half of it

Installed standalone (`make install`, tag == `lean-toolchain`), never as a Lake
`require` — the require-free lakefile and empty manifest are gates in
`tests/gates.sh`.

**The formatter, measured at its default width before deciding:**

* 66 of 71 files would be reformatted, **+8540 / −6173 lines**
* **894 of those diff lines touch tactic blocks** (`repeat'`, `all_goals`,
  `simp only`, `omega`)
* **502 commands it could not lay out at all** — "no layout passed validation"

The second number trips the kill criterion this spec wrote *before* measuring: "a
formatter that reflows those is a formatter this repo cannot use". AGENTS.md keeps
`repeat' split` + `all_goals first | …` shapes so a new branch does not break a
proof and so the script says which lemma discharged which arm. The third means the
result would not even be self-consistent — a partial reformat by construction.

Narrowing helped less than expected, and one knob backfired:
`declaration-body = "same-line"` does fix the `:= rfl` churn (the default moves
`rfl` off the statement line, costing a line on several hundred one-line proofs),
but `line-width = 80` — the width every docstring in this tree is wrapped to —
raised the unformattable count from 502 to **680**. The tool cannot format this tree
at this tree's own margin.

Two smaller style disagreements, recorded so nobody re-litigates them: it collapses
a deliberate vertical `else if` cascade onto one line where it fits the margin (in
`Status.classify`, whose docstring calls it "a priority cascade"), and it prefers
trailing `=`/`∧` where this tree uses leading.

**The linter is pure value and is now gating.** From 79 findings to
`71 files, no findings`:

* FMT016 (105) — dropped by reverting `select = ["all"]`. It is `default: off` and
  its own docs say it repeats what `format` would fix; since format is not run, all
  of it was noise.
* FMT005, import order (68) — **baselined, not fixed.** Report-only by design
  because "reordering imports can change initialization order in principle"; on a
  1467-theorem library that is real risk for cosmetic gain, and the current order is
  the Render ladder's own rung order.
* FMT004, redundant imports (11) — 8 are in the two **root** modules, where the
  redundancy IS the invariant (`lakefile.lean`: "Root module imports every
  Theorems.X — a proof file not imported there is a bug"). Suppressed there with
  that reason. The other 3 were genuine and removed.
* `check --fix` applied exactly one thing on its own: a redundant paren nest in
  `Theorems/Render/Grid.lean`. Conservative, which is the right behaviour.

Wired into `.pre-commit-config.yaml` as `lean-fmt check`, never `format`. Commit
cost went 1172 ms → 2757 ms, still nothing compiled. The hook skips with a note if
the binary is absent (right for a fresh clone) and CI installs it explicitly so the
skip cannot hide a finding there.

## The one thing to revisit

**The pin is a release candidate.** `v4.34.0` stable did not exist when this landed.
Move the pin when it ships *and* lean-fmt tags it — that is the whole trigger, and it
is recorded in AGENTS.md §Build rather than only here. If lean-fmt's layout engine
improves by then, re-measure the formatter: the decision above is about today's
numbers, not a permanent verdict.
