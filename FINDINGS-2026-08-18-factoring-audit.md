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

## 1. VERIFIED — split `Theorems/Render.lean`, then re-measure the heartbeat raises

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

## 2. CANDIDATE — is the 16:1 theorem:implementation ratio a hard core or bad factoring?

9,167 theorem lines against a ~560-line emitter is the corpus's widest ratio. The
case for *hard core*: it is the only **inverse** claim in the repo (emitter ∘
parser = identity; every other rung is forward preservation), mean 17 lines per
theorem, and the combinators were factored out once and then measured as "not a
line win … the value is in what the *next* layer costs."

The diagnostic that would settle it, and the one the skill generalizes from this
case: **classify the proof lines as *field bookkeeping* vs *the inverse
argument*.** That ratio, not the file size, is the diagnosis — cost in the
plumbing is a factoring signal, cost in the mathematics is not.

## 3. Note on the coverage floor

`tests/coverage.py` (`STATEMENT_CAP = 21`, comments stripped so "neither check can
be satisfied by writing prose") is the mechanism the skill now recommends
generally. Keep the ratchet monotone; it is doing work no review pass can.
