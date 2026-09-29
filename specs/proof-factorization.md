# Proof-guided factorization

Status: in progress — step 1 verified; integrating independent workstreams
Updated: 2026-09-29

## Intent

Audit all pure definitions, theorem families and proof shapes. Generalize where
one invariant can replace repeated reasoning, expose a natural code boundary,
or rule out invalid states at construction. Preserve existing endpoint
premises and conclusions. A conjunction of existing facts or a new abstraction
with no simplifying consumer is not by itself an improvement.

Keep the Lean v4.34.1 toolchain and use its library lemmas and proof facilities
where they shorten stable proofs. No new dependencies or generic framework
without demonstrated use. Do not replace the fixed terminal repertoire,
introduce a second parser, or claim kernel proofs establish OS scheduling and
wall-clock deadlines. Preserve the prior round's status and title behavior.

## Workstreams and ownership

1. The main writer audits byte codecs, bounded buffers, checkpoints, replay
   delivery and composed resume guarantees. It also owns the shared theorem
   ledger, source gates, spec, worklog, integration and publication.
2. A VT worker audits the shape, preservation and reachability contracts in
   `Linger/Core/Vt.lean`, `Theorems/Vt.lean` and `Tests/Vt.lean`.
3. A render worker audits compositional proof patterns in `Theorems/Render/`
   and may introduce a small shared proof module where existing consumers
   demonstrate its value. Existing terminal endpoint guarantees stay intact.
4. A session worker audits event/effect traces and session construction in
   `Linger/Core/Session.lean`, `Theorems/Session.lean` and `Tests/Session.lean`.
5. A CLI worker audits the pure status, listing, remote and `Tools/` policies
   with their proofs and unit tests. It preserves the user-facing interface.
6. A fresh reviewer checks the integrated changes. Run the full verifier,
   capture the useful generalized contracts and negative results, archive
   this spec, publish main and remove integrated worker branches/worktrees.

Workers have separate worktrees and disjoint write scopes. They report an
explicit bounded negative result when a proposed generalization would add
machinery or weaken a guarantee. They do not edit the shared ledger, gates,
worklog, spec or root import files; the main writer integrates those changes.
Checkpoint commits follow the numbered workstreams after their required
verification. Dependent changes may share a checkpoint when necessary.

## Proof obligations and verification

State candidate invariants in the theorem ledger before implementation.
Prefer one-step preservation plus a general composition theorem to repeating
an induction for each field. Prefer an exact frame or semantic equivalence
over exposing implementation internals merely to make a proof short.

Every changed behavior begins with a failing check. Pure refactors require
equivalence or unchanged existing semantic statements. Break verification
changes semantics while retaining well-typed code; a missing identifier or
proof-script shape mismatch is not evidence of a stronger guarantee. Retain
all useful existing checks and remove redundant scaffolding only after its
replacement is exercised. New pure definitions need exact-constant coverage.

Run `./lake build` and `./lake build Theorems Tests` before each commit.
Changes to runtime behavior and all deletions pass the complete foreground
`./tests/e2e.sh` stack. Verify generated C ABI, standalone formatting, source
gates, theorem coverage and the live assertion counts. Reassess any touched
proof-resource overrides. Record actual hosted results without representing
unexecuted checks as green.

## Progress

The starting checkpoint is `a29819d`, with a clean main worktree and no side
branches. Initial inventory identifies repeated stream predicates, VT
preservation families and event-trace lifts as candidates. Prior rejected
generalizations in `specs/archive/bigger-theorems.md` remain evidence to
respect: a new abstraction must retain hypothesis-free endpoints and pay for
itself through real consumers.

Step 1 establishes name sanitization as a retraction and idempotent operation,
and whole-queue identity when an input offer is refused. Existing title
observer endpoints now share the VT predicate-fold theorem; the standalone
wire round trip uses the suffix-general round trip. No production definition
changes in this checkpoint. Independent review and two compiling semantic
mutations support the new contracts.

The foreground Linux verifier passed from 16:58:09Z to 17:05:18Z, including
the clean build, ABI, formatting, coverage, all fourteen live suites and the
sentinel. All 159 tracked source identities stayed fixed. The preceding
restricted-sandbox attempt stopped at a refused socket bind; it is recorded
as an environment diagnostic, not a product failure or a live-test pass.
Evidence is in `/tmp/linger-proof-checkpoint-live-20260929/`.

VT, session and CLI workers have frozen their changes; the render worker is
finishing verification. Two independently identified CLI executor gate gaps
have eight compiling mutations that pass the old gates and fail the proposed
ones. Their integration and assembled verification remain outstanding.
