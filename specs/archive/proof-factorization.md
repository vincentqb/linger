# Proof-guided factorization

Status: closed — Linux verification passed; hosted CI blocked before execution
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

Steps 2–5 are integrated from frozen worktrees. VT operations now expose exact
frames for grid-only folds and insert/delete/erase operations. Renderer proofs
share stream traversals and exact CSI digit/tail equations. Session proofs
share guarded state/effect induction and terminal-predicate lifts. CLI proofs
characterize classification and validation in both directions, exact decoded
key identity, and least sufficient name-column width.

The only production refactors replace host search with `List.find?` and key
delivery with `Option.filter.toList`; worker certificates establish equivalence
to their predecessors for all inputs. The combined worker patch removes 762
Lean lines, including proof code. Its assembled theorem/test build passes.

Independent review identified two existing CLI executor gate gaps. The final
ties cover normalized host validation through traversal, and ordered keyboard
bytes through decoder state/key propagation to dispatch. Ten compiling
mutations exercise those boundaries; the byte-order and final-key-discard
cases also exposed an incomplete first version of the guard. Independent
review closes both executor findings. The renderer review preserves every
original statement and identifies an ANSI-colored handoff patch; a regenerated
uncolored patch passes Git parsing and retains identical source changes.

The assembled foreground Linux verifier passed from 17:18:57Z to 17:26:21Z:
clean build, generated C ABI, formatting, source gates, semantic coverage,
CI runner checks, POSIX smoke, all fourteen live suites and the sentinel.
All 434 live assertions pass, and all 159 tracked source identities remained
fixed. The elaborated theorem-type comparison preserves every retained
explicit statement; only three private helpers are replaced. Overall, the
round removes 739 Lean lines, with unchanged tests, C code and proof limits.
Evidence is in `/tmp/linger-proof-assembled-verifier-20260929/`.

Steps 2–5 share this assembled checkpoint. All five worker trees are frozen,
their changed sources match main, and their complete patches and source
copies are sealed in `/tmp/linger-proof-cleanup-20260929/`.

## Completion record

Checkpoints `329ccfd` and `c002f00` are committed and pushed to main.
Both required builds and all commit hooks passed before each checkpoint.
The assembled implementation remains the one that passed the complete
foreground Linux verifier above.

All agents are closed. Fresh removal checks verify the five worker branch
identities, zero unique commits, empty indexes/untracked inventories, and
only generated caches among ignored files. Every changed source and its
mode match the published checkpoint and the sealed recovery evidence.
All five worktrees and branches are removed; only main remains locally.
The fresh checks and completed removals are recorded in
`/tmp/linger-proof-cleanup-final-20260929/preflight.json` and `completed.json`.

The checkpoint's automatic push run `36605725740` failed before any job steps
ran. GitHub's annotation says recent account payments have failed or the
spending limit needs to be increased. The full-gate job was skipped.
These hosted checks did not execute. The actual run, jobs and annotations
are preserved in `/tmp/linger-proof-hosted-20260929/checkpoint/`.
No hosted Linux or macOS pass is claimed.

The closure checkpoint changes documentation only, archives this record,
and restores the no-live-spec pointer.
