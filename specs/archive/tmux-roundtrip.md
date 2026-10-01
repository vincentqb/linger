# tmux save round trips

Status: Complete
Updated: 2026-10-01

## Intent

Implement the two approved interchange guarantees. An unchanged imported
tmux-resurrect save exports with its original bytes, including records Linger
does not interpret. Native Linger sessions exported to tmux and imported again
retain the common fields: session identity and working directory.

Keep `LNGR` v1 unchanged. Native checkpoints continue to own terminal screens,
scrollback, modes and labels. Input recording, process resurrection, window
composition and an extension carrying additional native state are out of scope.

## Decisions to verify

- `linger import [SAVE]` retains validated foreign source data alongside local
  checkpoints. A small, atomically written provenance record pairs each source
  with the resolved common fields observed at import.
- `linger export SAVE` exports local live and resumable sessions. Reuse retained
  source only when the exported common fields match, independently of listing
  order. Otherwise generate a fresh tmux-resurrect save. Refuse incomplete
  snapshots and unsupported field encodings instead of silently losing data.
- Native identity must survive a tmux save that drops unknown comment records.
  Use an explicitly reserved, reversible session-name encoding and verify it
  with an isolated tmux server. Preserve the established projection for ordinary
  imported sessions.
- Foreign commands remain inert in Linger. Only a fresh default shell starts.
  The exact-file guarantee concerns the save file; any companion capture archive
  must be addressed explicitly rather than implied by that guarantee.
- Pure codec, projection and original-selection contracts belong in
  `Tools.Resurrect` and `Theorems.Resurrect`. IO serialization, process creation
  and file publication require executable regression checks and call-site gates.

## Step 1 — proved and executable interchange

Reads: `Tools/Resurrect.lean`, `Theorems/Resurrect.lean`,
`Tests/Resurrect.lean`, name contracts, installed tmux-resurrect format,
`Manager/Resurrect.lean`, `Tools/Entry.lean`, `Theorems/Entry.lean`,
`Tests/Entry.lean`, `Main.lean`, `Linger/Runtime/{Paths,Cli,Resume}.lean`,
and the existing E2E harness and import checks.

Writes: the policy, proof, unit-test, manager and entry files above; a focused
Lean interchange suite and its runner registration; `tests/gates.sh`;
`THEOREMS.md`; user documentation; this spec and append-only `SCRATCHPAD.md`.

Ownership: an isolated worker implements the pure codec and proofs. The
coordinator designs and implements the manager boundary while that worker runs.
Another isolated worker supplies executable regression checks. A read-only
worker verifies the real foreign format. The policy and its new IO consumers
form one verified checkpoint, so no intermediate commit references an API or
command that is not yet available.

Exit: new checks fail against the old behavior; the actual serialized save
parses back to its common fields; native names are reversible; ordinary foreign
mapping and command nonexecution remain covered. Real isolated sessions round
trip; raw source survives disk persistence
and export; changed common fields cannot reuse stale foreign bytes; invalid
sources, unavailable sessions and publication failures fail clearly; existing
destinations survive refused exports. All prior assertions and the full
foreground Linux verifier pass, including pure-definition coverage. Record
mutations that the new contracts and IO checks reject.
A fresh reviewer audits the assembled diff.
At most two review/revision rounds before revisiting unresolved design choices.

## Step 2 — publication and closure

Publish verified checkpoints to main, inspect hosted checks, integrate every
accepted worker change, preserve necessary evidence and remove worktrees with
no unique work. Append the completion record and archive this spec.

Exit: all intended work is committed and pushed, the checkout is clean, and the
report distinguishes proved guarantees, exercised behavior and unexecuted checks.

## Step 1 completion — 2026-10-01

The pure codec, retention policy, executor, command routing and documentation
are implemented. The final assembled foreground Linux verifier passes 470 live
assertions across 15 suites, including all 33 interchange checks, plus the
twelve CI checks, 63 shim checks, generated ABI, layout, both coverage checks,
fuzz and unrelated-session sentinel. All 356 pure definitions occur in theorem
types. Source identities remain unchanged throughout the 413-second run.

Mutations reject lost native identity, membership-only retention, a wrong
serialized directory, bypassed IO policy and incomplete export after home
normalization. The new HOME-absent/empty cases fail four assertions against the
wrong ordering and pass after correction. An isolated tmux-resurrect cycle
checks native identity and the supported directory repertoire. The second
independent review accepts the final assembled source with no remaining blocker.
Full evidence and limitations are recorded in `SCRATCHPAD.md`.

Hosted checks and worker cleanup were pending at the Step 1 checkpoint.
macOS was not executed in this round; the C shim, build wrapper and toolchain
are unchanged.

## Step 2 completion — 2026-10-01

Implementation commit `b0a8c69383e0d5a4f9f2a3419272a1f03eef80d7` is published
to main. [Hosted run 36884703338](https://github.com/vincentqb/linger/actions/runs/36884703338)
passes both jobs. Its log confirms all 15 live suites and 470 assertions,
the twelve CI checks, enforced 63 shim checks, pure coverage, and final
verifier success. All commit hygiene and semantic lint hooks pass.

Source gates take eight seconds. The full Linux job takes 584 seconds,
including 490 seconds in the verifier: compilation takes 50 seconds,
source gates and layout 38 seconds, semantic coverage 20 seconds, and
live suites 366 seconds. The new interchange suite takes 17 seconds.
The toolchain, build, formatter and hook caches restore successfully.

Both worker worktrees and branches are removed after exact source/mode
recovery and a fresh check for unique commits or unintegrated edits. Accepted
source matches the published implementation, allowing only the recorded
policy docstring normalization. Only main and the primary worktree remain.
Recovery and cleanup receipts are retained under
`/tmp/linger-tmux-recovery-20261001-YsiwYQ/`.

The completion checkpoint changes records only; its hosted checks will start
after publication and are pending as this record is written. No native
metadata companion, input recording or process restoration was implemented.
Full logs and count/timing audits are retained under
`/tmp/linger-tmux-main-20261001-bMcetC/`. This spec is archived.
