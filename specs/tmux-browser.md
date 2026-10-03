# Saved tmux browser

## Status

Active, 2026-10-03. Implementation and full assembled Linux verification pass.
Independent final review accepts the candidate. Publication and worktree cleanup
remain pending. One live spec.

## Intent

Keep `linger ls` and `linger select` for native sessions. Group saved-tmux
interchange under `linger tmux`: `ls [SAVE]`, `select [SAVE]`, `import [SAVE]`,
and `export SAVE`. Bare `linger tmux` explains those commands. Remove the old
top-level import/export spellings.

Both tmux browsing commands read the same validated save and preserve its pane
order. Show the resolved save path, modification time, original session/window
identity, and working directory. Default to the configured resurrect directory
when available, otherwise its conventional location; use `last`, not a merge of
historical snapshots. An explicit file selects a historical save.

Reuse the native selector's rendering, fuzzy matching, keys, refresh and terminal
lifetime. Saved-tmux selection has no Create row. Acceptance refers to the exact
displayed pane and directory, even if the save changes before acceptance.
Create a fresh shell in that directory when needed and attach through linger.
Saved commands are never executed. Browsing alone starts no sessions.

## Non-goals

Live tmux process takeover, process-tree restoration, shared windows/splits,
evaluating shell configuration, a second picker, new C wrappers, new dependencies,
or retaining inert tmux metadata in native checkpoints.

## Steps and ownership

1. Implement and verify the complete command group as one coherent checkpoint.
   Isolated workers own routing/help, the shared picker, interchange fixtures,
   and terminal selection fixtures. The main writer owns catalog/discovery,
   import integration, documentation and IO call-site gates. Prove ordered
   catalog/list/selection agreement, no foreign Create row, and acceptance of
   displayed identity. Each behavioral change starts with a failing check;
   negative controls, independent review and assembled verification precede
   the implementation commit.
2. Publish the verified checkpoint to main, inspect its hosted verification,
   archive this record with the actual results, and retire verified worktrees.
   Keep the completion record in a separate verified commit.

## Reads and writes

Read AGENTS.md, SCRATCHPAD.md, relevant archived decisions, Tools/Entry,
Tools/Picker, Tools/Resurrect, Manager/Picker, Manager/Resurrect, their proofs/tests,
CLI help, README, recipes, and the verifier gates. Apply code-minimalism,
spec-driven-build and compound-engineering skills.

Write the active source/proof/test/doc files for this interface, the gates and
suite assertion inventory as needed, this spec, AGENTS.md's active pointer, and
append-only SCRATCHPAD.md. Archived records and user tmux state are read-only.

## Exit criteria

- Exact routing/help and invalid-argument checks cover the new command group.
- `ls` and `select` consume one validated catalog with visible path/time.
- Names remain canonical, action directories retain their exact contents, saved
  commands remain inert, and ambiguous identities are rejected.
- Selection cannot create from search text or retarget to a refreshed snapshot.
- Refresh follows the same lookup path when a relative `last` symlink changes.
  Final attach retains the displayed directory if a session disappears and must
  be recreated.
- Missing tmux/server, configured and default directories, explicit older files,
  unsafe display text, missing directories and cancellation have focused checks.
- A cancelled listing peer cannot terminate its session. Client read errors
  follow the existing close transition; a real unread-reply disconnect checks
  that the same shell remains usable.
- Every new pure definition occurs in a meaningful theorem type; runtime uses
  are protected by source gates and real executable checks.
- Mutation checks catch representative regressions.
- `./lake build`, `./lake build Theorems Tests`, and foreground `./tests/e2e.sh`
  pass on the assembled tree, including formatting, ABI and semantic coverage.
- A fresh reviewer accepts the final change. Main is committed and pushed without
  rewriting history; hosted results and any limits are recorded accurately.

## Verification record

`./lake build` and `./lake build Theorems Tests` pass. The foreground assembled
`./tests/e2e.sh` passes in 141.548 seconds, including generated ABI, source gates,
formatting, semantic lint and coverage, verifier regression checks, fuzz, shim
checks and all fifteen live suites. Their retained logs contain 514 passing
assertions with no failures; all 144 non-record source entries remain unchanged
through the run. Evidence: `/tmp/linger-tmux-evidence/final-full-W9pOfR/`.

Independent review found the final-attach cwd and relative-`last` refresh races.
Before correction, the expanded Manager fixture passes its previous 120 checks
and fails exactly those two new checks. After correction, all 122 pass in the
isolated run and again in the assembled verifier. The unread-reply disconnect
regression likewise fails before its Lean-only fix and passes afterward,
requiring the original shell PID to execute a fresh output marker.

Deliberate mutations to catalog directories, selected action directories,
disabled creation, client-close state, the client read-error boundary, final
attach cwd and lookup-path preservation fail their corresponding proofs, unit
examples or source gates. Exact restoration passes. The worklog names the
retained receipts. No new C code or dependencies are introduced. Discovery has
a one-second result-polling deadline followed by cooperative child cleanup;
it does not claim a bounded return for helpers that ignore termination.

The final independent review accepts all corrections after inspecting the
actual isolated and assembled logs, negative controls, and current source hashes.
Its report is `/tmp/linger-tmux-evidence/reviews/browser-read-only-20261003.md`.
All four worker source trees and external test evidence are preserved; their
owned changes are integrated and their branches have no unique commits.
