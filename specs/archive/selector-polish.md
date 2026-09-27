# A calmer, live session selector

Status: complete — local verifier green; hosted checks pending at closure
Updated: 2026-09-27

## Intent

The user approves more breathing room and asks for nicer characters, automatic
refresh instead of Ctrl-R, and Ctrl-C to quit without terminating session
programs. Keep one default interface, with the terminal's own colors and no
new option or dependency.

The selector uses a quiet title, a separate query with a dim placeholder,
Unicode selection and key glyphs, clearly labelled creation, and contextual
Enter help. Small terminals give the selected row priority over decoration.
Text still clips by terminal cells and leaves the last column unused.

Refresh the complete local/remote listing automatically, starting the next
attempt one second after the previous one completes, with at most one listing
subprocess in flight. Slow listing must not block input or cancellation.
Preserve query and the selected exact target when it remains available,
including creation becoming attachment;
otherwise clamp the cursor to the new choices. Only repaint when state or
terminal size changes. A failed or malformed snapshot ends selection with a
visible error after terminal restoration.

Ctrl-C and Esc cancel selection with status 130, restore the terminal, and
never signal a session program. While attached, Ctrl-C continues to belong to
the foreground program. Remove the manual refresh key and its pure outcomes.
Background listing owns only its subprocess and must retire it on exit.
Apply a completed refresh after input from the displayed state, then draw the
new state before accepting further input.

Out of scope: changing attach/detach semantics, session composition, themes,
terminal-specific integration, new C or POSIX bindings, or periodic `linger ls`.

## Step 1 — polish and refresh the selector

Reads: `Tools/{Picker,Input,Key}.lean`, `Manager/Picker.lean`,
`Theorems/{Picker,Input}.lean`, `Tests/{Picker,Input}.lean`, `E2E/Manager.lean`,
`THEOREMS.md`, `README.md`, `recipes/README.md`, `tests/{gates,e2e}.sh`,
`SCRATCHPAD.md`, `specs/archive/selector-creation.md`, Lean core process/task APIs.

Writes: those current selector policy, executor, proof, test, documentation
and gate files; `AGENTS.md`, this spec and the append-only worklog.

The main writer owns pure selection refresh, removal of manual refresh events,
proofs and fixtures, documentation and source gates. A worker in a separate
worktree owns only `Manager/Picker.lean`, using the specified pure refresh API.
Another worker owns only `E2E/Manager.lean` in a separate worktree, retaining
predecessor executables for red/green evidence. An independent review has two
rounds before replanning any unresolved finding.

The user also requests a branch and worktree audit before cleanup. Three
read-only workers cover disjoint groups of existing branches, checking both
committed and uncommitted work against main and preserving diffs and meaningful
untracked files outside each worktree. Active selector branches wait until
their implementation is integrated. Remove only accounted-for worktrees and
branches, and retain any unique valuable work for verified integration.

Verify: the new behavioral checks fail against the predecessor and pass
against the assembled implementation. Kernel proofs establish refresh query
preservation, cursor bounds and exact-target retention, and keyboard
cancellation and ignored Ctrl-R. Source gates connect those values to IO.
Compiling mutations must be rejected by the appropriate oracle. Both required
Lean builds and the complete foreground Linux verifier, with reviewed exact
suite counts, pass. Inspect a captured terminal frame for the intended layout.
Archive the completed spec, commit and push the verified checkpoint, reporting
the actual hosted-check outcome.

## Completion record — 2026-09-27

Step 1 is complete. The selector has the approved spacing, Unicode glyphs,
contextual help and terminal-native colors. Automatic refresh preserves the
query and surviving exact target, clamps a missing target's cursor and starts
the next attempt one second after completion. Slow listings leave input
responsive. Ctrl-R is removed; selector Ctrl-C and Esc cancel with terminal
restoration while session programs remain running. Attached Ctrl-C retains its
foreground-program behavior.

Kernel proofs establish the pure refresh, identity, bounds and keyboard
contracts. Source gates connect them to displayed rows, refresh ordering and
owned process/reader cleanup. Four compiling policy mutations and seven
compiling runtime mutations are rejected. The first independent review found
two order variants that needed stronger gates; the final review confirms
those gaps closed and has no remaining finding. No C, raw binding, dependency
or CLI option was added.

The final manager harness uses public VT observations and the unchanged friend
set. The identical source and driver execute 103 assertions against the compiled
predecessor (83 PASS, 20 FAIL) and the assembled implementation (103 PASS,
zero failures). Real-program survival and attached Ctrl-C, held listings,
refresh, display, resize, clipping and tiny-terminal behavior are observed
through ptys. Captured frames were inspected.

The complete foreground Linux verifier passed on Lean v4.34.1, including its
clean build, generated C ABI, source gates, standalone formatting, theorem
coverage, CI runner checks, fuzz, POSIX smoke, all thirteen live suites
(381 assertions) and the unrelated-session sentinel. Both required final
builds and static checks pass; tested source and executable identities were
independently verified.

Read-only agents audited all thirty side branches, including their dirty and
untracked files. No unique commits remain outside main. Current work was
integrated and verified, and meaningful historical evidence preserved before
all thirty worktrees and branches were removed. Only the main worktree and
branch remain; the remote also has only main.

Receipts: `/tmp/linger-selector-polish-20260927/`,
`/tmp/linger-selector-polish-test-receipts-20260927/final-public-vt/handoff.md`
and `/tmp/linger-branch-audit-20260927/`. The append-only worklog records
diagnostic failures separately from verified evidence.

Hosted checks are pending at closure; the preceding checkpoint's jobs could
not start because of GitHub billing/spending limits. No macOS, live
GUI-terminal or real remote-host verification is claimed.
