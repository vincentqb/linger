# Explicit session selection

Status: complete — assembled Linux verification green; hosted checks pending at closure
Updated: 2026-09-27

## Intent

The user wants bare `linger` to explain the CLI and asks why selection is not
an explicit `linger select` command. Keep one public executable while making
help, selection, listing and creation distinct actions.

Bare invocation prints the same help as `linger help`, returns success and
does not inspect terminal streams or list sessions. Exactly `linger select`
opens the existing selector; it requires terminal input and output. Extra
selector operands are usage errors. `linger ls`, `linger attach [name]` and
`linger import [SAVE]` retain their contracts.

Selection continues to attach only original listed targets. A query with no
matches does not create a session. Listing refresh remains on entry, Ctrl-R
and return from attach. The current selector has no five-second timer; the
user's observation is being clarified. New creation actions, periodic remote
polling, terminal backends, dependencies and raw bindings are out of scope.

## Step 1 — make selection explicit

Reads: `Main.lean`, `Tools/Entry.lean`, `Theorems/Entry.lean`,
`Tests/Entry.lean`, `Linger/Runtime/Cli.lean`, `Manager/Picker.lean`,
`E2E/Manager.lean`, `E2E/Overview.lean`, `E2E/Recipes.lean`,
`tests/gates.sh`, `tests/e2e.sh`, `README.md`, `THEOREMS.md`, `recipes/`,
`SCRATCHPAD.md`, `specs/archive/single-entry-point.md`.

Writes: the entry route, its proofs and fixtures, `Main.lean`, CLI help,
the three named E2E suites, native terminal examples, current documentation,
source gates and suite counts, this spec, `AGENTS.md` and append-only worklog.

The main writer owns routing, integration, documentation and gates. A worker
in a fresh worktree owns only the manager and overview executable checks.
The checks first fail against the prior CLI. Kernel theorems characterize
the exact selector arguments, bare help, import forwarding and unchanged
session operands; IO gates and executable checks connect the route to `Main`.
Theorems state behavior, not the desirability of a user-interface preference.

Verify: both required Lean builds, source gates and standalone formatting pass.
The complete foreground verifier passes after assembly, including every
reviewed live-suite count. Compiling mutations demonstrate the changed route
and its executor tie are observed. A separate review has no unresolved
correctness finding. Archive the completed spec and commit/push the verified
checkpoint normally; report actual hosted CI status.

## Completion record — 2026-09-27

Step 1 is complete. The argument-only route replaces terminal-dependent bare
dispatch. Its kernel theorems, concrete fixtures, IO consumer gates, help and
native terminal settings agree. The manager's executable checks fail in eleven
cases against the preserved predecessor and all pass against the assembled
change. Overview keeps explicit listing checks and removes the obsolete bare
listing duplicates.

Four deliberate regressions compile before rejection: bare listing, selector
operands, bypassed argv and a discarded terminal probe before dispatch. The
last two include quoted canonical-call decoys. Independent review found the
probe gate gap; the strengthened gate rejects it and the original source is
restored. No correctness finding remains open.

The complete foreground verifier passes on Lean v4.34.1: clean build, kernel
proofs, fixtures, generated C ABI, source gates, standalone formatting,
coverage, POSIX smoke tests and all thirteen live suites with exact counts.
The new routing leaves creation and refresh policies unchanged. The
five-second loop found in history belongs to a retired status recipe; the
selector has no periodic listing refresh.

Receipts: `/tmp/linger-explicit-selection-20260927/` and
`/tmp/linger-explicit-selection-test-receipts-20260927/handoff.md`.
No macOS, live GUI-terminal or real remote-host verification is claimed.
Hosted checks have not run for this checkpoint at closure; the preceding
checkpoint's jobs did not start because of GitHub billing/spending limits.
