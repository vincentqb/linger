# Create sessions through selection

Status: complete — assembled Linux verification green; hosted checks pending at closure
Updated: 2026-09-27

## Intent

The user points out that `linger select` can create or attach just as
`linger attach` does. This reopens the earlier creation non-goal: the selector
is an interactive attach front end, and a visible creation row makes the
chosen action and target explicit without another key or CLI option.

Existing matching targets remain first, in listing order. Append a labelled
`Create <target>` row when the query is a valid exact target absent from the
snapshot; an empty query uses the existing attach default `main`. The same
canonical local-name and printable remote-suffix validation used for listing
targets applies. Do not silently sanitize query text into a different name.
An exact existing target has no duplicate creation row. Enter acts on the
highlighted row; editing, navigation, cancellation and refresh cannot attach
or create. Invalid input stays editable. The executor restores the terminal
before passing the exact target to the existing `linger attach` child and
returns to a fresh listing afterward.

Bare help, explicit selection, listing, import, terminal startup settings and
snapshot refresh scheduling retain their contracts. No new key, CLI option,
raw binding, dependency, session-creation backend or timer is in scope.

## Step 1 — make creation a selectable action

Reads: `Tools/Picker.lean`, `Theorems/Picker.lean`, `Tests/Picker.lean`,
`Manager/Picker.lean`, `E2E/Manager.lean`, `Linger/Core/Name.lean`,
`Linger/Runtime/Cli.lean`, `Theorems/Name.lean`, `THEOREMS.md`, `README.md`, `recipes/README.md`,
`tests/gates.sh`, `tests/e2e.sh`, `SCRATCHPAD.md`,
`specs/archive/explicit-selection.md`.

Writes: the pure picker model, its theorems and fixtures, its IO executor,
manager executable checks, CLI help, current user/theorem documentation,
source gates and reviewed suite count, `AGENTS.md`, this spec and the
append-only worklog.

Move the existing attach default into `Linger.Core.Name` so both entry paths
consume one pure value. Prove that default canonical and gate its CLI consumer.

The main writer owns policy, proofs, unit fixtures, executor, docs and gates.
A worker in a fresh worktree owns only `E2E/Manager.lean`. Preserve the baseline
executable and demonstrate failing creation checks before implementation.
An independent reviewer checks the assembled policy and IO ties against
these requirements; remediate correctness findings, with a two-round review
cap before replanning.

Verify: both required Lean builds, source gates and standalone formatting
pass. Kernel proofs characterize the two row kinds, valid exact creation
targets, original existing targets and bounded navigation. Compiling
mutations are rejected by the appropriate proof or executable check.
The full foreground Linux verifier passes on the assembled tree, including
all exact suite counts. Archive the completed spec, commit and push the
verified checkpoint normally, and report the actual hosted CI outcome.

## Completion record — 2026-09-27

Step 1 is complete. The selector appends a labelled creation choice for the
exact valid query, or the shared `main` default, only when absent from the
listing snapshot. Existing matches retain their order and remain selected
first. The executor sends both choices through the existing attach child
after restoring the terminal, then returns to a fresh listing.

Kernel proofs retain original-target provenance for attachment and establish
valid, canonical, exact and snapshot-absent targets for creation. A positive
empty-selector theorem proves creation of the default. Navigation and input
bounds cover both row kinds. Source gates connect the proved rows to their
displayed order, labels, cursor and shared attach argv. No C, raw binding,
dependency, timer or CLI option was added.

Before implementation, two pure guards and fifteen of the eighty-six manager
assertions fail against the preserved predecessor. The same manager source
passes all eighty-six checks afterward, including actual default and named
session creation, detach, fresh listing and terminal restoration.

Six regressions compile before the corresponding proof or source gate rejects
them. Independent review found that computing the correct labels alone did
not guarantee their display; the strengthened contiguous-render gate rejects
both reversed rows and discarded labels. The wrong-target handoff mutation
also carries a quoted canonical-call decoy. All mutated sources were restored
and the restored builds and gates pass. The final review has no unresolved
correctness finding.

The assembled foreground Linux verifier passes on Lean v4.34.1: clean build,
kernel proofs, fixtures, generated C ABI, source gates, standalone formatting,
coverage, CI runner checks, fuzz corpus, POSIX smoke tests, all thirteen live
suites with their exact counts and the unrelated-session sentinel. Both
required final builds, standalone lint and warning-level shellcheck pass.

Receipts: `/tmp/linger-select-create-20260927/` and
`/tmp/linger-select-create-test-receipts-20260927/handoff.md`.
No macOS, live GUI-terminal or real remote-host verification is claimed.
Hosted checks have not run for this checkpoint at closure; the preceding
checkpoint's jobs did not start because of GitHub billing/spending limits.
