# Manager defaults

Status: complete — local Linux verification green; hosted checks pending
Updated: 2026-09-26
Next: none
Predecessor: `specs/archive/optional-manager.md`

## Goal

The user wants good default behavior without maintaining command-line options.
Give the optional manager one selection lifecycle and the importer one import
policy. Remove the status recipe's host and interval switches. Keep arguments
that identify the input, rather than choosing a mode.

## Interface

- `lz` selects a session and returns to selection after attach exits. Escape,
  ctrl-c and ctrl-d still cancel with status 130.
- `lz import-resurrect [SAVE]` creates shells in the saved directories and skips
  existing identities. It never replays commands from the save. The optional
  path chooses a save; omission keeps the existing default-save discovery.
- `lz --help` and `lz -h` describe the interface without requiring a terminal.
- `lzs` lists local and configured remote sessions every five seconds. The
  editable recipe contains the refresh policy.
- `lza TARGET` and `lzo HOST` keep their required operands.
- Ghostty starts `direct:lz`.

Remove the one-shot selector branch, `--loop`, its initial-target shortcut,
`--restore-processes`, command allowlist and replay planning/execution.
Reject removed arguments rather than accepting them silently. A save whose
filename begins with `-` can be addressed by a relative or absolute path.

Core `linger` commands retain their session and scripting contracts. This work
does not introduce another configuration channel or a CLI parsing framework.

## Contracts and evidence

The existing selector provenance, input suppression, detach and terminal
handback theorems support the always-returning manager. PTY observations must
show another selection visit after success, failure and real detach, with the
terminal restored before every subprocess.

The importer retains whole-save validation, canonical and distinct projected
names, complete directory preflight, preserved order, skipping existing names,
and sequential idempotence. Parsed panes and plans retain no saved command.
Prove the simplified parser/planner contracts and tie the IO executor to the
proved plan and constant shell-creation argv with source gates. Demonstrate
ignored saved commands with unit, recorder and real-daemon checks.

These contracts support behavior; they do not prove a UX preference, IO
success, concurrent name claiming or GUI behavior.

## Steps

### Step 1 — simplify commands and prove the default policies

Complete. Failing checks preceded the default and argument changes. Separate
worktrees supplied the pure importer changes and manager terminal regressions.
The runtime, command surface, recipes, documentation, proofs and live checks
are integrated. The full foreground verifier and both required builds pass.
Compiling mutations demonstrate the regression checks and proof boundaries;
SCRATCHPAD.md records the receipts for the verified checkpoint.

The updated recipe suite first ran against the previous implementation in the
foreground. Its failures isolated argument rejection, the Ghostty default and
the retired import option; existing import and path checks passed. The parent
has integrated the runtime, CLI, recipes, importer proofs and manager terminal
regressions. Both workers are closed; their reviewed changes are in the main
checkout. Combined program, proof and unit builds pass, as do the actual
recipe and manager suites, source gates and formatting checks.

Four compiling pure-policy mutations fail both proofs and fixtures. Three
compiling IO mutations bypass the proved plan, change the constant launch
argument or ignore the saved directory; each fails its new source gate and
the corresponding actual-executable checks. Restored sources match their
verified hashes. A preliminary unused-binding compiler rejection is retained
separately and is not counted as mutation evidence.

## Verification

Keep receipts under `/tmp/linger-defaults-20260926/`. Exact suite counts and
source ratchets remain in their authoritative verifier scripts. Commit and push
ordinary mainline history after verification. Hosted CI was previously unable
to start because GitHub reported an account billing/spending limit issue; check
the result of this push and report its actual state.

## Completion record — 2026-09-26

`lz` now always returns to a fresh selection after attach exits; the one-shot,
loop switch and initial-target paths are gone. Import creates shells in the
saved directories, discards validated command text and has no replay option or
allowlist. `lzs` uses configured remotes and a fixed five-second pause. Ghostty
starts bare `lz`. Required target/host operands, optional save paths and help
remain. Removed options fail before subprocesses.

The complete foreground Linux verifier passes from an empty build on Lean
v4.34.1, including generated C ABI, source gates, standalone formatting,
semantic coverage, CI runner decisions, fuzz corpus, POSIX smoke tests, all
thirteen live suites and the unrelated-session sentinel. The final program
and theorem/unit builds also pass. `full-verifier.log`, `clean-build.log`,
`full-layout.log`, `full-suites/`, `step1-build.log` and
`step1-proofs-tests.log` preserve those results in the receipt directory.

Both workers are integrated and closed. No C, raw binding, dependency, partial
definition, fuel or proof-limit increase was added. Hosted checks are pending
at this checkpoint; no macOS, live Ghostty GUI or real remote-host result is
claimed. No spec remains in flight.
