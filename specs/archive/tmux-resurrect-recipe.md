# 2026-09-17 tmux-resurrect recipe — import panes without widening core

Status: complete (2026-09-17) — Step 1 done, archived
Updated: 2026-09-17
Next: nothing; open a new `specs/<slug>.md` for the next item
Predecessor: `specs/archive/minimality-audit.md` (complete)
Sync: local only by user direction; Pippin and Taskei are opted out

## Goal

Add one fish recipe that imports tmux-resurrect `pane` records as independent
linger sessions. Keep the foreign format, workspace composition, and command
restart policy outside the binary and checkpoint codec.

## Requirements

- **R1 — Recipe boundary.** WHEN a user imports a tmux-resurrect save, THE
  importer SHALL parse it only in `recipes/lzr.fish`; it SHALL NOT add a reader,
  option, dependency, or format branch to the linger binary.
- **R2 — Pane projection.** FOR EACH valid `pane` record whose projected name
  already satisfies linger's name alphabet and 80-character limit, THE importer
  SHALL create `<session>-w<window>-p<pane>` in the record's saved working
  directory; otherwise it SHALL fail before creating any session.
- **R3 — Sequential idempotence.** IF a projected identity appears in linger's
  initial local listing as live or resumable, THEN THE importer SHALL leave it
  unchanged and SHALL NOT revive it or resend its saved command. Concurrent
  imports and same-name creation after that snapshot are outside this recipe's
  contract because `linger run` has no atomic create-only operation.
- **R4 — Explicit process restart.** THE importer SHALL NOT execute saved
  commands by default. WHERE `--restore-processes` is supplied, THE importer
  SHALL send only commands whose first word is in its documented fixed allowlist.
- **R5 — Input validation.** IF the save is missing, contains a malformed `pane`
  record, names no panes, projects an invalid linger name, or names a working
  directory the recipe cannot enter, THEN THE importer SHALL return nonzero with
  a diagnostic before invoking linger.
- **R6 — Deliberate loss.** THE importer SHALL ignore window layouts, active
  state, grouped-session records, and captured pane contents.
- **R7 — Verification.** THE change SHALL pass a break-verified end-to-end recipe
  suite, both Lean builds, source gates, and the foreground whole-deliverable gate.

## Acceptance criteria

**Default import**
- Given a save at tmux-resurrect's default XDG path with one pane whose directory
  contains a space
- When `lzr` runs without arguments
- Then the projected linger session exists in that directory and no saved command
  executes

**Opt-in process restart**
- Given an empty saved command, one allowlisted command, and one command outside
  the allowlist
- When `lzr --restore-processes <save>` runs
- Then all three panes become sessions, commands stay aligned with their panes,
  only the allowlisted command executes, and a sequential second import does not
  execute it again

**Existing recovery state**
- Given a projected name whose linger daemon is gone but checkpoint remains
- When process restore is requested for that pane
- Then the importer leaves the checkpoint resumable and executes nothing

**Invalid input**
- Given a missing or malformed save, an invalid projected name, or a working
  directory the importer cannot enter
- When `lzr` reads it
- Then it returns nonzero with a specific diagnostic before creating a session

**Boundary**
- Given the completed diff
- When its paths are inspected
- Then the format parser exists only in the fish recipe and its Lean E2E fixture;
  `Linger/`, `Theorems/`, and `Tests/` are unchanged

## Design

`lzr [--restore-processes] [SAVE]` defaults to
`$HOME/.tmux/resurrect/last` when that directory exists, otherwise
`${XDG_DATA_HOME:-$HOME/.local/share}/tmux/resurrect/last`. It reads tab-separated
records into fish arrays and validates every pane before creating any session.
A pane's saved directory has its leading format sentinel removed, `\ ` decoded,
and a leading `~` expanded without `eval`. The recipe enters every directory as
part of validation and again immediately before creation. Projected names must
already be valid linger names so the binary's sanitizer cannot merge two panes.

After validation, one `linger ls --porcelain` snapshot supplies every existing
local identity, including resumable checkpoints. For each projected name absent
from that snapshot, the recipe changes its own working directory temporarily and
runs `linger run <name> true`; linger therefore creates the shell in that
directory using its existing upsert path. The snapshot and upsert are not atomic,
so this is deliberately a sequential migration recipe; making the claim atomic
would require a new create-only binary operation. The optional restart path checks
the saved full command's first word against the fixed process list in the recipe,
then passes the whole saved command as one `linger run` argument. Identities
present in the snapshot are skipped before either action.

A dedicated Lean E2E suite invokes fish against real linger daemons and synthetic
save files. It checks both default paths, empty-XDG fallback, escaped and
inaccessible working directories, no-command default, allowlist and command
alignment, live and resumable idempotence, canonical names, malformed input, and
missing input. No unit layer is added: all new logic is one boundary function,
and the integration suite drives that function directly.

## Steps

### Step 1 — test, implement, verify, and close — done ✓ (2026-09-17)

Added `lzr [--restore-processes] [SAVE]` as a fish-only importer. It validates
all pane records, directory access, canonical names, and duplicate projections
before touching linger; maps each pane to `<session>-w<window>-p<pane>`; skips
identities in the initial local listing, including resumable checkpoints; and
keeps full saved-command execution behind an explicit flag and fixed first-word
list. Window state and captured contents remain outside the mapping. No file
under `Linger/`, `Theorems/`, or `Tests/` changed.

RED: with the recipe absent, the new suite ran all ten initial assertions and
failed eight; the two negative command-execution assertions passed by absence.
The first run also caught a bad test failure path, and live inspection corrected
its nonexistent `cwd` lookup to linger's actual `start_dir` record before any
implementation was accepted.

The finished suite has 15 exact checks. Deliberate breaks proved the command-off
default, process list, empty-command alignment, live and resumable skip,
canonical-name rejection, pre-creation directory-access check, and empty-XDG
fallback independently. One suspected fish edge case was false: direct
`set -a commands (string sub ...)` preserves an empty result; deliberately
skipping that append is the mutation that fails alignment.

Three fresh read-only review passes found and closed fail-open existence probing,
post-sanitization name collisions, unchecked directory entry, an external `seq`
dependency, empty-XDG drift, and stale CI comments. The only irreducible boundary
is named rather than hidden: the listing snapshot and `linger run` upsert are not
atomic, so idempotence is sequential; concurrent same-name creation would require
a new create-only binary verb and is outside this recipe-only scope.

GREEN: fish syntax, `lean-fmt check`, canonical layout, source gates,
`./lake build`, `./lake build Theorems Tests`, the 15/15 recipe suite, and the
foreground `./tests/e2e.sh` all pass. The whole gate reports 11 live suites green.
The work remained local; Pippin, Taskei, pushing, and CR creation were skipped by
user direction.
