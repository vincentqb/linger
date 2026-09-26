# Optional Lean manager and portable recipes

Status: in progress — Step 1 verified; Step 2 terminal integration pending
Updated: 2026-09-26
Next: Step 2, optional executable, portable recipes and full verification
Predecessor: `specs/archive/recipe-boundaries.md`

## Goal

Implement the user's approved small session selector without fish or an external
picker. Consolidate it and the existing noninteractive save importer into one
optional `lz` executable. Keep the remaining reconnect, status-board and terminal
launch recipes editable as portable POSIX shell scripts.

The new reason for reopening the optional picker boundary is the user's explicit
preference for a shell-independent manager without a picker dependency. Bare
`linger` still lists and exits. The session daemon, VT toolkit, checkpoint format
and C boundary do not acquire manager policy.

## Interface

- `lz` selects once and returns the attach exit status.
- `lz --loop [NAME[@HOST]]` optionally attaches that exact target first, then
  returns to selection after each attach exit.
- `lz import-resurrect [--restore-processes] [SAVE]` preserves the existing
  standalone importer's preflight, planning, path and failure behavior.
- `lz --help` describes these forms without needing a terminal.

Selection uses ASCII-case-insensitive subsequence matching and stable listing order.
Other Unicode characters match exactly; no normalization is performed.
Up/down (also ctrl-p/ctrl-n), Home/End, backspace and ctrl-u edit the selection or
query. Enter attaches the selected original target. Esc, ctrl-c and ctrl-d
cancel with status 130. Ctrl-r refreshes the listing. A listing is fetched on
entry, explicit refresh, and return from attach, never by a timer. An empty
result stays editable. Query text cannot become a session-creation request.

The picker requires terminal input and output. It restores its terminal modes
and screen before handing control to `linger attach`, including on cancellation,
EOF and exceptions. It uses the existing POSIX interface, freezes the input fd
set before polling, and observes size changes without querying remote hosts.
Input decoding handles split escape sequences and UTF-8, consumes unsupported
CSI keyboard sequences, and prevents pasted newlines from accepting a selection.

## Contracts and evidence

| Decision | Required support |
|---|---|
| Small matcher and stable filter | Subsequence equivalence, filter provenance and preservation of listing order. |
| Selection over a snapshot | Bounded cursor, empty-list behavior, unchanged original target, cancellation cannot attach, query length bounded. |
| Raw input executor | Bounded decoder state and explicit key outcomes; PTY checks for split input, paste, resize, cleanup and handoff. |
| Single optional manager | Source closure gates prevent importing manager policy into `Linger/` or the VT toolkit; IO gates tie selection and import to their pure results. |
| Preserve import behavior | Existing parser/plan theorems and all importer regressions run through the new subcommand. |
| Portable shell composition | Existing retry, refresh, complete-listing validation and exact-argv checks drive the actual POSIX recipes. |
| Native terminal configuration | Ghostty uses its documented `direct:` command form; inspect the real config and its argv, without claiming a GUI result. |

Theorems cover the pure semantics, not terminal IO, process execution, SSH
availability or language preference. A selection snapshot can become stale before
attach. The importer retains its documented sequential, non-atomic behavior.

## Steps

### Step 1 — prove the selector and input model

Complete. Added `Tools.Key`, `Tools.Picker` and `Tools.Input`, with their
theorem and fixture modules. The combined semantic census covers every explicit
tool definition, including escaped identifiers, and the source gates constrain
purity and imports. Both required Lean builds, source gates, standalone lint
and layout checks pass. Compiling mutations fail the semantic proofs, fixtures,
purity/import gates and unclaimed-definition census as intended. Receipts and
the checkpoint detail are in SCRATCHPAD.md.

### Step 2 — execute the manager and port the recipes

Pending. Add the terminal executor and unified entry point, relocate importer
IO, remove the superseded fish picker and standalone importer entry point, and
port the three composition helpers. Update installation and Ghostty guidance.
Integrate the new manager PTY suite and preserve importer coverage. Every
behavior change begins with a failing check; all deletions survive the full
foreground verifier. Commit a green checkpoint, archive this spec and push.

## Work and verification

Independent workers use fresh worktrees with disjoint files: selection policy,
input decoding, portable recipes, and manager PTY checks. The main writer owns
the executor, entry point, build/gate wiring, documentation and integration.
No new dependency, C wrapper, raw binding or proof-limit raise is planned.

Keep receipts under `/tmp/linger-manager-20260926/`, exact live assertion counts
in `tests/e2e.sh`, and append break/verify and completion notes to SCRATCHPAD.md.
Run `./lake build` and `./lake build Theorems Tests` before each commit. Run the
complete verifier in the foreground for the runtime/deletion checkpoint, then
push ordinary commits to main without rewriting history.
