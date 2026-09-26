# One public entry point

Status: in progress — step 1 complete; step 2, executable integration
Updated: 2026-09-26
Next: compose the existing executors in `Main`, then verify the complete CLI
Predecessor: `specs/archive/manager-defaults.md`

## Goal

The user finds the separate shortcuts overwhelming and wants `linger` as the
entry point everywhere. The user also wants terminal integration to work with
Ghostty, kitty, WezTerm and other terminals through a generic interface, without
terminal-specific CLI policy.

This explicitly reopens the earlier decision to keep the selector in a separate
optional executable. Preserve the session and VT library boundaries; change
which components the executable composes.

## Interface

- Bare `linger` selects a session when both stdin and stdout are terminals.
  After attach returns, selection starts again from a fresh listing.
- With either stream redirected, bare `linger` lists and exits. Explicit
  `linger ls` always lists and exits, including in a terminal.
- `linger import [SAVE]` performs the existing directory-only import. Saved
  commands never execute. The optional path selects input, not an import mode.
- Help describes the single executable and its defaults. Existing session
  commands, argument vectors and internal daemon dispatch remain intact.
- Selector and importer children use the running executable's absolute path.
  Installing an absolute command in a terminal does not require a second
  executable lookup through PATH.
- Native terminal examples all launch the same bare `linger`. They select no
  terminal backend or tab/window layout inside the program.

Retire the retry, status-board and kitty-tab helper scripts. The user confirmed
the common terminal-launch interface; after leaving the optional helper
preference open, the implementation takes the smaller default within the
authorized shortcut cleanup. Recipes contain only native terminal/SSH
configuration. There is no replacement shortcut binary or terminal backend.

## Contracts and limits

One small pure routing function chooses selection exactly for empty argv with
two terminal streams. All other session argv are preserved, independent of
terminal detection; import retains its full trailing argv for validation.
Universal proofs, concrete guards, compiling mutations and executable checks
cover these decisions. Source gates tie `Main` to the proved route and the
resolved executable.

The selector's existing provenance, order, bounded-state and paste-suppression
proofs remain unchanged. Its terminal checks cover cleanup and repeated attach.
Importer proofs retain complete validation, directory-only plans, skipped
identities, order and sequential idempotence. IO tests continue to cover
preflight, executable identity, physical paths and partial failures.

Theorems establish these contracts, not the desirability of a UX or the behavior
of a GUI terminal. Native configurations are inspected against their documented
settings. No live GUI, macOS or remote-host verification is implied.

## Steps

### Step 1 — prove the entry-point decision

Complete. One pure routing function has eight semantic proofs and six fixture
guards covering all stream modes and complete argument vectors. The census
covers its exact constant, and its import closure is empty. A compiling model
of the old dispatch fails the selector and import fixtures. Four compiling
mutations fail both proofs and fixtures: one-terminal selection, swallowed
explicit commands, reversed import argv and terminal-dependent import.

Both required parent builds, source gates, standalone lint and layout checks
pass. The full layout check identified only the changed Lake roots declaration;
formatting it and repeating its layout/lint checks and both builds is green.
The runtime still uses the predecessor entry point at this checkpoint.

### Step 2 — compose one executable and simplify terminal integration

In progress. Route `Main` through the proved decision, reuse the existing selector
and importer, remove the separate executable, and update help, documentation,
native configuration examples and IO call-site gates. Adapt synthetic probes
without introducing production test options, and retain actual CLI checks.
Run the complete foreground verifier after deletions, then both required
builds, close this spec, commit and push the integrated mainline.

## Work and verification

Workers own disjoint paths in fresh worktrees: routing/proofs/fixtures,
selector/PTY checks, and importer/import checks. The main writer owns the entry
point, help, build/gate wiring, native examples, documentation and integration.
No C, raw binding, dependency, proof-limit raise or new configuration channel is
planned. Receipts live in `/tmp/linger-entry-20260926/`.

Exact suite counts and source ratchets remain in the verifier scripts. Hosted
CI was last blocked before starting by GitHub billing/spending limits; inspect
the actual result of this push instead of assuming it has recovered.
