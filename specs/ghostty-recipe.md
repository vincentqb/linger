# Recipe language audit and Ghostty configuration

Status: in progress (2026-09-25)
Updated: 2026-09-25
Next: commit the audit checkpoint, then document Ghostty configuration and close
Predecessor: `specs/archive/lean-4.34.1.md`

## Goal

Audit each existing recipe, resolve the apparent conflict between the recorded
fish policy and AGENTS.md's broad Lean wording, and add a Ghostty recipe. Keep
terminal composition and migration policy outside the linger binary.

## Requirements

- Record a per-recipe language and correctness assessment, including ssh_config.
- Prefer the smallest implementation that preserves the intended behavior.
- Fix demonstrated failures with a failing check first.
- Keep tests proportional to the boundary they verify. A command recorder does
  not verify an actual GUI window or a terminal application's own parser.
- Use Ghostty's documented launch interface and preserve session names across
  its command boundary. Document any platform restrictions verified from source.
- Keep linger mechanisms, checkpoints, proofs and C unchanged.
- Correct current policy documentation without rewriting archived decisions.

## Verification

Run recipe syntax checks, targeted checks for demonstrated failures, both
required Lean builds, formatting and source gates, and the foreground full
verifier. Any permanent Lean checks belong to the existing recipe suite, with
its exact assertion count maintained only in tests/e2e.sh. Record the scope of
platform verification without claiming a recorded launch is a live GUI test.

## Steps

### Step 1 — audit the boundary and fix existing recipes

Complete (2026-09-25). `specs/archive/tmux-resurrect-recipe.md` explicitly chose a
fish implementation with Lean tests; SCRATCHPAD.md's 2026-09-15 inventory also
names fish recipes as deliberate non-Lean files. The earlier lean-suites
migration removed Python test code; it did not migrate recipe implementations.

| Recipe | Language decision | Finding and change |
|---|---|---|
| `lz.fish` | Keep fish: picker composition | Stop on failed partial listings; require one picker result; preserve failure/cancel status. |
| `lzh.fish` | Keep fish: picker/attach loop | Same picker guards; reject extra targets; preserve picker errors. |
| `lza.fish` | Keep fish: retry policy | Require one target; preserve attach status; stop when the retry pause fails. |
| `lzs.fish` | Keep fish: refresh policy | Empty host uses configured remotes; validate the interval; stop before clearing on listing failure and on failed pauses. |
| `lzo.fish` | Keep fish: terminal and SSH composition | Require a host; preserve SSH errors; validate all names before launching; stop on a failed tab launch. |
| `lzr.fish` | Keep fish: optional foreign-save import | Resolve the executable and relative state paths before entering saved directories. Existing import policy remains intact. |
| `ssh_config` | Keep native SSH configuration | Parsed with `ssh -G`; no correction needed. |

The shared Lean recipe checks fail against the original helpers. Separate live
importer checks fail for relative PATH and LINGER_DIR, then pass after resolving
those paths in the invocation directory. A final symlink/parent regression
rejects lexical normalization of a state path; filesystem resolution preserves
its meaning. The canonical check count lives only in tests/e2e.sh.

The uncommitted E2E/Ghostty.lean draft has been withdrawn. It preceded the
implementation, duplicated many launcher assumptions, and verified only command
recording. Its red-run receipt remains in /tmp/linger-ghostty-red.log; no Ghostty
recipe or corresponding test change had been committed.

The helper worker's changes were reviewed and integrated from its isolated
worktree. Both required builds, fish syntax, SSH configuration parsing,
formatting, source gates, and the final foreground full verifier pass.
Receipts are `/tmp/linger-recipe-step1-build.log`,
`/tmp/linger-recipe-step1-proofs-tests.log`,
`/tmp/linger-recipe-symlink-{red,green}.log`, and
`/tmp/linger-recipe-audit-final-verifier.log`. Earlier failing helper and
relative-path runs remain in `/tmp/linger-recipe-audit-red.log` and
`/tmp/linger-recipe-path-red.log`. These are local Linux results.

### Step 2 — add a proportionate Ghostty recipe and close

Reuse `lzh` through Ghostty's native `command = direct:fish -c lzh` setting
(documented since Ghostty 1.2). This gives new windows the existing picker and
detach-to-switch loop without a second launcher or picker implementation.
The platform-specific launcher research is unnecessary for this configuration
recipe. No GUI execution is available on this host.
