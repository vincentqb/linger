# Contributing to linger

Terminal session attachment, recovery and selection in Lean 4. The executable,
namespaces and source tree use `linger` / `Linger`; checkpoints use `LNGR` v1.

## Build and verify

Always use `./lake`, including on macOS. The toolchain is pinned to v4.34.1.

```sh
./lake build
./lake build Theorems Tests
./tests/e2e.sh
```

Both builds must pass before committing. Run the full verifier for runtime
changes, deletions and changes to verification itself. Run it in the foreground:
a background shell job disables signals required by the tests. Use the default
test state directories; reserve `LINGER_TEST_DIR` for focused single-suite runs.
Compiler upgrades require the full verifier after `./lake clean`.

Install the hook with `git config core.hooksPath .githooks`. Stage tracked edits
before committing. The hook runs hygiene, source gates and installed
`actionlint` / `lean-fmt` checks; CI requires both tools on Linux.
Install `lean-fmt` standalone, never as a Lake dependency.
See [.github/workflows/ci.yml](.github/workflows/ci.yml) for tool installation.

Linux verifies every push. macOS runs on scheduled changes, release tags and
manual dispatch; request a manual run for changes to `c/shim.c` or `./lake`.

## Implementation rules

- `Linger/Core/*` and `Tools/*` are pure: no `IO`, `partial def` or `sorry`.
  Model effects as data; execute them in `Linger/Runtime/*` and `Manager/*`.
- Every pure `def` needs a theorem type containing its exact fully qualified
  constant in the same commit, checked by `Theorems/Coverage.lean`.
  State invariants in `THEOREMS.md` and design code for provability.
- Runtime uses of proved values need call-site gates. IO behavior is tested,
  not proved. Start behavioral fixes with a failing check and verify that new
  assertions detect a deliberate break.
- Raw OS access belongs in `Linger/Posix.lean` and `c/shim.c`; all `@[extern]`
  declarations stay in the former. Keep the shim to syscalls and errno.
  Return `-errno`, avoid numeric errno values in Lean, and validate signal PIDs
  with `Linger.Posix.checkPid`.
- Sanitize session names before paths and freeze each poll loop's fd set.
  Compose displays through `Title.compose` and `Status.summary` in the order
  `session · application title · attention`, reserving room for attention.
- Program logic, proofs and automated suites are Lean. No Python. The C shim,
  build wrapper, shell verifier and native configuration recipes are boundaries.
- Ratchets live only in `tests/gates.sh`; exact suite counts only in
  `tests/e2e.sh`. Tests assert against the implementation's definitions.
  Keep `Tests/` distinct from `tests/`, including on case-insensitive filesystems.
- Avoid fuel parameters and unnecessary `partial def`. Recheck raised
  heartbeat or recursion limits after refactoring. Under `Theorems/`, refer
  to compiled evaluation without spelling its tactic name in docstrings.

## Scope and maintenance

One daemon per session. No windows, tabs, splits, shared server, process-tree
restoration, retained images or terminfo negotiation. Creation in a selector
must be an explicit highlighted choice. Attaching inside a session may nest;
never silently switch sessions. Terminal handback clears the title; do not
introduce a title stack. Keep documentation factual and concise.

Use one writer per tree and a separate worktree for another writer. Copy into
a fresh destination. Commit verified changes as `step N: <summary>`; never
rewrite pushed history.

Git history holds plans, work logs and retired documentation, including paths
cited by older source comments. Do not add progress logs or continuity files.
