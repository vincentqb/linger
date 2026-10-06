# Contributing to linger

Terminal session attachment, recovery and selection in Lean 4. The executable,
namespaces and source tree use `linger` / `Linger`; checkpoints use `LNGR` v1.

## Build and verify

Always use `./lake`, including on macOS. The toolchain is pinned to v4.34.1.

```sh
./lake build
./lake build Theorems Tests
./lake lint
./lake test
```

Both builds must pass before committing. Run the full verifier for runtime
changes, deletions and changes to verification itself. Run it in the foreground:
a background shell job disables signals required by the tests. Use the default
test state directories; reserve `LINGER_TEST_DIR` for focused single-suite runs.
Compiler upgrades require the full verifier after `./lake clean`.

Install the hooks with `pip install --upgrade pre-commit` and `pre-commit install`.
For a clone previously using `.githooks`, first run
`git config --local --unset-all core.hooksPath`.
The configuration and `./lake lint` share `scripts/lint.sh`: hygiene, source
gates, workflow validation, formatting and semantic lint.
CI requires `actionlint` and `lean-fmt` on Linux.
Pre-commit temporarily shelves unstaged changes while checking the staged content.
Use `pre-commit run --all-files` to check the working tree.
Install `lean-fmt` standalone, never as a Lake dependency.
See [.github/workflows/ci.yml](.github/workflows/ci.yml) for tool installation.

Linux verifies every push. macOS runs on scheduled changes, release tags and
manual dispatch; request a manual run for changes to `c/shim.c` or `./lake`.

## Layout

- `Linger/Core/`: pure session and terminal models.
- `Linger/Runtime/` and `Linger/Posix.lean`: session IO and the OS boundary.
- `Linger/Tools/` and `Linger/Manager/`: CLI policies and their IO executors.
- `Theorems/`: proofs; `Tests/`: elaboration-time unit tests.
- `E2E/`: executable suites; `scripts/`: build and verification orchestration.

Keep module paths and namespaces aligned. Use ordinary `import` for implementation
dependencies; reserve `public import` for types in the public interface and
deliberate reexports. `Linger.lean` is the session library's umbrella module.
Keep proofs separate to control imports and verification, not for binary size:
Lean erases proofs regardless of file placement.

## Implementation rules

- `Linger/Core/*` and `Linger/Tools/*` are pure: no `IO`, `partial def` or `sorry`.
  Model effects as data; execute them in `Linger/Runtime/*` and `Linger/Manager/*`.
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
- Validate session names without rewriting them before paths; fuzzy matching
  belongs only in interactive selection. Freeze each poll loop's fd set.
  Compose displays through `Title.compose` and `Status.summary` in the order
  `session · application title · attention`, reserving room for attention.
- Program logic, proofs and automated suites are Lean. Python is used only by
  the external `pre-commit` framework. The C shim, build wrapper, shell verifier
  and native configuration recipes are boundaries.
- Ratchets live only in `scripts/gates.sh`; exact suite counts only in
  `scripts/e2e.sh`. Tests assert against the implementation's definitions.
  Use `scripts/` for shell orchestration; do not recreate a lowercase `tests/`.
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
