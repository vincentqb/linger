# Contributing to linger

Terminal session attachment, recovery and selection in Lean 4. The executable,
namespaces and source tree use `linger` / `Linger`; checkpoints use `LNGR` v1.

## Build and verify

Always use `./lake`, including on macOS. The toolchain is pinned to v4.35.0.

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

CI runs at 06:17 UTC on the first of each month, on Linux and macOS, when the month
brought commits, and on manual dispatch. Pushes and pull requests do not trigger it.

`./lake script run software_challenge/grade <commit>` judges a commit as the Lean Software
Challenge does: it refuses one that changes a file the audit lists as `Owned:`, then builds it
from scratch in a temporary worktree and runs `lake comparator` and `lake test` there. Run it
in the foreground, as the verifier.

## Layout

- `Linger/<Component>/`: a component's pure modules, its `Shell.lean` or `Shell/` for IO
  and, for the OS, `Boundary.lean` for the foreign declarations; then `Proofs/`, `Tests/`
  (elaboration-time unit tests) and `Suites/` (executable suites). `Spec.lean` holds what
  gives headline theorems their meaning: value types, reference models and predicates over
  the program's operations, never the representation of a state or code that runs. It
  imports only `Spec` modules.
- `Linger/Os/`: linger's environment policies (`Env.lean`) and the shim's smoke tests
  (`Suites/Shim.lean`, `./lake exe lingertest`).
- `Linger/Target/`: session names and remote targets.
- `Linger/Display/`: session status, titles and listings.
- `Linger/Terminal/Suites/`: live suites of the VT toolkit as linger runs it.
- `Linger/Session.lean` and `Linger/Session/`: the session machine, its effect `Driver`,
  `Wire` format, `Buf` queues and `Checkpoint`s; `Shell/` holds the daemon, the attach
  client, checkpoint files and state paths.
- `Linger/Selector/`: interactive selection: `Key` bindings of the `input` package's keys and
  the `Picker`, which ranks names with the `fuzzy` package; `Shell.lean` runs the picker on a
  terminal.
- `Linger/Import/`: importing tmux-resurrect saves: the `Resurrect` policy, and `Shell.lean`
  runs it.
- `Linger/App/`: the command line: the `Entry` route and, in `Shell.lean`, the commands.
- `Challenge.lean`: the program parts headline theorems name, declared as holes, and the
  headline theorems and their kills, stated with `sorry`. It imports only `Spec` modules; `comparator.json`
  names the holes and theorems for `lake comparator`.
- `Audit.lean`: the Lean Software Challenge role of each module prefix; `./lake build` runs the audit.
  List a new component there: a module no entry covers is tooling, which program code
  cannot import.
- `Theorems/`: the headline proofs (`Solution.lean`), the cross-component contracts and the
  coverage census; `Verify/`: the verifier's harness, runner and own suites.
- `packages/`: Lake packages linger requires by path, each with its own `Challenge`, solution,
  `comparator.json` and audit: `fuzzy`, the fuzzy matcher (module and namespace `Fuzzy`),
  `input`, the bounded terminal key decoder (`Input`), `terminal`, the VT toolkit
  (`Terminal`): the emulator `Vt`, `Render`, streaming `Replay`, child-facing `Mediation` and
  safe `Title` updates, and `os`, the operating system (`Os`): `Boundary.lean` holds the
  foreign declarations, `c/shim.c` the C they bind, `Shell.lean` the checked surface callers
  use and `Wait.lean` the bounded wait. Linger's audit trusts each package, and linger's
  headlines may name a package's parts, which its own headlines claim. Build one alone with
  `../../lake build` in its directory; it shares linger's `.lake/packages`.
- `scripts/`: build and verification orchestration.

Components depend downward only: `Os` and `Target`; then `Display`; then `Session` and
`Selector`; then `Import`; then `App`. Packages import no component.

Keep module paths and namespaces aligned. Use ordinary `import` for implementation
dependencies; reserve `public import` for types in the public interface and
deliberate reexports. `Linger.lean` is the session library's umbrella module.
Keep proofs separate to control imports and verification, not for binary size:
Lean erases proofs regardless of file placement.

## Implementation rules

- Pure modules have no `IO`, `partial def` or `sorry`: a component's top module and each
  component's modules other than `Boundary.lean` and `Shell.lean`. Model effects as data;
  execute them in `Shell.lean` or `Shell/`.
- Every `def` or `abbrev` in a pure module needs a written
  theorem whose type contains its exact fully qualified constant in the same
  commit, checked by `Theorems/Coverage.lean`; generated lemmas do not count.
  State invariants in `THEOREMS.md` and design code for provability.
- The files the audit lists as `Owned:` (`Challenge.lean`, `comparator.json`, `Audit.lean`,
  each `Spec.lean`, `packages/os/Os/Boundary.lean`, the Lake configuration and the toolchain) say
  what linger claims. Change them to change a claim, never to make a proof pass, and restate a
  theorem there no weaker than its source.
- Every headline in `Challenge.lean` needs a kill: a theorem there stating the headline's
  negation with a wrong part in place of a hole, proved in `Theorems/Solution.lean`.
- State each assumption about the outside world as a `WorldClaim` in a `Spec.lean`, and mark
  the suites that exercise it with `@[exercises]`. A module that declares claims imports their
  syntax with a private `import SoftwareChallenge.Commands`, which `Audit.lean` trusts:
  `lake shake` rejects a `meta` import there, and a public one would pass Lean's own syntax to
  every importer, where `{ id }` then reads as a singleton set.
- Every public declaration in a library needs a docstring: `lakefile.lean` enables
  `linter.missingDocs` for every library but `Verify`, and `scripts/verify.sh` checks the
  modules under `Linger/` outside `Proofs/` and `Tests/` directly.
- State user-visible behavior, not only invariants, and bound every input-controlled
  loop or reply count in the model with a theorem (`repeatAtMost_eq_repeat`,
  `step_bytes_one_reply`); `scripts/gates.sh` rejects a CSI loop that bypasses
  `Vt.repeatAtMost`.
- Runtime uses of proved values need call-site gates, unless making the unproved
  alternative private enforces it. IO behavior is tested, not proved. Start behavioral
  fixes with a failing check and verify that new assertions detect a deliberate break;
  a check of a failure or cleanup path also asserts that the path was reached.
- Read SHELL, HOME for remote hosts and for a resume, and LINGER_NO_DETACH_KEY once, into
  the pure policies of `Linger/Os/Env.lean`, which `scripts/gates.sh` ties to each read,
  and run every variable the program reads unset and empty in a suite.
- Raw OS access belongs in the `os` package: `packages/os/Os/` and `packages/os/c/shim.c`.
  Every `@[extern]` declaration stays private in `packages/os/Os/Boundary.lean`, which declares
  nothing else, and `packages/os/Os/Shell.lean` wraps each one: it is the surface callers use.
  Keep the shim to syscalls and errno.
  Return `-errno` and avoid numeric errno values in Lean. A binding that takes a pid also
  takes the proof `Os.Shell.checkPid` returns.
- Validate session names without rewriting them before paths; fuzzy matching
  belongs only in interactive selection. Freeze each poll loop's fd set.
  Compose displays through `Title.compose` and `Status.summary` in the order
  `session · application title · attention`, reserving room for attention.
- Place the target of every attach or capture argv the program builds for itself
  with `Remote.targetOperands`, proved against `Remote.targetArgs`
  (`targetArgs_targetOperands`); `scripts/gates.sh` rejects a literal attach argv.
- Program logic, proofs and automated suites are Lean. Python is used only by
  the external `pre-commit` framework. The C shim, build wrapper, shell verifier
  and native configuration recipes are boundaries.
- Ratchets live only in `scripts/gates.sh`; exact suite counts only in
  `scripts/verify.sh`. Tests assert against the implementation's definitions.
  Use `scripts/` for shell orchestration; do not recreate a lowercase `tests/`.
- In `scripts/`, `Verify/` and each `Suites/`, scratch without sockets lives under
  `${TMPDIR:-/tmp}`, in Lean through `Verify.Harness.tempRoot`, `IO.FS.withTempDir` or
  `IO.FS.createTempDir`, and a directory that will hold a Unix socket lives under `/tmp`,
  through `Verify.Harness.socketRoot` or `socket_root` in `scripts/verify.sh`, since macOS's
  `TMPDIR` alone takes about 49 of a socket path's 104 bytes; `scripts/gates.sh` rejects
  any other hard-coded `/tmp` there and in the CI workflow, except in
  `Linger/Session/Suites/Paths.lean` and `Linger/Display/Suites/Overview.lean`, which
  assert product defaults.
- No `partial def`, fuel parameter or `set_option` in any Lean file (`scripts/gates.sh`):
  options come from `lakefile.lean`. Proofs add no axioms:
  `Theorems/Coverage.lean` rejects every axiom declared in pure or proof
  modules, including those native evaluation (`native_decide`,
  `decide +native`, `bv_decide`) adds, and fails unless its imports reach
  every such module. In comments, quote code in backticks; source gates skip
  backticked spans.

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
