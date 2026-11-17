# Contributing to linger

Terminal session attachment, recovery and selection in Lean 4. The executable,
namespaces and source tree use `linger` / `Linger`; checkpoints use `LNGR` v4, and v1 to v3 still load.

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

`./lake test` is the full verifier, `scripts/verify.sh`: among its stages it runs every `Check`
of linger's world claims and of each package's, as the challenge library's checks runner does.
`./lake script run software_challenge/test_challenge` is the library's own test: the build,
`lake lint --builtin-lint`, which runs the lint driver and Lean's builtin linters on each default
target's roots, every `Check` and, once every headline is proved, a sandboxed `lake comparator`.
`./lake script run software_challenge/grade <commit>` judges a commit as the Lean Software
Challenge does: it refuses one that changes a file the audit lists as `Owned:`, then builds it
from scratch in a temporary worktree and runs `lake comparator` and `lake test` there. Run it
in the foreground, as the verifier.

## Layout

A module's role is the first component of its name that is `CoreSpec`, `CoreCode`, `WorldSpec`
or `WorldCode`, as the Lean Software Challenge reads it, and any other module is tooling.

- `Linger/<Component>/`: `CoreSpec.lean` holds what gives headline theorems their meaning: value
  types, reference models and predicates over the program's operations, never the
  representation of a state or code that runs, and the wrong parts kills name. `WorldSpec.lean`
  holds the component's world claims. `CoreCode.lean` and `CoreCode/` hold its pure code,
  `WorldCode.lean` and `WorldCode/` its IO, and `WorldCode/Checks.lean` the checks of its world
  claims; then `Proofs/`, `Tests/` (elaboration-time unit tests) and `Suites/` (executable
  suites).
- `Linger/Os/`: the answers every command gives (`CoreSpec.lean`, `CoreCode/Answer.lean`),
  linger's environment policies (`CoreCode/Env.lean`) and the shim's smoke tests
  (`Suites/Shim.lean`, `./lake exe lingertest`).
- `Linger/Target/`: session names, remote targets and the transports that reach their hosts, and
  the world claims of login shells and transports.
- `Linger/Display/`: session status, titles and listings.
- `Linger/Terminal/Suites/`: live suites of the VT toolkit as linger runs it.
- `Linger/Session/`: the session machine (`CoreCode.lean`), its effect `Driver`, `Wire` format,
  `Buf` queues, `Checkpoint`s, the `Handoff` an upgrade carries to the daemon's new image and the
  `Names` that lead to sessions' IDs (`CoreCode/`); `WorldCode/` holds the daemon, the attach
  client, checkpoint files, state paths, keyed by ID, and the names directory.
- `Linger/Selector/`: interactive selection: `Key` bindings of the `input` package's keys and
  the `Picker`, which ranks names with the `fuzzy` package; `WorldCode.lean` runs the picker on
  a terminal.
- `Linger/Import/`: the latest tmux-resurrect save, a source linger reads and never writes: the
  `Resurrect` policy, and `WorldCode.lean` reads it for `ls`, an attach and a kill.
- `Linger/App/`: the command line: the `Entry` route and, in `WorldCode.lean`, the commands;
  `WorldCode/Main.lean` holds `main`.
- `Challenge.lean`: the program parts headline theorems name, declared as holes, and the
  headline theorems and their kills, stated with `sorry`. It imports only `CoreSpec` and
  `WorldSpec` modules and the packages' modules, and the build writes `comparator.json` from it
  for `lake comparator`.
- `Linger.lean`: the session library's umbrella module.
- `Theorems/`: the headline proofs (`Solution.lean`) and `Coverage.lean`, which checks the
  pure code's `@[csimp]` replacements and lists its definitions for the emitter check in
  `Verify/Coverage.lean`; `Verify/`: the verifier's harness, runner and own suites.
- `packages/`: Lake packages linger requires by path, each with its own `Challenge.lean`,
  solution, audit and `owned.lock`, and laid out by role as a component is: `fuzzy`, the fuzzy
  matcher (namespace `Fuzzy`), `input`, the bounded terminal key decoder (`Input`), `terminal`,
  the VT toolkit (`Terminal`): the emulator `Vt`, `Render`, streaming `Replay`, child-facing
  `Mediation` and safe `Title` updates, and `os`, the operating system (`Os`): `WorldSpec.lean`
  holds the foreign declarations and the world claims the bounded waits, an upgrade's exec, the
  names of sessions and a session's ending rest on, `c/shim.c` the
  C they bind, `WorldCode.lean` the checked surface callers use, `CoreCode/Wait.lean` the
  bounded wait and `CoreCode/Write.lean` what a full write does after each attempt. The `os`
  library compiles each module to a shared library too, so a check can reach the shim. Linger's
  audit trusts every module outside linger's package, and linger's headlines may name a
  package's parts, which its own headlines claim. Build one alone with `../../lake build` in its
  directory; it shares linger's `.lake/packages`.
- `first/`: a package linger requires first, which declares nothing and whose build directory is
  linger's: a workspace looks for a module in its dependencies' builds, the first required last,
  before its own, and each package names its challenge `Challenge`, as linger does.
- `scripts/`: build and verification orchestration.

Components depend downward only: `Os` and `Target`; then `Display`; then `Session` and
`Selector`; then `Import`; then `App`. Packages import no component.

Namespaces do not change; module paths gain a role component: `Linger.Session.Buf` lives in
`Linger/Session/CoreCode/Buf.lean` and `Linger.Session.Shell.Daemon` in
`Linger/Session/WorldCode/Daemon.lean`. Use ordinary `import` for implementation
dependencies; reserve `public import` for types in the public interface and
deliberate reexports. Keep proofs separate to control imports and verification, not for binary
size: Lean erases proofs regardless of file placement.

## Implementation rules

- `CoreSpec` and `CoreCode` modules are pure: each build's audit rejects IO, `partial`,
  `unsafe`, `@[extern]`, `@[implemented_by]`, initializers and `dbg` there, and lets `CoreCode`
  import only `CoreSpec` and `CoreCode`. A `WorldSpec` module holds `@[extern] opaque`
  declarations and world claims and is otherwise pure, and `WorldCode` does the IO. Model effects
  as data; execute them in `WorldCode`.
- State invariants in `Challenge.lean` and the `CoreSpec` modules, and design code for
  provability.
- The files the audit lists as `Owned:` (`Challenge.lean`, each `CoreSpec` and `WorldSpec`
  module, the Lake configuration and the toolchain) say what linger claims. Change them to
  change a claim, never to make a proof pass, and restate a theorem there no weaker than its
  source. Each package root's `owned.lock` records their hashes, and a build fails when one
  drifts: delete the lock to record a changed claim, build twice, and commit the new lock with
  it. The challenges follow the library's convention: a module doc says what is claimed and
  what is not, and holes, headlines and kills carry no doc comments.
- Every headline in `Challenge.lean` needs a kill marked `@[kills headline]`: a theorem there
  stating the headline's negation with a wrong part in place of a hole, proved in
  `Theorems/Solution.lean`. The audit matches a kill against its headline term by term, ignoring
  binder names and metadata, so a wrong part is a closed term of the hole's type as written: when
  a hole takes type parameters, or the elaborator would widen a lambda's type, name the wrong part
  in a `CoreSpec` module (`Offloop.eager`, `Render.escape`). Statements bind no `let` and match
  no pattern, whose auxiliary definitions a challenge may not declare. The audit rejects two
  headlines that state the same up to binder names, and the report marks a headline that
  quantifies over no input `(one instance)` and a world claim its proof never uses `unused by the
  proof`, which it reads from a linter that runs where `SoftwareChallenge.Commands` is loaded: a
  module that proves headlines loads it, as a package's `Solution` does with
  `meta import SoftwareChallenge`.
- State each assumption about the outside world as a `WorldClaim` in a `WorldSpec` module, over
  the foreign behaviour it constrains, and give it a `Check` in its component's
  `WorldCode/Checks.lean` that tests the real behaviour on the host: the check names the
  claim's parameter with a bodiless `opaque` and observes it by running the real thing. No
  program module imports a module of checks, and the `Checks` library, a default target, builds
  each one so that the audit counts them. A module that declares claims or checks imports their
  syntax with a private `import SoftwareChallenge.Commands`: `lake shake` rejects a `meta`
  import there, and a public one would pass Lean's own syntax to every importer, where `{ id }`
  then reads as a singleton set.
- Every public declaration in a library needs a docstring: `lakefile.lean` enables
  `linter.missingDocs` for every library but `Verify` and the challenges, and
  `scripts/verify.sh` checks the modules under `Linger/` outside `Proofs/` and `Tests/` directly.
- State user-visible behavior, not only invariants, and bound every input-controlled
  loop or reply count in the model with a theorem (`repeatAtMost_eq_repeat`,
  `step_bytes_one_reply`); `scripts/gates.sh` rejects a CSI loop that bypasses
  `Vt.repeatAtMost`.
- Runtime uses of proved values need call-site gates, unless making the unproved
  alternative private enforces it. IO behavior is tested, not proved. Start behavioral
  fixes with a failing check and verify that new assertions detect a deliberate break;
  a check of a failure or cleanup path also asserts that the path was reached.
- A command exists only for an `Op` of `Linger/App/CoreSpec.lean`, with one spelling and each
  option one parameter of it: adding one changes the owned `Op`, a claim change
  (`commands_minimal`).
- One signal, one meaning: every signal that crosses linger's boundary means what its standard
  says, and linger gives none a meaning of its own. That covers a sequence a program writes
  (ECMA-48 and the xterm, OSC 9, 52, 133 and 777 conventions), a key a person presses (readline
  and fzf), a variable (no-color.org's NO_COLOR, `TERM=dumb`) and an exit status (128 + N for
  signal N; 124 to 127 as `timeout` and `env` use them; 130 for a cancelled chooser, as fzf
  uses it). A standard signal that reports something linger tells, such as an ending or a
  request for attention, is told as its standard means it. Where no standard covers what linger
  must say, linger's own word keeps one meaning: a status glyph or a porcelain name never takes
  a second subject.
- One view, one meaning: a view is a function of the records and of what the person did, and it
  changes only on an event that changes its meaning, never on sampling, repetition or refresh. A
  keystroke repaints only the rows it changed, a refresh does not reorder the chooser, printing or
  going quiet does not move a row, a steady redraw keeps one status, and an alert fires once per
  change into asking.
- Read SHELL, HOME for remote hosts and for a resume, and LINGER_NO_DETACH_KEY once, and
  NO_COLOR and TERM once for each of `ls` and the chooser, into the pure policies of
  `Linger/Os/CoreCode/Env.lean`, which `scripts/gates.sh` ties to each read, and run every
  variable the program reads unset and empty in a suite.
- Raw OS access belongs in the `os` package: `packages/os/Os/` and `packages/os/c/shim.c`.
  Every `@[extern]` declaration stays private in `packages/os/Os/WorldSpec.lean`, which declares
  nothing else but the world claims the waits, the exec, the names and the ending rest on, and
  `packages/os/Os/WorldCode.lean`, the one
  module that imports all of it, wraps each one in `Os.Shell`: it is the surface callers use.
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
  options come from `lakefile.lean`. Proofs add no axioms: each audit, linger's and each
  package's, rejects a declaration in a module its default targets build that uses an axiom
  beyond `propext`, `Quot.sound` and `Classical.choice`, as native evaluation (`native_decide`,
  `decide +native`, `bv_decide`) does. In comments, quote code in backticks; source gates skip
  backticked spans.

## Scope and maintenance

One daemon per session. No windows, tabs, splits, shared server, process-tree
restoration, retained images or terminfo negotiation. An upgrade replaces a daemon's image in
place and restores nothing. Creation in a selector
must be an explicit highlighted choice. Attaching inside a session may nest;
never silently switch sessions. Terminal handback clears the title; do not
introduce a title stack. Keep documentation factual and concise.

Use one writer per tree and a separate worktree for another writer. Copy into
a fresh destination. Commit verified changes as `step N: <summary>`; never
rewrite pushed history.

Git history holds plans, work logs and retired documentation, including paths
cited by older source comments. Do not add progress logs or continuity files.
