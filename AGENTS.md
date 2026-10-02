# linger

Session attach/detach + a CLI session overview in pure-function Lean 4.
Everything is `linger` — binary, namespaces, `Linger/` tree, shim
symbols; the checkout directory is still `lean-zmx`. The checkpoint
magic is `"LNGR"` v1 and nothing else is accepted; a reader for the
pre-rename `"LZMX"` tag is green at commit `e1ac562` if such a file ever
turns up. `SCRATCHPAD.md` and `specs/archive/` keep old names and paths
in their historical entries — read pre-2026-08-19 `Zmx/…` as `Linger/…`
and never rewrite them.

Full rationale for everything below lives in `SCRATCHPAD.md` (the
worklog), `specs/archive/` (closed build records), the comments in
`tests/gates.sh`, and git history.

## Where things stand — read this first after any compaction

1. `specs/ci-redesign.md` is active, opened 2026-10-02: remove duplicate
   verification and the Python hook framework, preserve the checks, and measure
   the resulting CI path. The preceding build/format audit is archived in
   `specs/archive/build-format-latency.md`; its source checkpoints and final
   records checkpoint pass hosted Linux CI.
   New work opens a new `specs/<slug>.md`, names itself here, and keeps the
   live count at one; every behavioral fix starts with a failing check and
   every deletion survives the full verifier stack.
2. `SCRATCHPAD.md` — append-only worklog: proof recipes, measurements,
   break-verify records, negative results. Read before writing; append
   after; never delete prior entries.
3. `specs/archive/` — closed records with their completion nuance.
   Never edit them; archive a finished spec with a completion record
   rather than editing it.
4. After a compaction, re-ground on the live spec + `SCRATCHPAD.md`
   (and `.claude/last-compact-state.md` if present), not on the
   compaction summary.
5. Close each round: update the spec's status block, commit a verified
   checkpoint.

## Settled non-goals — don't build these

Each was decided with a recorded reason (specs/archive/, SCRATCHPAD.md,
git history); re-opening one needs a new reason.

- Windows, tabs, splits — the OS window manager owns composition.
- Silent creation from a selector query — creation must be a labelled,
  highlighted choice (`specs/archive/selector-creation.md`); existing selections keep
  their original listed targets. The user's 2026-09-27 clarification permits
  `linger select` to create through the same attach path.
- Storing images across reattach — passthrough plus the application's
  own redraw only (`E2E/Graphics.lean`, README Graphics).
- Restoring the process tree on resume — screen and state yes, programs
  no.
- A shared multi-session server — one daemon per session IS the
  cross-session isolation: there is no shared object to state a theorem
  about, and the caps are per-process.
- Terminfo / capability negotiation — the fixed repertoire is what
  makes the receiver-quantified fidelity theorems statable. Do not
  "fix" the window title with the xterm title stack; it would weaken
  `leave_canonical_all`.
- `attach` switching instead of nesting inside a session — nesting
  works; refuse loudly is the house pattern, never silently switch.
- A pure poll plan / `revents` classifier — killed,
  `specs/archive/runtime-invariants.md`.

## Build

- Always `./lake build` (the wrapper, not bare `lake`), on Linux and
  macOS both; it routes C compilation through Homebrew clang where the
  toolchain's clang cannot run, and is a pass-through on macOS.
- Green before any commit: `./lake build` and
  `./lake build Theorems Tests`; for commits touching the runtime, also
  `./tests/e2e.sh` — run it in the FOREGROUND (a `&` job breaks the
  `^C` assertion; the script probes for this and refuses).
- The toolchain pin is `v4.34.1`. Compiler upgrades must pass the full
  verifier from `./lake clean`, including generated C ABI and standalone
  formatter checks.
- `lean-fmt` installs standalone, never as a Lake `require`; the CI
  workflow pins its source independently of the compiler. Settings and
  history live in `.lean-fmt.toml` and `SCRATCHPAD.md`.

## Gates, hooks and CI

`tests/gates.sh` is the ONLY place a ratchet number lives — never copy
one out (copies rot). Install once per clone:
`git config core.hooksPath .githooks`. The native hook runs
`tests/hygiene.sh`, the gates and installed `actionlint`/`lean-fmt` tools.
CI requires both tools on Linux; no Python hook framework is involved.
Semantic lint can build missing imports; run the required builds first.
CI is two jobs: `gates` runs hygiene, validates the workflow and selects
runners; `e2e` runs the complete verifier, including layout and semantic
lint once after compilation. Branches and PRs can reuse a successful full
verification keyed by all non-record file contents, paths, modes and runner
OS/architecture/image. The lookup has no fallback prefix. On reuse, source
gates still check current records. `tests/ci-inputs.sh` defines the key and
`E2E/Ci.lean` exercises it. Build artifacts remain a separate, content-checked
cache; scheduled, manual and tag runs always verify with clean build and
formatter-result caches.
Live suites run as isolated processes through `E2E.Runner`, with a bounded
concurrency limit and the sole assertion inventory in `tests/e2e.sh`.
Use the default per-process state directories for the full verifier;
`LINGER_TEST_DIR` is reserved for focused single-suite runs.
**macOS is not on the per-push path**: ubuntu runs every
push, macOS on a weekly cron (only when commits landed), a `v*` tag, or
`workflow_dispatch` — reach for that when a commit touches `c/shim.c` or
the `./lake` wrapper. The decision is `tests/ci-runners.sh`, driven by
`E2E/Ci.lean`; the measurement behind it is in SCRATCHPAD and is
deliberately not repeated elsewhere. There is
deliberately no pre-push hook.

## Rules

- `Linger/Core/*` and `Tools/*` are pure: no `IO`,
  no `partial def`, no `sorry`. Effects are data; IO executes them.
- Only `Linger/Posix.lean` and `c/shim.c` reach the OS *raw*: every
  `@[extern]` lives in `Linger/Posix.lean` (gated), and the runtime
  otherwise goes through Lean core's `IO`. Keep the shim logic-free
  (syscall + errno only); its wrapper count is ratcheted (`SHIM_CAP`),
  and every export was re-audited 2026-09-25 as not removable — evidence in
  SCRATCHPAD.md. The full verifier checks the generated Lean ABI against C;
  the source gate inventories post-fork call regions. The shim returns
  `-errno`; never write errno numbers in
  Lean, and never let a pid selector (`0`, a negative `pid_t`) reach a
  signal — `Linger.Posix.checkPid` refuses them, and a gate covers the
  shell.
- Theorems resolve tensions: state the invariant in THEOREMS.md, prove
  it, then code to it. Restructure code for provability rather than
  weakening a theorem: name the stages, clamp bounds locally, prefer
  order-robust proof scripts.
- A theorem or test that cannot fail is worthless: break the code once
  to see it catch, and record the break in SCRATCHPAD.md.
- Every `Linger/Core` or `Tools` `def` lands with a
  theorem type containing that exact fully qualified constant, in the same commit
  (`Theorems/Coverage.lean`).
- A proved pure value consumed by runtime or tool IO needs a grep gate to bite:
  `Linger/Runtime/*` and `Manager/*` use `IO` and no theorem can see a call site —
  re-measured against v4.34's Hoare framework (no `WP IO` instance
  exists; probes in SCRATCHPAD.md). Same for guards no test can observe.
- A `maxHeartbeats` or `maxRecDepth` raise is a measurement and it
  expires: after any refactor, try deleting them (both ratcheted; a new
  raise is a signal to read, not silence).
- A `while`/`for` loop in a `do` block does not need `partial def`, and
  never add a fuel parameter to shed the keyword (ratcheted).
- Session names pass `Linger.Core.Name.sanitize` before touching any
  path.
- Any poll loop must freeze its fd set before polling.
- `Tests/` (Lean unit tests) and `tests/` (orchestrator) are two
  tracked directories; on a case-insensitive filesystem check
  `git ls-files --stage` after adding a file. Pty suites live in `E2E/`
  (`./lake exe e2e <suite>`), are `IO` — never theorems — and assert
  against the code's own definitions, not copies.
- `FAILURES: 0` does not mean anything ran: every pty suite carries
  an exact check count in `tests/e2e.sh`; any addition or deletion is a
  reviewable edit.
- Program logic, proofs and automated test suites are Lean. Optional
  user-editable recipes contain native terminal and SSH configuration
  (`recipes/README.md`).
  `linger` is the sole public executable; `Main` composes session commands,
  terminal selection and foreign-save import.
  `Tools/` holds pure policies and `Manager/` their IO executors, with the same
  theorem census and IO call-site gates. Their import closures stay outside
  the session library and VT toolkit.
  The C shim, build wrapper, configuration hooks and verifier scripts are
  deliberate non-Lean boundaries. No Python, ever.
  `tests/e2e.sh`, `tests/gates.sh` and `tests/ci-runners.sh` stay shell.
  The third one is the CI runner decision: the `gates` job compiles
  nothing (that is what makes it cheap), so its decision cannot be a
  Lean exe — but it lives in a script rather than inline in the YAML so
  `E2E/Ci.lean` can drive the real thing instead of a copy, and a gate
  ties the workflow to calling it.
- The purity greps read prose as well as code: never write the
  compiled-evaluation tactic's name in a docstring under `Theorems/` —
  say "compiled evaluation".
- Do not editorialize about other codebases: never characterize, rank,
  or make factual claims about what another project does. The one
  sanctioned peer mention is README §Design's prior-art list — bare
  names and links, gated. Environment mentions stay: wire formats,
  control sequences, terminfo values, tools a recipe drives — a format
  has to be named to be supported. Borrowing a rule is fine;
  attributing it is the editorial.
- One writer at a time on this tree; give a second writer a worktree,
  and use a FRESH `cp -a` destination (`cp -a` into an existing
  directory nests instead of replacing).

## Scratchpad

`SCRATCHPAD.md` is shared notes. Read before writing; append
`## Step N notes — <ISO date>` after; don't delete prior entries.

## Commits

One commit per spec step: `step N: <summary>`. Don't rewrite pushed
history.
