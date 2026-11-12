#!/bin/sh
# Complete verifier (`./lake test`): build, generated ABI, lint and source gates,
# coverage, verifier regressions, shim smoke tests and live pty suites, each with an
# exact assertion count. Run in the foreground (checked below).
set -e
cd "$(dirname "$0")/.."

verifier_phase=''
finish_phase() {
  [ -n "$verifier_phase" ] || return 0
  verifier_elapsed=$(( $(date +%s) - verifier_started ))
  [ "${GITHUB_ACTIONS-}" != true ] || printf '::endgroup::\n'
  printf '  %s: OK (%ss)\n' "$verifier_phase" "$verifier_elapsed"
  if [ -n "${GITHUB_STEP_SUMMARY-}" ]; then
    printf '| %s | %s s |\n' "$verifier_phase" "$verifier_elapsed" >> "$GITHUB_STEP_SUMMARY"
  fi
}
say() {
  finish_phase
  verifier_phase=$1
  verifier_started=$(date +%s)
  if [ "${GITHUB_ACTIONS-}" = true ]; then
    printf '::group::%s\n' "$1"
  else
    printf '\n=== %s ===\n' "$1"
  fi
}
fail() {
  [ "${GITHUB_ACTIONS-}" != true ] || printf '::endgroup::\n'
  printf 'VERIFY FAIL: %s\n' "$1" >&2
  exit 1
}
if [ -n "${GITHUB_STEP_SUMMARY-}" ]; then
  printf '| Verification phase | Elapsed |\n| --- | ---: |\n' >> "$GITHUB_STEP_SUMMARY"
fi

# --- SIGINT must be deliverable ---------------------------------------------
# A shell without job control starts a `&` job with SIGINT and SIGQUIT disabled,
# and that survives `execve`, so every descendant inherits it: the `suites` binary,
# the daemon, the session shell the daemon spawns on the pty, and the child that
# shell runs. `^C` then generates a signal that kills nothing, and the agent suite's
# `send - carries ^C` assertion fails — while passing standalone every time, which
# is why it reads as a flake. Check inherited signal behavior before any suite runs.
#
# The probe is BEHAVIOURAL, so it holds on both halves of the CI matrix: a fresh
# `sh -c` inherits the state, traps INT and signals itself. Delivered -> the trap
# runs -> 9. Disabled -> the signal never arrives -> 7. The child never dies OF a
# signal, and that is not incidental: a child killed by SIGINT makes some shells
# abandon the enclosing script (measured, ksh), so the obvious probe would
# sometimes kill this script instead of reporting on it.
#
# Reading `SigBlk` from /proc/self/status was the alternative, and it is wrong
# twice. It is Linux-only, and worse, it is INCOMPLETE: measured here, bash 4.2
# implements `&` as `SigIgn 0x6`, NOT `SigBlk 0x6`, so a check reading `SigBlk` alone
# would have passed in the very shell that reproduces the bug. /proc is used only to
# PRINT both masks when the probe fires, where its absence on macOS costs a line of
# diagnosis and not the check.
#
# Any exit but 9 refuses, deliberately: an unexpected probe result is not evidence
# that SIGINT works. And this cannot false-positive, because the probe tests
# exactly the precondition the agent suite already depends on — an environment that
# fails it is an environment where the suite could not have passed anyway. It is NOT
# in scripts/gates.sh: that file also runs from `pre-commit`, where a backgrounded
# commit is nobody's bug.
sigint=0
sh -c 'trap "exit 9" INT; kill -s INT $$; exit 7' > /dev/null 2>&1 || sigint=$?
if [ "$sigint" -ne 9 ]; then
  printf 'SIGINT is blocked or ignored in this process, and every descendant inherits it.\n' >&2
  if [ -r /proc/self/status ]; then                    # Linux only, and diagnosis only
    grep -E '^Sig(Blk|Ign):' /proc/self/status >&2 || true
  fi
  printf 'The agent suite asserts that ^C reaches the session child, so it would fail\n' >&2
  printf 'for a reason that is not linger. Run this script in the FOREGROUND: a job\n' >&2
  printf 'started with & in a shell without job control gets SIGINT and SIGQUIT disabled,\n' >&2
  printf 'and that survives execve. setsid and nohup are fine alone; the & is what does it.\n' >&2
  fail "SIGINT is not deliverable (probe exited $sigint, want 9) — run in the foreground, not with '&'"
fi
# One log directory per run, so concurrent worktrees never share a log. The suites
# write theirs here too; it is removed only after a green run.
logs="$(mktemp -d "${TMPDIR:-/tmp}/linger-verify.XXXXXX")"
export LINGER_LOG_DIR="$logs"

say "1. build (program + theorems + tests + audit)"
# Lake checks source/dependency content and replays cached diagnostics. Rehash
# artifacts too, and fail on warnings even after a local warningAsError override.
# Run `./lake clean` first for clean release/compiler validation. The list holds every
# default target (scripts/gates.sh checks), so a fresh checkout runs the Lean Software Challenge audit
# here, as a local `./lake build` does.
./lake --rehash --wfail build Linger \
    Theorems Tests Suites linger lingertest suites audit > "$logs/build.log" 2>&1 \
  || { tail -30 "$logs/build.log"; fail "build (see $logs/build.log)"; }
# --wfail ignores warnings from elaborating lakefile.lean; this grep sees them.
if grep -qE '^(warning|error)' "$logs/build.log"; then
  grep -E '^(warning|error)' "$logs/build.log"
  fail "build is not warning-clean"
fi
# Shake reads the oleans just built. The proof library has no root module, so the proof
# modules are named one by one. Tests stay out: shake cannot see `example` or
# `#guard` uses. Linger.Os.Suites.Shim and Verify.Main stay out to bound the cost.
shake_modules="$(git ls-files 'Theorems/*.lean' 'Linger/*/Proofs/*.lean' | sed 's/[.]lean$//; s#/#.#g')"
# shellcheck disable=SC2086  # one module name per word
./lake shake --keep-implied Linger Main $shake_modules > "$logs/shake.log" 2>&1 \
  && [ ! -s "$logs/shake.log" ] \
  || { cat "$logs/shake.log"; fail "lake shake suggests import changes"; }
# The generated C of the program's modules, linger's and each package's, named from the
# tracked sources: a module that moved leaves its old C file in .lake, which must not answer
# for it. A component's or package's Proofs, Tests, Suites and Solution are not program code,
# nor is a package's challenge or audit.
program_c="$(
  git ls-files 'Main.lean' 'Linger.lean' 'Linger/*.lean' \
    | awk -F/ 'NF <= 3 || (NF == 4 && $3 == "Shell")' \
    | sed 's#^#.lake/build/ir/#; s#[.]lean$#.c#'
  git ls-files 'packages/*.lean' | awk -F/ '
    { root = toupper(substr($2, 1, 1)) substr($2, 2); rel = substr($0, length($1 "/" $2 "/") + 1)
      n = split(rel, part, "/")
      if (rel == root ".lean" || (n == 2 && part[1] == root && part[2] !~ /^(Proofs|Tests|Solution)[.]lean$/) \
          || (n == 3 && part[1] == root && part[2] == "Shell")) {
        sub(/[.]lean$/, ".c", rel); print $1 "/" $2 "/.lake/build/ir/" rel } }')"
[ -n "$program_c" ] || fail "no generated C named for the program's modules"
# The initializer of a module that uses the Lean package calls lean_initialize
# instead of lean_initialize_runtime_module, which starts the whole Lean frontend in
# every linger process; none may. grep exits 1 only when it read every file and
# found no such call.
lean_init=0
# shellcheck disable=SC2086  # one path per word
grep -l '^lean_initialize();$' $program_c || lean_init=$?
[ "$lean_init" -ne 0 ] \
  || fail "a program module uses the Lean package; every process would initialize the whole Lean frontend"
[ "$lean_init" -eq 1 ] || fail "could not read the generated C of every program module"

say "1b. generated Lean / C shim ABI"
# Compile declarations emitted by THIS pinned Lean together with the shim.
# Source-looking FFI types are insufficient: Int32 is emitted as uint32_t bits,
# and this toolchain erases IO's world argument. Compare all three symbol sets
# so an empty extraction or an unused/missing export cannot pass.
abi_dir="$(mktemp -d "${TMPDIR:-/tmp}/linger-abi.XXXXXX")"
trap 'rm -r "$abi_dir"' EXIT HUP TERM
awk '/^lean_object\* linger_[[:alnum:]_]+\([^;]*\);$/ {
  sub(/\(\);$/, "(void);"); print; count++
} END { if (!count) exit 1 }' packages/os/.lake/build/ir/Os/Boundary.c > "$abi_dir/prototypes" \
  || fail "no generated shim prototypes"
sed 's/^lean_object\* //; s/(.*//' "$abi_dir/prototypes" | sort > "$abi_dir/generated"
sed -n 's/^LEAN_EXPORT lean_obj_res \(linger_[[:alnum:]_]*\)(.*/\1/p' packages/os/c/shim.c \
  | sort > "$abi_dir/exports"
sed -n 's/^@\[extern "\(linger_[[:alnum:]_]*\)"\].*/\1/p' packages/os/Os/Boundary.lean \
  | sort > "$abi_dir/externs"
cmp -s "$abi_dir/generated" "$abi_dir/exports" \
  || fail "generated ABI and C export inventories differ"
cmp -s "$abi_dir/generated" "$abi_dir/externs" \
  || fail "generated ABI and Lean extern inventories differ"
{
  printf '%s\n' '#define _GNU_SOURCE' '#include <lean/lean.h>'
  cat "$abi_dir/prototypes"
  printf '%s\n' '#include "shim.c"'
} > "$abi_dir/check.c"
# Resolve the compiler before `lake env` prepends its bundled one.
abi_cc="$(command -v clang)" || fail "clang missing for ABI check"
abi_prefix="$(./lake env lean --print-prefix)"
"$abi_cc" -fsyntax-only -Wall -Werror -Wstrict-prototypes \
  -isystem "$abi_prefix/include" -I "$PWD/packages/os/c" "$abi_dir/check.c" \
  || fail "C shim conflicts with the generated Lean ABI"
rm -r "$abi_dir"
trap - EXIT HUP TERM
# A lost `@[csimp]` leaves every caller on the specification and passes every proof, so
# check the generated C: each fast twin is still called, outside its own boxed wrapper.
# Private mangling keeps the suffix, so the module-local feedMsgsTR is matched too. A symbol
# is `lp_<package>_<name>`, whichever package compiled it.
for twin in Linger_Session_feedMsgsTR Terminal_Vt_Row_mendFast Terminal_Render_rowAnsiLinear; do
  # shellcheck disable=SC2086  # one path per word
  awk -v twin="$twin" '
    /^(LEAN_EXPORT|static) .*[)][{]$/ { fn = $0 }
    $0 ~ ("= lp_[[:alnum:]]+_[[:alnum:]_]*" twin "[(]") && fn !~ (twin "___boxed[(]") { n++ }
    END { exit !n }' $program_c \
    || fail "compiled code no longer calls $twin: its @[csimp] replacement is gone"
done

say "2. hygiene, source gates, formatting and semantic lint"
# Semantic lint needs compiled imports. Use the same checks as pre-commit.
./lake lint || fail "lint"
# Every public declaration under Linger/ has a docstring, however lakefile.lean
# assigns options: elaborate each module with the linter on and warnings fatal. The Theorems
# and Tests globs already build every module under a component's Proofs/ and Tests/ with that
# linter on (gates.sh pins both), so those are not elaborated twice.
git ls-files -z 'Linger/*.lean' ':!Linger/*/Proofs/*' ':!Linger/*/Tests/*' \
  | xargs -0 -n 1 -P 16 ./lake env lean -DwarningAsError=true -Dlinter.missingDocs=true \
    > "$logs/docs.log" 2>&1 \
  || { grep 'missing doc' "$logs/docs.log" | head -20; fail "a public declaration under Linger/ has no docstring"; }

say "2b. semantic coverage of pure code + runtime emitter classification"
# Verify.Coverage calls the shared exact-constant theorem census, then classifies
# resolved references from the program just built above. Invoke Lean directly
# so source-only changes cannot reuse a cached census.
./lake env lean Verify/Coverage.lean > "$logs/coverage.log" 2>&1 \
  || { cat "$logs/coverage.log"; fail "semantic coverage and emitter classification"; }
grep '^pure semantic coverage:' "$logs/coverage.log" || true
tail -1 "$logs/coverage.log" | grep -q '^FAILURES: 0$' || fail "coverage gate"
printf '  coverage and emitter checks: OK (details: %s/coverage.log)\n' "$logs"

say "2c. verifier regression tests (CI policy, caches and suite isolation)"
# Verify.Ci runs the real runner-selection script, including its `git log --since`
# against throwaway repositories with real commit dates, and the pinned Lake
# against a temporary project.
# The same runner checks exit status, final verdict, every assertion and both
# streams. Intentional failures inside these tests stay in their captured logs.
./.lake/build/bin/suites --suites ci:59 hygiene:56 \
  || fail "verifier regression checks (see $logs/linger-ci.out and linger-hygiene.out)"

say "2d. headline theorems (Challenge.lean against Theorems/Solution.lean)"
# `lake comparator` builds both modules, exports them and replays the claims' proofs through
# the kernel in a separate process; it accepts only when every statement matches and no axiom
# outside comparator.json's list is used. Its bwrap sandbox protects a judge from code the
# judge did not write. This verifier builds and runs this code anyway, so the sandbox would
# add nothing here, and running without it keeps the check the same on macOS.
./lake comparator --inadvisably-no-sandbox > "$logs/comparator.log" 2>&1 \
  || { grep -v '^Exporting' "$logs/comparator.log" | tail -20; fail "lake comparator rejected the headline theorems (see $logs/comparator.log)"; }
[ "$(tail -1 "$logs/comparator.log")" = 'Your solution is okay!' ] \
  || fail "lake comparator did not accept the headline theorems (see $logs/comparator.log)"
# The Challenge library silences only `sorry`, whose every use scripts/gates.sh checks in the
# source, so building it warns about nothing.
if grep '^warning' "$logs/comparator.log"; then
  fail "Challenge.lean has warnings (see $logs/comparator.log)"
fi

say "2e. packages (each package's build, audit and headline theorems, on its own)"
# Each package under packages/ is a Lake package with its own challenge and audit, which linger
# trusts: build it alone, with its unit tests and audit, and check that its solution proves its
# challenge. It shares this checkout's packages (`packagesDir`), so this fetches nothing.
for pkg in packages/*/; do
  pkg="${pkg%/}"
  name="$(basename "$pkg")"
  (cd "$pkg" && ../../lake --rehash --wfail build) > "$logs/$name-build.log" 2>&1 \
    || { tail -30 "$logs/$name-build.log"; fail "$pkg does not build (see $logs/$name-build.log)"; }
  if grep -qE '^(warning|error)' "$logs/$name-build.log"; then
    grep -E '^(warning|error)' "$logs/$name-build.log"
    fail "$pkg is not warning-clean"
  fi
  (cd "$pkg" && ../../lake comparator --inadvisably-no-sandbox) > "$logs/$name-comparator.log" 2>&1 \
    || { grep -v '^Exporting' "$logs/$name-comparator.log" | tail -20; fail "lake comparator rejected $pkg's headline theorems"; }
  [ "$(tail -1 "$logs/$name-comparator.log")" = 'Your solution is okay!' ] \
    || fail "lake comparator did not accept $pkg's headline theorems (see $logs/$name-comparator.log)"
  printf '  %s: build, audit and headline theorems OK\n' "$pkg"
done

say "3. posix shim smoke tests"
shim_out="$logs/shim.out"
./.lake/build/bin/lingertest > "$shim_out" 2>&1 \
  || { tail -25 "$shim_out"; fail "lingertest"; }
tail -1 "$shim_out" | grep -q '^ALL PASS$' || fail "lingertest"
shim_n="$(grep -c '^PASS ' "$shim_out")"
[ "$shim_n" -eq 69 ] \
  || fail "lingertest ran $shim_n checks (expected exactly 69)"

# Keep one real session in another state directory through every suite. A suite
# may clean up its own Env, never the user's process namespace. State directories hold
# Unix sockets, whose paths must fit sun_path (packages/os/c/shim.c rejects longer ones), so they stay
# under socket_root whatever TMPDIR is, as the suites' directories stay under
# Verify.Harness.socketRoot, whose docstring records the measured path lengths. Only logs
# and scratch files follow `${TMPDIR:-/tmp}`.
socket_root=/tmp
sentinel_dir="$socket_root/linger-verify-sentinel-$$"
sentinel_name="sentinel-$$"
cleanup_sentinel() {
  LINGER_DIR="$sentinel_dir" ./.lake/build/bin/linger kill "$sentinel_name" >/dev/null 2>&1 || true
  [ ! -e "$sentinel_dir" ] || rm -r "$sentinel_dir"
}
trap cleanup_sentinel EXIT HUP TERM
LINGER_DIR="$sentinel_dir" ./.lake/build/bin/linger start "$sentinel_name" sleep 600
LINGER_DIR="$sentinel_dir" ./.lake/build/bin/linger info "$sentinel_name" >/dev/null \
  || fail "sentinel session did not start"

say "4. live suites (separate processes, at most four at once)"
# One assertion inventory, consumed by the tested Lean runner, longer suites first.
# Each child keeps $logs/linger-<suite>.out; zero exit, final verdict and exact count
# must all agree, and no explicit FAIL line is accepted. A check that reads /proc says SKIP
# where there is none, as on macOS, and `<suite>:<checks>:<skips>` pins how many of a
# suite's checks skip. A verdict here depends on the code, not on how fast the host is;
# what the largest workloads cost is the opt-in `./.lake/build/bin/suites perf [strict]`.
# Ordinary child spawning preserves SIGINT, unlike a shell's asynchronous list.
# No suite shares an Env directory, and the runner waits for all of them on failure.
if [ -d /proc/self ]; then
  resume_skips=0 robust_skips=0 title_skips=0 quiet_skips=0
else
  resume_skips=1 robust_skips=2 title_skips=1 quiet_skips=4
fi
# shellcheck disable=SC2086  # each skip count is a number
./.lake/build/bin/suites --suites \
  manager:128 delivery:37 attach:64 agent:63 \
  resume:29:$resume_skips watch:50 title:18:$title_skips graphics:9 robust:33:$robust_skips \
  interop:72 recipes:56 status:18 terminal:12 overview:15 remote:68 identity:25 \
  quiet:5:$quiet_skips \
  || fail "live suites (see $logs/linger-*.out)"

LINGER_DIR="$sentinel_dir" ./.lake/build/bin/linger info "$sentinel_name" >/dev/null \
  || fail "a suite terminated the unrelated sentinel session"
cleanup_sentinel
trap - EXIT HUP TERM
finish_phase
rm -r "$logs"
printf '\nVERIFY OK\n'
