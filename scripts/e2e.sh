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
  printf 'E2E FAIL: %s\n' "$1" >&2
  exit 1
}
if [ -n "${GITHUB_STEP_SUMMARY-}" ]; then
  printf '| Verification phase | Elapsed |\n| --- | ---: |\n' >> "$GITHUB_STEP_SUMMARY"
fi

# --- SIGINT must be deliverable ---------------------------------------------
# A shell without job control starts a `&` job with SIGINT and SIGQUIT disabled,
# and that survives `execve`, so every descendant inherits it: the `e2e` binary,
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
logs="$(mktemp -d /tmp/linger-verify.XXXXXX)"
export LINGER_LOG_DIR="$logs"

say "1. build (program + theorems + tests)"
# Lake checks source/dependency content and replays cached diagnostics. Rehash
# artifacts too, and fail on warnings even after a local warningAsError override.
# Run `./lake clean` first for clean release/compiler validation.
./lake --rehash --wfail build Linger LingerVt LingerVtTheorems LingerInput LingerInputTheorems \
    LingerFuzzy Theorems Tests linger lingertest e2e > "$logs/build.log" 2>&1 \
  || { tail -30 "$logs/build.log"; fail "build (see $logs/build.log)"; }
# --wfail ignores warnings from elaborating lakefile.lean; this grep sees them.
if grep -qE '^(warning|error)' "$logs/build.log"; then
  grep -E '^(warning|error)' "$logs/build.log"
  fail "build is not warning-clean"
fi
# Shake reads the oleans just built. Theorems.lean is not a `module`, so the proof
# modules are named one by one. Tests stay out: shake cannot see `example` or
# `#guard` uses. LingerTest and E2ETest stay out to bound the cost.
shake_modules="$(git ls-files 'Theorems/*.lean' | sed 's/[.]lean$//; s#/#.#g')"
# shellcheck disable=SC2086  # one module name per word
./lake shake --keep-implied Linger Main $shake_modules > "$logs/shake.log" 2>&1 \
  && [ ! -s "$logs/shake.log" ] \
  || { cat "$logs/shake.log"; fail "lake shake suggests import changes"; }

say "1b. generated Lean / C shim ABI"
# Compile declarations emitted by THIS pinned Lean together with the shim.
# Source-looking FFI types are insufficient: Int32 is emitted as uint32_t bits,
# and this toolchain erases IO's world argument. Compare all three symbol sets
# so an empty extraction or an unused/missing export cannot pass.
abi_dir="$(mktemp -d /tmp/linger-abi.XXXXXX)"
trap 'rm -r "$abi_dir"' EXIT HUP TERM
awk '/^lean_object\* linger_[[:alnum:]_]+\([^;]*\);$/ {
  sub(/\(\);$/, "(void);"); print; count++
} END { if (!count) exit 1 }' .lake/build/ir/Linger/Posix.c > "$abi_dir/prototypes" \
  || fail "no generated shim prototypes"
sed 's/^lean_object\* //; s/(.*//' "$abi_dir/prototypes" | sort > "$abi_dir/generated"
sed -n 's/^LEAN_EXPORT lean_obj_res \(linger_[[:alnum:]_]*\)(.*/\1/p' c/shim.c \
  | sort > "$abi_dir/exports"
sed -n 's/^@\[extern "\(linger_[[:alnum:]_]*\)"\].*/\1/p' Linger/Posix.lean \
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
  -isystem "$abi_prefix/include" -I "$PWD/c" "$abi_dir/check.c" \
  || fail "C shim conflicts with the generated Lean ABI"
rm -r "$abi_dir"
trap - EXIT HUP TERM

say "2. hygiene, source gates, formatting and semantic lint"
# Semantic lint needs compiled imports. Use the same checks as pre-commit.
./lake lint || fail "lint"

say "2b. semantic coverage of pure code + runtime emitter classification"
# E2E.Coverage calls the shared exact-constant theorem census, then classifies
# resolved references from the program just built above. Invoke Lean directly
# so source-only changes cannot reuse a cached census.
./lake env lean E2E/Coverage.lean > "$logs/coverage.log" 2>&1 \
  || { cat "$logs/coverage.log"; fail "semantic coverage and emitter classification"; }
grep '^pure semantic coverage:' "$logs/coverage.log" || true
tail -1 "$logs/coverage.log" | grep -q '^FAILURES: 0$' || fail "coverage gate"
printf '  coverage and emitter checks: OK (details: %s/coverage.log)\n' "$logs"

say "2c. verifier regression tests (CI policy, caches and suite isolation)"
# E2E.Ci runs the real runner-selection script, including its `git log --since`
# against throwaway repositories with real commit dates, and the pinned Lake
# against a temporary project.
# The same runner checks exit status, final verdict, every assertion and both
# streams. Intentional failures inside these tests stay in their captured logs.
./.lake/build/bin/e2e --suites ci:52 hygiene:56 \
  || fail "verifier regression checks (see $logs/linger-ci.out and linger-hygiene.out)"

say "3. posix shim smoke tests"
shim_out="$logs/shim.out"
./.lake/build/bin/lingertest > "$shim_out" 2>&1 \
  || { tail -25 "$shim_out"; fail "lingertest"; }
tail -1 "$shim_out" | grep -q '^ALL PASS$' || fail "lingertest"
shim_n="$(grep -c '^PASS ' "$shim_out")"
[ "$shim_n" -eq 61 ] \
  || fail "lingertest ran $shim_n checks (expected exactly 61)"

# Keep one real session in another state directory through every suite. A suite
# may clean up its own Env, never the user's process namespace.
sentinel_dir="/tmp/linger-e2e-sentinel-$$"
sentinel_name="sentinel-$$"
cleanup_sentinel() {
  LINGER_DIR="$sentinel_dir" ./.lake/build/bin/linger kill "$sentinel_name" >/dev/null 2>&1 || true
  [ ! -e "$sentinel_dir" ] || rm -r "$sentinel_dir"
}
trap cleanup_sentinel EXIT HUP TERM
LINGER_DIR="$sentinel_dir" ./.lake/build/bin/linger run "$sentinel_name" sleep 600
LINGER_DIR="$sentinel_dir" ./.lake/build/bin/linger info "$sentinel_name" >/dev/null \
  || fail "sentinel session did not start"

say "4. live suites (separate processes, at most four at once)"
# One assertion inventory, consumed by the tested Lean runner, longer suites first.
# Each child keeps $logs/linger-<suite>.out; zero exit, final verdict and exact count
# must all agree, and no explicit FAIL line is accepted.
# Ordinary child spawning preserves SIGINT, unlike a shell's asynchronous list.
# No suite shares an Env directory, and the runner waits for all of them on failure.
./.lake/build/bin/e2e --suites \
  manager:123 delivery:37 attach:50 agent:48 \
  resume:18 watch:40 title:19 graphics:9 robust:29 \
  interop:61 recipes:58 status:17 terminal:12 overview:15 remote:67 identity:25 \
  || fail "live suites (see $logs/linger-*.out)"

LINGER_DIR="$sentinel_dir" ./.lake/build/bin/linger info "$sentinel_name" >/dev/null \
  || fail "a suite terminated the unrelated sentinel session"
cleanup_sentinel
trap - EXIT HUP TERM
finish_phase
rm -r "$logs"
printf '\nE2E OK\n'
