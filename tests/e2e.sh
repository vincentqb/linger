#!/bin/sh
# Whole-deliverable check (specs/lean-zmx.md Step 10). Exits 0 only if
# everything below holds. Run from the repo root: ./tests/e2e.sh
#
#   1. clean build of program + proofs + unit tests, zero warnings
#   2. no `sorry` / `partial` in the pure core or the proofs
#   3. posix shim smoke tests (ztest)
#   4. attach/detach/reattach/mirror/wait e2e (real ptys)
#   5. reboot-resume e2e (SIGKILL + restore + corrupt tolerance)
#   6. session-manager TUI e2e (drive the picker in a pty)
#   7. remote-over-ssh e2e (fake ssh: list, preview, attach argv)
#   8. adverse timing: busy-daemon listing (§Row) + name-ownership race
set -e
cd "$(dirname "$0")/.."

say() { printf '\n=== %s ===\n' "$1"; }
fail() { printf 'E2E FAIL: %s\n' "$1" >&2; exit 1; }

# no stray daemons from a previous run may influence the checks
pkill -x lzmx 2>/dev/null || true
sleep 0.2

say "1. build (program + theorems + tests)"
rm -rf .lake/build
./lake build Zmx Theorems Tests lzmx ztest > /tmp/lzmx-build.log 2>&1 \
  || { tail -30 /tmp/lzmx-build.log; fail "build"; }
if grep -qE '^(warning|error)' /tmp/lzmx-build.log; then
  grep -E '^(warning|error)' /tmp/lzmx-build.log
  fail "build is not warning-clean"
fi
grep -c 'Build completed successfully' /tmp/lzmx-build.log > /dev/null \
  || fail "build did not report success"

say "2. purity of the core (no sorry, no partial, no IO)"
! git grep -n 'sorry' -- 'Zmx/Core/*' 'Theorems/*' || fail "sorry found"
! git grep -n 'sorryAx' -- 'Zmx/Core/*' 'Theorems/*' || fail "sorryAx found"
! git grep -nE '\bpartial def\b' -- 'Zmx/Core/*' || fail "partial def in pure core"
! git grep -nE ': *IO ' -- 'Zmx/Core/*' || fail "IO in pure core"
# the OS surface stays where AGENTS.md says it is
[ "$(git grep -l '@\[extern' -- 'Zmx/*' | tr -d ' ')" = "Zmx/Posix.lean" ] \
  || fail "extern declarations outside Zmx/Posix.lean"
[ "$(ls c/ | tr -d ' \n')" = "shim.c" ] || fail "more than one C file"

say "3. posix shim smoke tests"
./lake exe ztest | tail -1 | grep -q '^ALL PASS$' || fail "ztest"

say "4. attach / detach / reattach / mirror / wait"
pkill -x lzmx 2>/dev/null || true; sleep 0.2
python3 tests/attach_test.py | tail -1 | grep -q '^FAILURES: 0$' || fail "attach_test"

say "5. reboot resume"
pkill -x lzmx 2>/dev/null || true; sleep 0.2
python3 tests/resume_test.py | tail -1 | grep -q '^FAILURES: 0$' || fail "resume_test"

say "6. session-manager TUI"
pkill -x lzmx 2>/dev/null || true; sleep 0.2
python3 tests/tui_test.py | tail -1 | grep -q '^FAILURES: 0$' || fail "tui_test"

say "7. remote sessions over ssh"
pkill -x lzmx 2>/dev/null || true; sleep 0.2
python3 tests/remote_test.py | tail -1 | grep -q '^FAILURES: 0$' || fail "remote_test"

say "8. adverse timing (busy daemon listing, name-ownership race)"
pkill -x lzmx 2>/dev/null || true; sleep 0.2
python3 tests/robust_test.py | tail -1 | grep -q '^FAILURES: 0$' || fail "robust_test"

pkill -x lzmx 2>/dev/null || true
printf '\nE2E OK — lzmx builds clean, core is pure, 5 live suites green.\n'
