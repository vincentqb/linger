#!/bin/sh
# Whole-deliverable check (specs/lean-zmx.md Step 10). Exits 0 only if
# everything below holds. Run from the repo root: ./tests/e2e.sh
#
#   1. clean build of program + proofs + unit tests, zero warnings
#   2. no `sorry` / `partial` in the pure core or the proofs
#  2b. unclaimed pure-core surface: defs named by no theorem (ratchet)
#   3. posix shim smoke tests (ztest)
#   4. attach/detach/reattach/mirror/wait e2e (real ptys)
#   5. reboot-resume e2e (SIGKILL + restore + corrupt tolerance)
#   6. overview e2e (bare `linger`/`ls` print a list and exit, not a picker)
#   7. remote-over-ssh e2e (fake ssh: `-r` listing, attach name@host argv)
#   8. adverse timing: busy-daemon listing (§Row) + name-ownership race
#   9. graphics passthrough (kitty APC / sixel DCS reach the client raw)
#  10. terminal ownership (query progress with zero/one/two clients + stable env)
#  11. status column: attach marks seen, output while away marks unread
#  (1) also covers Tests/Fuzz.lean: randomized §Replay round-trip search
set -e
cd "$(dirname "$0")/.."

say() { printf '\n=== %s ===\n' "$1"; }
fail() { printf 'E2E FAIL: %s\n' "$1" >&2; exit 1; }

# no stray daemons from a previous run may influence the checks
pkill -x linger 2>/dev/null || true
sleep 0.2

say "1. build (program + theorems + tests)"
rm -rf .lake/build
./lake build Zmx Theorems Tests linger ztest > /tmp/linger-build.log 2>&1 \
  || { tail -30 /tmp/linger-build.log; fail "build"; }
if grep -qE '^(warning|error)' /tmp/linger-build.log; then
  grep -E '^(warning|error)' /tmp/linger-build.log
  fail "build is not warning-clean"
fi
grep -c 'Build completed successfully' /tmp/linger-build.log > /dev/null \
  || fail "build did not report success"

say "2. purity of the core (no sorry, no partial, no IO)"
! git grep -n 'sorry' -- 'Zmx/Core/*' 'Theorems/*' || fail "sorry found"
! git grep -n 'sorryAx' -- 'Zmx/Core/*' 'Theorems/*' || fail "sorryAx found"
! git grep -nE '\bpartial def\b' -- 'Zmx/Core/*' || fail "partial def in pure core"
! git grep -nE ': *IO ' -- 'Zmx/Core/*' || fail "IO in pure core"
# Proofs must reduce in the kernel, never by compiled evaluation: a
# `native_decide` in Theorems/ would trust the compiler + `Decidable`
# instance instead of the kernel, and (unlike the tests, where evaluating
# golden bytes is the point) that is a hole in a *proof*. THEOREMS.md's
# "Reading a row" makes this a promise; this makes it enforced.
! git grep -nE '\bnative_decide\b' -- 'Theorems/*' || fail "native_decide in a proof (Theorems/)"
# the OS surface stays where AGENTS.md says it is
[ "$(git grep -l '@\[extern' -- 'Zmx/*' | tr -d ' ')" = "Zmx/Posix.lean" ] \
  || fail "extern declarations outside Zmx/Posix.lean"
[ "$(ls c/ | tr -d ' \n')" = "shim.c" ] || fail "more than one C file"
# README promises "no external Lean dependencies"; make it fail-closed rather
# than rest on inspection (README-promise coverage audit, the unbacked-promise
# class). A `require` in the lakefile would pull in a package.
! grep -qE '^[[:space:]]*require ' lakefile.lean || fail "external Lean dependency in lakefile.lean (README promises none)"
[ "$(tr -d ' \n' < lake-manifest.json | grep -o '\"packages\":\[[^]]*\]')" = '"packages":[]' ] \
  || fail "lake-manifest has packages (README promises no external Lean deps)"
# shim-size ratchet: the C trust boundary must not grow silently. This
# number only ever goes DOWN without discussion; raising it is a
# deliberate, reviewable act — the checkpoint for "does this genuinely
# need a syscall wrapper, or does Lean core already have it?" (see the
# C-vs-Rust and shrink-the-shim notes in SCRATCHPAD.md).
SHIM_CAP=27
shim_n="$(grep -c LEAN_EXPORT c/shim.c)"
[ "$shim_n" -le "$SHIM_CAP" ] \
  || fail "shim grew to $shim_n wrappers (cap $SHIM_CAP); justify the new syscall and bump the cap"

say "2b. unclaimed pure-core surface (ratchet)"
# Every bug this project found by PROVING was an assumption nobody wrote
# down, so a definition with no theorem naming it at all is the shape to
# watch. This is a ratchet, not a target: it may only go down. Lowering the
# cap when a claim lands is the point; raising it is a deliberate edit that
# says "new surface, no claim yet".
CLAIM_CAP=10
unclaimed=0
unclaimed_list=""
for name in $(grep -h '^\(private \)*def ' Zmx/Core/*.lean \
                | sed 's/^\(private \)*def \([A-Za-z0-9_.]*\).*/\2/' \
                | sed 's/.*\.//' | sort -u); do
  if ! grep -qw -- "$name" Theorems/*.lean; then
    unclaimed=$((unclaimed + 1))
    unclaimed_list="$unclaimed_list $name"
  fi
done
printf 'unclaimed core defs: %s (cap %s)\n' "$unclaimed" "$CLAIM_CAP"
printf '  %s\n' "$unclaimed_list"
[ "$unclaimed" -le "$CLAIM_CAP" ] || fail "unclaimed core surface grew past $CLAIM_CAP"

say "2c. fuzz corpus: no held-out mutations, failure lists asserted empty"
# The §Replay fuzzer is only a guarantee if nothing is excluded and the
# empty-failure assertions are not quietly shrunk. The Tests build already
# proves `failing/failingDeep = []` (the examples fail to compile otherwise);
# these greps stop the *assertions themselves* from being weakened or the
# exclusion list from regrowing — asserted here rather than trusted to a reader.
grep -qE 'def knownGap : Array String := #\[\]' Tests/Fuzz.lean \
  || fail "fuzz: knownGap exclusion list is not empty (a mutation is held out)"
grep -qE 'example : failing 400 = \[\]' Tests/Fuzz.lean \
  || fail "fuzz: 'failing 400 = []' assertion missing or weakened"
grep -qE 'example : failingDeep 150 = \[\]' Tests/Fuzz.lean \
  || fail "fuzz: 'failingDeep 150 = []' assertion missing or weakened"

say "3. posix shim smoke tests"
./lake exe ztest | tail -1 | grep -q '^ALL PASS$' || fail "ztest"

say "4. attach / detach / reattach / mirror / wait"
pkill -x linger 2>/dev/null || true; sleep 0.2
python3 tests/attach_test.py | tail -1 | grep -q '^FAILURES: 0$' || fail "attach_test"

say "5. reboot resume"
pkill -x linger 2>/dev/null || true; sleep 0.2
python3 tests/resume_test.py | tail -1 | grep -q '^FAILURES: 0$' || fail "resume_test"

say "6. overview listing (bare linger / ls)"
pkill -x linger 2>/dev/null || true; sleep 0.2
python3 tests/overview_test.py | tail -1 | grep -q '^FAILURES: 0$' || fail "overview_test"

say "7. remote sessions over ssh"
pkill -x linger 2>/dev/null || true; sleep 0.2
python3 tests/remote_test.py | tail -1 | grep -q '^FAILURES: 0$' || fail "remote_test"

say "8. adverse timing (busy daemon listing, name-ownership race)"
pkill -x linger 2>/dev/null || true; sleep 0.2
python3 tests/robust_test.py | tail -1 | grep -q '^FAILURES: 0$' || fail "robust_test"

say "9. graphics passthrough (kitty / sixel)"
pkill -x linger 2>/dev/null || true; sleep 0.2
python3 tests/graphics_test.py | tail -1 | grep -q '^FAILURES: 0$' || fail "graphics_test"

say "10. terminal ownership (queries + stable child profile)"
pkill -x linger 2>/dev/null || true; sleep 0.2
python3 tests/terminal_query_test.py | tail -1 | grep -q '^FAILURES: 0$' || fail "terminal_query_test"

say "11. status column (unread / seen transitions)"
pkill -x linger 2>/dev/null || true; sleep 0.2
python3 tests/status_test.py | tail -1 | grep -q '^FAILURES: 0$' || fail "status_test"

pkill -x linger 2>/dev/null || true
printf '\nE2E OK — linger builds clean, core is pure, 8 live suites green.\n'
