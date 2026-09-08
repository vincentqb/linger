#!/bin/sh
# Whole-deliverable check (specs/lean-zmx.md Step 10). Exits 0 only if
# everything below holds. Run from the repo root: ./tests/e2e.sh
#
#   1. clean build of program + proofs + unit tests, zero warnings
#   2. no `sorry` / `partial` in the pure core or the proofs
#  2b. coverage: defs named by no theorem STATEMENT (ratchet), and every byte
#      stream the runtime emits classified as proved or bounded
#   3. posix shim smoke tests (lingertest)
#   4. attach/detach/reattach/mirror/wait e2e (real ptys)
#   5. reboot-resume e2e (SIGKILL + restore + corrupt tolerance)
#   6. overview e2e (bare `linger`/`ls` print a list and exit, not a picker)
#   7. remote-over-ssh e2e (fake ssh: `-r` listing, attach name@host argv)
#   8. adverse timing: busy-daemon listing (§Row) + name-ownership race
#   9. graphics passthrough (kitty APC / sixel DCS reach the client raw)
#  10. terminal ownership (query progress with zero/one/two clients + stable env)
#  11. status column: attach marks seen, output while away marks unread
#  12. agent verbs (info geometry/outseq, capture, send - , resize)
#  13. watch: the read-only mirror (geometry, keyboard, hand-back, marks seen)
#  (1) also covers Tests/Fuzz.lean: randomized §Replay round-trip search
#  every pty suite also carries a CHECK-COUNT FLOOR (see `suite` below): green
#  means "no failures AND at least N assertions actually ran".
set -e
cd "$(dirname "$0")/.."

say() { printf '\n=== %s ===\n' "$1"; }
fail() { printf 'E2E FAIL: %s\n' "$1" >&2; exit 1; }

# Run one pty suite: no failures AND a floor on how many checks actually ran
# (pin-the-gaps item 7). `FAILURES: 0` says nothing went wrong; it does not say
# anything HAPPENED. Several suites nest assertions in a `for` over a list, and a
# list that silently became empty still prints `FAILURES: 0` — so the gate would
# stay green on a suite that had stopped checking. The floors are the measured
# live counts; they only ever go UP without discussion, and a drop is a
# deliberate, reviewable edit, exactly like SHIM_CAP below.
suite() {                                   # suite <name> <check floor>
  pkill -x linger 2>/dev/null || true
  sleep 0.2
  out="/tmp/linger-$1.out"
  ./.lake/build/bin/e2e "$1" > "$out" 2>&1 \
    || { tail -25 "$out"; fail "$1 suite"; }
  tail -1 "$out" | grep -q '^FAILURES: 0$' \
    || { tail -25 "$out"; fail "$1 suite"; }
  # `^(PASS|FAIL) ` with the space: `FAILURES: 0` also starts with FAIL.
  n="$(grep -cE '^(PASS|FAIL) ' "$out")"
  [ "$n" -ge "$2" ] \
    || fail "$1 suite ran $n checks (floor $2) — an assertion stopped executing; a loop's list probably went empty"
  printf '  %s: %s checks (floor %s)\n' "$1" "$n" "$2"
}

# no stray daemons from a previous run may influence the checks
pkill -x linger 2>/dev/null || true
sleep 0.2

say "1. build (program + theorems + tests)"
rm -rf .lake/build
./lake build Linger Theorems Tests linger lingertest e2e > /tmp/linger-build.log 2>&1 \
  || { tail -30 /tmp/linger-build.log; fail "build"; }
if grep -qE '^(warning|error)' /tmp/linger-build.log; then
  grep -E '^(warning|error)' /tmp/linger-build.log
  fail "build is not warning-clean"
fi
grep -c 'Build completed successfully' /tmp/linger-build.log > /dev/null \
  || fail "build did not report success"

say "2. source-tree gates (purity, the OS surface, five ratchets)"
# Extracted to tests/gates.sh so `.githooks/pre-commit` runs the SAME numbers.
# A hook with its own copy of a cap is worse than no hook.
sh tests/gates.sh || fail "source-tree gates"

say "2b. coverage of the code by the theorems (two ratchets)"
# Every bug this project found by PROVING was an assumption nobody wrote down, so
# the shape to watch is a definition no theorem says anything about. This used to
# be a grep over all of Theorems/, which could not tell a claim from a word:
# `Render.history` — a stream the binary writes to the user's terminal — passed it
# because "history" occurs in a doc comment. `E2E/Coverage.lean` measures theorem
# *statements* with comments stripped, and separately requires every byte stream
# the runtime emits to be classified as proved or bounded. See its header.
./.lake/build/bin/e2e coverage | tee /tmp/linger-coverage.log
tail -1 /tmp/linger-coverage.log | grep -q '^FAILURES: 0$' || fail "coverage gate"

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
./lake exe lingertest | tail -1 | grep -q '^ALL PASS$' || fail "lingertest"

say "4. attach / detach / reattach / mirror / wait"
suite attach 35

say "5. reboot resume"
suite resume 9

say "6. overview listing (bare linger / ls)"
suite overview 7

say "7. remote sessions over ssh"
suite remote 11

say "8. adverse timing (busy daemon listing, name-ownership race)"
suite robust 14

say "9. graphics passthrough (kitty / sixel)"
suite graphics 9

say "10. terminal ownership (queries + stable child profile)"
suite terminal 12

say "11. status column (unread / seen transitions)"
suite status 5

say "12. agent verbs (info / capture / send - / resize)"
suite agent 24

say "13. watch (read-only mirror: geometry, keyboard, hand-back, seen)"
suite watch 17

pkill -x linger 2>/dev/null || true
printf '\nE2E OK — linger builds clean, core is pure, 10 live suites green.\n'
