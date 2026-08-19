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
./lake build Linger Theorems Tests linger lingertest > /tmp/linger-build.log 2>&1 \
  || { tail -30 /tmp/linger-build.log; fail "build"; }
if grep -qE '^(warning|error)' /tmp/linger-build.log; then
  grep -E '^(warning|error)' /tmp/linger-build.log
  fail "build is not warning-clean"
fi
grep -c 'Build completed successfully' /tmp/linger-build.log > /dev/null \
  || fail "build did not report success"

say "2. purity of the core (no sorry, no partial, no IO)"
! git grep -n 'sorry' -- 'Linger/Core/*' 'Theorems/*' || fail "sorry found"
! git grep -n 'sorryAx' -- 'Linger/Core/*' 'Theorems/*' || fail "sorryAx found"
! git grep -nE '\bpartial def\b' -- 'Linger/Core/*' || fail "partial def in pure core"
! git grep -nE ': *IO ' -- 'Linger/Core/*' || fail "IO in pure core"
# Proofs must reduce in the kernel, never by compiled evaluation: a
# `native_decide` in Theorems/ would trust the compiler + `Decidable`
# instance instead of the kernel, and (unlike the tests, where evaluating
# golden bytes is the point) that is a hole in a *proof*. THEOREMS.md's
# "Reading a row" makes this a promise; this makes it enforced.
! git grep -nE '\bnative_decide\b' -- 'Theorems/*' || fail "native_decide in a proof (Theorems/)"
# the OS surface stays where AGENTS.md says it is
[ "$(git grep -l '@\[extern' -- 'Linger/*' | tr -d ' ')" = "Linger/Posix.lean" ] \
  || fail "extern declarations outside Linger/Posix.lean"
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

# The runtime keeps no byte queue of its own. `Linger/Core/Buf.lean` owns the two
# long-lived queues -- their caps, their drop and cut policies, and the fact that
# nothing written is retained (`Theorems/Buf.lean`) -- and `Linger/Runtime/*` is `IO`,
# so NO theorem can see that the daemon calls those functions rather than
# open-coding the same sums. Without this grep the Buf theorems are arithmetic
# about a value nothing forces the runtime to use. A source-tree property cannot
# be a theorem, so it is a gate, in the same spirit as SHIM_CAP above: evadeable
# by deliberately writing something new, not by reverting a fix.
# On the commit before Buf landed these three found 5 hits (Conn.out, Rt.ptyIn,
# Cli.queryInfo's accumulator, and two .extract compactions).
! grep -qE '^[[:space:]]+[a-zA-Z_]+ : ByteArray' Linger/Runtime/*.lean \
  || { grep -nE '^[[:space:]]+[a-zA-Z_]+ : ByteArray' Linger/Runtime/*.lean; \
       fail "a ByteArray field in Linger/Runtime (use Linger.Core.Buf, which is proved)"; }
! grep -qE 'mut [a-zA-Z_]+ : ByteArray' Linger/Runtime/*.lean \
  || { grep -nE 'mut [a-zA-Z_]+ : ByteArray' Linger/Runtime/*.lean; \
       fail "an accumulating ByteArray local in Linger/Runtime (use Linger.Core.Buf: it is capped)"; }
! grep -qE '\.extract\b' Linger/Runtime/*.lean \
  || { grep -nE '\.extract\b' Linger/Runtime/*.lean; \
       fail "buffer arithmetic in Linger/Runtime (Buf.bufAdvance owns it, and is proved)"; }

# heartbeat ratchet. A `set_option maxHeartbeats` raise is a MEASUREMENT, and it
# has an expiry date that nothing else enforces: the 2026-08-18 factoring audit
# deleted 18 of 20, and the control run showed six of those were already
# deletable BEFORE the file split — budget added when the proofs were rougher and
# never re-measured once the surrounding lemmas were factored. So the sweep is
# cheap and the number only goes DOWN: after a refactor, try deleting them. The
# two that remain are real (`Checkpoint.load_save` and `Vt.renderable_stepGround`,
# plus the record-width cost THEOREMS.md describes); a new one means a proof got
# harder, which is the signal design-for-provability says to read, not silence.
HEARTBEAT_CAP=2
hb_n="$(grep -rc 'set_option maxHeartbeats' Theorems/ | awk -F: '{s+=$2} END {print s+0}')"
[ "$hb_n" -le "$HEARTBEAT_CAP" ] \
  || fail "maxHeartbeats raises grew to $hb_n (cap $HEARTBEAT_CAP); a proof got harder — read that, or re-measure and delete a stale one"

# runtime `partial def` ratchet. Five of the seven shed the keyword on 2026-08-18
# once someone checked: `while`/`for` in a `do` block never needed it, and none of
# the five self-recursed. Two are honest — `pump` (genuinely unbounded recursion
# without a two-pass argument) and `parseLs` (wants a `decreasing_by`). Ratcheted
# so the keyword cannot creep back by habit; §Total in THEOREMS.md names both.
RUNTIME_PARTIAL_CAP=2
rp_n="$(grep -rc 'partial def' Linger/Runtime/*.lean | awk -F: '{s+=$2} END {print s+0}')"
[ "$rp_n" -le "$RUNTIME_PARTIAL_CAP" ] \
  || fail "Linger/Runtime grew to $rp_n partial defs (cap $RUNTIME_PARTIAL_CAP); a do-block loop does not need the keyword"

say "2b. coverage of the code by the theorems (two ratchets)"
# Every bug this project found by PROVING was an assumption nobody wrote down, so
# the shape to watch is a definition no theorem says anything about. This used to
# be a grep over all of Theorems/, which could not tell a claim from a word:
# `Render.history` — a stream the binary writes to the user's terminal — passed it
# because "history" occurs in a doc comment. `tests/coverage.py` measures theorem
# *statements* with comments stripped, and separately requires every byte stream
# the runtime emits to be classified as proved or bounded. See its header.
python3 tests/coverage.py | tee /tmp/linger-coverage.log
tail -1 /tmp/linger-coverage.log | grep -q '^FAILURES: 0$' || fail "coverage.py"

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
