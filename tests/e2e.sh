#!/bin/sh
# Whole-deliverable check (specs/archive/lean-zmx.md Step 10). Exits 0 only if
# everything below holds. Run from the repo root: ./tests/e2e.sh
#
#   1. content-checked build of program + proofs + unit tests, zero warnings
#   2. no `sorry` / `partial` in the pure core or the proofs
#  2b. coverage: every inventoried pure definition occurs in a theorem
#      type, and compiled renderer/replay references are classified
#   3. posix shim smoke tests (lingertest)
#   4. attach/detach/reattach/mirror/wait e2e (real ptys)
#   5. reboot-resume e2e (SIGKILL + restore + corrupt tolerance)
#   6. overview e2e (`linger ls` prints a list and exits)
#   7. remote-over-ssh e2e (fake ssh: `-r` listing, attach name@host argv)
#   8. adverse timing: busy-daemon listing (§Row) + name-ownership race
#   9. graphics passthrough (kitty APC / sixel DCS reach the client raw)
#  10. terminal ownership (query progress with zero/one/two clients + stable env)
#  11. status column: attach marks seen, output while away marks unread
#  12. agent verbs (info geometry/outseq, capture, send - , resize)
#  13. watch: the read-only mirror (geometry, keyboard, hand-back, marks seen)
#  14. recipes: native terminal launch settings; Lean import against daemons
#  15. delivery: bounded replay, margin continuation, byte order and close deadlines
#  16. manager: terminal selector, exact targets, paste, resize, cleanup and return
#  17. titles: attention refresh, split output, pipe-error recovery and handback
#  18. interchange: discarded foreign metadata, current fields and exclusive export
#  (1) also covers Tests/Fuzz.lean: randomized §Replay round-trip search
#  every pty suite also carries an EXACT CHECK COUNT (see `suite` below): green
#  means "no failures AND every recorded assertion ran".
#
# RUN THIS IN THE FOREGROUND. Enforced, not requested: see "SIGINT must be
# deliverable" below, which carries the measurement and the reasoning.
set -e
cd "$(dirname "$0")/.."

say() { printf '\n=== %s ===\n' "$1"; }
fail() { printf 'E2E FAIL: %s\n' "$1" >&2; exit 1; }

# --- SIGINT must be deliverable ---------------------------------------------
# A shell without job control starts a `&` job with SIGINT and SIGQUIT disabled,
# and that survives `execve`, so every descendant inherits it: the `e2e` binary,
# the daemon, the session shell the daemon spawns on the pty, and the child that
# shell runs. `^C` then generates a signal that kills nothing, and step 12's
# `send - carries ^C` assertion fails — while passing standalone every time, which
# is why it reads as a flake. It cost an hour on 2026-09-11 (SCRATCHPAD.md, "`&`
# blocks SIGINT"). The remedy was three copies of a warning in prose; this check
# is what replaces them, and the two surviving mentions (AGENTS.md's gate rule and
# the comment on the assertion in E2E/Agent.lean) now point here.
#
# The probe is BEHAVIOURAL, so it holds on both halves of the CI matrix: a fresh
# `sh -c` inherits the state, traps INT and signals itself. Delivered -> the trap
# runs -> 9. Disabled -> the signal never arrives -> 7. The child never dies OF a
# signal, and that is not incidental: a child killed by SIGINT makes some shells
# abandon the enclosing script (measured, ksh), so the obvious probe would
# sometimes kill this script instead of reporting on it.
#
# Reading `SigBlk` from /proc/self/status was the alternative, and it is wrong
# twice. It is Linux-only, and AGENTS.md keeps platform splits to two places — but
# worse, it is INCOMPLETE: measured here, bash 4.2 implements `&` as
# `SigIgn 0x6`, NOT `SigBlk 0x6`, so a check reading `SigBlk` alone would have
# passed in the very shell that reproduces the bug. /proc is used only to PRINT
# both masks when the probe fires, where its absence on macOS costs a line of
# diagnosis and not the check.
#
# Any exit but 9 refuses, deliberately: an unexpected probe result is not evidence
# that SIGINT works. And this cannot false-positive, because the probe tests
# exactly the precondition step 12 already depends on — an environment that fails
# it is an environment where the suite could not have passed anyway. It is NOT in
# tests/gates.sh: that file also runs from `pre-commit`, where a backgrounded
# commit is nobody's bug.
sigint=0
sh -c 'trap "exit 9" INT; kill -s INT $$; exit 7' > /dev/null 2>&1 || sigint=$?
if [ "$sigint" -ne 9 ]; then
  printf 'SIGINT is blocked or ignored in this process, and every descendant inherits it.\n' >&2
  if [ -r /proc/self/status ]; then                    # Linux only, and diagnosis only
    grep -E '^Sig(Blk|Ign):' /proc/self/status >&2 || true
  fi
  printf 'Step 12 asserts that ^C reaches the session child, so it would fail for a\n' >&2
  printf 'reason that is not linger. Run this script in the FOREGROUND: a job started\n' >&2
  printf 'with & in a shell without job control gets SIGINT and SIGQUIT disabled, and\n' >&2
  printf 'that survives execve. setsid and nohup are fine alone; the & is what does it.\n' >&2
  fail "SIGINT is not deliverable (probe exited $sigint, want 9) — run in the foreground, not with '&'"
fi

# Run one pty suite: no failures and exactly the recorded number of checks.
# Exactness removes headroom: adding a check requires updating the number now,
# instead of silently allowing a later assertion to disappear.
suite() {                                   # suite <name> <exact checks>
  out="/tmp/linger-$1.out"
  ./.lake/build/bin/e2e "$1" > "$out" 2>&1 \
    || { tail -25 "$out"; fail "$1 suite"; }
  tail -1 "$out" | grep -q '^FAILURES: 0$' \
    || { tail -25 "$out"; fail "$1 suite"; }
  n="$(grep -c '^PASS ' "$out")"
  [ "$n" -eq "$2" ] \
    || fail "$1 suite ran $n checks (expected exactly $2) — update the expectation for an intentional addition; a deletion is a regression"
  printf '  %s: %s checks\n' "$1" "$n"
}

say "1. build (program + theorems + tests)"
# Lake checks source/dependency content and replays cached diagnostics. Rehash
# artifacts too, and fail on warnings even after a local warningAsError override.
# Run `./lake clean` first for clean release/compiler validation.
./lake --rehash --wfail build Linger Theorems Tests linger lingertest e2e > /tmp/linger-build.log 2>&1 \
  || { tail -30 /tmp/linger-build.log; fail "build"; }
if grep -qE '^(warning|error)' /tmp/linger-build.log; then
  grep -E '^(warning|error)' /tmp/linger-build.log
  fail "build is not warning-clean"
fi
grep -c 'Build completed successfully' /tmp/linger-build.log > /dev/null \
  || fail "build did not report success"

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
# Resolve before `lake env` prepends its bundled compiler. On this Linux host
# only Homebrew clang can run; elsewhere the installed compiler is sufficient.
if [ "$(uname -s)" = Linux ] && [ -x /home/linuxbrew/.linuxbrew/bin/clang ]; then
  abi_cc=/home/linuxbrew/.linuxbrew/bin/clang
else
  abi_cc="$(command -v clang)" || fail "clang missing for ABI check"
fi
abi_prefix="$(./lake env lean --print-prefix)"
"$abi_cc" -fsyntax-only -Wall -Werror -Wstrict-prototypes \
  -isystem "$abi_prefix/include" -I "$PWD/c" "$abi_dir/check.c" \
  || fail "C shim conflicts with the generated Lean ABI"
rm -r "$abi_dir"
trap - EXIT HUP TERM

say "2. source-tree gates (purity, boundaries, and the ratchets)"
# Extracted to tests/gates.sh so the `pre-commit` hook and CI run the SAME numbers.
# A hook with its own copy of a cap is worse than no hook.
sh tests/gates.sh || fail "source-tree gates"

# The layout half of lean-fmt. The `pre-commit` hook runs `lean-fmt check` (the
# linter); `format --check` re-renders every file it visits and is CI-tier by the
# two-tier split, which is why it is here and not in the hook — but it belongs
# SOMEWHERE local: eight files drifted past it because the only enforcement was
# in CI, and the linter passing locally looked like the formatter passing too.
# ~22 s warm inside a run that already costs minutes. Absent binary is a skip,
# as in the hook: a fresh clone must still be able to run this script.
if command -v lean-fmt > /dev/null; then
  lean-fmt format --check > /tmp/linger-fmt.log 2>&1 \
    || { cat /tmp/linger-fmt.log >&2; fail "lean-fmt format --check"; }
  printf '  layout: %s\n' "$(head -1 /tmp/linger-fmt.log)"
else
  say "   (lean-fmt absent; layout drift unchecked — see README.md)"
fi

say "2b. semantic coverage of pure code + runtime emitter classification"
# `Theorems.Coverage` resolves exact environment constants in theorem types;
# E2E.Coverage reads resolved references from the program just built above.
# Invoke Lean directly so source-only changes cannot reuse a cached census.
./lake env lean Theorems/Coverage.lean || fail "semantic coverage gate"
./lake env lean E2E/Coverage.lean > /tmp/linger-coverage.log 2>&1 \
  || { cat /tmp/linger-coverage.log; fail "runtime emitter classification"; }
cat /tmp/linger-coverage.log
tail -1 /tmp/linger-coverage.log | grep -q '^FAILURES: 0$' || fail "coverage gate"

say "2c. CI runner selection and Lake build reuse"
# Which runners CI asks for decides the bill (measurements in SCRATCHPAD.md) and, in the
# other direction, whether AGENTS.md's macOS claim is checked by anything. `E2E.Ci` runs
# the real script, including its `git log --since` against throwaway repositories with
# real commit dates, and the pinned Lake against a temporary project.
ci_out=/tmp/linger-ci.out
./.lake/build/bin/e2e ci > "$ci_out" 2>&1 || { cat "$ci_out"; fail "CI checks"; }
cat "$ci_out"
tail -1 "$ci_out" | grep -q '^FAILURES: 0$' || fail "CI checks"
ci_n="$(grep -c '^PASS ' "$ci_out")"
[ "$ci_n" -eq 12 ] \
  || fail "e2e ci ran $ci_n checks (expected exactly 12)"

say "2d. fuzz corpus: no held-out mutations, failure lists asserted empty"
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
shim_out=/tmp/linger-shim.out
./.lake/build/bin/lingertest > "$shim_out" 2>&1 \
  || { tail -25 "$shim_out"; fail "lingertest"; }
tail -1 "$shim_out" | grep -q '^ALL PASS$' || fail "lingertest"
shim_n="$(grep -c '^PASS ' "$shim_out")"
[ "$shim_n" -eq 63 ] \
  || fail "lingertest ran $shim_n checks (expected exactly 63)"

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
sleep 1
LINGER_DIR="$sentinel_dir" ./.lake/build/bin/linger info "$sentinel_name" >/dev/null \
  || fail "sentinel session did not start"

say "4. attach / detach / reattach / mirror / wait"
suite attach 47

say "5. reboot resume"
suite resume 15

say "6. overview listing (linger ls)"
suite overview 16

say "7. remote sessions over ssh"
suite remote 21

say "8. adverse timing (busy daemon listing, name-ownership race)"
suite robust 18

say "9. graphics passthrough (kitty / sixel)"
suite graphics 9

say "10. terminal ownership (queries + stable child profile)"
suite terminal 12

say "11. status column (unread / seen transitions)"
suite status 17

say "12. agent verbs (info / capture / send - / resize)"
suite agent 46

say "13. watch (read-only mirror: geometry, keyboard, hand-back, seen)"
suite watch 18

say "14. recipes (native terminal settings and tmux-resurrect import)"
suite recipes 55

say "15. delivery (large replay, ordering, exit tails and retired transports)"
suite delivery 34

say "16. manager (entry dispatch, selection, creation, input and terminal handoff)"
suite manager 111

say "17. attached titles (attention, complete boundaries and default handback)"
suite title 18

say "18. save interchange (current fields, discarded metadata and exclusive publication)"
suite interop 33

LINGER_DIR="$sentinel_dir" ./.lake/build/bin/linger info "$sentinel_name" >/dev/null \
  || fail "a suite terminated the unrelated sentinel session"
cleanup_sentinel
trap - EXIT HUP TERM
printf '\nE2E OK — linger builds clean, core is pure, 15 live suites green.\n'
