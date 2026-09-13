#!/bin/sh
# tests/gates.sh — the SOURCE-TREE gates, and the only place the ratchet numbers live.
#
# Split out of tests/e2e.sh (2026-08-29) for one reason: these checks are
# milliseconds of `git grep` and `awk`, but inside e2e.sh they only fired AFTER a
# `rm -rf .lake/build`, a full rebuild and ten pty suites. The `pre-commit` hook now
# runs them at the moment the mistake is made, and e2e.sh runs THIS SAME FILE — so a
# cap can never disagree between the hook and the gate, which is the one failure mode
# that would make a hook worse than no hook.
#
# Every number here only ever goes DOWN without discussion. Raising one is a
# deliberate, reviewable edit, and that review is the whole point of the ratchet.
#
# Run standalone:  sh tests/gates.sh
set -e
cd "$(dirname "$0")/.."
fail() { printf 'GATE FAIL: %s\n' "$1" >&2; exit 1; }
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

# The vt-toolkit's import closure (`specs/vt-toolkit.md` Step 4). The toolkit is
# Linger/Core/{Vt,Render,Terminal}.lean, and the claim worth having is that its
# closure contains NOTHING else -- no Posix, no Runtime, no Checkpoint, no Session.
# `lean_lib LingerVt` in lakefile.lean is the positive half: it elaborates the
# closure. It cannot be the whole claim, because Lake resolves imports through one
# package-wide LEAN_PATH, so a lib with restricted `roots` compiles an out-of-set
# module happily -- `import Linger.Posix` in Terminal.lean builds under
# `./lake build LingerVt` without a murmur. Measured, twice, not assumed. A
# build-level failure needs a sub-package with its own srcDir and a path `require`,
# and the two gates immediately above forbid `require`. So this grep is the half
# that bites: the same species of oracle as SHIM_CAP below, evadeable by
# deliberately editing the list, not by reverting a fix.
#
# EXACT SETS, not a denylist of names to fear: a closure gate that only knows the
# imports someone thought of is not a closure gate. And exact means it also fires
# when an import GOES, which is right -- the list below is the recorded header, so
# Step 2/3 taking a friend import out is a reviewable edit here rather than a
# silent one. Vt imports nothing; Render imports Vt; Terminal imports Render; the
# two `import all Linger.Core.Vt` are the seal's friend imports (Step 1) and are
# inside the boundary by construction. Because Vt is a leaf, an exact check on
# these three files IS the closure.
toolkit_import_re='^(public |private |meta )*import '
toolkit_closure() {
  # Anchored at column 0, so neither a `--` comment nor a docstring's prose
  # mention of `import all` counts. ';'-joined to keep the diagnostic one line.
  tk_got="$(grep -E "$toolkit_import_re" "$1" | tr '\n' ';')"
  [ "$tk_got" = "$2" ] || { \
    printf '  %s import lines:\n' "$1" >&2; \
    { grep -nE "$toolkit_import_re" "$1" >&2 || printf '    (none)\n' >&2; }; \
    printf '  want: %s\n   got: %s\n' "${2:-(no imports)}" "${tk_got:-(no imports)}" >&2; \
    fail "$1 left the vt-toolkit import closure (lakefile.lean's lean_lib LingerVt)"; }
}
toolkit_closure Linger/Core/Vt.lean ''
toolkit_closure Linger/Core/Render.lean \
  'public import Linger.Core.Vt;import all Linger.Core.Vt;'
toolkit_closure Linger/Core/Terminal.lean \
  'public import Linger.Core.Render;import all Linger.Core.Vt;'

# shim-size ratchet: the C trust boundary must not grow silently. This
# number only ever goes DOWN without discussion; raising it is a
# deliberate, reviewable act — the checkpoint for "does this genuinely
# need a syscall wrapper, or does Lean core already have it?" (see the
# C-vs-Rust and shrink-the-shim notes in SCRATCHPAD.md).
SHIM_CAP=22
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

# `linger watch`'s client-side read-only guards (pin-the-gaps item 1). Read-only
# is enforced DAEMON-side: the 0x0 attach geometry sets `sizer := false` and
# `onMsg .input`/`onMsg .resize` then drop a non-sizer's traffic
# (`onMsg_input_readonly`). So these two `!readOnly` call sites are defence in
# depth and a pty test CANNOT see them — remove either and not one observable
# byte changes. That makes a grep the only honest oracle, the same species as
# SHIM_CAP above; faking it as a pty assertion would be decoration.
# `E2E/Watch.lean` covers guard A (the 0x0 attach), which IS observable.
grep -qE 'if size != lastSize && !readOnly' Linger/Runtime/Client.lean \
  || fail "Client.attach lost its read-only resize guard (a watcher would fight the user's size)"
grep -qE 'if !out.isEmpty && !readOnly' Linger/Runtime/Client.lean \
  || fail "Client.attach lost its read-only input guard (a watcher would forward keystrokes)"
grep -qE 'sendMsg fd \(\.attach 0 0\)' Linger/Runtime/Client.lean \
  || fail "Client.attach no longer marks a read-only client with a 0x0 attach (the wire's only read-only bit)"

# The checkpoint decoder must not grow its forge back (`specs/vt-toolkit.md` Step 2).
# `Linger/Core/Checkpoint.lean` keeps a PERMANENT `import all Linger.Core.Vt`: `wVt` reads
# 17 sealed fields, and dropping the import would force `Vt.ofDecoded` to be public — a
# second public door admitting any `Good` state, for every module forever, which is a
# wider hole than the one it replaces. The trade is that this one file retains the raw
# constructor, so "the decoder validates instead of forging" is a source-tree property,
# and a source-tree property cannot be a theorem. Same species of oracle as SHIM_CAP
# above, with the same limitation: evadeable by deliberately writing something new (a
# 20-field anonymous constructor), not by reverting the fix.
# Positive: the decoder goes through the smart constructor. Negative: no `Vt` field is
# assigned anywhere in the file. `cols`/`rows`/`grid`/`bot`/`tabs` have no defaults, so a
# fresh literal must name all five; `pstate`/`u8need`/`u8acc` catch a `{ v with … }`.
# The leading-backtick exclusion is deliberate: these greps read prose as well as code
# (AGENTS.md, and it has cost a full e2e run twice), and this file's docstrings have to be
# able to QUOTE the forge they describe. A gate nobody can write about is a gate someone
# deletes. The positive check wants a TRAILING SPACE for the same reason — in prose the
# name is always closed by a backtick, in code it is followed by its first argument.
# Break-verified both ways: a real forge at the decoder's old position, and the call
# deleted with the docstrings left in place.
grep -qE '(^|[^`[:alnum:]_.])Vt\.ofDecoded ' Linger/Core/Checkpoint.lean \
  || fail "Linger/Core/Checkpoint.lean no longer decodes through Vt.ofDecoded (a corrupt checkpoint could carry a zero column count)"
FORGE='(^|[^`[:alnum:]_])(cols|rows|grid|bot|tabs|pstate|u8need|u8acc) *:='
! grep -qE "$FORGE" Linger/Core/Checkpoint.lean \
  || { grep -nE "$FORGE" Linger/Core/Checkpoint.lean; \
       fail "a Vt field is assigned in Linger/Core/Checkpoint.lean — the decoder forge is back; go through Vt.ofDecoded, which validates"; }

# heartbeat ratchet. A `set_option maxHeartbeats` raise is a MEASUREMENT, and it
# has an expiry date that nothing else enforces: the 2026-08-18 factoring audit
# deleted 18 of 20, and the control run showed six of those were already
# deletable BEFORE the file split — budget added when the proofs were rougher and
# never re-measured once the surrounding lemmas were factored. So the sweep is
# cheap and the number only goes DOWN: after a refactor, try deleting them. The
# one that remains is real: `Vt.renderable_stepGround` (re-measured 2026-09-11 on
# v4.34.0-rc2 — still fails without it; `Checkpoint.load_save` shed its raise when
# `stripMagic` became a named stage). A new one means a proof got harder, which is
# the signal design-for-provability says to read, not silence.
HEARTBEAT_CAP=1
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

# Zero-Python invariant. The pty suites and the coverage gate are Lean (`E2E/`, run
# as `./lake exe e2e <suite>`); `tests/` holds this file and the orchestrator. A `.py`
# creeping back is how a two-language split returns, one convenience at a time.
if git ls-files '*.py' | grep -q .; then
  git ls-files '*.py'
  fail "a .py file is tracked; the suites and the coverage gate are Lean (see E2E/)"
fi

# `Tests/` and `tests/` are two tracked directories, and on a case-insensitive
# filesystem git silently records a new `tests/x` as `Tests/x` (AGENTS.md). Assert the
# split instead of trusting a reader to run `git ls-files --stage` after adding a file.
git ls-files 'Tests/*' | grep -qvE '\.lean$' \
  && fail "a non-Lean file under Tests/ (Lean unit tests only; orchestration lives in tests/)" || true
git ls-files 'tests/*' | grep -qE '\.lean$' \
  && fail "a .lean file under tests/ (it belongs in Tests/ or E2E/ — the case trap)" || true

# E2E `partial def` ratchet: the sibling of RUNTIME_PARTIAL_CAP above, for the same
# reason (the keyword creeps back by habit) and covering the files its glob misses.
# All five are honest, and two were MEASURED not assumed: rewriting `stripCsi` and
# `stripComments` around `List.dropWhile` STILL fails the termination check, because
# the recursion is on a dropWhile-then-drop of a tail, not a structural sub-term.
# Shedding them needs a real `decreasing_by` — proof work, not cleanup, and AGENTS.md
# rules out a fuel parameter. The rest: `leanFiles` (filesystem depth), two `drain`s
# (wall-clock deadline), `stripComments` (a two-token delimiter scan).
E2E_PARTIAL_CAP=5
ep_n="$(grep -rc 'partial def' E2E/*.lean LingerTest.lean | awk -F: '{s+=$2} END {print s+0}')"
[ "$ep_n" -le "$E2E_PARTIAL_CAP" ] \
  || fail "E2E/ grew to $ep_n partial defs (cap $E2E_PARTIAL_CAP); a do-block loop does not need the keyword"

printf 'gates OK — purity, the OS surface, and five ratchets\n'
