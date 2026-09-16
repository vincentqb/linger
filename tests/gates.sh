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

# --- code_grep: the gates read CODE, not prose -------------------------------
# Every source grep below goes through this, and the reason is one trap on its
# FOURTH sighting: these greps read DOCSTRINGS as well as code. `native_decide`
# in a doc comment under `Theorems/` fails the purity gate exactly as it would in
# a proof (fb6a0e6; again 2026-08-29; again 2026-09-13), and the decoder-forge
# gate once failed on its OWN documentation, which quoted the forge it had just
# removed. That last one was fixed by teaching ONE gate to skip backtick-quoted
# text — and a fix inside one gate is a fact the next gate has to rediscover,
# which is exactly how this reached a fourth sighting. So it lives here, once,
# and a gate inherits it by being written.
#
# `code_grep <ere> <pathspec>...` is `git grep -nE` minus every backtick-DELIMITED
# span: same `file:line:content` output, same exit convention (0 = found), and the
# content printed VERBATIM — a diagnostic that quotes a line the file does not
# contain sends the reader after the wrong string (the friend-set gate's first
# draft did that). An UNPAIRED backtick and everything after it is KEPT, because
# Lean writes `Name literals and `(quotations) with a single one and those are
# code. Backticks only: a `--` comment still counts as code, deliberately —
# commented-out code is code someone uncomments, and the trap here is prose.
#
# Two rules for any regex handed to it, both because the matcher is POSIX awk and
# not GNU grep:
#   * no `\b` — spell a word boundary `(^|[^[:alnum:]_])x([^[:alnum:]_]|$)`;
#   * no backslash escapes — spell a literal as a bracket expression: `[.]`.
# The regex travels in the ENVIRONMENT rather than through `-v`, because `-v`
# escape-processes its value and would eat a backslash before awk compiled it.
# shellcheck disable=SC2016  # $0/$1 below are awk's fields; single quotes are the point
CODE_AWK='
BEGIN { re = ENVIRON["CG_RE"] }
{ code = ""; rest = $0
  while ((i = index(rest, "`")) > 0) {
    j = index(substr(rest, i + 1), "`")
    if (j == 0) break                        # unpaired: the rest is code, verbatim
    code = code substr(rest, 1, i - 1) " "   # a SPACE, so deleting a span can never
    rest = substr(rest, i + j + 1) }         # splice a match out of its two sides
  if ((code rest) ~ re) { printf "%s:%d:%s\n", FILENAME, FNR, $0; hits++ } }
END { exit (hits > 0 ? 0 : 1) }'
code_grep() {                                # code_grep <ere> <pathspec>...
  cg_re="$1"; shift
  cg_files="$(git ls-files -- "$@")"
  [ -n "$cg_files" ] || fail "code_grep: nothing tracked matches '$*' (a gate points at a path that moved)"
  # Deliberate word split: no tracked path in this tree has a space. `/dev/null`
  # is the last operand so awk can never fall back to stdin and hang.
  # shellcheck disable=SC2086
  CG_RE="$cg_re" awk "$CODE_AWK" $cg_files /dev/null
}
code_count() { code_grep "$@" | awk 'END { print NR + 0 }'; }   # -> a number

# A pathspec that stops matching makes a `! code_grep …` gate pass by finding
# nothing, and a ratchet read through `code_count` reads 0 — the one way a gate
# rots in silence. `Linger/Core/Vt.lean` used to carry the only such guard, for
# the friend set; this is that guard generalized to every path named below. (It
# cannot live inside `code_grep`, because `code_count` runs it down a pipe and an
# `exit` there would only leave the subshell.)
for p in Linger/Core Linger/Core/Vt.lean Linger/Core/Checkpoint.lean \
         Linger/Runtime Linger/Runtime/Client.lean Linger/Runtime/Daemon.lean \
         Theorems Theorems/Session.lean Tests E2E \
         LingerTest.lean c/shim.c lakefile.lean lake-manifest.json README.md; do
  [ -e "$p" ] || fail "$p is gone — a gate below would pass by matching nothing"
done

! code_grep 'sorry' 'Linger/Core/*' 'Theorems/*' || fail "sorry found"
! code_grep 'sorryAx' 'Linger/Core/*' 'Theorems/*' || fail "sorryAx found"
! code_grep '(^|[^[:alnum:]_])partial def([^[:alnum:]_]|$)' 'Linger/Core/*' \
  || fail "partial def in pure core"
! code_grep ': *IO ' 'Linger/Core/*' || fail "IO in pure core"
# Proofs must reduce in the kernel, never by compiled evaluation: a
# `native_decide` in Theorems/ would trust the compiler + `Decidable`
# instance instead of the kernel, and (unlike the tests, where evaluating
# golden bytes is the point) that is a hole in a *proof*. THEOREMS.md's
# "Reading a row" makes this a promise; this makes it enforced.
! code_grep '(^|[^[:alnum:]_])native_decide([^[:alnum:]_]|$)' 'Theorems/*' \
  || fail "native_decide in a proof (Theorems/)"
# the OS surface stays where AGENTS.md says it is
[ "$(code_grep '@[[]extern' 'Linger/*' | awk -F: '!seen[$1]++ { print $1 }' | tr -d ' ')" = "Linger/Posix.lean" ] \
  || fail "extern declarations outside Linger/Posix.lean"
# `unsafe` and `@[implemented_by]` — the Lean-side twin of the `@[extern` gate just
# above, and the only route that makes the theorems false OF THE SHIPPED BINARY rather
# than of some value inside it (SCRATCHPAD.md, "the adversarial audit of the seal",
# finding R4). Re-measured here, in `Theorems/Render/Ends.lean`, on v4.34.0-rc2:
#
#   unsafe def launderImpl (_v : Vt) : Vt := unsafeCast (0 : Nat)
#   @[implemented_by launderImpl] def launder (v : Vt) : Vt := v
#   theorem launder_id (v : Vt) : launder v = v := rfl
#
# → `Build completed successfully (108 jobs)`, `#print axioms launder_id` → "does not
# depend on any axioms", and one `#eval` of the result's `colCount` → `Lean exited with
# code 139`, a segfault. The kernel sees an honest identity; the compiled program reads
# arbitrary memory. So every theorem about `launder` is true and none of them is about
# what runs — and no proof can ever see that, because `@[implemented_by]` is by
# construction the part the kernel does not check. A source-tree gate is the only
# possible oracle, the SHIM_CAP species: evadeable by deliberately editing this line,
# not by reverting a fix. Control: on the tree carrying that exhibit, every other gate
# in this file said OK.
#
# TREE-WIDE and fail-closed — measured zero hits across all 71 tracked `.lean` files, so
# there is nothing to grandfather and no exemption list to rot. `Tests/` and `E2E/` are
# inside it on purpose: a suite that laundered a value would be asserting about a state
# the binary cannot produce, which is this defect wearing a test's clothes.
#
# `unsafe` is matched as "not preceded by an identifier character", which catches the
# keyword AND every `unsafe*` name in one alternative (`unsafeCast`, `unsafeIO`,
# `unsafeBaseIO`, `unsafePerformIO`, …) instead of the single name the audit happened to
# use. `implemented_by` is unanchored for the same reason: `@[implemented_by f]` and
# `attribute [implemented_by f] g` both set it.
#
# DECLINED: adding `opaque`. Measured rather than deferred to the earlier decision —
# `opaque` has 26 hits over tracked `.lean`, 22 of them the actual `@[extern`
# declarations in `Linger/Posix.lean`, so the gate could only ever read "opaque outside
# Posix.lean". What that would catch is not a forge: with no `@[extern]` and no
# `@[implemented_by]` the compiler emits no value at all, so `opaque x : Vt` is a
# liveness hazard, not an implementation that disagrees with the model (the R5 family,
# which the spec bounds as compile-time prose). Its three remaining uses are the English
# word in prose and `code_grep` strips none of them — all three are unbackticked — so the
# helper does not make it cheaper either.
! code_grep '(^|[^[:alnum:]_])(unsafe|implemented_by)' '*.lean' \
  || fail "unsafe / @[implemented_by] in Lean — the compiled program may then disagree with every theorem about it (R4; see the comment on this gate)"
[ "$(ls c/ | tr -d ' \n')" = "shim.c" ] || fail "more than one C file"
# README promises "no external Lean dependencies"; make it fail-closed rather
# than rest on inspection (README-promise coverage audit, the unbacked-promise
# class). A `require` in the lakefile would pull in a package.
! code_grep '^[[:space:]]*require ' 'lakefile.lean' \
  || fail "external Lean dependency in lakefile.lean (README promises none)"
[ "$(tr -d ' \n' < lake-manifest.json | grep -o '\"packages\":\[[^]]*\]')" = '"packages":[]' ] \
  || fail "lake-manifest has packages (README promises no external Lean deps)"

# README's prior-art list stays BARE — names and links, nothing else. AGENTS.md's
# "do not editorialize about other codebases" rule sanctions exactly one place to
# name a peer project, and this is it; 4551a5b cut the list back to that shape after
# it had grown "(the gold standard)", "(the attach/detach decoupling linger mirrors,
# down to the verb surface)" and "(the interface bar — its crashes under load are why
# §Bound and §Total are theorems here)". The 2026-09-14 sweep removed the same species
# of clause from 30 other sites. Nothing stops it growing back, so: SHAPE, not a
# wordlist.
#
# The block is `Prior art:` to the next blank line. Strip the lead-in, every
# `[name](url)` span and the list separators; anything LEFT is a characterization.
# That is the rule stated as an assertion — a bare pointer has no residue.
#
# WHY SHAPE AND NOT A WORDLIST, measured, because the wordlist is the obvious design
# and it is the wrong one:
#   * `screen` is one of the five projects the list names, and it CANNOT be in a
#     wordlist: as a standalone word it has 463 hits over tracked `.lean`/`.md`
#     (`screenText`, `screensAnsi`, "the screen", …), exactly ONE of which is the
#     project. So a wordlist gate is structurally blind to a fifth of its own subject.
#   * a wordlist must let the sanctioned links through, and once it does it goes
#     silent on the motivating violation: every characterization above sits OUTSIDE
#     its link span and contains no project name at all. Measured on the real text —
#     with `[name](url)` spans stripped (needed so the list itself passes), a
#     {tmux,abduco,zellij,zmx,dtach} grep does not fire on pre-4551a5b README. A gate
#     that passes clean on the tree that motivated it is the spec-citation gate's
#     `code_grep` trap in a new costume.
#   * and it is a denylist of names someone thought of — the objection the friend-set
#     gate above records against gating edges instead of the closure.
# What this gate buys instead is narrow and real: the ONE sanctioned location cannot
# silently stop being a bare pointer. The rest of the standard is prose discipline
# under AGENTS.md §Rules, declined deliberately rather than faked.
#
# Break-verified six ways: pre-4551a5b README (fires, 5 lines), 4551a5b (silent),
# this tree (silent), `Prior art:` renamed (exit 2, the vacuous-pass probe — a gate
# whose block went missing must not pass), a new BARE entry appended (silent: the
# list may grow), and one characterization re-added to an existing link (fires).
#
# POSIX awk: bracket expressions, no backslash escapes, per `code_grep`'s rules. Not
# `code_grep` itself — the sanctioned form is a markdown link, not a backtick span,
# and stripping backticks would neither admit it nor find the residue.
awk '
  /^Prior art:/ { inblock = 1 }
  inblock && /^[[:space:]]*$/ { inblock = 0 }
  inblock {
    seen++
    s = $0
    sub(/^Prior art:/, "", s)
    gsub(/[[][^]]*[]][(][^)]*[)]/, "", s)
    gsub(/and/, "", s)
    gsub(/[,.[:space:]]/, "", s)
    if (s != "") { printf "  %s:%d:%s\n", FILENAME, FNR, $0; bad++ } }
  END {
    if (seen == 0) {
      print "  no `Prior art:` block found in README.md — renamed or removed, and this"
      print "  gate would then pass by checking nothing"
      exit 2 }
    exit (bad > 0 ? 1 : 0) }' README.md >&2 \
  || fail "README's prior-art list is not a bare pointer any more (see the lines above): name and link only, no characterization of another project — AGENTS.md, 'do not editorialize about other codebases'"

# The vt-toolkit's import closure (`specs/archive/vt-toolkit.md` Step 4). The toolkit is
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
  # Anchored at column 0 AND read through `code_grep`, so neither a `--` comment,
  # nor an inline `import all` inside backticks, nor a docstring line that happens
  # to begin with the word counts. ';'-joined to keep the diagnostic one line.
  tk_got="$(code_grep "$toolkit_import_re" "$1" | sed 's/^[^:]*:[0-9]*://' | tr '\n' ';')"
  [ "$tk_got" = "$2" ] || { \
    printf '  %s import lines:\n' "$1" >&2; \
    { code_grep "$toolkit_import_re" "$1" >&2 || printf '    (none)\n' >&2; }; \
    printf '  want: %s\n   got: %s\n' "${2:-(no imports)}" "${tk_got:-(no imports)}" >&2; \
    fail "$1 left the vt-toolkit import closure (lakefile.lean's lean_lib LingerVt)"; }
}
toolkit_closure Linger/Core/Vt.lean ''
toolkit_closure Linger/Core/Render.lean \
  'public import Linger.Core.Vt;import all Linger.Core.Vt;'
toolkit_closure Linger/Core/Terminal.lean \
  'public import Linger.Core.Render;import all Linger.Core.Vt;'

# The `Vt` friend set — who may forge a `Vt` (SCRATCHPAD.md, "the adversarial audit of
# the seal", finding R1). `import all M` grants M's OWN all-access set, including
# whatever M has all-access to, so **`import all` TRANSITS** and
# `git grep -l 'import all Linger.Core.Vt'` is NOT an enumeration of the friend set.
# Measured in the real position, not a scratch file: one added
# `import all Linger.Core.Render` in `Linger/Runtime/Client.lean` (which already
# `public import`s Render) plus a five-field `{ cols := 0, rows := 0, grid := #[], … }`
# gives `./lake build linger` exit 0 AND `sh tests/gates.sh` exit 0. Two hops is the
# same: `import all Theorems.Listing` from a file holding neither
# `import all Linger.Core.Vt` nor `import all Linger.Core.Render` compiles the identical
# forge. That is the Step 4 situation exactly — the compiler consents, so a grep is the
# only possible oracle — except that until now no grep existed, which made joining the
# friend set cost one line that nothing objected to, and made `private` on 20 fields
# worth one line of anyone's diff.
#
# CLOSURE, not edges. Transit follows `import all` edges ONLY (measured:
# `import all Linger.Core.Session` — a plain `public import`er of `Vt` — does not
# transit, and neither does the `Linger` umbrella, whose imports are all `public`), so
# the closure over those edges IS the friend set and nothing else can widen it. Gating
# the edges instead would mean recording all 78 of them, of which about five matter, and
# would fire on every legitimate rewire of the `Theorems/Render/*` chain — noise on the
# common change, which is how a gate stops being read.
#
# The permitted region is an EXACT four-file list plus two directories, and that split
# is by edit frequency, measured: of 192 commits, 36 added a `.lean` under `Theorems/`
# or `Tests/` — about one commit in five — against 11 under `Linger/Core/`, only four of
# which are in the closure. So a per-file list over `Theorems/**` would be edited
# reflexively, while these four are edited essentially never, which is what makes them a
# checkpoint. `Theorems/**` and `Tests/**` are friends BY DECLARATION (see
# `Linger/Core/Vt.lean`, "## Every door"), and `Tests/` deliberately forges invalid
# states in its negative fixtures, so listing its files one by one would gate a
# non-property. Everything else is outside and fail-closed — `E2E/**`,
# `LingerTest.lean`, `Main.lean`, `Linger/Posix.lean`, all of `Linger/Runtime/` and the
# other seven `Linger/Core/` modules. `E2E/**` is outside deliberately: a pty suite
# asserts on bytes the real binary emitted, so a forged `Vt` there would be an assertion
# about a state the binary cannot reach — the very bug the seal exists to prevent.
#
# EXACT means both directions, as with the three toolkit lists above: a recorded friend
# that stops reaching `Vt` fails too, so a future step taking a friend import out is a
# reviewable edit here rather than a silent one. No cardinality number is recorded — the
# Step 4 record killed the job-count ratchet because cardinality is blind to identity,
# and that argument transfers whole.
#
# The regex is deliberately LOOSER than column 0, because `  import all Foo` (leading
# spaces) and `meta import all Foo` both compile — measured, along with the two that do
# not: `public import all` and `private import all` are rejected by Lean, and a tab is
# refused before it reaches here. Anchoring at column 0 would leave a one-space evasion.
# The prose hazard the loose regex used to buy (AGENTS.md: these greps read docstrings)
# is now `code_grep`'s, not this gate's — a backticked `import all Foo` anywhere in a
# docstring is invisible to it. What survives is narrower and still worth writing down:
# do not begin a docstring line with a BARE, unbackticked `import all`.
VT_ALL_RE='^[[:space:]]*(meta[[:space:]]+)*import[[:space:]]+all[[:space:]]+'
VT_FRIEND_EXACT='Linger/Core/Vt.lean Linger/Core/Render.lean Linger/Core/Terminal.lean Linger/Core/Checkpoint.lean'
VT_FRIEND_DIRS='Theorems/ Tests/'
code_grep "$VT_ALL_RE" '*.lean' \
| awk -F: -v seed='Linger/Core/Vt.lean' -v exact="$VT_FRIEND_EXACT" -v dirs="$VT_FRIEND_DIRS" '
  BEGIN { ne = split(exact, E, " "); nd = split(dirs, D, " ") }
  { mod = $3
    sub(/^[ \t]*(meta[ \t]+)*import[ \t]+all[ \t]+/, "", mod); sub(/[ \t\r]+$/, "", mod)
    tgt = mod; gsub(/[.]/, "/", tgt)
    n++; src[n] = $1; ln[n] = $2; raw[n] = $3; dst[n] = tgt ".lean" }
  END {
    # Breadth-first BACKWARDS from the seal, so via[] is a shortest witness chain and
    # the two-hop case prints as the two hops it is rather than as one bare filename.
    q[1] = seed; inset[seed] = 1; qn = 1
    for (qi = 1; qi <= qn; qi++)
      for (i = 1; i <= n; i++)
        if (dst[i] == q[qi] && !(src[i] in inset)) {
          inset[src[i]] = 1; via[src[i]] = i; qn++; q[qn] = src[i] }
    bad = 0
    for (i = 1; i <= n; i++) {   # input order: git grep sorts, so the report is stable
      f = src[i]
      if (!(f in inset) || (f in seen)) continue
      seen[f] = 1
      ok = 0
      for (j = 1; j <= ne; j++) if (f == E[j]) ok = 1
      for (j = 1; j <= nd; j++) if (substr(f, 1, length(D[j])) == D[j]) ok = 1
      if (ok) continue
      bad++
      printf "  %s has all-access to Linger.Core.Vt -- its 20 private fields, its\n", f
      printf "  private constructor and Vt.ofDecoded -- by this chain of import all:\n"
      for (cur = f; cur != seed; cur = dst[via[cur]])
        printf "    %s:%s:%s\n", src[via[cur]], ln[via[cur]], raw[via[cur]] }
    for (j = 1; j <= ne; j++)
      if (!(E[j] in inset)) { bad++
        printf "  %s is a RECORDED friend that no longer reaches Linger.Core.Vt", E[j]
        printf " (renamed, moved, or its import all went)\n" }
    if (bad > 0) printf "  permitted: %s -- plus anything under: %s\n", exact, dirs
    exit (bad == 0 ? 0 : 1) }' >&2 \
  || fail "the Linger.Core.Vt friend set changed (import all TRANSITS: it re-grants whatever the imported module itself has all-access to)"

# shim-size ratchet: the C trust boundary must not grow silently. This
# number only ever goes DOWN without discussion; raising it is a
# deliberate, reviewable act — the checkpoint for "does this genuinely
# need a syscall wrapper, or does Lean core already have it?" (see the
# C-vs-Rust and shrink-the-shim notes in SCRATCHPAD.md).
SHIM_CAP=22
shim_n="$(code_count 'LEAN_EXPORT' 'c/shim.c')"
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
# Cli.queryInfo's accumulator, and two .extract compactions). Each used to spell its
# regex twice — once to test, once to print the hits — and `code_grep` prints them, so
# the duplicate is gone: two copies of a pattern is two things to keep in step.
! code_grep '^[[:space:]]+[a-zA-Z_]+ : ByteArray' 'Linger/Runtime/*' \
  || fail "a ByteArray field in Linger/Runtime (use Linger.Core.Buf, which is proved)"
! code_grep 'mut [a-zA-Z_]+ : ByteArray' 'Linger/Runtime/*' \
  || fail "an accumulating ByteArray local in Linger/Runtime (use Linger.Core.Buf: it is capped)"
! code_grep '[.]extract([^[:alnum:]_]|$)' 'Linger/Runtime/*' \
  || fail "buffer arithmetic in Linger/Runtime (Buf.bufAdvance owns it, and is proved)"

# `Session.resumeVt` ↔ `Daemon.lean`'s `vt0` — the resume door's model/runtime tie, and
# the direct sibling of the three Buf greps above: same gap, same species of oracle.
# `Theorems/Session.lean`'s `resumeVt` IS the daemon's fallback expression with the `IO`
# peeled off, and it is load-bearing — `liveReachable_resumeVt`, `run_resume_vt_shape`
# and `run_resume_load_save` are claims about the daemon ONLY through that
# correspondence, which was prose next to the def until this gate. `Linger/Runtime/*` is
# `IO`, so no theorem can see the call site (AGENTS.md's rule): change the daemon's
# fallback to, say, `Vt.init 24 80` and all three theorems stay true — of a term the
# daemon no longer computes. Evadeable by deliberately editing both ends, which is
# exactly the review this buys.
#
# TWO-SIDED, deliberately. A gate watching only `Daemon.lean` passes by vacuous truth
# the moment the model is deleted, and it is the correspondence being gated, not either
# end of it. Same argument as the toolkit closure lists and the friend set below, where
# a RECORDED friend that stops reaching `Vt` also fails: exact means both directions.
#
# Through `code_grep`, so a comment QUOTING the call site cannot satisfy a gate about
# the call site — the inverse of the decoder-forge gate's problem and the more dangerous
# half, since it fails open. `Theorems/Session.lean` quotes this exact line twice
# (:1016, :1037, inside docstring fences) and `Daemon.lean` names `Vt.init 80 24` in
# prose at :348; measured, each regex matches exactly one line.
#
# One known false-positive mode, and it is the right one: if either line grows past the
# formatter's width and wraps, the gate fires. That is a loud failure on precisely the
# edit that should be reviewed, not a silent pass. A lockstep change of the fallback
# dimensions fires too, and deliberately — both literals are recorded, in the same style
# as the toolkit closure lists, so re-deciding what a checkpointless resume looks like is
# a reviewable edit here rather than a silent one.
#
# And the BOUND, which is what this gate does not buy: it pins the modelled EXPRESSION,
# not the value the daemon ends up booting from. A later line reassigning `vt0` — say a
# conditional override further down `serve` — leaves both greps green while `resumeVt`
# stops modelling anything the daemon computes. That is semantic and no grep reaches it;
# it is the same limitation every gate in this file carries, stated here rather than
# discovered. What this catches is an EDIT to the modelled line, which is the way the
# correspondence has actually been at risk.
code_grep '[.]getD [(]Linger[.]Core[.]Vt[.]Vt[.]init 80 24[)]' 'Linger/Runtime/Daemon.lean' > /dev/null \
  || fail "Daemon.serve's vt0 no longer falls back to Vt.init 80 24 via getD — Theorems/Session.lean's resumeVt models THAT expression, so re-derive it and its three claims, or restore the line"
code_grep '^def resumeVt .*[.]getD [(]Vt[.]Vt[.]init 80 24[)]' 'Theorems/Session.lean' > /dev/null \
  || fail "Theorems/Session.lean lost resumeVt, or its fallback changed — the resume claims no longer model Daemon.lean's vt0, and the gate above would then pass vacuously"

# `linger watch`'s client-side read-only guards (pin-the-gaps item 1). Read-only
# is enforced DAEMON-side: the 0x0 attach geometry sets `sizer := false` and
# `onMsg .input`/`onMsg .resize` then drop a non-sizer's traffic
# (`onMsg_input_readonly`). So these two `!readOnly` call sites are defence in
# depth and a pty test CANNOT see them — remove either and not one observable
# byte changes. That makes a grep the only honest oracle, the same species as
# SHIM_CAP above; faking it as a pty assertion would be decoration.
# `E2E/Watch.lean` covers guard A (the 0x0 attach), which IS observable.
code_grep 'if size != lastSize && !readOnly' 'Linger/Runtime/Client.lean' > /dev/null \
  || fail "Client.attach lost its read-only resize guard (a watcher would fight the user's size)"
code_grep 'if !out.isEmpty && !readOnly' 'Linger/Runtime/Client.lean' > /dev/null \
  || fail "Client.attach lost its read-only input guard (a watcher would forward keystrokes)"
code_grep 'sendMsg fd [(][.]attach 0 0[)]' 'Linger/Runtime/Client.lean' > /dev/null \
  || fail "Client.attach no longer marks a read-only client with a 0x0 attach (the wire's only read-only bit)"

# The checkpoint decoder must not grow its forge back (`specs/archive/vt-toolkit.md` Step 2).
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
# This pair is where the backtick rule was first learned: this file's docstrings have to
# be able to QUOTE the forge they describe, and a gate nobody can write about is a gate
# someone deletes. `code_grep` now owns that, for every gate — the leading-backtick class
# and the TRAILING SPACE below are what is left of the local fix, kept because they still
# bite on an UNPAIRED backtick, which `code_grep` deliberately treats as code.
# Break-verified both ways: a real forge at the decoder's old position, and the call
# deleted with the docstrings left in place.
code_grep '(^|[^`[:alnum:]_.])Vt[.]ofDecoded ' 'Linger/Core/Checkpoint.lean' > /dev/null \
  || fail "Linger/Core/Checkpoint.lean no longer decodes through Vt.ofDecoded (a corrupt checkpoint could carry a zero column count)"
FORGE='(^|[^`[:alnum:]_])(cols|rows|grid|bot|tabs|pstate|u8need|u8acc) *:='
! code_grep "$FORGE" 'Linger/Core/Checkpoint.lean' \
  || fail "a Vt field is assigned in Linger/Core/Checkpoint.lean — the decoder forge is back; go through Vt.ofDecoded, which validates"

# heartbeat ratchet. A `set_option maxHeartbeats` raise is a MEASUREMENT, and it
# has an expiry date that nothing else enforces: the 2026-08-18 factoring audit
# deleted 18 of 20, and the control run showed six of those were already
# deletable BEFORE the file split — budget added when the proofs were rougher and
# never re-measured once the surrounding lemmas were factored. So the sweep is
# cheap and the number only goes DOWN: after a refactor, try deleting them.
# **The cap is now ZERO** (2026-09-14): the last raise was
# `Vt.renderable_stepGround`, and it did not need a bigger budget — it needed a
# better closer. Re-measured in tree: the `first | ...` script genuinely still
# timed out at the default 200000 (confirmed, not assumed), but `grind` with the
# four `renderable_*` lemmas closes every branch inside it, retiring that raise
# AND the `maxRecDepth 4096` above it, and cutting `./lake build Theorems` from
# 115.9s to 78.2s. Break-verified twice: drop `renderable_congr` from the lemma
# set, or drop the `Renderable v` hypothesis, and `grind` fails.
# Like the semantic pure-core coverage gate, zero flips this from a budget to
# spend into an invariant to keep: a new raise means a proof got harder, which is the signal
# design-for-provability says to read, not silence.
HEARTBEAT_CAP=0
hb_n="$(code_count 'set_option maxHeartbeats' 'Theorems/*')"
[ "$hb_n" -le "$HEARTBEAT_CAP" ] \
  || fail "maxHeartbeats raises grew to $hb_n (cap $HEARTBEAT_CAP); a proof got harder — read that, or re-measure and delete a stale one"

# recursion-depth ratchet — the sibling the heartbeat one lacked for a year, added
# 2026-09-14 because the same rot was found by the same argument. `maxRecDepth` is a
# MEASUREMENT with the same expiry as `maxHeartbeats` and had no gate, so nobody
# re-measured: of the three raises in `Theorems/Vt.lean`, TWO were stale — `8000` on
# `uaz_stepGround` and `2000` on `stick_stepGround` both deleted with the proofs
# untouched and the build green. The third (`4096` on `stepGround`'s `Good` proof) is
# real: line 730 hits the recursion limit without it, and `grind` cannot retire it
# either — measured, not assumed. The `4096` on `renderable_stepGround` went with that
# proof's `grind` rewrite, so 3 became 1 in one round.
# Same direction-of-travel rule as above: DOWN without discussion, up only as a signal
# to read. A raise here means a term got deeper, which is usually a dispatch that grew
# arms — the thing design-for-provability says to restructure rather than budget for.
RECDEPTH_CAP=1
rd_n="$(code_count 'set_option maxRecDepth' 'Theorems/*')"
[ "$rd_n" -le "$RECDEPTH_CAP" ] \
  || fail "maxRecDepth raises grew to $rd_n (cap $RECDEPTH_CAP); a term got deeper — read that, or re-measure and delete a stale one"

# runtime `partial def` ratchet. Five of the seven shed the keyword on 2026-08-18
# once someone checked: `while`/`for` in a `do` block never needed it, and none of
# the five self-recursed. Two are honest — `pump` (genuinely unbounded recursion
# without a two-pass argument) and `parseLs` (wants a `decreasing_by`). Ratcheted
# so the keyword cannot creep back by habit; §Total in THEOREMS.md names both.
RUNTIME_PARTIAL_CAP=2
rp_n="$(code_count 'partial def' 'Linger/Runtime/*')"
[ "$rp_n" -le "$RUNTIME_PARTIAL_CAP" ] \
  || fail "Linger/Runtime grew to $rp_n partial defs (cap $RUNTIME_PARTIAL_CAP); a do-block loop does not need the keyword"

# Test-orchestrator safety. The pty suites isolate themselves by LINGER_DIR; an
# unscoped process-name kill reaches real sessions outside that directory. A skipped
# required regression is not a pass, and an executable Python snippet is still a
# second-language dependency even when embedded in a Lean string rather than tracked
# as a .py file. These are syntactic runtime ties, so the source gate is the oracle.
! code_grep '(^|[^[:alnum:]_])(pkill|killall)[[:space:]].*linger' 'tests/e2e.sh' \
  || fail "tests/e2e.sh kills by process name — suites may terminate only processes they created"
# A process-GROUP selector is the same hazard wearing a pid. POSIX reads `kill 0` as
# "every process in my group" and `kill -N` as group N, so one of these in a test
# script signals the harness, the agent running it, and whatever shell shares that
# group — which is exactly what happened on 2026-09-15, from `kill 0 15` inside
# `lingertest`. Scoped to the shell and the shim, because that is where nothing else
# stops it: from Lean the call goes through `Linger.Posix.checkPid`, which rejects 0
# and every value that casts to a negative `pid_t` — a mechanism, not a grep — and
# `LingerTest.lean`'s `kill 0 15` is that mechanism's regression test, so including
# Lean here would flag the assertion instead of the hazard. `kill -0 $pid` (the
# liveness probe) is a signal flag, not a target, and is deliberately not matched.
! code_grep 'kill([[:space:]]+-[A-Za-z0-9]+)*[[:space:]]+(--[[:space:]]+)?(0|-[0-9]+)([^0-9]|$)' \
    'tests/*.sh' 'c/shim.c' \
  || fail "a signal targets process group 0 or a negative pid — name the pid the suite created"
! code_grep '["]python([0-9.]*)' 'E2E/*' \
  || fail "an E2E suite executes embedded Python — use the e2e binary as the child probe"
! code_grep 'IO[.]println[[:space:]]+"PASS[[:space:]].*skip' 'E2E/*' \
  || fail "an E2E suite counts a skipped required check as PASS"

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

# Every `specs/….md` path cited in the tree must EXIST. Archiving a spec silently
# orphans every citation of it, and it has happened repeatedly — most recently when the
# vt-toolkit spec moved from its old top-level path to `specs/archive/vt-toolkit.md` at
# 051b2b4, leaving 31 tracked files pointing at a path that is not there:
# `Linger/Core/*`, fourteen `Theorems/` files, `Tests/*`, `lakefile.lean`, and this file.
# No count of the archive is written here on purpose; AGENTS.md records that two such
# counts already rotted, and `specs/archive/` can be listed. The rot is invisible because
# a citation is prose: it compiles, it formats, and no reader chases it until one does and
# finds nothing. With this gate the NEXT archive fails at archive time, when the move is
# one `sed` away, instead of at the moment someone needs the document.
#
# PLAIN `git grep`, NOT `code_grep`, and this is the one gate in the file where that is
# correct. Measured, because the difference IS the gate: citations are written in prose
# inside backticks, which is exactly the span `code_grep` deletes by design. Over this
# tree `code_grep` sees 29 citation lines and NOT ONE of the 31 stale ones — a
# `code_grep` version of this gate passes clean on the very tree that motivated it. So do
# not "fix" this to match the rest of the file; the helper's rule is right for code and
# wrong here, where the citation IS the prose.
#
# One consequence, and it is by construction rather than an oversight: a live file cannot
# spell a spec path that does not exist, INCLUDING this comment. That is why the move
# above is described by its destination instead of quoted from its source. The decoder
# forge gate below had the mirror-image problem — it needed to quote what it forbade —
# and `code_grep` solved that one; nothing can solve this one, because the forbidden
# string is the citation itself.
#
# `SCRATCHPAD.md` and `specs/archive/**` are EXCLUDED, and not for convenience.
# AGENTS.md makes the worklog append-only and the archived specs closed records: an
# entry citing a spec's old path was TRUE when it was written, and editing it would
# falsify the record. Those files legitimately name paths that no longer exist, so a
# gate over them would demand a lie. Measured consequence, worth knowing: with the two
# exclusions applied, the vt-toolkit spec's old path is the ONLY stale one in the tree —
# every other archived spec is cited by its old path in the worklog and the archive
# alone. The exclusions hide nothing a live reader would follow.
#
# Existence means TRACKED (`git ls-files`), not present (`-e`): an untracked local file
# would pass here and fail in CI, which is the same failure one commit later.
#
# `specs/<slug>.md` in AGENTS.md is the one deliberate placeholder and needs no
# exemption — `<` is outside the character class, so it never matches. Measured too:
# no occurrence anywhere is preceded by a path character, so the unanchored match
# cannot currently be satisfied by a longer word ending in `specs/`.
spec_cites="$(git grep -h -o -E 'specs/[A-Za-z0-9._/-]*[.]md' \
  -- ':!SCRATCHPAD.md' ':!specs/archive' | sort -u)"
# A matcher that stops matching makes this gate pass by finding nothing — the exact
# failure mode the existence-check loop at the top of this file guards against for
# PATHS, and that loop cannot guard a regex. AGENTS.md, THEOREMS.md and this file all
# cite specs, so an empty result means the extraction broke, not that the tree is clean.
[ -n "$spec_cites" ] \
  || fail "no specs/*.md citation found in the tree — the extraction regex broke, and this gate is now passing vacuously"
spec_bad=0
# Deliberate word split, as with `code_grep`'s file list: no path here has a space.
# shellcheck disable=SC2086
for sc in $spec_cites; do
  if [ -n "$(git ls-files -- "$sc")" ]; then continue; fi
  spec_bad=1
  printf '  %s is cited but does not exist:\n' "$sc" >&2
  git grep -n -F "$sc" -- ':!SCRATCHPAD.md' ':!specs/archive' >&2 || true
done
[ "$spec_bad" -eq 0 ] \
  || fail "a cited specs/*.md path does not exist — archiving a spec orphans its citations, so move the citations in the same commit as the file (SCRATCHPAD.md and specs/archive/ are exempt: their entries were true when written)"

# E2E `partial def` ratchet: the sibling of RUNTIME_PARTIAL_CAP above, for the same
# reason (the keyword creeps back by habit) and covering the files its glob misses.
# All three are honest. `E2E/Harness.drain` and `LingerTest.drain` recur on a
# wall-clock deadline, and `RemoteLive.stripCsi` was MEASURED not assumed: rewriting
# it around `List.dropWhile` STILL fails the termination check, because the recursion
# is on a dropWhile-then-drop of a tail, not a structural sub-term. Shedding it needs
# a real `decreasing_by` — proof work, not cleanup, and AGENTS.md rules out a fuel
# parameter. The cap was 5 while only 3 existed: `leanFiles` and `stripComments` were
# the text-based coverage scanner's, deleted with it in step 2, and a cap holding
# slots for deleted code is a cap that has stopped biting.
E2E_PARTIAL_CAP=3
ep_n="$(code_count 'partial def' 'E2E/*' 'LingerTest.lean')"
[ "$ep_n" -le "$E2E_PARTIAL_CAP" ] \
  || fail "E2E/ grew to $ep_n partial defs (cap $E2E_PARTIAL_CAP); a do-block loop does not need the keyword"

printf 'gates OK — purity, the OS and unsafe surfaces, the Vt friend set, the runtime ties, spec citations, the prior-art shape, and the ratchets\n'
