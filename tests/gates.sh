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
         Linger/Core/Session.lean Linger/Core/Replay.lean Linger/Core/Title.lean \
         Linger/Runtime Linger/Runtime/Client.lean Linger/Runtime/Daemon.lean \
         Linger/Runtime/Command.lean Theorems/Title.lean Theorems/TerminalTitle.lean \
         Theorems Theorems/Session.lean Theorems/Replay.lean Tests E2E \
         Tools/Resurrect.lean Theorems/Resurrect.lean Manager/Resurrect.lean \
         Tools/Key.lean Tools/Fuzzy.lean Tools/Picker.lean Tools/Input.lean \
         Tools/Entry.lean Theorems/Entry.lean \
         Theorems/Picker.lean Theorems/Input.lean Theorems/Key.lean \
         Main.lean Manager/Picker.lean E2E/Manager.lean \
         LingerTest.lean c/shim.c lakefile.lean lake-manifest.json README.md; do
  [ -e "$p" ] || fail "$p is gone — a gate below would pass by matching nothing"
done

! code_grep 'sorry' 'Linger/Core/*' 'Tools/*' 'Theorems/*' || fail "sorry found"
! code_grep 'sorryAx' 'Linger/Core/*' 'Tools/*' 'Theorems/*' || fail "sorryAx found"
! code_grep '(^|[^[:alnum:]_])partial def([^[:alnum:]_]|$)' 'Linger/Core/*' 'Tools/*' \
  || fail "partial def in pure core"
! code_grep ': *IO ' 'Linger/Core/*' 'Tools/*' || fail "IO in pure core"
# Proofs must reduce in the kernel, never by compiled evaluation: a
# `native_decide` in Theorems/ would trust the compiler + `Decidable`
# instance instead of the kernel, and (unlike the tests, where evaluating
# golden bytes is the point) that is a hole in a *proof*. THEOREMS.md's
# "Reading a row" makes this a promise; this makes it enforced.
! code_grep '(^|[^[:alnum:]_])native_decide([^[:alnum:]_]|$)' 'Theorems/*' \
  || fail "native_decide in a proof (Theorems/)"
# the OS surface stays where AGENTS.md says it is
[ "$(code_grep '@[[]extern' '*.lean' | awk -F: '!seen[$1]++ { print $1 }' | tr -d ' ')" = "Linger/Posix.lean" ] \
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
# Lean/libuv may have worker threads when the application forks. The child
# paths and their two execution helpers must not allocate, format through
# stdio, mutate the environment, or use execvp's libc internals. Inventory the
# regions as well: deleting a marker must fail rather than checking nothing.
# This is a source guard for the listed calls, not a whole-program safety proof.
awk '
  /^static void (spawn_fail|exec_search)\(/ { helper = 1; helpers++ }
  /^    if \(pid == 0\) \{/ { child = 1; children++ }
  helper || child {
    if ($0 ~ /(^|[^[:alnum:]_])(malloc|calloc|realloc|free|getenv|setenv|putenv|execvp|snprintf|printf|strerror|lean_[[:alnum:]_]+)[[:space:]]*\(/) {
      print "  forbidden call after fork at " FNR ": " $0
      failed = 1
    }
  }
  helper && /^}/ { helper = 0 }
  child && /^    }/ { child = 0 }
  END {
    if (helpers != 2 || children != 2) {
      print "  fork guard expected two helpers and two child blocks, saw " helpers ", " children
      failed = 1
    }
    exit failed
  }' c/shim.c >&2 || fail "fork child call boundary changed"
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
# Linger/Core/{Vt,Render,Terminal,Replay}.lean, and the claim worth having is that its
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
# silent one. Vt imports nothing; Render imports Vt; Terminal and Replay import
# Render. The `import all Linger.Core.Vt` lines grant access within the sealed
# toolkit. Because Vt is a leaf, these four headers define the whole closure.
import_re='^[[:space:]]*((public|private|meta)[[:space:]]+)*import[[:space:]]+'
module_imports() {
  # Imports precede the module body. Stop at `public section` so a later
  # multiline help string such as "import [SAVE]" is not a module dependency.
  code_grep "$import_re|^[[:space:]]*public[[:space:]]+section([[:space:]]|$)" "$@" \
  | awk -F: '
      $3 ~ /^[[:space:]]*public[[:space:]]+section([[:space:]]|$)/ { body[$1] = 1; next }
      !body[$1] { print }'
}
import_closure() {
  # Read through `code_grep`: a backticked quotation cannot satisfy the gate.
  # Include leading whitespace, because an indented import still compiles.
  # ';'-joined to keep the diagnostic one line.
  tk_got="$(module_imports "$1" | sed 's/^[^:]*:[0-9]*://' | tr '\n' ';')"
  [ "$tk_got" = "$2" ] || { \
    printf '  %s import lines:\n' "$1" >&2; \
    { module_imports "$1" >&2 || printf '    (none)\n' >&2; }; \
    printf '  want: %s\n   got: %s\n' "${2:-(no imports)}" "${tk_got:-(no imports)}" >&2; \
    fail "$1 left its declared import closure — review the library boundary"; }
}
import_closure Linger/Core/Vt.lean ''
import_closure Linger/Core/Render.lean \
  'public import Linger.Core.Vt;import all Linger.Core.Vt;'
import_closure Linger/Core/Terminal.lean \
  'public import Linger.Core.Render;import all Linger.Core.Vt;'
import_closure Linger/Core/Replay.lean \
  'public import Linger.Core.Render;import all Linger.Core.Vt;'

# Named targets must build the promised roots, not just happen to succeed.
# Read declaration lines through code_grep, then compare their verbatim Name
# literals: multiple backticks on a roots line are Lean syntax, not prose.
library_roots() {
  lr_got="$(code_grep '^lean_lib |^[[:space:]]+#[[]' lakefile.lean \
    | sed 's/^[^:]*:[0-9]*://' \
    | awk -v lib="$1" '
        $1 == "lean_lib" { active = ($2 == lib) }
        active { $1 = $1; printf "%s ", $0 }')"
  [ "$lr_got" = "lean_lib $1 where roots := $2 " ] \
    || fail "$1 lost its independent library roots: $lr_got"
}
library_roots LingerVt '#[`Linger.Core.Terminal, `Linger.Core.Replay]'
library_roots LingerVtTheorems '#[`Theorems.Terminal, `Theorems.TerminalTitle, `Theorems.Replay]'
library_roots LingerInput '#[`Tools.Input]'
library_roots LingerInputTheorems '#[`Theorems.Input]'
library_roots LingerFuzzy '#[`Tools.Fuzzy]'

# Check every member of the proof family, not only the root headers: an
# intermediate renderer lemma must not pull session policy into the VT target.
module_imports Theorems/Vt.lean Theorems/Terminal.lean Theorems/TerminalTitle.lean \
  Theorems/Replay.lean Theorems/Render.lean 'Theorems/Render/*' \
| awk -F: '
  { mod = $3
    sub(/^[[:space:]]*((public|private|meta)[[:space:]]+)*import[[:space:]]+(all[[:space:]]+)?/, "", mod)
    sub(/[[:space:]]+--.*/, "", mod); sub(/[[:space:]]+$/, "", mod)
    if (mod !~ /^(Linger[.]Core[.](Vt|Render|Terminal|Replay)|Theorems[.](Vt|Terminal|TerminalTitle|Replay|Render([.][[:alnum:]_]+)*)|Init[.]Data[.]String[.](Legacy|Lemmas[.](TakeDrop|IsEmpty)))$/) {
      print "  " $0; bad = 1
    }
  }
  END { exit bad }' >&2 || fail "the VT proofs import outside the standalone library boundary"

# Entry and manager policies have explicit, small import closures. Main
# composes their executors with the session backend. The session library never
# imports them, even through an intermediate module: every library import
# stays in Linger or the one standard-library dependency owned by Posix.
import_closure Tools/Resurrect.lean 'public import Linger.Core.Name;'
import_closure Tools/Key.lean 'public import Tools.Input;'
import_closure Tools/Fuzzy.lean ''
import_closure Tools/Picker.lean 'public import Tools.Key;public import Tools.Fuzzy;public import Linger.Core.Name;public import Linger.Core.Listing;'
import_closure Tools/Input.lean ''
import_closure Theorems/Input.lean 'public import Tools.Input;import all Tools.Input;'
import_closure Tools/Entry.lean ''
import_closure Linger/Core/Name.lean ''
import_closure Linger/Core/Remote.lean 'public import Linger.Core.Name;'
import_closure Linger/Core/Title.lean 'public import Linger.Core.Name;'
import_closure Linger/Runtime/Command.lean ''
import_closure Manager/Resurrect.lean 'public import Tools.Resurrect;public import Linger.Core.Remote;'
import_closure Manager/Picker.lean \
  'public import Tools.Picker;public import Tools.Input;public import Linger.Posix;public import Linger.Core.Terminal;public import Linger.Runtime.Command;'
import_closure Main.lean \
  'public import Linger.Runtime.Cli;public import Linger.Runtime.Resume;public import Tools.Entry;public import Manager.Picker;public import Manager.Resurrect;'
module_imports 'Linger/*' Linger.lean \
| awk -F: '
  { mod = $3
    sub(/^[[:space:]]*((public|private|meta)[[:space:]]+)*import[[:space:]]+(all[[:space:]]+)?/, "", mod)
    sub(/[[:space:]]+--.*/, "", mod); sub(/[[:space:]]+$/, "", mod)
    if (mod !~ /^(Linger([.][[:alnum:]_]+)*|Std[.]Async[.]System)$/) {
      print "  " $0; bad = 1
    }
  }
  END { exit bad }' >&2 || fail "the session library imports outside its declared closure"

# Pure route proofs do not observe terminal IO or inspect Main's call sites.
# Pin dispatch before terminal observations, exact argv and executable identity;
# E2E.Manager and E2E.Recipes exercise these same boundaries in subprocesses.
for claim in route_bare_help route_selector_iff route_session_argv \
             route_select_operands route_daemon_argv route_ls_argv route_import_argv; do
  code_grep "^theorem $claim " Theorems/Entry.lean >/dev/null \
    || fail "entry-point contract disappeared: $claim"
done
# Fold layout whitespace for Main's small dispatch. Reuse the backtick-aware
# matcher below, so quoted prose cannot stand in for these call sites.
entry_code="$(awk '{ $1 = $1; printf "%s ", $0 }' Main.lean)"
for tie in \
  'def main [(]args : List String[)] : IO UInt32 := do try match Tools[.]Entry[.]route args with' \
  '[|] [.]selector => Manager[.]Picker[.]run [(]← IO[.]appPath[)][.]toString' \
  '[|] [.]importSave rest => Manager[.]Resurrect[.]run [(]← IO[.]appPath[)][.]toString rest' \
  '[|] [.]session argv => Linger[.]Runtime[.]Cli[.]main Linger[.]Runtime[.]Resume[.]hooks argv'; do
  printf '%s\n' "$entry_code" | CG_RE="(^|[[:space:]])$tie([[:space:]]|$)" awk "$CODE_AWK" >/dev/null \
    || fail "entry point bypassed its proved route or fixed IO boundary: $tie"
done

# The proof covers the returned parser/plan values. These call-site gates make
# bypassing them a reviewable change; IO tests check preflight/failure ordering
# and actual argv. As with the runtime ties below, this is not an IO theorem.
for claim in diagnostic_printable diagnostic_eq_self \
             parseSave_valid parseRow_command_valid parseRow_command_irrelevant \
             mem_plan plan_order plan_sequential_idempotent; do
  code_grep "^(private )?theorem $claim " Theorems/Resurrect.lean >/dev/null \
    || fail "importer contract disappeared: $claim"
done
code_grep '^[[:space:]]+IO[.]eprintln s!"linger import: [{]diagnostic [(]toString e[)][}]"$' Manager/Resurrect.lean >/dev/null \
  || fail "importer no longer displays the proved control-free diagnostic"
code_grep '^[[:space:]]+let panes ← IO[.]ofExcept [(]parseSave home [(]← IO[.]FS[.]readFile save[)][)]$' Manager/Resurrect.lean >/dev/null \
  || fail "importer no longer consumes the proved whole-save parser"
code_grep '^[[:space:]]+for pane in plan existing panes do$' Manager/Resurrect.lean >/dev/null \
  || fail "importer no longer iterates the proved import plan"
import_code="$(awk '{ $1 = $1; printf "%s ", $0 }' Manager/Resurrect.lean)"
printf '%s\n' "$import_code" | CG_RE='(^|[[:space:]])let created ← IO[.]Process[.]output [{] cmd := executable, args := #[[]"run", pane[.]name, "true"[]], cwd := some [(]System[.]FilePath[.]mk [(]absolute pane[.]dir[)][)], env [}] unless created[.]exitCode == 0 do throw [(]IO[.]userError s!"could not create session: [{]pane[.]name[}]: [{]created[.]stdout[}][{]created[.]stderr[}]"[)]([[:space:]]|$)' awk "$CODE_AWK" >/dev/null \
  || fail "importer bypasses planned creation argv/cwd, captured output or its diagnostic catch"
code_grep '^[[:space:]]+importSave executable args[.]head[?]$' Manager/Resurrect.lean >/dev/null \
  || fail "importer no longer forwards the entry point executable"
code_grep '^[[:space:]]+let listing ← IO[.]Process[.]output [{] cmd := executable, args := #[[]"ls", "--porcelain"[]], env [}]$' Manager/Resurrect.lean >/dev/null \
  || fail "importer no longer lists with the supplied executable"

# Selector and decoder proofs concern pure values. Tie each IO consumer to the
# proved function and retain exact attach argv and an immutable poll snapshot.
# E2E.Manager drives the terminal lifetime, failure paths and handoff itself.
for claim in align_optimal align_isSome_iff_sublist align_marks_length align_spells \
             align_score_max align_earliest align_default \
             alignWith_optimal alignWith_isSome_iff_sublist alignWith_marks_length \
             alignWith_spells alignWith_score_max alignWith_earliest \
             alignWith_scoring_irrelevant alignWith_smart_sensitive alignWith_smart_insensitive; do
  code_grep "^theorem $claim " Theorems/Fuzzy.lean >/dev/null \
    || fail "fuzzy alignment contract disappeared: $claim"
done
for claim in matches_iff_sublist align_isSome_iff_matches visible_order parseListing_valid parseSnapshot_complete \
             parseSnapshot_rejects presentation_existing presentation_existing_humanRow \
             presentation_creation highlightedPresentation_projection \
             highlightedPresentation_existing_humanRow highlightedPresentation_creation \
             highlightedPresentation_existing_marked_iff emphasizeCells_at emphasizeCells_projection \
             markPiece_marked_iff items_existing_prefix \
             mem_items_create step_stay_valid step_attach_mem step_create_iff \
             step_create_valid step_init_empty step_cancel refresh_query refresh_candidates \
             refresh_valid refresh_selected refresh_missing; do
  code_grep "^(private )?theorem $claim([[:space:]]|:)" Theorems/Picker.lean >/dev/null \
    || fail "selector contract disappeared: $claim"
done
for claim in feed_storage_bound feed_text_valid feed_paste_only_text feed_control flush_no_enter; do
  code_grep "^(private )?theorem $claim " Theorems/Input.lean >/dev/null \
    || fail "input contract disappeared: $claim"
done
for claim in ofInput_control_iff feed_byte_bindings feed_paste_no_commands feed_ctrl_r flush_no_accept; do
  code_grep "^theorem $claim " Theorems/Key.lean >/dev/null \
    || fail "selector binding contract disappeared: $claim"
done
for tie in \
  'let incoming ← IO[.]ofExcept [(]Tools[.]Picker[.]parseSnapshot result[.]stdout[)]' \
  'let items := Tools[.]Picker[.]items state[.]candidates state[.]query' \
  'let mut state := Tools[.]Picker[.]init [[]]' \
  'let mut decoder := Tools[.]Input[.]init' \
  'match Tools[.]Picker[.]step state key with' \
  'let cells := Linger[.]Core[.]Vt[.]charWidth c' \
  'let fds := #[[]stdinFd[]]' \
  'let events := #[[]POLLIN[]]' \
  'let ready ← poll fds events 50' \
  'let frame := draw state snapshot loaded withColor current[.]1 current[.]2' \
  'let withColor := [(]← IO[.]getEnv "NO_COLOR"[)][.]isNone' \
  'writeAll stdoutFd [(]ByteArray[.]mk [(]Linger[.]Core[.]Terminal[.]Title[.]ansi "linger"[)][.]toArray[)]' \
  'writeAll stdoutFd [(]ByteArray[.]mk [(]Linger[.]Core[.]Terminal[.]Title[.]ansi ""[)][.]toArray[)]' \
  'writeAll stdoutFd frame[.]toUTF8' \
  'discard child[.]wait' \
  'let child ← IO[.]Process[.]spawn [{] cmd := executable, args := #[[]"attach", target[]] [}]'; do
  code_grep "^[[:space:]]+$tie$" Manager/Picker.lean >/dev/null \
    || fail "manager bypassed a proved value or fixed IO boundary: $tie"
done
picker_code="$(awk '{ $1 = $1; printf "%s ", $0 }' Manager/Picker.lean)"
# Pin traversal through shared row pieces, frame insertion and complete metadata
# replacement. Computing rows or refreshed state without consuming them is
# insufficient. The loop seams fix draw, poll/decode/step, then refresh ordering.
# A completed snapshot must not replace the target underneath an unread key.
# Preserve byte order and consume both decoder results through the proved
# application binding before dispatch.
for tie in \
  'for byte in bytes[.]toList do let [(]next, emitted[)] := Tools[.]Input[.]feed decoder byte decoder := next keys := keys [+][+] [(]emitted[.]filterMap Tools[.]Key[.]ofInput[)][.]toArray else if Tools[.]Input[.]pending decoder && [(]← monotonicMs[)] - lastInput ≥ 150 then let [(]next, emitted[)] := Tools[.]Input[.]flush decoder decoder := next keys := [(]emitted[.]filterMap Tools[.]Key[.]ofInput[)][.]toArray for key in keys do' \
  'let nameCol := Linger[.]Core[.]Listing[.]nameWidth [(]snapshot[.]candidates[.]map fun target => [[][(]"name", target[)][]][)]' \
  'let mut index := start for item in [(]items[.]drop start[)][.]take slots do let chosen := index == state[.]cursor let selection := if chosen then "\\x1b[[]7m" else "" let mut pieces := #[[][(]if chosen then " ▸ " else " ", selection[)][]] let chars := Tools[.]Picker[.]highlightedPresentation snapshot nameCol state[.]query item for char in Tools[.]Picker[.]emphasizeCells chars do let statusStyle := if withColor then [(]char[.]status[.]map Linger[.]Core[.]Status[.]style[)][.]getD "" else "" let emphasis := if char[.]matched then "\\x1b[[]4m" else "" pieces := pieces[.]push [(]String[.]singleton char[.]char, selection [+][+] statusStyle [+][+] emphasis[)] lines := lines[.]push pieces index := index [+] 1' \
  'let mut frame := "\\x1b[[]0m\\x1b[[]H\\x1b[[]2J" let mut first := true for line in lines do if !first then frame := frame [+][+] "\\r\\n" first := false let mut used := 0 let mut clipped := false let mut activeStyle := "" for [(]text, style[)] in line do if clipped then break if style != activeStyle then frame := frame [+][+] "\\x1b[[]0m" [+][+] style activeStyle := style for raw in text[.]toList do let c := if raw[.]toNat < 0x20 [|][|] [(]raw[.]toNat ≥ 0x7F && raw[.]toNat < 0xA0[)] then '"'"'[?]'"'"' else raw let cells := Linger[.]Core[.]Vt[.]charWidth c if used [+] cells > width then clipped := true break frame := frame[.]push c used := used [+] cells if !activeStyle[.]isEmpty then frame := frame [+][+] "\\x1b[[]0m" return frame' \
  'let next := if loaded then Tools[.]Picker[.]refresh state incoming[.]candidates else [{] [(]Tools[.]Picker[.]init incoming[.]candidates[)] with query := state[.]query [}] dirty := dirty [|][|] !loaded [|][|] next != state [|][|] incoming != snapshot state := next snapshot := incoming loaded := true nextListing := [(]← monotonicMs[)] [+] 1000' \
  'while true do let current ← winsizeGet stdoutFd if dirty [|][|] current != size then let frame := draw state snapshot loaded withColor current[.]1 current[.]2 if frame != lastFrame [|][|] current != size then writeAll stdoutFd frame[.]toUTF8 lastFrame := frame size := current dirty := false let ready ← poll fds events 50' \
  'for key in keys do if !loaded && key == [.]accept then continue match Tools[.]Picker[.]step state key with [|] [.]stay next => dirty := dirty [|][|] next != state state := next [|] [.]attach target [|] [.]create target => return [.]attach target [|] [.]cancel => return [.]cancel if let some result[[:space:]]*← Linger[.]Runtime[.]Command[.]poll pending then' \
  'nextListing := [(]← monotonicMs[)] [+] 1000 if [(]← pending[.]get[)][.]isNone && [(]← monotonicMs[)] ≥ nextListing then pending[.]set [(]some [(]← Linger[.]Runtime[.]Command[.]start executable #[[]"ls", "-r", "--porcelain"[]][)][)] return [.]cancel finally' \
  'finally Linger[.]Runtime[.]Command[.]stop pending' \
  '[|] [.]attach target [|] [.]create target => return [.]attach target'; do
  printf '%s\n' "$picker_code" | CG_RE="(^|[[:space:]])$tie([[:space:]]|$)" awk "$CODE_AWK" >/dev/null \
    || fail "manager lost its selection, refresh, process ownership or attach contract: $tie"
done
code_grep '^[[:space:]]+cmdAttach hooks Linger[.]Core[.]Name[.]defaultName [[]]$' Linger/Runtime/Cli.lean >/dev/null \
  || fail "attach no longer shares the proved default session name with selection"

# Both terminal loops own their helper through this one executor. Reap only
# after both pipes close; clear ownership before a reader error can throw.
# Cancellation signals the isolated group before reaping its reserved leader
# PID, then joins both readers even when termination or reaping throws.
command_code="$(awk '{ $1 = $1; printf "%s ", $0 }' Linger/Runtime/Command.lean)"
for tie in \
  'IO[.]Process[.]spawn [{] cmd := executable, args, stdin := [.]null, stdout := [.]piped, stderr := [.]piped, setsid := true [}] let stdout ← IO[.]asTask child[.]stdout[.]readToEnd Task[.]Priority[.]dedicated let stderr ← IO[.]asTask child[.]stderr[.]readToEnd Task[.]Priority[.]dedicated return [{] child, stdout, stderr [}]' \
  'def poll [(]pending : IO[.]Ref [(]Option Job[)][)] : IO [(]Option IO[.]Process[.]Output[)] := do if let some job[[:space:]]*← pending[.]get then if [(]← IO[.]hasFinished job[.]stdout[)] && [(]← IO[.]hasFinished job[.]stderr[)] then if let some exitCode[[:space:]]*← job[.]child[.]tryWait then pending[.]set none let stdout ← IO[.]ofExcept [(]← IO[.]wait job[.]stdout[)] let stderr ← IO[.]ofExcept [(]← IO[.]wait job[.]stderr[)] return some [{] exitCode, stdout, stderr [}] return none' \
  'if let some job[[:space:]]*← pending[.]get then pending[.]set none try try job[.]child[.]kill finally discard job[.]child[.]wait finally discard <[|] IO[.]wait job[.]stdout discard <[|] IO[.]wait job[.]stderr'; do
  printf '%s\n' "$command_code" | CG_RE="(^|[[:space:]])$tie([[:space:]]|$)" awk "$CODE_AWK" >/dev/null \
    || fail "owned command lost its process or pipe lifetime contract: $tie"
done

# Pure rendering and summary claims cannot see CLI/terminal IO. Pin the actual
# consumers: validated host order, one shared row, palette-only badge styling,
# and plain redirected or NO_COLOR output. Prompt sampling shares one reply deadline; a busy
# nonblocking connect remains unknown and cannot authorize stale-socket removal.
for claim in style_palette attentionCounts_exact attentionCounts_mem summary_exact \
             summary_omits_zero summary_alphabet summary_printable; do
  code_grep "^theorem $claim " Theorems/Status.lean >/dev/null \
    || fail "status presentation contract disappeared: $claim"
done
for claim in rowPieces_printable rowPieces_styles rowPieces_nameSpan nameWidth_covers \
             renderPieces_plain terminalListing_plain; do
  code_grep "^theorem $claim " Theorems/Listing.lean >/dev/null \
    || fail "shared listing contract disappeared: $claim"
done
cli_code="$(awk '{ $1 = $1; printf "%s ", $0 }' Linger/Runtime/Cli.lean)"
for tie in \
  'match Linger[.]Core[.]Remote[.]checkHosts hosts with [|] [.]ok l => return l [|] [.]error e => throw [(]IO[.]userError e[)]' \
  'for host in remotes do for [(]rname, rlive, rcmd, rstatus[)] in ← listRemote host do' \
  '[|] some [(]porcelain, remoteFlag[)] => cmdList porcelain [(]← resolveRemotes remoteFlag[)]' \
  'let withColor := [(]← [(]← IO[.]getStdout[)][.]isTty[)] && [(]← IO[.]getEnv "NO_COLOR"[)][.]isNone writeAll stdoutFd [(]ByteArray[.]mk [(]Linger[.]Core[.]Listing[.]terminalListing withColor rows[)][.]toArray[)]' \
  'let rows ← localRows [(]some [(][(]← monotonicMs[)] [+] 250[)][)] let summary := Linger[.]Core[.]Status[.]summary [(]rows[.]map fun info => Linger[.]Core[.]Status[.]ofName [(][(]info[.]lookup "status"[)][.]getD "unknown"[)][)] if !summary[.]isEmpty then IO[.]println summary return 0' \
  'if let some deadline := stopAt then if [(]← monotonicMs[)] ≥ deadline then return some [(][.]error [(]IO[.]userError "overview deadline reached"[)][)] match ← Client[.]connect name stopAt[.]isSome with [|] none => if stopAt[.]isSome then return some [(][.]error [(]IO[.]userError "overview connection unavailable"[)][)] return none [|] some fd => try let info ← [(]readInfo fd stopAt[)][.]toBaseIO return some info finally close fd' \
  'Client[.]sendMsg fd [.]info let deadline := stopAt[.]getD [(][(]← monotonicMs[)] [+] 2000[)]' \
  'while go && [(]← monotonicMs[)] < deadline do let remaining := deadline - [(]← monotonicMs[)] let revs ← poll #[[]fd[]] #[[]POLLIN[]] [(]Int32[.]ofNat [(]min 100 remaining[)][)]' \
  'match ← queryInfo name stopAt with [|] some info => confirmedLive := confirmedLive [+][+] [[]name[]] rows := rows [+][+] [[]liveRow name [(]info[.]toOption[.]getD [[][]][)][]] [|] none => if ![(]← removeStaleSocket name[)] then'; do
  printf '%s\n' "$cli_code" | CG_RE="(^|[[:space:]])$tie([[:space:]]|$)" awk "$CODE_AWK" >/dev/null \
    || fail "listing or prompt bypassed its shared policy: $tie"
done
code_grep '^[[:space:]]+let r ← unixConnect path nonblocking$' Linger/Runtime/Client.lean >/dev/null \
  || fail "status connect lost its nonblocking boundary"

# Title writes use the bounded, control-free encoder and the existing VT
# observer. Observe raw application bytes only, reassert repeated OSC titles,
# and defer every injected title until the parser and UTF-8 decoder are idle.
code_grep '^theorem compose_parts ' Theorems/Title.lean >/dev/null \
  || fail "session title composition contract disappeared"
for claim in payload_safe ansi_payload_bound ansi_ends update_waits \
             update_nonempty_iff update_requires_boundary; do
  code_grep "^(public )?theorem $claim " Theorems/TerminalTitle.lean >/dev/null \
    || fail "title contract disappeared: $claim"
done
for claim in observe_append observe_no_history observe_dims observe_invariants \
             observe_esc_intermediates observe_escInter_pending observe_del_boundary \
             step_escInter_final_boundary; do
  code_grep "^(public )?theorem $claim " Theorems/Vt.lean >/dev/null \
    || fail "pending terminal sequence contract disappeared: $claim"
done
code_grep '^theorem leave_boundary_title ' Theorems/Render/Modes.lean >/dev/null \
  || fail "default title handback theorem disappeared"
client_code="$(awk '{ $1 = $1; printf "%s ", $0 }' Linger/Runtime/Client.lean)"
for tie in \
  'let mut observer := Linger[.]Core[.]Vt[.]Vt[.]init 1 1' \
  'while !leaving do try if let some output[[:space:]]*← Command[.]poll pending then let fresh := if output[.]exitCode == 0 then output[.]stdout[.]trimAscii[.]toString else String[.]singleton [(]Linger[.]Core[.]Status[.]icon [.]unknown[)] titleDirty := titleDirty [|][|] fresh != summary summary := fresh nextSummary := [(]← monotonicMs[)] [+] 1000 if [(]← pending[.]get[)][.]isNone && [(]← monotonicMs[)] ≥ nextSummary then pending[.]set [(]some [(]← Command[.]start self[.]toString #[[]"status"[]][)][)] catch _ => summary := String[.]singleton [(]Linger[.]Core[.]Status[.]icon [.]unknown[)] titleDirty := true nextSummary := [(]← monotonicMs[)] [+] 1000 let revs ← poll #[[]stdinFd, fd[]] #[[]POLLIN, POLLIN[]] 200' \
  'writeAll stdoutFd [(]ByteArray[.]mk payload[.]toArray[)] observer := observer[.]observe payload receivedOutput := true' \
  'if receivedOutput && titleDirty && !leaving then let title := Linger[.]Core[.]Title[.]compose name summary observer[.]windowTitle let bytes := Linger[.]Core[.]Terminal[.]Title[.]update observer title if !bytes[.]isEmpty then writeAll stdoutFd [(]ByteArray[.]mk bytes[.]toArray[)] titleDirty := false' \
  'try try writeAll stdoutFd [(]ByteArray[.]mk Linger[.]Core[.]Render[.]leaveAnsi[.]toArray[)] finally termRestore stdinFd saved finally Command[.]stop pending'; do
  printf '%s\n' "$client_code" | CG_RE="(^|[[:space:]])$tie([[:space:]]|$)" awk "$CODE_AWK" >/dev/null \
    || fail "attached title lost its observer, sampler or handback contract: $tie"
done
[ "$(code_count 'observer := observer[.]observe' Linger/Runtime/Client.lean)" -eq 1 ] \
  || fail "title observer must consume application output exactly once"
[ "$(code_count '(^|[[:space:]])observer([[:space:]]+:[^=]*)?[[:space:]]*(:=|←)' Linger/Runtime/Client.lean)" -eq 2 ] \
  || fail "title observer may only initialize once and consume application output"
awk '
  /receivedOutput := true/ { output = 1; next }
  output && /^[[:space:]]*--/ { next }
  output { if ($0 !~ /^[[:space:]]*titleDirty := true$/) bad = 1; output = 0; checked++ }
  END { exit (checked != 1 || bad) }
' Linger/Runtime/Client.lean \
  || fail "repeated application titles no longer trigger reassertion"

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
# The permitted region is an EXACT file list plus two directories, and that split
# is by edit frequency, measured: of 192 commits, 36 added a `.lean` under `Theorems/`
# or `Tests/` — about one commit in five — against 11 under `Linger/Core/`, only four of
# which are in the closure. So a per-file list over `Theorems/**` would be edited
# reflexively, while the core list changes rarely, which is what makes it a
# checkpoint. `Theorems/**` and `Tests/**` are friends BY DECLARATION (see
# `Linger/Core/Vt.lean`, "## Every door"), and `Tests/` deliberately forges invalid
# states in its negative fixtures, so listing its files one by one would gate a
# non-property. Everything else is outside and fail-closed — `E2E/**`,
# `LingerTest.lean`, `Main.lean`, `Linger/Posix.lean`, all of `Linger/Runtime/` and the
# other `Linger/Core/` modules. Replay joins only to read shared immutable rows.
# `E2E/**` is outside deliberately: a pty suite
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
VT_FRIEND_EXACT='Linger/Core/Vt.lean Linger/Core/Render.lean Linger/Core/Terminal.lean Linger/Core/Checkpoint.lean Linger/Core/Replay.lean'
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
# kinds of long-lived queue -- their caps, their drop and cut policies, and the
# removal of written prefixes (`Theorems/Buf.lean`) -- and `Linger/Runtime/*` is `IO`,
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

# The cursor proofs describe pure values. These ties keep the runtime on the
# captured snapshot, bounded advances and shared byte allowance. The delivery
# suite separately observes framing, prior/replay/live ordering and exit tails.
for claim in start_faithful next_faithful next_bounded next_progress steps_storage \
             drain_start; do
  code_grep "^(public )?theorem $claim " 'Theorems/Replay.lean' > /dev/null \
    || fail "replay claim $claim disappeared"
done
for claim in followingCap_front followingCap_frame followingCap_iff; do
  code_grep "^theorem $claim " Theorems/Buf.lean >/dev/null \
    || fail "shared buffer allowance claim $claim disappeared"
done
code_grep '^theorem onMsg_attach_snapshot ' 'Theorems/Session.lean' > /dev/null \
  || fail "the attach snapshot theorem disappeared"
code_grep '^theorem onMsg_attach_already ' 'Theorems/Session.lean' > /dev/null \
  || fail "the repeated-attach refusal theorem disappeared"
code_grep '^[[:space:]]+effs [+][+] [[][.]replay c[.]id [(]Replay[.]start s[.]vt[)][]] [+][+]$' 'Linger/Core/Session.lean' > /dev/null \
  || fail "attach no longer captures its resulting snapshot"
code_grep '^[[:space:]]+replay : Option Replay[.]Plan := none$' 'Linger/Runtime/Daemon.lean' > /dev/null \
  || fail "each connection must retain one optional replay cursor"
code_grep '^[[:space:]]+after : Buf := [.]empty$' 'Linger/Runtime/Daemon.lean' > /dev/null \
  || fail "following output bypasses the proved byte buffer"
code_grep '^[[:space:]]+[|] [.]replay id plan =>$' 'Linger/Runtime/Daemon.lean' > /dev/null \
  || fail "the runtime no longer receives the captured replay plan"
code_grep '^[[:space:]]+match ← flushConn [{] c with replay := some plan [}] with$' 'Linger/Runtime/Daemon.lean' > /dev/null \
  || fail "the runtime no longer executes the captured replay plan"
! code_grep 'Replay[.]start|Render[.]restore' 'Linger/Runtime/Daemon.lean' \
  || fail "the daemon must consume the captured cursor without constructing another repaint"
code_grep '^[[:space:]]+match Replay[.]next Linger[.]Core[.]Session[.]outputChunk plan with$' 'Linger/Runtime/Daemon.lean' > /dev/null \
  || fail "replay advancement no longer uses the proved output chunk"
code_grep '^def replayFrameCap : Nat := Linger[.]Core[.]Session[.]outputChunk [+] [(]Wire[.]encode [(][.]output [[][]][)][)][.]length$' 'Linger/Runtime/Daemon.lean' > /dev/null \
  || fail "replay reservation no longer includes the wire encoder's frame overhead"
code_grep '^[[:space:]]+let cap := followingCap outbufCap replayFrameCap [(]owedLen c[.]out[)]$' 'Linger/Runtime/Daemon.lean' > /dev/null \
  || fail "following output no longer shares the front buffer allowance"
code_grep '^[[:space:]]+bufEnqueue [(]outbufCap - owedLen c[.]after[)] [.]empty$' 'Linger/Runtime/Daemon.lean' > /dev/null \
  || fail "replay frames no longer account for following output debt"

# A logically closed peer still owns its transport until it drains or expires.
# It therefore counts towards admission, and ordinary polls must retire it
# before taking the fd snapshot. Deadlines use Nat and the same grace constant
# as shutdown. A repeated close cannot buy another grace period.
code_grep '^[[:space:]]+closeBy : Option Nat := none$' 'Linger/Runtime/Daemon.lean' > /dev/null \
  || fail "transport close deadlines no longer use Nat"
[ "$(code_count '^[[:space:]]+let deadline := [(]← IO[.]monoMsNow[)] [+] drainTimeoutMs$' 'Linger/Runtime/Daemon.lean')" -eq 2 ] \
  || fail "ordinary close and shutdown must share the Nat drain deadline"
code_grep '^[[:space:]]+if c[.]closeBy[.]any [(]now ≥ ·[)] then$' 'Linger/Runtime/Daemon.lean' > /dev/null \
  || fail "retired transport expiry no longer checks its fixed deadline"
code_grep '^[[:space:]]+return [(]rt[.]setConn [{] c with closeBy := some deadline [}], [[][.]closed id[]][)]$' 'Linger/Runtime/Daemon.lean' > /dev/null \
  || fail "logical close no longer reports removal while retaining accepted bytes"
awk '
  /^  [|] [.]close id =>/ { inclose = 1 }
  inclose && /if c[.]closing then/ { guarded = 1 }
  inclose && /if c[.]pending then/ { checked++; if (!guarded) bad = 1 }
  /^  [|] [.]writePty / { inclose = 0 }
  /^def pollRound / { inpoll = 1 }
  inpoll && /let rt ← expireConns rt now/ { expired = 1 }
  inpoll && /let polled := rt[.]conns/ { frozen++; if (!expired) bad = 1 }
  /^def drainConns / { inpoll = 0 }
  END { exit (checked != 1 || frozen != 1 || bad) }
' Linger/Runtime/Daemon.lean \
  || fail "repeated-close guard or expire-before-poll-snapshot ordering changed"
code_grep '^[[:space:]]+timeout := min timeout [(]deadline - now[)]$' 'Linger/Runtime/Daemon.lean' > /dev/null \
  || fail "ordinary polling ignores close deadlines"
code_grep '^[[:space:]]+#[[][(]if rt[.]conns[.]length < maxClients then POLLIN else 0[)],$' 'Linger/Runtime/Daemon.lean' > /dev/null \
  || fail "listener admission no longer counts every owned transport"
code_grep '^[[:space:]]+for _ in List[.]range [(]maxClients - rt[.]conns[.]length[)] do$' 'Linger/Runtime/Daemon.lean' > /dev/null \
  || fail "accept budget no longer includes retired transports"
[ "$(code_count '^[[:space:]]+let polled := rt[.]conns$' 'Linger/Runtime/Daemon.lean')" -eq 2 ] \
  || fail "ordinary and shutdown polling must each freeze their fd set"
[ "$(code_count '^[[:space:]]+for c in polled do$' 'Linger/Runtime/Daemon.lean')" -eq 2 ] \
  || fail "ordinary fd construction and readiness must use the same frozen connections"
code_grep '^[[:space:]]+let fds := [(]polled[.]map [(]·[.]fd[)][)][.]toArray$' 'Linger/Runtime/Daemon.lean' > /dev/null \
  || fail "shutdown fd list diverged from its frozen connections"
code_grep '^[[:space:]]+for [(]c, i[)] in polled[.]zipIdx do$' 'Linger/Runtime/Daemon.lean' > /dev/null \
  || fail "shutdown readiness no longer indexes the frozen connection list"
code_grep '^[[:space:]]+rt ← drainConns rt$' 'Linger/Runtime/Daemon.lean' > /dev/null \
  || fail "serve no longer drains accepted bytes after exit"

# A decoded close/exit stops its packet in the proved fold. Runtime feedback
# then retires the client before the next queued event, preserving effect order.
# The delivery suite distinguishes same-packet, queued and other-client closes.
for claim in feedMsgs_after_close feedMsgs_after_exit; do
  code_grep "^theorem $claim " 'Theorems/Session.lean' > /dev/null \
    || fail "decoded command stopping claim $claim disappeared"
done
awk '
  /^def pump / { inpump = 1 }
  inpump && /let mut feedback := \[\]/ { init++ }
  inpump && /feedback := feedback [+][+] more/ { collect++ }
  inpump && /queue := feedback [+][+] rest/ { consume++ }
  /^def pollRound / { inpump = 0 }
  END { exit (init != 1 || collect != 1 || consume != 1) }
' Linger/Runtime/Daemon.lean \
  || fail "effect feedback must precede queued events in effect order"

# An info answer can span several frames. The pure producer proves the bound;
# keep the IO accumulator on that same policy rather than a copied number.
code_grep '^theorem onMsg_info_bounded ' 'Theorems/Session.lean' > /dev/null \
  || fail "the info producer's framing theorem disappeared"
code_grep '^abbrev infoReplyCap : Nat := Linger[.]Core[.]Session[.]infoReplyCap$' 'Linger/Runtime/Cli.lean' > /dev/null \
  || fail "the CLI info policy diverged from the proved producer"
code_grep '^[[:space:]]+Linger[.]Core[.]Buf[.]bufOffer infoReplyCap acc [(]ByteArray[.]mk payload[.]toArray[)]$' 'Linger/Runtime/Cli.lean' > /dev/null \
  || fail "the info accumulator no longer uses the shared byte policy"

# The remote command crosses SSH's shell join. Keep the proved name alphabet
# on that actual argument, not only on local paths or a displayed listing row.
code_grep '^theorem sanitize_valid ' 'Theorems/Name.lean' > /dev/null \
  || fail "the sanitized-name alphabet theorem disappeared"
code_grep '^[[:space:]]+let sess := Linger[.]Core[.]Name[.]sanitize sess$' 'Linger/Runtime/Cli.lean' > /dev/null \
  || fail "remote attach no longer sanitizes its session argument"
printf '%s\n' "$cli_code" | CG_RE='(^|[[:space:]])let child ← IO[.]Process[.]spawn [{] cmd := "ssh", args := #[[]"-t", "--", host, "linger", "attach", sess[]] [}] try child[.]wait finally' awk "$CODE_AWK" >/dev/null \
  || fail "review the remote command argument and handback against sanitize_valid"
[ "$(code_count '^[[:space:]]+writeAll stdoutFd [(]ByteArray[.]mk Linger[.]Core[.]Render[.]leaveAnsi[.]toArray[)]$' Linger/Runtime/Cli.lean)" -eq 1 ] \
  || fail "remote SSH termination no longer establishes canonical handback"

# `onMsg_resizePty_agrees` connects every emitted pty size to the resulting
# emulator's effective dimensions. IO is outside the theorem: keep the effect
# interpreter forwarding those exact dimensions, in order. Both ends are
# checked so deleting the claim cannot silently leave a decorative runtime tie.
code_grep '^theorem onMsg_resizePty_agrees ' 'Theorems/Session.lean' > /dev/null \
  || fail "the session-to-pty geometry correspondence theorem disappeared"
code_grep '^[[:space:]]+[|] [.]resizePty cols rows =>' 'Linger/Runtime/Daemon.lean' > /dev/null \
  || fail "review the pty effect interpreter against onMsg_resizePty_agrees"
code_grep '^[[:space:]]+winsizeSet rt[.]ptyFd cols rows$' 'Linger/Runtime/Daemon.lean' > /dev/null \
  || fail "the pty interpreter no longer forwards the proved dimensions in order"

# The elapsed-time theorems use Nat. Keep the actual monotonic source and the
# daemon tick on that representation; narrowing here is invisible to the proofs.
code_grep '^theorem step_tick_before_interval ' 'Theorems/Session.lean' > /dev/null \
  || fail "the no-early-checkpoint theorem disappeared"
code_grep '^theorem step_tick_checkpoint_elapsed ' 'Theorems/Session.lean' > /dev/null \
  || fail "the checkpoint elapsed-time theorem disappeared"
code_grep '^def monotonicMs : IO Nat := IO[.]monoMsNow$' 'Linger/Posix.lean' > /dev/null \
  || fail "the monotonic clock no longer forwards Lean's Nat clock directly"
code_grep '^[[:space:]]+let now ← monotonicMs$' 'Linger/Runtime/Daemon.lean' > /dev/null \
  || fail "the daemon tick no longer reads the monotonic clock"
code_grep "^[[:space:]]+rt ← pump rt' [(]events [+][+] [[][.]tick now[]][)]$" 'Linger/Runtime/Daemon.lean' > /dev/null \
  || fail "the daemon no longer forwards the monotonic value to the proved tick"

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

# Extensional reader theorems cannot distinguish reject-before-expansion from
# expand-then-reject. The latter passed every semantic check in the audit, and
# generated C confirmed that it allocated first. Pin these short guarded bodies
# and rVt's prefix through its first row read; ignore layout, but inventory every
# region so a missing declaration or terminator cannot pass.
awk '
  BEGIN {
    want["rList"] = "let(n,rest)←rNatlifmaxCount.all(funlimit=>n≤limit)thenrListAuxrnrestelsenone"
    want["rRLE"] = "let(groups,rest)←rList(rPairrNatr)bytesifmaxLength.all(funlimit=>(groups.mapProd.fst).sum≤limit)thensome(expandgroups,rest)elsenone"
    want["rVt"] = "let(cols,l)←rNatllet(rows,l)←rNatlifcols!=clampDimcols||rows!=clampDimrowsthennoneelsedolet(grid,l)←rList(funbytes=>rRowbytes(somecols))l(somerows)"
  }
  /^def (rList|rRLE|rVt) / {
    split($0, fields, " "); name = fields[2]
    seen[name]++; body = ""; collecting = 0
  }
  name != "" {
    line = $0
    if (!collecting) {
      if (!sub(/^.*(:= do|:= fun l => do)/, "", line)) next
      collecting = 1
    }
    gsub(/[[:space:]]/, "", line)
    body = body line
    if ((name == "rVt" && index(line, "let(grid,l)←") > 0) ||
        (name != "rVt" && line == "none")) {
      if (body != want[name]) {
        print "  " name ": checkpoint rejection must precede counted decoding or expansion"
        bad = 1
      }
      checked[name]++; name = ""
    }
  }
  END {
    for (region in want)
      if (seen[region] != 1 || checked[region] != 1) {
        print "  missing or repeated checkpoint guard region: " region
        bad = 1
      }
    exit bad
  }' Linger/Core/Checkpoint.lean >&2 || fail "checkpoint allocation guard changed"
code_grep '^[[:space:]]+let [(]cs, l[)] ← rRLE rCell l maxLength$' 'Linger/Core/Checkpoint.lean' > /dev/null \
  || fail "the row reader stopped forwarding its expansion bound"
code_grep '^[[:space:]]+let [(]rows, l[)] ← rList rRow l maxRows$' 'Linger/Core/Checkpoint.lean' > /dev/null \
  || fail "the history reader stopped forwarding its row bound"
code_grep '^[[:space:]]+let [(]rows, l[)] ← rList [(]fun bytes => rRow bytes maxCols[)] l maxRows$' 'Linger/Core/Checkpoint.lean' > /dev/null \
  || fail "the alternate screen reader stopped forwarding its dimensions"
code_grep '^[[:space:]]+let [(]tabs, l[)] ← rList rBool l [(]some cols[)]$' 'Linger/Core/Checkpoint.lean' > /dev/null \
  || fail "the checkpoint tab reader stopped using validated columns"
code_grep '^[[:space:]]+let [(]sb, l[)] ← rRing l [(]some sbCap[)]$' 'Linger/Core/Checkpoint.lean' > /dev/null \
  || fail "the checkpoint history reader stopped using its row cap"
code_grep '^[[:space:]]+let [(]altGrid, l[)] ← rAlt l [(]some cols[)] [(]some rows[)]$' 'Linger/Core/Checkpoint.lean' > /dev/null \
  || fail "the checkpoint alternate screen stopped using validated dimensions"

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
# untouched and the build green. The third (`4096` on `stepGround`'s `Good` proof)
# was real at that revision: line 730 hit the recursion limit without it.
# The audit's explicit Good.stepGround dispatch now proves each branch under
# the default limit. The last raise is gone. The `4096` on
# `renderable_stepGround` went with that proof's earlier `grind` rewrite.
# Same direction-of-travel rule as above: DOWN without discussion, up only as a signal
# to read. A raise here means a term got deeper, which is usually a dispatch that grew
# arms — the thing design-for-provability says to restructure rather than budget for.
RECDEPTH_CAP=0
rd_n="$(code_count 'set_option maxRecDepth' 'Theorems/*')"
[ "$rd_n" -le "$RECDEPTH_CAP" ] \
  || fail "maxRecDepth raises grew to $rd_n (cap $RECDEPTH_CAP); a term got deeper — read that, or re-measure and delete a stale one"

# runtime `partial def` ratchet. Five of the seven shed the keyword on 2026-08-18
# once someone checked: `while`/`for` in a `do` block never needed it, and none of
# the five self-recursed. `pump` became an explicit IO loop when exit acquired
# a queue-stop condition. `parseLs` now exposes its structurally smaller tail.
# Ratcheted so the keyword cannot creep back by habit.
RUNTIME_PARTIAL_CAP=0
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
    'tests/*.sh' 'c/shim.c' 'recipes/*' '.claude/*.sh' \
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

# The status glyphs are a user-facing contract of exactly seven characters, and README
# is where a user reads them. They drifted silently: `Status.icon` emitted `⣀` for idle
# while README printed `⡀` (one dot, not four), which no test could see — the suites
# compare against `Status.icon` itself, which is right for them and blind to this.
# So the gate is both directions: every glyph the code emits appears in README, and
# README shows no glyph the code cannot emit. The porcelain `Status.name` strings are
# not checked here because README does not list them; it says only that the same seven
# states appear as a `status` field, which `icon_injective`/`name_injective` carry.
#
# BOTH extractions assert their count, and the reverse one earned that the hard way:
# it first filtered the README side with `grep -vE '^[[:alnum:][:punct:][:space:]]$'`
# to drop non-glyph noise, but glibc classifies `⣀ ⣷ ⣿ ✓` as `[[:punct:]]`, so the
# filter deleted all seven and the loop body never ran. The gate reported "both
# directions" while only one existed, and the two break-verifications recorded for it
# had both landed on the forward half. A `for` over an empty list is the same vacuous
# pass the spec-citation gate above guards against, and it is why nothing here trusts
# an extraction it has not counted.
icon_glyphs="$(code_grep "^ *[|] [.][a-zA-Z]+ => '" 'Linger/Core/Status.lean' \
  | sed "s/.*=> '//; s/'.*//")"
icon_n="$(printf '%s\n' "$icon_glyphs" | grep -c .)"
[ "$icon_n" -eq 7 ] \
  || fail "extracted $icon_n status glyphs from Status.icon, expected the seven §Status states (a new state lands with its README row)"
# `set -f` for both loops, and it is load-bearing rather than tidy: two of the seven
# glyphs are `?` and `!`, and an UNQUOTED `$icon_glyphs` in a `for` undergoes pathname
# expansion — `?` matches any single-character name in the working directory, which in
# this repo is the `c/` directory, so the loop saw `c`. Downstream that read as
# "is `c` in README", which is trivially yes, so the `?` glyph silently went unchecked
# in the forward direction too. Found only because fixing the reverse loop surfaced it.
set -f
for g in $icon_glyphs; do
  grep -qF -- "$g" README.md \
    || fail "Status.icon emits '$g' but README does not show it — the glyph set is what a user reads"
done
set +f
# The reverse direction, scoped to the section that states the contract: a glyph in
# README that `icon` cannot emit is a state the code dropped and the docs kept.
readme_glyphs="$(sed -n '/^## Session status/,/^## Graphics/p' README.md \
  | grep -oE '`[^`]`' | tr -d '`')"
readme_n="$(printf '%s\n' "$readme_glyphs" | grep -c .)"
[ "$readme_n" -eq 7 ] \
  || fail "extracted $readme_n glyphs from README's §Session status, expected 7 (a single-character backtick added there breaks this on purpose — it is a seven-character contract)"
set -f
for g in $readme_glyphs; do
  printf '%s\n' "$icon_glyphs" | grep -qF -- "$g" \
    || fail "README shows glyph '$g' but Status.icon cannot emit it"
done
set +f

# Every declaration name THEOREMS.md cites must resolve to a declaration. This is
# gated rather than reviewed because reviewing it produced a FALSE CLEAN: the one-off
# check run in step 8 grepped each name with `git grep -w`, which matches prose and
# comments, so `scrollbackAnsi_le` — named by THEOREMS.md and by two code comments, and
# declared nowhere — satisfied it. A doc that promises a theorem is unfalsifiable until
# something looks for the declaration, so this looks for `theorem|lemma|def|abbrev`.
#
# Basenames, because a citation is written unqualified while the declaration sits in a
# namespace. CamelCase names (types, structures) and file/section names are skipped:
# the target here is the `snake_case` claim names, which is what a reader would try to
# look up. The count is asserted so a broken extraction fails instead of passing empty.
thm_cites="$(grep -oE '`[a-z][A-Za-z0-9_.]*`' THEOREMS.md | tr -d '`' \
  | grep '_' | grep -vE '[.](md|lean|sh)$' | sed 's/.*[.]//' | sort -u)"
thm_n="$(printf '%s\n' "$thm_cites" | grep -c .)"
[ "$thm_n" -ge 80 ] \
  || fail "extracted only $thm_n declaration citations from THEOREMS.md (expected ~100+); the pattern broke and this gate is passing vacuously"
thm_decls="$(git grep -hoE '^ *(public )?(private )?(theorem|lemma|def|abbrev) [A-Za-z][A-Za-z0-9_.]*' \
  -- '*.lean' | sed 's/.*[[:space:]]//; s/.*[.]//' | sort -u)"
thm_bad=0
for name in $thm_cites; do
  printf '%s\n' "$thm_decls" | grep -qxF -- "$name" && continue
  thm_bad=1
  printf '  THEOREMS.md cites `%s`, which is declared nowhere\n' "$name" >&2
done
[ "$thm_bad" -eq 0 ] \
  || fail "THEOREMS.md names a declaration that does not exist — state an absent proof as absent, not as a forward reference"

# The CI matrix. macOS came off the per-push path on 2026-09-15 for a cost reason
# measured in SCRATCHPAD.md — not repeated here, because that figure was copied into
# seven files and had already started to rot — but the decision reaches the matrix
# through a `fromJSON` job output, and actionlint does NOT
# check it — verified by mistyping it deliberately, which actionlint accepted. Two
# ways that goes wrong silently: someone simplifies the matrix to ubuntu only and
# macOS is never checked again, or drops the schedule and it never runs. Neither is
# a Lean property, so this is the same species of oracle as SHIM_CAP.
ci_yml='.github/workflows/ci.yml'
# The runtime tie, and the load-bearing one: `E2E/Ci.lean` tests
# `tests/ci-runners.sh`, and no Lean can see whether the workflow actually CALLS it.
# Re-inline the decision as a `case` in the YAML and the suite would keep passing
# against a script nothing runs. Same species as the `Buf` gate below.
#
# Match the INVOCATION, not the path: the first version of this grep looked for
# `ci-runners.sh` anywhere in the file, and the workflow's own comment names the
# script — so it passed with the call replaced by an inline `echo`. Break-verified
# after the fix.
grep -qE '(^|[^[:alnum:]_])sh[[:space:]]+tests/ci-runners[.]sh' "$ci_yml" \
  || fail "$ci_yml: the runner decision is not a call to tests/ci-runners.sh — E2E/Ci.lean would then be testing a script CI does not use"
[ -n "$(git ls-files -- tests/ci-runners.sh)" ] \
  || fail "tests/ci-runners.sh is not tracked — the workflow calls it, so a local-only copy passes here and fails in CI"
grep -qE '^ *os: [$][{][{] fromJSON[(]needs[.]gates[.]outputs[.]os[)] [}][}]$' "$ci_yml" \
  || fail "$ci_yml: the e2e matrix must use the tested runner decision through needs.gates.outputs.os"
# Semantic lint can build ordinary imports, but E2E.Coverage loads Main
# dynamically. On a cold checkout, lint before the full build misses Main and
# fails. Bind the ordering to the real commands rather than their step names.
awk '
  /^[[:space:]]+run: [.][/]tests[/]e2e[.]sh$/ { build = NR }
  /^[[:space:]]+pre-commit run --all-files/ { lint = NR }
  END { exit !(build && lint > build) }
' "$ci_yml" \
  || fail "$ci_yml: run ./tests/e2e.sh before pre-commit so semantic lint sees every compiled import"
# E2E.Ci exercises Lake's invalidation and cached warnings. The real verifier
# must use the same flags; otherwise those checks protect only their fixture.
grep -qE '^[.]/lake --rehash --wfail build[[:space:]]' tests/e2e.sh \
  || fail "tests/e2e.sh: the build must use the cache-checking flags exercised by E2E.Ci (--rehash --wfail)"
grep -qE '^ +- cron:' "$ci_yml" \
  || fail "$ci_yml: no schedule — with macOS off the per-push path, the cron IS when macOS runs"
grep -q 'workflow_dispatch' "$ci_yml" \
  || fail "$ci_yml: no workflow_dispatch — a commit touching c/shim.c needs a way to ask for macOS without waiting a week"
# …and the decision's own shape, in the script that now holds it. `E2E/Ci.lean`
# checks the BEHAVIOUR of all of this; these three only catch a wholesale deletion,
# which is what a suite cannot see (a deleted branch is a check that stops applying).
ci_sh='tests/ci-runners.sh'
grep -q 'ubuntu-latest' "$ci_sh" \
  || fail "$ci_sh: no ubuntu runner — every push must still get the full gate"
grep -q 'macos-latest' "$ci_sh" \
  || fail "$ci_sh: no macos runner — AGENTS.md claims the tree passes on macOS, and CI is the only thing that checks it"
grep -q -- "--since=" "$ci_sh" \
  || fail "$ci_sh: the scheduled run no longer checks for commits — a weekly macOS build of an unchanged tree pays the expensive rate to re-learn last week's answer"
# E2E `partial def` ratchet: the sibling of RUNTIME_PARTIAL_CAP above, for the same
# reason (the keyword creeps back by habit) and covering the files its glob misses.
# `LingerTest.drain` and `E2E/Harness.drain` now use total do-block loops.
# `RemoteLive.stripCsi` uses the library's dropWhile sublist bound to prove that
# each recursive call shortens its input. No helper needs fuel or partiality.
E2E_PARTIAL_CAP=0
ep_n="$(code_count 'partial def' 'E2E/*' 'LingerTest.lean')"
[ "$ep_n" -le "$E2E_PARTIAL_CAP" ] \
  || fail "E2E/ grew to $ep_n partial defs (cap $E2E_PARTIAL_CAP); a do-block loop does not need the keyword"

printf 'gates OK — purity, the OS and unsafe surfaces, the Vt friend set, the runtime ties, spec citations, the status glyphs, the prior-art shape, and the ratchets\n'
