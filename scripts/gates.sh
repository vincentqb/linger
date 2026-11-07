#!/bin/sh
# scripts/gates.sh — the SOURCE-TREE gates, and the only place the ratchet numbers live.
#
# The `pre-commit` hook and the full verifier both run this file through
# scripts/lint.sh, so a cap can never disagree between the hook and the gate.
#
# Every number here only ever goes DOWN without discussion. Raising one is a
# deliberate, reviewable edit, and that review is the whole point of the ratchet.
#
# Run standalone:  sh scripts/gates.sh
set -e
cd "$(dirname "$0")/.."
# fail() inside $(...) or a pipeline still stops the gates: it signals this shell. The
# EXIT trap keeps status 1 where ksh93 would report the interrupted pipeline's status.
trap 'gates_failed=1; exit 1' TERM
trap '[ -z "${gates_failed-}" ] || exit 1' EXIT
fail() { printf 'GATE FAIL: %s\n' "$1" >&2; kill -s TERM "$$"; exit 1; }

# --- code_grep: the gates read CODE, not prose -------------------------------
# Every source grep below goes through this, and the reason is one trap on its
# FOURTH sighting: these greps read DOCSTRINGS as well as code. `native_decide`
# in a doc comment under `Theorems/` failed the purity gate exactly as it would in
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
  # Every pathspec must match a tracked file: a `! code_grep …` gate or a ratchet
  # whose path moved would otherwise pass by finding nothing.
  cg_files="$(git ls-files --error-unmatch -- "$@" 2>/dev/null)" \
    || fail "code_grep: a pathspec in $* matches nothing tracked (a gate points at a path that moved)"
  # Deliberate word split: no tracked path in this tree has a space. `/dev/null`
  # is the last operand so awk can never fall back to stdin and hang.
  # shellcheck disable=SC2086
  CG_RE="$cg_re" awk "$CODE_AWK" $cg_files /dev/null
}
code_count() { code_grep "$@" | awk 'END { print NR + 0 }'; }   # -> a number

# Which modules are pure code and which are proofs, read from the tree with the rule
# `Theorems/Coverage.lean` (`pureModule`, `proofModule`) applies to module names: pure code is
# a component's top module (`Linger/Session.lean`) and each component's top-level modules other
# than its boundary and shell; proofs are each component's `Proofs/` plus the legacy
# `Theorems/`. Deliberate word splitting below: no tracked path in this tree has a space.
pure_paths="$(git ls-files -- 'Linger/*.lean' | awk -F/ '
  NF == 2 || NF == 3 && $3 != "Boundary.lean" && $3 != "Shell.lean"')"
proof_paths="$(git ls-files -- 'Theorems/*.lean' 'Linger/*/Proofs/*.lean')"
[ -n "$pure_paths" ] && [ -n "$proof_paths" ] || fail "no pure or proof modules found"

# shellcheck disable=SC2086
! code_grep 'sorry' $pure_paths $proof_paths || fail "sorry found"
# Termination is proved everywhere, never asserted with the keyword.
! code_grep '(^|[^[:alnum:]_])partial def([^[:alnum:]_]|$)' '*.lean' \
  || fail "partial def: use structural or well-founded recursion, or a do-block loop"
# A raised limit means a proof or term got harder; that is a signal to restructure.
! code_grep 'set_option[[:space:]]+(maxHeartbeats|maxRecDepth)' '*.lean' \
  || fail "raised maxHeartbeats/maxRecDepth: restructure instead of budgeting"
# Fuel makes a recursion total by cutting it off, so the claims hold of a truncation.
! code_grep '[(]fuel[[:space:]]*:' '*.lean' \
  || fail "a fuel parameter: recurse on the data or a decreasing measure"
# Any `IO`, `BaseIO` or `EIO` token, in a type or a call, is an effect in pure code.
# shellcheck disable=SC2086
! code_grep '(^|[^[:alnum:]_.])(E|Base)?IO([^[:alnum:]_]|$)' $pure_paths \
  || fail "IO in pure core"
# A predicate preserved by each step is preserved by the fold: one `invariant_foldl`.
# shellcheck disable=SC2086
! code_grep '[(][a-z][A-Za-z0-9]*_foldl f hf as [(]f v a[)][)][.]trans [(]hf v a[)]' $proof_paths \
  || fail "hand-rolled fold-preservation lemma: derive it from invariant_foldl"
# The build proves both fuzz claims; this keeps them in place at their full ranges.
for c in '^example : failing 400 = [[][]] := by native_decide$' \
         '^example : failingDeep 150 = [[][]] := by native_decide$'; do
  code_grep "$c" Linger/Terminal/Tests/Fuzz.lean >/dev/null || fail "fuzz claim weakened or disabled: $c"
done
# A CSI count reaches 65535, so every repeat it drives goes through Vt.repeatAtMost, which
# clamps it by the screen (repeatAtMost_eq_repeat). A loop counting `a1`, an `arg` or a
# stage's count `n` itself lets one CSI 65535 S fill the history ring with blank rows.
csi_loop='(List[.]range|Array[.]range|Nat[.]fold|Nat[.]repeat[[:space:]]+[[:alnum:]_.]+)[[:space:]]+'
csi_count='([(][^)]*[^[:alnum:]_.]|[(])?(a1|n)([^[:alnum:]_]|$)|[(][^)]*[.]arg([^[:alnum:]_]|$)'
! code_grep "$csi_loop($csi_count)" Linger/Terminal/Vt.lean \
  || fail "a loop counts a CSI parameter directly: route it through Vt.repeatAtMost, which clamps it by the screen"
# ECH's span is the one other loop a count sizes. Its clamp to the screen's width shows in
# no result, since cells past the row are skipped either way, so this pins it at the call;
# without it one CSI 65535 X runs 65535 iterations.
code_grep '^[[:space:]]+v[.]eraseRowSpan v[.]cursor[.]y v[.]cursor[.]x [(]min [(]v[.]cursor[.]x [+] n[)] v[.]cols[)]$' \
  Linger/Terminal/Vt.lean >/dev/null || fail "ECH lost its clamp: its span must end at min (v.cursor.x + n) v.cols"
# the OS surface stays where AGENTS.md says it is
[ "$(code_grep '@[[]extern' '*.lean' | awk -F: '!seen[$1]++ { print $1 }' | tr -d ' ')" = "Linger/Os/Boundary.lean" ] \
  || fail "extern declarations outside Linger/Os/Boundary.lean"
# The boundary declares foreign functions and nothing else: no Lean body, no wrapper.
! code_grep '^[[:space:]]*(private[[:space:]]+)?(def|abbrev|theorem|instance|structure|inductive)[[:space:]]' \
    Linger/Os/Boundary.lean \
  || fail "Linger/Os/Boundary.lean holds a Lean definition: wrappers and checks belong in Linger/Os/Shell.lean"
# Each binding is private, and Linger/Os/Shell.lean wraps it (its one importer is pinned
# with the import closures below), so a caller reaches the shim only through a wrapper.
! code_grep '^[[:space:]]*(public[[:space:]]+)?opaque[[:space:]]' Linger/Os/Boundary.lean \
  || fail "Linger/Os/Boundary.lean declares a public binding: keep it private and wrap it in Linger/Os/Shell.lean"
# `unsafe` and `@[implemented_by]` — the Lean-side twin of the `@[extern` gate just
# above, and the only route that makes the theorems false OF THE SHIPPED BINARY rather
# than of some value inside it (SCRATCHPAD.md, "the adversarial audit of the seal",
# finding R4). Re-measured here, in `Linger/Terminal/Proofs/Render/Ends.lean`, on v4.34.0-rc2:
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
# TREE-WIDE and fail-closed — measured zero hits across the tracked `.lean` files, so
# there is nothing to grandfather and no exemption list to rot. Tests and suites are
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
# most `opaque` hits over tracked `.lean` are actual `@[extern` declarations in
# `Linger/Os/Boundary.lean`, so the gate could only ever read "opaque outside the boundary".
# What that would catch is not a forge: with no `@[extern]` and no
# `@[implemented_by]` the compiler emits no value at all, so `opaque x : Vt` is a
# liveness hazard, not an implementation that disagrees with the model (the R5 family,
# which the spec bounds as compile-time prose). The remaining uses are mostly the English
# word in unbackticked prose, which `code_grep` keeps, so the helper does not make it
# cheaper either.
! code_grep '(^|[^[:alnum:]_])(unsafe|implemented_by)' '*.lean' \
  || fail "unsafe / @[implemented_by] in Lean — the compiled program may then disagree with every theorem about it (R4; see the comment on this gate)"
[ "$(git ls-files c/)" = c/shim.c ] || fail "more than one C file"
# The shim returns -errno and errno numbers differ by platform: 918c671's
# `r == -111` meant ECONNREFUSED only on Linux.
! code_grep '(==|!=)[[:space:]]*[(]?-([2-9]|[1-9][0-9]+)([^0-9]|$)' 'Linger/*/Shell.lean' 'Linger/*/Shell/*' \
    'Main.lean' 'Verify/*' 'Linger/*/Suites/*' \
  || fail "a negative literal comparison looks like an errno number: compare the sign, or classify the errno in c/shim.c"
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
# The only external Lean dependency is the LeanEvidence audit, pinned to a commit.
! code_grep '^[[:space:]]*require ' 'lakefile.lean' | grep -qv 'require lean_evidence from git$' \
  || fail "external Lean dependency in lakefile.lean"
lake_packages="$(tr -d ' \n' < lake-manifest.json | grep -o '"packages":\[[^]]*\]')"
[ "$(printf '%s' "$lake_packages" | grep -o '"name":"[^"]*"')" = '"name":"lean_evidence"' ] \
  && printf '%s' "$lake_packages" | grep -q '"url":"https://github.com/vincentqb/lean-evidence"' \
  && printf '%s' "$lake_packages" | grep -qE '"inputRev":"[0-9a-f]{40}"' \
  || fail "lake-manifest may list only lean_evidence, pinned to a commit"
# The audit stays a default target, and the verifier builds every default target: CI starts
# from a fresh checkout, so a default target missing from that list is never built there.
default_targets="$(code_grep '^@[[]default_target[]]' lakefile.lean \
  | sed 's/^[^:]*:[0-9]*:@[[]default_target[]][[:space:]]*//' | awk '{ print $2 }')"
printf '%s\n' "$default_targets" | grep -qx audit \
  || fail "the LeanEvidence audit is no longer a default target"
verify_build="$(awk '
  /^[.][/]lake --rehash --wfail build / { on = 1 }
  on { words = words " " $0; if ($0 !~ /[\\]$/) { print words; exit } }' scripts/verify.sh \
  | sed 's/>.*//; s/[\\]//g' | tr -s ' \t' '\n\n')"
[ -n "$verify_build" ] || fail "scripts/verify.sh lost its build command"
for default_target in $default_targets; do
  printf '%s\n' "$verify_build" | grep -qx "$default_target" \
    || fail "scripts/verify.sh does not build the default target $default_target"
done

# The vt-toolkit's import closure (`specs/archive/vt-toolkit.md` Step 4). The toolkit is
# Linger/Terminal/{Spec,Vt,Render,Mediation,Title,Replay}.lean, and the claim worth having is
# that its closure contains NOTHING else -- no Posix, no Runtime, no Checkpoint, no Session.
# `lean_lib LingerVt` in lakefile.lean is the positive half: it elaborates the
# closure. It cannot be the whole claim, because Lake resolves imports through one
# package-wide LEAN_PATH, so a lib with restricted `roots` compiles an out-of-set
# module happily -- `import Linger.Os.Shell` in Mediation.lean builds under
# `./lake build LingerVt` without a murmur. Measured, twice, not assumed. A
# build-level failure needs a sub-package with its own srcDir and a path `require`,
# and the two gates immediately above forbid every `require` but LeanEvidence's. So this grep is the half
# that bites: the same species of oracle as SHIM_CAP below, evadeable by
# deliberately editing the list, not by reverting a fix.
#
# EXACT SETS, not a denylist of names to fear: a closure gate that only knows the
# imports someone thought of is not a closure gate. And exact means it also fires
# when an import GOES, which is right -- the list below is the recorded header, so
# Step 2/3 taking a friend import out is a reviewable edit here rather than a
# silent one. Vt imports only the Terminal spec, which imports nothing; Render imports Vt;
# Mediation, Title and Replay import Render. The `import all Linger.Terminal.Vt` lines grant
# access within the sealed toolkit; Title reads only the public surface. Because the spec is a
# leaf, these six headers define the whole closure.
import_re='^[[:space:]]*((public|private|meta)[[:space:]]+)*import[[:space:]]+'
module_imports() {
  # Imports precede the module body. Stop at `public section` so a later
  # multiline help string such as "import [SAVE]" is not a module dependency.
  code_grep "$import_re|^[[:space:]]*public[[:space:]]+section([[:space:]]|$)" "$@" \
  | awk -F: '
      $3 ~ /^[[:space:]]*public[[:space:]]+section([[:space:]]|$)/ { body[$1] = 1; next }
      !body[$1] { print }'
}
# import_mod(line) is the module an import line names: the line less its modifiers,
# `all` and a trailing `--` comment, which Lean accepts after the name. Each gate that
# maps import lines to modules prepends IMPORT_AWK to its awk program, so all share one
# parse, as all share code_grep.
IMPORT_AWK='
function import_mod(line) {
  sub(/^[[:space:]]*((public|private|meta)[[:space:]]+)*import[[:space:]]+(all[[:space:]]+)?/, "", line)
  sub(/[[:space:]]+--.*/, "", line); sub(/[[:space:]]+$/, "", line)
  return line }'
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
import_closure Linger/Terminal/Spec.lean ''
import_closure Linger/Terminal/Vt.lean 'public import Linger.Terminal.Spec;'
import_closure Linger/Terminal/Render.lean \
  'public import Linger.Terminal.Vt;import all Linger.Terminal.Vt;'
import_closure Linger/Terminal/Mediation.lean \
  'public import Linger.Terminal.Vt;import Linger.Terminal.Render;import all Linger.Terminal.Vt;'
import_closure Linger/Terminal/Title.lean 'public import Linger.Terminal.Vt;import Linger.Terminal.Render;'
import_closure Linger/Terminal/Replay.lean \
  'public import Linger.Terminal.Vt;import Linger.Terminal.Render;import all Linger.Terminal.Vt;'

# Named targets must build the promised roots, not just happen to succeed.
# Read declaration lines through code_grep, then compare their verbatim Name
# literals: multiple backticks on a roots line are Lean syntax, not prose.
library_decl() {                             # `lean_lib $1` with its indented fields
  code_grep '.' lakefile.lean \
    | sed 's/^[^:]*:[0-9]*://' \
    | awk -v lib="$1" '
        /^--/ { next }
        /^(@[[][^]]*[]][[:space:]]+)?lean_lib / {
          sub(/^@[[][^]]*[]][[:space:]]+/, ""); active = ($2 == lib)
          if (active) { $1 = $1; printf "%s ", $0 }
          next
        }
        /^[[:space:]]/ { if (active) { $1 = $1; printf "%s ", $0 }; next }
        { active = 0 }'
}
library_roots() {
  lr_got="$(library_decl "$1")"
  [ "$lr_got" = "lean_lib $1 where roots := $2 ${3:+$3 }" ] \
    || fail "$1 lost its independent library roots or options: $lr_got"
}
# Every library but Verify shares implementationOptions, which turns on linter.missingDocs:
# the libraries overlap, and Lake builds a module with one containing library's options.
# scripts/verify.sh also checks every Linger module outside Proofs/ and Tests/ directly; the
# globs below build those two with these options.
library_roots LingerVt '#[`Linger.Terminal.Mediation, `Linger.Terminal.Title, `Linger.Terminal.Replay]' \
  'leanOptions := implementationOptions'
library_roots LingerVtTheorems '#[`Linger.Terminal.Proofs.Mediation, `Linger.Terminal.Proofs.Title, `Linger.Terminal.Proofs.Replay]' \
  'leanOptions := implementationOptions'
library_roots LingerInput '#[`Linger.Selector.Input]' 'leanOptions := implementationOptions'
library_roots LingerInputTheorems '#[`Linger.Selector.Proofs.Input]' 'leanOptions := implementationOptions'
library_roots LingerFuzzy '#[`Linger.Selector.Fuzzy]' 'leanOptions := implementationOptions'
[ "$(library_decl Linger)" = "lean_lib Linger where leanOptions := implementationOptions " ] \
  || fail "the Linger library lost implementationOptions: $(library_decl Linger)"
[ "$(library_decl Suites)" = "lean_lib Suites where globs := #[.submodules \`Linger.Session.Suites] leanOptions := implementationOptions " ] \
  || fail "the Suites library lost its globs or implementationOptions: $(library_decl Suites)"
[ "$(git grep -c 'def implementationOptions : Array LeanOption := #\[⟨`linter.missingDocs, true⟩\]$' -- lakefile.lean)" = lakefile.lean:1 ] \
  || fail "implementationOptions no longer enables linter.missingDocs"
# Proofs and fixtures build every module under their directories, so every module is
# checked without a root module importing it: the legacy `Theorems/` tree and each
# component's `Proofs/` and `Tests/`, in component order. The glob omits the root
# itself, so a Theorems.lean or Tests.lean would never be built.
lib_globs() {                                # lib_globs <lib> <component subdirectory>
  lg_parts=''
  [ -z "$(git ls-files -- "$1/*.lean")" ] || lg_parts=".submodules \`$1"
  for lg_c in $(git ls-files -- "Linger/*/$2/*.lean" | cut -d/ -f2 | sort -u); do
    lg_parts="${lg_parts:+$lg_parts, }.submodules \`Linger.$lg_c.$2"
  done
  printf 'lean_lib %s where globs := #[%s] leanOptions := implementationOptions ' "$1" "$lg_parts"
}
for lib in 'Theorems Proofs' 'Tests Tests'; do
  lr_lib="${lib% *}"; lr_dir="${lib#* }"
  lr_want="$(lib_globs "$lr_lib" "$lr_dir")"
  lr_got="$(library_decl "$lr_lib")"
  [ "$lr_got" = "$lr_want" ] \
    || fail "the $lr_lib library must build exactly the $lr_dir directories: want $lr_want, got $lr_got"
  [ -z "$(git ls-files -- "$lr_lib.lean")" ] \
    || fail "$lr_lib.lean is tracked, but the $lr_lib library builds only the modules under its directories"
done

# Check every member of the proof family, not only the root headers: an
# intermediate VT or renderer lemma must not pull session policy into the target.
module_imports Linger/Terminal/Proofs/Vt.lean 'Linger/Terminal/Proofs/Vt/*' Linger/Terminal/Proofs/Mediation.lean Linger/Terminal/Proofs/Title.lean \
  Linger/Terminal/Proofs/Replay.lean Linger/Terminal/Proofs/Render.lean 'Linger/Terminal/Proofs/Render/*' \
| awk -F: "$IMPORT_AWK"'
  { mod = import_mod($3)
    if (mod !~ /^(Linger[.]Terminal[.](Vt|Render|Mediation|Title|Replay|Spec)|Linger[.]Terminal[.]Proofs[.]((Vt|Render)([.][[:alnum:]_]+)*|Mediation|Title|Replay)|Init[.]Data[.]String[.]Legacy)$/) {
      print "  " $0; bad = 1
    }
  }
  END { exit bad }' >&2 || fail "the VT proofs import outside the standalone library boundary"

# Entry and manager policies have explicit, small import closures. Main
# composes their executors with the session backend. The session library never
# imports them, even through an intermediate module: every library import
# stays in Core, Runtime or the OS boundary.
import_closure Linger/Import/Resurrect.lean 'import Linger.Target.Name;import Linger.Display.Status;public import Linger.Terminal.Vt;public import Linger.Session.Spec;'
import_closure Linger/Selector/Key.lean 'public import Linger.Selector.Input;'
import_closure Linger/Selector/Fuzzy.lean ''
import_closure Linger/Selector/Picker.lean 'public import Linger.Selector.Key;import Linger.Selector.Fuzzy;import Linger.Target.Name;import Linger.Display.Listing;public import Linger.Display.Status;import Linger.Target.Remote;import Linger.Terminal.Vt;'
import_closure Linger/Selector/Input.lean ''
import_closure Linger/Selector/Proofs/Input.lean 'public import Linger.Selector.Input;import all Linger.Selector.Input;'
import_closure Linger/App/Entry.lean ''
import_closure Linger/Target/Name.lean 'import Linger.Target.Spec;'
import_closure Linger/Target/Remote.lean 'import Linger.Target.Name;'
import_closure Linger/Display/Title.lean 'import Linger.Target.Name;'
import_closure Linger/Os/Env.lean ''
import_closure Linger/Os/Boundary.lean ''
# Linger/Os/Shell.lean is the one module that may import the private bindings.
[ "$(module_imports '*.lean' | awk -F: "$IMPORT_AWK"'
    import_mod($3) == "Linger.Os.Boundary" && !seen[$1]++ { print $1 }')" = "Linger/Os/Shell.lean" ] \
  || fail "a module other than Linger/Os/Shell.lean imports Linger.Os.Boundary"
import_closure Linger/Os/Shell/Command.lean 'import Linger.Os.Shell;'
import_closure Linger/Import/Shell.lean 'import Linger.Import.Resurrect;import Linger.Session.Checkpoint;import Linger.Os.Shell;import Linger.Display.Listing;import Linger.Session.Shell.Paths;import Linger.Session.Shell.Resume;import Linger.Session.Shell.Inventory;import Linger.Os.Shell.Command;import Linger.Target.Remote;import Linger.Selector.Shell;import Std.Async.System;'
import_closure Linger/Selector/Shell.lean \
  'public import Linger.Selector.Picker;import Linger.Os.Shell;import Linger.Display.Listing;import Linger.Target.Remote;import Linger.Terminal.Title;import Linger.Os.Shell.Command;'
import_closure Main.lean \
  'import Linger.App.Shell;import Linger.App.Entry;import Linger.Selector.Shell;import Linger.Import.Shell;'
# `lean_lib Linger` builds the umbrella's closure, so this list is what `./lake build`
# checks of the session library.
import_closure Linger.lean "$(printf 'public import Linger.%s;' Session.Buf Os.Shell Session.Wire \
  Terminal.Vt Terminal.Render Terminal.Mediation Terminal.Title Target.Name Session \
  Session.Driver Session.Checkpoint \
  Target.Remote Display.Listing Display.Status Display.Title Os.Env Session.Shell.Paths \
  Os.Shell.Command Session.Shell.Daemon Session.Shell.Client Session.Shell.Inventory App.Shell \
  Session.Shell.Resume)"
module_imports Linger/Session.lean ':(glob)Linger/Session/*.lean' 'Linger/Session/Shell/*' \
    Linger/Os/Shell/Command.lean Linger/App/Shell.lean Linger/Os/Boundary.lean Linger/Os/Shell.lean \
    Linger/Os/Env.lean Linger/Target/Name.lean Linger/Target/Remote.lean Linger/Display/Status.lean \
    Linger/Display/Title.lean Linger/Display/Listing.lean Linger/Terminal/Vt.lean \
    Linger/Terminal/Render.lean Linger/Terminal/Mediation.lean Linger/Terminal/Title.lean \
    Linger/Terminal/Replay.lean Linger.lean \
| awk -F: "$IMPORT_AWK"'
  { mod = import_mod($3)
    if (mod !~ /^(Linger[.]Session|Linger[.](Session|Os|Target|Display|Terminal)[.][[:alnum:]_.]+|Linger[.]App[.]Shell|Std[.]Async[.](System|Signal))$/ \
        && mod != "LeanEvidence.Commands") {
      print "  " $0; bad = 1
    }
  }
  END { exit bad }' >&2 || fail "the session library imports outside its declared closure"

# Components depend downward only, as AGENTS.md's layout lists them: a module imports
# modules of its own component or of a lower layer, never a peer's or a higher one's.
# Suites run the composed program and may import any component. A component this table
# does not name fails, so a new one has to be placed before it can import anything.
component_layers='Os:0 Target:0 Terminal:0 Display:1 Session:2 Selector:2 Import:3 App:4'
layer_bad="$(module_imports 'Linger/*' ':!Linger/*/Suites/*' \
| awk -F: -v layers="$component_layers" "$IMPORT_AWK"'
  BEGIN { n = split(layers, L, " ")
          for (i = 1; i <= n; i++) { split(L[i], kv, ":"); rank[kv[1]] = kv[2] } }
  { src = $1; sub(/^Linger[/]/, "", src); sub(/[/.].*/, "", src)
    mod = import_mod($3)
    if (mod !~ /^Linger[.][A-Za-z]/) next
    dst = mod; sub(/^Linger[.]/, "", dst); sub(/[.].*/, "", dst)
    if (!(src in rank) || !(dst in rank)) { print "  unplaced component: " $1 ": " $3; next }
    if (dst != src && rank[dst] >= rank[src]) print "  " $1 ": " $3 }')"
[ -z "$layer_bad" ] || {
  printf '%s\n' "$layer_bad" >&2
  fail "a component imports a peer or a higher layer (layers: $component_layers)"; }

# Headline theorems. Manifest.lean declares the program parts the headlines name as holes
# (`@[expose]`, then `def <full name> : <type> := sorry`) and states the headlines with `sorry`;
# Theorems/Claims.lean proves the same statements of the program's parts; comparator.json names
# both; and `./lake comparator` (scripts/verify.sh) checks that each part has its declared type,
# that each proof matches its statement, and that no other axiom is used. These gates keep the
# lists equal, so neither a headline nor a hole can leave that check by being dropped from one
# of them, and keep the statements' meaning out of the program: the Manifest and the Spec
# modules import only Spec modules.
headline_names() {                           # headline_names <file>: theorem names, in order
  code_grep '^theorem [A-Za-z_][A-Za-z0-9_]*' "$1" | sed 's/^[^:]*:[0-9]*://; s/^theorem //; s/[[:space:]].*//'
}
manifest_names="$(headline_names Manifest.lean)"
manifest_count="$(printf '%s\n' "$manifest_names" | awk 'END { print NR }')"
[ -n "$manifest_names" ] || fail "Manifest.lean states no headline theorem"
[ "$(headline_names Theorems/Claims.lean)" = "$manifest_names" ] \
  || fail "Theorems/Claims.lean must prove exactly the theorems Manifest.lean states, in its order"
hole_names="$(awk 'prev == "@[expose]" && /^def Linger[.]/ { print $2 } { prev = $0 }' Manifest.lean)"
hole_count="$(printf '%s' "$hole_names" | awk 'END { print NR }')"
config_want="$(printf '%s\n' "$manifest_names" "--" "$hole_names" | awk '
  $0 == "--" { holes = 1; next }
  !holes { names[++n] = $0; next }
  $0 != "" { defs[++m] = $0 }
  END {
    print "{"
    print "  \"challenge_module\": \"Manifest\","
    print "  \"solution_module\": \"Theorems.Claims\","
    print "  \"theorem_names\": ["
    for (i = 1; i <= n; i++) printf "    \"Linger.Claims.%s\"%s\n", names[i], (i < n ? "," : "")
    print "  ],"
    if (m == 0) print "  \"definition_names\": [],"
    else {
      print "  \"definition_names\": ["
      for (i = 1; i <= m; i++) printf "    \"%s\"%s\n", defs[i], (i < m ? "," : "")
      print "  ],"
    }
    print "  \"permitted_axioms\": [\"propext\", \"Quot.sound\", \"Classical.choice\"]"
    print "}" }')"
[ "$(cat comparator.json)" = "$config_want" ] \
  || fail "comparator.json must list exactly the theorems and holes Manifest.lean declares, in its order, with the three standard axioms"
# Each headline's proof is `by sorry` and each hole's body `sorry`, however the formatter breaks
# the line, and the Manifest declares nothing else. Statements may contain `:=` (structure
# instances), so the check counts each `sorry`, each `:= by sorry` and each `:= sorry`.
manifest_code="$(code_grep '.' Manifest.lean | sed 's/^[^:]*:[0-9]*://' | tr '\n' ' ' | tr -s ' \t' '  ')"
[ "$(code_count 'sorry' Manifest.lean)" -eq "$((manifest_count + hole_count))" ] \
  && [ "$(printf '%s\n' "$manifest_code" | awk '{ print gsub(/:= by sorry([^[:alnum:]_]|$)/, "") }')" -eq "$manifest_count" ] \
  && [ "$(printf '%s\n' "$manifest_code" | awk '{ print gsub(/:= sorry([^[:alnum:]_]|$)/, "") }')" -eq "$hole_count" ] \
  || fail "every Manifest.lean theorem must be proved by exactly 'by sorry', and every hole be exactly 'sorry'"
! code_grep '^(@[[][^]]*[]][[:space:]]*)?((private|public|protected|noncomputable)[[:space:]]+)*(abbrev|instance|axiom|opaque|structure|inductive|class|example|lemma)([^[:alnum:]_]|$)' \
    Manifest.lean \
  || fail "Manifest.lean declares something other than a hole or a headline theorem"
hole_lines="$(awk 'prev == "@[expose]" && /^def Linger[.]/ { print FNR } { prev = $0 }' Manifest.lean)"
! code_grep '(^|[[:space:]])def[[:space:]]' Manifest.lean | awk -F: -v holes="$hole_lines" '
    BEGIN { n = split(holes, h, "\n"); for (i = 1; i <= n; i++) hole[h[i]] = 1 }
    !($2 in hole) { print; bad = 1 }
    END { exit !bad }' \
  || fail "a Manifest.lean definition must be a hole: '@[expose]', then 'def' and the full name"
# Each hole and headline says in words what it is or guarantees: a docstring ends on the line
# above it.
awk '(/^theorem / || /^@[[]expose[]]$/) && prev !~ /-[/]$/ { print FILENAME ":" FNR ": " $0; bad = 1 }
  { prev = $0 }
  END { exit bad }' Manifest.lean >&2 \
  || fail "every Manifest.lean hole and theorem needs a docstring"
manifest_imports_bad="$(module_imports Manifest.lean | awk -F: "$IMPORT_AWK"'
  { if ($3 !~ /^public[[:space:]]+import[[:space:]]+Linger[.]/ || $3 ~ /import[[:space:]]+all[[:space:]]/ \
        || import_mod($3) !~ /^Linger[.][A-Z][A-Za-z]*[.]Spec$/) print "  " $0 }')"
[ -z "$manifest_imports_bad" ] || {
  printf '%s\n' "$manifest_imports_bad" >&2
  fail "Manifest.lean imports only Spec modules, publicly"; }
spec_imports_bad="$(module_imports 'Linger/*/Spec.lean' | awk -F: "$IMPORT_AWK"'
  { if ($3 ~ /import[[:space:]]+all[[:space:]]/ || (import_mod($3) !~ /^Linger[.][A-Z][A-Za-z]*[.]Spec$/ \
        && import_mod($3) != "LeanEvidence.Commands"))
      print "  " $0 }')"
[ -z "$spec_imports_bad" ] || {
  printf '%s\n' "$spec_imports_bad" >&2
  fail "Spec modules import only Spec modules and LeanEvidence.Commands"; }
[ "$(library_decl Manifest)" = "lean_lib Manifest where leanOptions := #[⟨\`warn.sorry, false⟩, ⟨\`linter.missingDocs, true⟩] " ] \
  || fail "the Manifest library may silence only its sorry warnings, and must require docstrings: $(library_decl Manifest)"
! grep -qE '^@[[]default_target[]][[:space:]]+lean_lib Manifest' lakefile.lean \
  || fail "the Manifest library proves nothing; keep it out of the default targets"

# Pure route proofs do not observe terminal IO or inspect Main's call sites.
# Pin dispatch before terminal observations, exact argv and executable identity;
# Linger.App.Suites.Manager, Linger.Import.Suites.Recipes and Linger.Import.Suites.Interop exercise them in subprocesses.
for claim in route_bare_help route_selector_iff route_session_argv \
             route_attach_operands route_select_retired route_daemon_argv route_ls_argv route_import_argv \
             route_export_argv route_tmux_argv route_tmux_iff; do
  code_grep "^theorem $claim " Linger/App/Proofs/Entry.lean >/dev/null \
    || fail "entry-point contract disappeared: $claim"
done
# Fold layout whitespace for Main's small dispatch. Reuse the backtick-aware
# matcher below, so quoted prose cannot stand in for these call sites.
entry_code="$(awk '{ $1 = $1; printf "%s ", $0 }' Main.lean)"
for tie in \
  'def main [(]args : List String[)] : IO UInt32 := do try match Linger[.]App[.]Entry[.]route args with' \
  '[|] [.]selector readOnly => Linger[.]Selector[.]Shell[.]run [(]← IO[.]appPath[)][.]toString readOnly' \
  '[|] [.]tmux rest => Linger[.]Import[.]Shell[.]run [(]← IO[.]appPath[)][.]toString rest' \
  '[|] [.]session argv => Linger[.]App[.]Shell[.]main argv'; do
  printf '%s\n' "$entry_code" | CG_RE="(^|[[:space:]])$tie([[:space:]]|$)" awk "$CODE_AWK" >/dev/null \
    || fail "entry point bypassed its proved route or fixed IO boundary: $tie"
done

# The proof covers the returned parser/plan values. These call-site gates make
# bypassing them a reviewable change; IO tests check preflight/failure ordering
# and actual argv. As with the runtime ties below, this is not an IO theorem.
for claim in diagnostic_printable diagnostic_eq_self \
             catalogRows_common catalogRows_lines catalogRows_status catalogRows_printable catalogRows_command \
             selectedPane_exact selectedPane_valid \
             parseSave_valid parseRow_command_valid parseRow_metadata parseRow_metadata_irrelevant parseRow_other \
             layoutLeaves_bounded layoutSizes_bounded preparePane_preserves contentMember_exact \
             captureLimit_eq captureBytes_bounded commandNotice_eq commandNotice_bounded checkpoint_notice \
             checkpoint_live checkpoint_roundtrip checkpoint_metadata \
             selectedPane_metadata \
             mem_plan plan_order plan_sequential_idempotent \
             common_cons encodeName_reversible projectName_native \
             projectName_reserved_topology projectName_foreign \
             parseSave_home_independent renderSave_directories renderSave_valid \
             renderSave_empty renderSave_roundtrip; do
  code_grep "^(private )?theorem $claim " Linger/Import/Proofs/Resurrect.lean >/dev/null \
    || fail "interchange contract disappeared: $claim"
done
code_grep '^[[:space:]]+IO[.]eprintln s!"linger tmux [{]command[}]: [{]diagnostic [(]toString e[)][}]"$' Linger/Import/Shell.lean >/dev/null \
  || fail "tmux commands no longer display the proved control-free diagnostic"
code_grep '^[[:space:]]+let content ← IO[.]FS[.]readFile path$' Linger/Import/Shell.lean >/dev/null \
  || fail "tmux catalog no longer reads the complete resolved save before parsing"
code_grep '^[[:space:]]+let panes ← IO[.]ofExcept [(]parseSave home content[)]$' Linger/Import/Shell.lean >/dev/null \
  || fail "tmux catalog no longer consumes the proved whole-save parser"
code_grep '^[[:space:]]+for pane in plan existing panes do$' Linger/Import/Shell.lean >/dev/null \
  || fail "importer no longer iterates the proved import plan"
import_code="$(awk '{ $1 = $1; printf "%s ", $0 }' Linger/Import/Shell.lean)"
printf '%s\n' "$import_code" | CG_RE='(^|[[:space:]])let created ← IO[.]Process[.]output [{] cmd := executable, args := #[[]"run", pane[.]name, "true"[]], cwd := some [(]System[.]FilePath[.]mk pane[.]dir[)] [}] unless created[.]exitCode == 0 do throw [(]IO[.]userError s!"could not create session: [{]pane[.]name[}]: [{]created[.]stdout[}][{]created[.]stderr[}]"[)]([[:space:]]|$)' awk "$CODE_AWK" >/dev/null \
  || fail "importer bypasses planned creation argv/cwd, captured output or its diagnostic catch"
printf '%s\n' "$import_code" | CG_RE='(^|[[:space:]])[|] "import" => importSave executable paths[.]head[?]; return 0([[:space:]]|$)' awk "$CODE_AWK" >/dev/null \
  || fail "importer no longer forwards the entry point executable"
code_grep '^[[:space:]]+let listing ← IO[.]Process[.]output [{] cmd := executable, args := #[[]"ls", "--porcelain"[]] [}]$' Linger/Import/Shell.lean >/dev/null \
  || fail "importer no longer lists with the supplied executable"
# Native listing observes the caller's checkpoint namespace, including its
# no-HOME `/tmp` fallback. Only those fields reach the checked serializer.
printf '%s\n' "$import_code" | CG_RE='(^|[[:space:]])private def writeSave [(]path : String[)] [(]capture : IO [(]List [(]String × String[)][)] := snapshot[)] : IO Unit := do let fields ← capture let content ← IO[.]ofExcept [(]renderSave fields[)] publish path content([[:space:]]|$)' awk "$CODE_AWK" >/dev/null \
  || fail "exporter bypasses the current native snapshot, checked serializer or exclusive publication"
printf '%s\n' "$import_code" | CG_RE='(^|[[:space:]])[|] _ => writeSave [(]paths[.]headD ""[)]; return 0([[:space:]]|$)' awk "$CODE_AWK" >/dev/null \
  || fail "export command bypasses its native snapshot"
# Both views consume the same ordered catalog. Display strings are scrubbed;
# action fields have string-literal framing so display cleanup cannot retarget them.
# Acceptance must use the displayed snapshot, then pass its exact validated
# record to the shared creation executor. A suite checks the save-refresh race.
for tie in \
  'let save ← readSave origin home file let rows := catalogRows save[.]content save[.]panes' \
  'let value := if [[]"directory", "session", "window", "pane", "title", "command", "saved-command", "window-title"[]][.]contains key then value[.]quote else diagnostic value' \
  'Linger[.]Os[.]Shell[.]writeAll Linger[.]Os[.]Shell[.]stdoutFd [(]ByteArray[.]mk [(]Linger[.]Display[.]Listing[.]terminalListing withColor rows[)][.]toArray[)]' \
  'let save ← readSave origin home file createPanes executable origin save[.]panes [(]readArchive save[.]path[)]' \
  'let path ← savePath origin home file while true do match ← Linger[.]Selector[.]Shell[.]choose executable [(]some path[.]toString[)] with' \
  '[|] [.]attach target displayed => unless displayed[.]candidates[.]contains target do throw [(]IO[.]userError "selected pane was absent from the displayed save"[)] let row := displayed[.]row target' \
  'let some dir := [(]row[.]lookup "directory"[)][.]bind fun value => [(]Lean[.]Syntax[.]decodeStrLit value[)][.]filter [(]·[.]quote == value[)] [|] throw [(]IO[.]userError "selected pane has no directory"[)]' \
  'let some pane := selectedPane target dir line details [|] throw [(]IO[.]userError "invalid selected pane"[)]' \
  'createPanes executable origin [[]pane[]] archive let child ← IO[.]Process[.]spawn [{] cmd := executable, args := Linger[.]Selector[.]Shell[.]attachArgs pane[.]name, cwd := some [(]System[.]FilePath[.]mk pane[.]dir[)] [}] discard child[.]wait' \
  'let panes := panes[.]map [(]preparePane content panes[)]' \
  'let archive ← if [(]plan existing panes[)][.]isEmpty then pure none else archive for pane in plan existing panes do let contents ← capturedPane archive pane unless ← seedPane pane contents do continue' \
  'preflight origin panes let listing ← IO[.]Process[.]output [{] cmd := executable, args := #[[]"ls", "--porcelain"[]] [}]'; do
  printf '%s\n' "$import_code" | CG_RE="(^|[[:space:]])$tie([[:space:]]|$)" awk "$CODE_AWK" >/dev/null \
    || fail "tmux browser lost its catalog, displayed selection or preflight contract: $tie"
done
# Captures belong to the adjacent latest save only. Freeze their revision across
# display and acceptance, read the exact proved member to stdout, then publish
# the proved checkpoint while owning both identity locks. No saved command is run.
for tie in \
  'unless ← latestSave save do return none' \
  'metadata[.]byteSize[.]toNat ≤ 64 [*] 1024 [*] 1024' \
  'let text ← archiveOutput #[[]"-tzf", path[.]toString[]] [(]1024 [*] 1024[)]' \
  'let some member := contentMember pane [|] throw [(]IO[.]userError "invalid pane capture identity"[)] checkArchive archive match archive[.]members[.]filter [(]· == member[)] with' \
  'let text ← archiveOutput #[[]"-xOzf", archive[.]path[.]toString, "--", member[]] captureLimit checkArchive archive return some text' \
  'metadata[.]type == [.]file && metadata[.]modified == archive[.]modified && metadata[.]byteSize == archive[.]byteSize && [(]← latestSave archive[.]save[)]' \
  'unless text "archive" == some found[.]path[.]toString && row[.]lookup "archive-revision" == some [(]archiveRevision found[)] do throw [(]IO[.]userError "pane capture archive changed; refresh the saved panes"[)]' \
  'private def seedPane [(]pane : Pane[)] [(]contents : Option String[)] : IO Bool := Paths[.]withSessionLock pane[.]name do' \
  'if [(]← [(]System[.]FilePath[.]mk path[)][.]pathExists[)] [|][|] [(]← [(]System[.]FilePath[.]mk socket[)][.]pathExists[)] then return false' \
  'let handle ← IO[.]FS[.]Handle[.]mk tmp [.]writeNew try Linger[.]Os[.]Shell[.]chmod tmp[.]toString 0o600 handle[.]write [(]Linger[.]Session[.]Checkpoint[.]saveBytes [(]checkpoint pane contents[)][)] handle[.]flush IO[.]FS[.]hardLink tmp path finally IO[.]FS[.]removeFile tmp' \
  'pending[.]set [(]some [(]← Command[.]startLimited "tar" args limit[)][)] let deadline := [(]← Linger[.]Os[.]Shell[.]monotonicMs[)] [+] 5000' \
  'throw [(]IO[.]userError "pane capture archive timed out"[)] finally Command[.]stop pending'; do
  printf '%s\n' "$import_code" | CG_RE="(^|[[:space:]])$tie([[:space:]]|$)" awk "$CODE_AWK" >/dev/null \
    || fail "tmux capture import lost its bounded reader, frozen archive or checkpoint contract: $tie"
done
# Configuration lookup has one polling deadline and an owned subprocess.
# Cleanup force-retires that group. Explicit files never need tmux,
# and selection discovers the default only once before refreshing. Preserve
# its lookup spelling: readSave resolves the current symlink target each time.
for tie in \
  'Command[.]start "tmux" #[[]"show-options", "-gqv", "@resurrect-dir"[]]' \
  'let deadline := [(]← Linger[.]Os[.]Shell[.]monotonicMs[)] [+] 1000 while [(]← Linger[.]Os[.]Shell[.]monotonicMs[)] < deadline do' \
  'finally Command[.]stop pending' \
  'match file with [|] some path => pure path [|] none => if let some dir[[:space:]]*← configuredDirectory then' \
  'let path := System[.]FilePath[.]mk path return if path[.]isAbsolute then path else origin / path' \
  'let path ← IO[.]FS[.]realPath save let metadata ← path[.]metadata let content ← IO[.]FS[.]readFile path'; do
  printf '%s\n' "$import_code" | CG_RE="(^|[[:space:]])$tie([[:space:]]|$)" awk "$CODE_AWK" >/dev/null \
    || fail "tmux discovery lost its explicit path, polling deadline or child cleanup: $tie"
done

# Selector and decoder proofs concern pure values. Tie each IO consumer to the
# proved function, build attach argv from Remote.targetOperands and retain an
# immutable poll snapshot. Between remote queries a native visit lists local rows
# alone and keeps the last full listing's remote rows (withRemote_row_local,
# withRemote_row_remote); every visit starts with a full listing.
# Linger.App.Suites.Manager drives the terminal lifetime, failure paths, cadence and handoff itself.
for claim in align_optimal align_isSome_iff_sublist align_marks_length align_spells \
             align_score_max align_earliest align_default \
             alignWith_optimal alignWith_isSome_iff_sublist alignWith_marks_length \
             alignWith_spells alignWith_score_max alignWith_earliest \
             alignWith_scoring_irrelevant alignWith_smart_sensitive alignWith_smart_insensitive; do
  code_grep "^theorem $claim " Linger/Selector/Proofs/Fuzzy.lean >/dev/null \
    || fail "fuzzy alignment contract disappeared: $claim"
done
for claim in matches_iff_sublist align_isSome_iff_matches visible_order parseListing_valid parseSnapshot_complete \
             parseSnapshot_rejects presentation_existing presentation_existing_humanRow \
             presentation_creation highlightedPresentation_projection \
             highlightedPresentation_existing_humanRow highlightedPresentation_creation \
             highlightedPresentation_existing_marked_iff emphasizeCells_at emphasizeCells_projection \
             markPiece_marked_iff items_existing_prefix items_disabled selected_no_create \
             mem_items_create step_stay_valid step_attach_mem step_create_iff \
             step_create_valid step_init_empty step_cancel refresh_query refresh_candidates \
             refresh_valid refresh_selected refresh_missing init_allowCreate \
             refresh_allowCreate step_stay_allowCreate step_no_create step_accept_disabled \
             remoteTarget_check rowRecords_row mem_withRemote withRemote_nodup \
             withRemote_row_local withRemote_row_remote; do
  code_grep "^(private )?theorem $claim([[:space:]]|:)" Linger/Selector/Proofs/Picker.lean >/dev/null \
    || fail "selector contract disappeared: $claim"
done
for claim in feed_storage_bound feed_text_valid feed_paste_only_text feed_control flush_no_enter; do
  code_grep "^(private )?theorem $claim " Linger/Selector/Proofs/Input.lean >/dev/null \
    || fail "input contract disappeared: $claim"
done
for claim in ofInput_control_iff feed_byte_bindings feed_paste_no_commands feed_ctrl_r flush_no_accept; do
  code_grep "^theorem $claim " Linger/Selector/Proofs/Key.lean >/dev/null \
    || fail "selector binding contract disappeared: $claim"
done
for tie in \
  'let listed ← IO[.]ofExcept [(]Linger[.]Selector[.]Picker[.]parseSnapshot result[.]stdout[)]' \
  'let incoming := if full then listed else listed[.]withRemote lastFull' \
  'let items := Linger[.]Selector[.]Picker[.]items state[.]candidates state[.]query state[.]allowCreate' \
  'let mut state := Linger[.]Selector[.]Picker[.]init [[]] [(]!savedTmux && !readOnly[)]' \
  'let mut decoder := Linger[.]Selector[.]Input[.]init' \
  'let fds := #[[]stdinFd[]]' \
  'let events := #[[]POLLIN[]]' \
  'let ready ← poll fds events 50' \
  'let withColor := [(]← IO[.]getEnv "NO_COLOR"[)][.]isNone' \
  'writeAll stdoutFd [(]ByteArray[.]mk [(]Linger[.]Terminal[.]Title[.]ansi "linger"[)][.]toArray[)]' \
  'writeAll stdoutFd [(]ByteArray[.]mk [(]Linger[.]Terminal[.]Title[.]ansi ""[)][.]toArray[)]' \
  'discard child[.]wait' \
  'let child ← IO[.]Process[.]spawn [{] cmd := executable, args := attachArgs target readOnly [}]'; do
  code_grep "^[[:space:]]+$tie$" Linger/Selector/Shell.lean >/dev/null \
    || fail "manager bypassed a proved value or fixed IO boundary: $tie"
done
picker_code="$(awk '{ $1 = $1; printf "%s ", $0 }' Linger/Selector/Shell.lean)"
# Pin traversal through shared row pieces, frame insertion and complete metadata
# replacement. Computing rows or refreshed state without consuming them is
# insufficient. The loop seams fix draw, poll/decode/step, then refresh ordering.
# A completed snapshot must not replace the target underneath an unread key.
# Preserve byte order and consume both decoder results through the proved
# application binding before dispatch.
for tie in \
  'for byte in bytes do let [(]next, emitted[)] := Linger[.]Selector[.]Input[.]feed decoder byte decoder := next keys := keys [+][+] [(]emitted[.]filterMap Linger[.]Selector[.]Key[.]ofInput[)][.]toArray else if Linger[.]Selector[.]Input[.]pending decoder && [(]← monotonicMs[)] - lastInput ≥ 150 then let [(]next, emitted[)] := Linger[.]Selector[.]Input[.]flush decoder decoder := next keys := [(]emitted[.]filterMap Linger[.]Selector[.]Key[.]ofInput[)][.]toArray for key in keys do' \
  'let nameCol := Linger[.]Display[.]Listing[.]nameWidth [(]snapshot[.]candidates[.]map fun target => [[][(]"name", target[)][]][)]' \
  'let mut index := start for item in [(]items[.]drop start[)][.]take slots do let chosen := index == state[.]cursor let selection := if chosen then "\\x1b[[]7m" else "" let mut pieces := #[[][(]if chosen then " ▸ " else " ", selection[)][]] let chars := Linger[.]Selector[.]Picker[.]highlightedPresentation snapshot nameCol state[.]query item for char in Linger[.]Selector[.]Picker[.]emphasizeCells chars do let statusStyle := if withColor then [(]char[.]status[.]map Linger[.]Display[.]Status[.]style[)][.]getD "" else "" let emphasis := if char[.]matched then "\\x1b[[]4m" else "" pieces := pieces[.]push [(]String[.]singleton char[.]char, selection [+][+] statusStyle [+][+] emphasis[)] lines := lines[.]push pieces index := index [+] 1' \
  'let mut frame := "\\x1b[[]0m\\x1b[[]H\\x1b[[]2J" let mut first := true for line in lines do if !first then frame := frame [+][+] "\\r\\n" first := false let mut used := 0 let mut clipped := false let mut activeStyle := "" for [(]text, style[)] in line do if clipped then break if style != activeStyle then frame := frame [+][+] "\\x1b[[]0m" [+][+] style activeStyle := style for raw in text[.]toList do let c := if Linger[.]Selector[.]Input[.]printable raw then raw else '"'"'[?]'"'"' let cells := Linger[.]Terminal[.]Vt[.]charWidth c if used [+] cells > width then clipped := true break frame := frame[.]push c used := used [+] cells if !activeStyle[.]isEmpty then frame := frame [+][+] "\\x1b[[]0m" return frame' \
  'let next := if loaded then Linger[.]Selector[.]Picker[.]refresh state incoming[.]candidates else [{] [(]Linger[.]Selector[.]Picker[.]init incoming[.]candidates state[.]allowCreate[)] with query := state[.]query [}] dirty := dirty [|][|] !loaded [|][|] next != state [|][|] incoming != snapshot state := next snapshot := incoming loaded := true nextListing := [(]← monotonicMs[)] [+] 1000' \
  'while true do let current ← winsizeGet stdoutFd if dirty [|][|] current != size then let frame := draw state snapshot loaded withColor savedTmux current[.]1 current[.]2 if frame != lastFrame [|][|] current != size then writeAll stdoutFd frame[.]toUTF8 lastFrame := frame size := current dirty := false let ready ← poll fds events 50' \
  'for key in keys do if !loaded && key == [.]accept then continue match Linger[.]Selector[.]Picker[.]step state key with [|] [.]stay next => dirty := dirty [|][|] next != state state := next [|] [.]attach target [|] [.]create target => return [.]attach target snapshot [|] [.]cancel => return [.]cancel if let some result[[:space:]]*← Linger[.]Os[.]Shell[.]Command[.]poll pending then' \
  'if full then lastFull := listed nextRemote := [(]← monotonicMs[)] [+] remoteRefreshMs let incoming := if full then listed else listed[.]withRemote lastFull let next :=' \
  'nextListing := [(]← monotonicMs[)] [+] 1000 if [(]← pending[.]get[)][.]isNone && [(]← monotonicMs[)] ≥ nextListing then full := savedTmux [|][|] [(]← monotonicMs[)] ≥ nextRemote let args := if full then fullArgs else #[[]"ls", "--porcelain"[]] pending[.]set [(]some [(]← Linger[.]Os[.]Shell[.]Command[.]start executable args[)][)] return [.]cancel finally' \
  'finally Linger[.]Os[.]Shell[.]Command[.]stop pending [(]if savedTmux then 0 else 1000[)]' \
  'let fullArgs := if savedTmux then #[[]"tmux", "ls", "--porcelain"[]] [+][+] save[.]toArray else #[[]"ls", "-r", "--porcelain"[]]' \
  'match ← choose executable [(]readOnly := readOnly[)] with' \
  'def attachArgs [(]target : String[)] [(]readOnly : Bool := false[)] : Array String := [(]"attach" :: [(]if readOnly then [[]"--read-only"[]] else [[][]][)] [+][+] Linger[.]Target[.]Remote[.]targetOperands target[)][.]toArray'; do
  printf '%s\n' "$picker_code" | CG_RE="(^|[[:space:]])$tie([[:space:]]|$)" awk "$CODE_AWK" >/dev/null \
    || fail "manager lost its selection, refresh, process ownership or attach contract: $tie"
done
code_grep '^def remoteRefreshMs : Nat := [1-9][0-9]*$' Linger/Selector/Shell.lean >/dev/null \
  || fail "remote rows must refresh on a positive, fixed cadence"
# Terminal loops and remote discovery own helpers through this one executor. Reap only
# after both pipes close; clear ownership before a reader error can throw.
# Cancellation can first request cooperative cleanup. It always force-retires
# the isolated group before reaping its reserved leader PID, then joins both
# readers even when termination or reaping throws.
command_code="$(awk '{ $1 = $1; printf "%s ", $0 }' Linger/Os/Shell/Command.lean)"
for tie in \
  'IO[.]Process[.]spawn [{] cmd := executable, args, stdin := [.]null, stdout := [.]piped, stderr := [.]piped, setsid := true [}] let stdout ← IO[.]asTask child[.]stdout[.]readToEnd Task[.]Priority[.]dedicated let stderr ← IO[.]asTask child[.]stderr[.]readToEnd Task[.]Priority[.]dedicated return [{] child, stdout, stderr [}]' \
  'IO[.]Process[.]spawn [{] cmd := executable, args, stdin := [.]null, stdout := [.]piped, stderr := [.]piped, setsid := true [}] let stdout ← IO[.]asTask [(]readLimited child[.]stdout limit[)] Task[.]Priority[.]dedicated let stderr ← IO[.]asTask [(]readLimited child[.]stderr [(]64 [*] 1024[)][)] Task[.]Priority[.]dedicated return [{] child, stdout, stderr [}]' \
  'let chunk ← handle[.]read 4096 if chunk[.]isEmpty then break if !exceeded && bytes[.]size [+] chunk[.]size ≤ limit then bytes := bytes [+][+] chunk else exceeded := true' \
  'if exceeded then throw [(]IO[.]userError s!"command output exceeds [{]limit[}] bytes"[)] let some text := String[.]fromUTF8[?] bytes [|] throw [(]IO[.]userError "command output is not UTF-8"[)] return text' \
  'def poll [(]pending : IO[.]Ref [(]Option Job[)][)] : IO [(]Option IO[.]Process[.]Output[)] := do if let some job[[:space:]]*← pending[.]get then if [(]← IO[.]hasFinished job[.]stdout[)] && [(]← IO[.]hasFinished job[.]stderr[)] then if let some exitCode[[:space:]]*← job[.]child[.]tryWait then pending[.]set none let stdout ← IO[.]ofExcept [(]← IO[.]wait job[.]stdout[)] let stderr ← IO[.]ofExcept [(]← IO[.]wait job[.]stderr[)] return some [{] exitCode, stdout, stderr [}] return none' \
  'if let some job[[:space:]]*← pending[.]get then pending[.]set none try try try if graceMs > 0 then Linger[.]Os[.]Shell[.]kill job[.]child[.]pid 15 let deadline := [(]← Linger[.]Os[.]Shell[.]monotonicMs[)] [+] graceMs while [(]← Linger[.]Os[.]Shell[.]monotonicMs[)] < deadline do if [(]← IO[.]hasFinished job[.]stdout[)] && [(]← IO[.]hasFinished job[.]stderr[)] then break IO[.]sleep 5 finally retireGroup job finally discard job[.]child[.]wait finally discard <[|] IO[.]wait job[.]stdout discard <[|] IO[.]wait job[.]stderr' \
  'private def retireGroup [(]job : Job[)] : IO Unit := do try job[.]child[.]kill catch err => match err with [|] [.]permissionDenied [.][.] [|] [.]noSuchThing [.][.] => Linger[.]Os[.]Shell[.]kill job[.]child[.]pid 9 [|] _ => throw err'; do
  printf '%s\n' "$command_code" | CG_RE="(^|[[:space:]])$tie([[:space:]]|$)" awk "$CODE_AWK" >/dev/null \
    || fail "owned command lost its process or pipe lifetime contract: $tie"
done

# Pure rendering and summary claims cannot see CLI/terminal IO. Pin the actual
# consumers: validated host order, one shared row, palette-only badge styling,
# and plain redirected or NO_COLOR output. Prompt sampling shares one reply deadline; a busy
# nonblocking connect remains unknown and cannot authorize stale-socket removal.
for claim in style_palette attentionCounts_exact attentionCounts_mem summary_exact \
             summary_omits_zero summary_alphabet summary_printable; do
  code_grep "^theorem $claim " Linger/Display/Proofs/Status.lean >/dev/null \
    || fail "status presentation contract disappeared: $claim"
done
for claim in rowPieces_printable rowPieces_styles rowPieces_nameSpan nameWidth_covers \
             renderPieces_plain terminalListing_plain; do
  code_grep "^theorem $claim " Linger/Display/Proofs/Listing.lean >/dev/null \
    || fail "shared listing contract disappeared: $claim"
done
cli_code="$(awk '{ $1 = $1; printf "%s ", $0 }' Linger/App/Shell.lean)"
for tie in \
  'match Linger[.]Target[.]Remote[.]checkHosts hosts with [|] [.]ok l => return l [|] [.]error e => throw [(]IO[.]userError e[)]' \
  'for [(]host, output[)] in remotes[.]zip remote[.]toList do for row in Linger[.]Target[.]Remote[.]parse output do' \
  '[|] some [(]porcelain, remoteFlag[)] => cmdList porcelain [(]← resolveRemotes remoteFlag[)]' \
  'let withColor := [(]← [(]← IO[.]getStdout[)][.]isTty[)] && [(]← IO[.]getEnv "NO_COLOR"[)][.]isNone writeAll stdoutFd [(]ByteArray[.]mk [(]Linger[.]Display[.]Listing[.]terminalListing withColor rows[)][.]toArray[)]' \
  'def summaryText : IO String := do let rows ← localRows [(]some [(][(]← monotonicMs[)] [+] 250[)][)] return Linger[.]Display[.]Status[.]summary [(]rows[.]map fun info => Linger[.]Display[.]Status[.]ofName [(][(]info[.]lookup "status"[)][.]getD "unknown"[)][)]' \
  'def cmdSummary : IO UInt32 := do let summary ← summaryText if !summary[.]isEmpty then IO[.]println summary return 0' \
  'let fd ← connectUpsert name cmd Client[.]attach name fd summaryText' \
  '[|] [[]"ls", "--summary"[]] [|] [[]"list", "--summary"[]] [|] [[]"l", "--summary"[]] => cmdSummary'; do
  printf '%s\n' "$cli_code" | CG_RE="(^|[[:space:]])$tie([[:space:]]|$)" awk "$CODE_AWK" >/dev/null \
    || fail "listing or prompt bypassed its shared policy: $tie"
done
# The session inventory the listing, the prompt summary, `get` and the importer share.
inventory_code="$(awk '{ $1 = $1; printf "%s ", $0 }' Linger/Session/Shell/Inventory.lean)"
for tie in \
  'if let some deadline := stopAt then if [(]← monotonicMs[)] ≥ deadline then return some [(][.]error [(]IO[.]userError "overview deadline reached"[)][)] match ← Client[.]connect name stopAt[.]isSome with [|] none => if stopAt[.]isSome && retainUnavailable then return some [(][.]error [(]IO[.]userError "overview connection unavailable"[)][)] return none [|] some fd => try let info ← [(]readInfo fd stopAt[)][.]toBaseIO return some info finally close fd' \
  'Client[.]sendMsg fd [.]info let deadline := stopAt[.]getD [(][(]← monotonicMs[)] [+] 2000[)]' \
  'while go && [(]← monotonicMs[)] < deadline do let remaining := deadline - [(]← monotonicMs[)] let revs ← poll #[[]fd[]] #[[]POLLIN[]] [(]Int32[.]ofNat [(]min 100 remaining[)][)]' \
  'let infos ← queryInfos sockets deadline stopAt[.]isSome' \
  'for [(]name, result[)] in sockets[.]zip infos do match result with [|] some info => confirmedLive := confirmedLive [+][+] [[]name[]] rows := rows [+][+] [[]liveRow name [(]info[.]toOption[.]getD [[][]][)][]] [|] none => if ![(]← removeStaleSocket name[)] then'; do
  printf '%s\n' "$inventory_code" | CG_RE="(^|[[:space:]])$tie([[:space:]]|$)" awk "$CODE_AWK" >/dev/null \
    || fail "listing or prompt bypassed its shared policy: $tie"
done
# Environment policies decide unset and empty values for every input. The runtime
# reads SHELL and LINGER_NO_DETACH_KEY once each, and HOME once for remote hosts, into
# their policies. An unset or empty HOME configures no remote hosts
# (remotesFile_eq_none_iff): a fallback such as world-writable `/tmp` would let another
# account choose them, and a suite cannot create `/tmp/.config`.
for claim in shellOf_ne_empty shellOf_set shellOf_absent remotesFile_eq_none_iff remotesFile_set \
             detachEnabled_readOnly detachEnabled_writable; do
  code_grep "^theorem $claim " Linger/Os/Proofs/Env.lean >/dev/null \
    || fail "environment policy contract disappeared: $claim"
done
printf '%s\n' "$cli_code" | CG_RE='(^|[[:space:]])match Linger[.]Os[.]Env[.]remotesFile [(]← IO[.]getEnv "HOME"[)] with [|] none => pure [[][]] [|] some path => if ← System[.]FilePath[.]pathExists path then pure [(][(]← IO[.]FS[.]readFile path[)][.]splitOn([[:space:]]|$)' awk "$CODE_AWK" >/dev/null \
  || fail "remote configuration bypasses Env.remotesFile, which reads no file for an unset or empty HOME"
for var in SHELL LINGER_NO_DETACH_KEY; do
  [ "$(code_count "getEnv \"$var\"" 'Linger/*' Main.lean)" -eq 1 ] \
    || fail "$var is read more than once or not at all; read it once, into its Env policy"
done
# Discovery keeps bounded ownership until completion. Remote signal handlers
# are installed before spawning isolated SSH groups, so cancelling the chooser
# reaches those groups through its listing helper. Linger.Target.Suites.Remote checks overlap,
# output order, slot reuse, shared deadlines and descendant cleanup.
for tie in \
  'for signal in [[]Std[.]Async[.]Signal[.]sigterm, [.]sigint, [.]sighup[]] do let waiter ← Std[.]Async[.]Signal[.]Waiter[.]mk signal true try let task ← waiter[.]wait signals[.]modify [(]·[.]push [(]waiter, task[)][)] catch e => waiter[.]stop throw e let deadline := [(]← monotonicMs[)] [+] remoteQueryTimeoutMs' \
  'for [(]_, signal[)] in ← signals[.]get do if [(]← signal[.]getState[)] == [.]finished then return none if [(]← monotonicMs[)] ≥ deadline then break' \
  'while next < hosts[.]size && [(]← jobs[.]get[)][.]size < remoteQueryLimit && [(]← monotonicMs[)] < deadline do' \
  'finally for [(]_, pending[)] in ← jobs[.]get do try Command[.]stop pending catch _ => pure [(][)] for [(]waiter, _[)] in ← signals[.]get do waiter[.]stop' \
  'let task ← IO[.]asTask localRows Task[.]Priority[.]dedicated try let remote ← listRemotes remotes[.]toArray let locals ← IO[.]ofExcept [(]← IO[.]wait task[)] pure [(]locals, remote[)] finally discard <[|] IO[.]wait task'; do
  printf '%s\n' "$cli_code" | CG_RE="(^|[[:space:]])$tie([[:space:]]|$)" awk "$CODE_AWK" >/dev/null \
    || fail "discovery lost its bounded task or process ownership: $tie"
done
for tie in \
  'while next < names[.]size && [(]← pending[.]get[)][.]size < localQueryLimit && [(]← monotonicMs[)] < deadline do' \
  'IO[.]asTask [(]queryInfo names[[]index[]]! [(]some deadline[)] retainUnavailable[)] Task[.]Priority[.]dedicated' \
  'finally for [(]_, task[)] in ← pending[.]get do discard <[|] IO[.]wait task'; do
  printf '%s\n' "$inventory_code" | CG_RE="(^|[[:space:]])$tie([[:space:]]|$)" awk "$CODE_AWK" >/dev/null \
    || fail "discovery lost its bounded task or process ownership: $tie"
done
code_grep '^[[:space:]]+let r ← unixConnect path nonblocking$' Linger/Session/Shell/Client.lean >/dev/null \
  || fail "status connect lost its nonblocking boundary"

# Title writes use the bounded, control-free encoder and the existing VT
# observer. Observe raw application bytes only, reassert repeated OSC titles,
# and defer every injected title until the parser and UTF-8 decoder are idle.
# Attention is sampled in the client's process, one task at a time, and an
# outstanding sample is joined after the socket closes. Linger.Display.Suites.Title checks that an
# idle client reaps no children and that detach joins a held sample.
for claim in compose_parts compose_context compose_attention_last compose_bound \
             compose_payload_attention_last; do
  code_grep "^theorem $claim " Linger/Display/Proofs/Title.lean >/dev/null \
    || fail "shared display composition contract disappeared: $claim"
done
for claim in payload_safe payload_append ansi_payload_bound ansi_ends update_waits \
             update_nonempty_iff update_requires_boundary; do
  code_grep "^(public )?theorem $claim " Linger/Terminal/Proofs/Title.lean >/dev/null \
    || fail "title contract disappeared: $claim"
done
for claim in observe_append observe_no_history observe_dims observe_invariants \
             observe_esc_intermediates observe_escInter_pending observe_del_boundary \
             step_escInter_final_boundary; do
  code_grep "^(public )?theorem $claim " Linger/Terminal/Proofs/Vt.lean >/dev/null \
    || fail "pending terminal sequence contract disappeared: $claim"
done
code_grep '^theorem leave_boundary_title ' Linger/Terminal/Proofs/Render/Modes.lean >/dev/null \
  || fail "default title handback theorem disappeared"
client_code="$(awk '{ $1 = $1; printf "%s ", $0 }' Linger/Session/Shell/Client.lean)"
for tie in \
  'let mut observer := Linger[.]Terminal[.]Vt[.]Vt[.]init 1 1' \
  'while !leaving do if let some task[[:space:]]*← pending[.]get then if ← IO[.]hasFinished task then pending[.]set none let fresh := match ← IO[.]wait task with [|] [.]ok text => text [|] [.]error _ => String[.]singleton [(]Linger[.]Display[.]Status[.]icon [.]unknown[)] titleDirty := titleDirty [|][|] fresh != summary summary := fresh nextSummary := [(]← monotonicMs[)] [+] 1000 if [(]← pending[.]get[)][.]isNone && [(]← monotonicMs[)] ≥ nextSummary then pending[.]set [(]some [(]← IO[.]asTask sample Task[.]Priority[.]dedicated[)][)] let revs ← poll #[[]stdinFd, fd[]] #[[]POLLIN, POLLIN[]] 200' \
  'writeAll stdoutFd [(]ByteArray[.]mk payload[.]toArray[)] observer := observer[.]observe payload receivedOutput := true' \
  'if receivedOutput && titleDirty && !leaving then let title := Linger[.]Display[.]Title[.]compose name observer[.]windowTitle summary Linger[.]Terminal[.]Title[.]maxChars let bytes := Linger[.]Terminal[.]Title[.]update observer title if !bytes[.]isEmpty then writeAll stdoutFd [(]ByteArray[.]mk bytes[.]toArray[)] titleDirty := false' \
  'try writeAll stdoutFd [(]ByteArray[.]mk Linger[.]Terminal[.]Render[.]leaveAnsi[.]toArray[)] finally termRestore stdinFd saved return result finally close fd' \
  'def attach [(]name : String[)] [(]fd : UInt32[)] [(]sample : IO String[)] [(]readOnly : Bool := false[)] : IO Outcome := do let pending ← IO[.]mkRef [(]none : Option [(]Task [(]Except IO[.]Error String[)][)][)] try converse name fd sample readOnly pending finally if let some task[[:space:]]*← pending[.]get then discard <[|] IO[.]wait task'; do
  printf '%s\n' "$client_code" | CG_RE="(^|[[:space:]])$tie([[:space:]]|$)" awk "$CODE_AWK" >/dev/null \
    || fail "attached title lost its observer, sampler or handback contract: $tie"
done
! code_grep 'IO[.]Process|Command[.]|spawnDetached|spawnPty|appPath' Linger/Session/Shell/Client.lean \
  || fail "the attach client starts processes; it samples title attention in its own process"
[ "$(code_count 'observer := observer[.]observe' Linger/Session/Shell/Client.lean)" -eq 1 ] \
  || fail "title observer must consume application output exactly once"
[ "$(code_count '(^|[[:space:]])observer([[:space:]]+:[^=]*)?[[:space:]]*(:=|←)' Linger/Session/Shell/Client.lean)" -eq 2 ] \
  || fail "title observer may only initialize once and consume application output"
awk '
  /receivedOutput := true/ { output = 1; next }
  output && /^[[:space:]]*--/ { next }
  output { if ($0 !~ /^[[:space:]]*titleDirty := true$/) bad = 1; output = 0; checked++ }
  END { exit (checked != 1 || bad) }
' Linger/Session/Shell/Client.lean \
  || fail "repeated application titles no longer trigger reassertion"

# The `Vt` friend set — who may forge a `Vt` (SCRATCHPAD.md, "the adversarial audit of
# the seal", finding R1). `import all M` grants M's OWN all-access set, including
# whatever M has all-access to, so **`import all` TRANSITS** and
# `git grep -l 'import all Linger.Terminal.Vt'` is NOT an enumeration of the friend set.
# Measured in the real position, not a scratch file: one added
# `import all Linger.Terminal.Render` in `Linger/Session/Shell/Client.lean` plus a five-field
# `{ cols := 0, rows := 0, grid := #[], … }` gives `./lake build linger` exit 0 AND
# `sh scripts/gates.sh` exit 0. Two hops is the same: `import all Linger.Display.Proofs.Listing` from
# a file holding neither `import all Linger.Terminal.Vt` nor `import all Linger.Terminal.Render`
# compiles the identical forge. That is the Step 4 situation exactly — the compiler
# consents, so a grep is the only possible oracle — except that until now no grep
# existed, which made joining the friend set cost one line that nothing objected to, and
# made `private` on 20 fields worth one line of anyone's diff.
#
# CLOSURE, not edges. Transit follows `import all` edges ONLY (measured:
# `import all Linger.Session` — a plain `public import`er of `Vt` — does not
# transit, and neither does the `Linger` umbrella, whose imports are all `public`), so
# the closure over those edges IS the friend set and nothing else can widen it. Gating
# the edges instead would mean recording all of them, though few matter, and
# would fire on every legitimate rewire of the `Linger/Terminal/Proofs/Render/*` chain — noise on the
# common change, which is how a gate stops being read.
#
# The permitted region is an EXACT file list plus the proof and fixture directories,
# `Theorems/` and each component's `Proofs/` and `Tests/`, and that split is by
# edit frequency: commits add a `.lean` under those more often than
# one beside `Vt`, and few of those join the closure. So a per-file list over
# `Theorems/**` would be edited reflexively, while the core list changes rarely, which
# is what makes it a checkpoint. The proof and fixture directories are friends BY
# DECLARATION (see `Linger/Terminal/Vt.lean`, "## Every door"), and a component's `Tests/` deliberately forges invalid
# states in its negative fixtures, so listing its files one by one would gate a
# non-property. Everything else is outside and fail-closed — `Verify/**`, each component's
# `Suites/`, `Main.lean`, every shell and the other component modules. Replay joins only
# to read shared immutable rows.
# The suites are outside deliberately: a pty suite asserts on bytes the real binary
# emitted, so a forged `Vt` there would be an assertion about a state the binary cannot
# reach — the very bug the seal exists to prevent.
#
# EXACT means both directions, as with the toolkit lists above: a recorded friend
# that stops reaching `Vt` fails too, so a future step taking a friend import out is a
# reviewable edit here rather than a silent one. No cardinality number is recorded — the
# Step 4 record killed the job-count ratchet because cardinality is blind to identity,
# and that argument transfers whole.
#
# The regex is deliberately LOOSER than column 0, because `  import all Foo` (leading
# spaces) and `meta import all Foo` both compile — measured, along with the two that do
# not: `public import all` and `private import all` are rejected by Lean, and a tab is
# refused before it reaches here. Anchoring at column 0 would leave a one-space evasion.
# The prose hazard the loose regex used to buy is now `code_grep`'s, not this gate's —
# a backticked `import all Foo` anywhere in a docstring is invisible to it. What
# survives is narrower and still worth writing down: do not begin a docstring line with
# a BARE, unbackticked `import all`.
VT_ALL_RE='^[[:space:]]*(meta[[:space:]]+)*import[[:space:]]+all[[:space:]]+'
VT_FRIEND_EXACT='Linger/Terminal/Vt.lean Linger/Terminal/Render.lean Linger/Terminal/Mediation.lean Linger/Session/Checkpoint.lean Linger/Terminal/Replay.lean'
VT_FRIEND_DIRS='Theorems/'
VT_FRIEND_RE='^Linger/[^/]+/(Proofs|Tests)/'
code_grep "$VT_ALL_RE" '*.lean' \
| awk -F: -v seed='Linger/Terminal/Vt.lean' -v exact="$VT_FRIEND_EXACT" -v dirs="$VT_FRIEND_DIRS" \
    -v friend_re="$VT_FRIEND_RE" \
    "$IMPORT_AWK"'
  BEGIN { ne = split(exact, E, " "); nd = split(dirs, D, " ") }
  { tgt = import_mod($3); gsub(/[.]/, "/", tgt)
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
      if (f ~ friend_re) ok = 1
      if (ok) continue
      bad++
      printf "  %s has all-access to Linger.Terminal.Vt -- its private fields, its\n", f
      printf "  private constructor and Vt.ofDecoded -- by this chain of import all:\n"
      for (cur = f; cur != seed; cur = dst[via[cur]])
        printf "    %s:%s:%s\n", src[via[cur]], ln[via[cur]], raw[via[cur]] }
    for (j = 1; j <= ne; j++)
      if (!(E[j] in inset)) { bad++
        printf "  %s is a RECORDED friend that no longer reaches Linger.Terminal.Vt", E[j]
        printf " (renamed, moved, or its import all went)\n" }
    if (bad > 0) printf "  permitted: %s -- plus anything under: %s, or matching %s\n", exact, dirs, friend_re
    exit (bad == 0 ? 0 : 1) }' >&2 \
  || fail "the Linger.Terminal.Vt friend set changed (import all TRANSITS: it re-grants whatever the imported module itself has all-access to)"

# shim-size ratchet: the C trust boundary must not grow silently. This
# number only ever goes DOWN without discussion; raising it is a
# deliberate, reviewable act — the checkpoint for "does this genuinely
# need a syscall wrapper, or does Lean core already have it?" (see the
# C-vs-Rust and shrink-the-shim notes in SCRATCHPAD.md).
SHIM_CAP=21
shim_n="$(code_count 'LEAN_EXPORT' 'c/shim.c')"
[ "$shim_n" -le "$SHIM_CAP" ] \
  || fail "shim grew to $shim_n wrappers (cap $SHIM_CAP); justify the new syscall and bump the cap"

# The runtime keeps no byte queue of its own. `Linger/Session/Buf.lean` owns the two
# kinds of long-lived queue -- their caps, their drop and cut policies, and the
# removal of written prefixes (`Linger/Session/Proofs/Buf.lean`) -- and the runtime shells
# (the session's, the CLI and command jobs) are `IO`,
# so NO theorem can see that the daemon calls those functions rather than
# open-coding the same sums. Without this grep the Buf theorems are arithmetic
# about a value nothing forces the runtime to use. A source-tree property cannot
# be a theorem, so it is a gate, in the same spirit as SHIM_CAP above: evadeable
# by deliberately writing something new, not by reverting a fix.
# On the commit before Buf landed these three found 5 hits (Conn.out, Rt.ptyIn,
# Cli.queryInfo's accumulator, and two .extract compactions). Each used to spell its
# regex twice — once to test, once to print the hits — and `code_grep` prints them, so
# the duplicate is gone: two copies of a pattern is two things to keep in step.
! code_grep '^[[:space:]]+[a-zA-Z_]+ : ByteArray' 'Linger/App/Shell.lean' 'Linger/Os/Shell/Command.lean' 'Linger/Session/Shell/*' \
  || fail "a ByteArray field in a runtime shell (use Linger.Session.Buf, which is proved)"
! code_grep 'mut [a-zA-Z_]+ : ByteArray' 'Linger/App/Shell.lean' 'Linger/Os/Shell/Command.lean' 'Linger/Session/Shell/*' \
  || fail "an accumulating ByteArray local in a runtime shell (use Linger.Session.Buf: it is capped)"
! code_grep '[.]extract([^[:alnum:]_]|$)' 'Linger/App/Shell.lean' 'Linger/Os/Shell/Command.lean' 'Linger/Session/Shell/*' \
  || fail "buffer arithmetic in a runtime shell (Buf.bufAdvance owns it, and is proved)"

# The cursor proofs describe pure values. These ties keep the runtime on the
# captured snapshot, bounded advances and shared byte allowance. The delivery
# suite separately observes framing, prior/replay/live ordering and exit tails.
for claim in start_faithful next_faithful next_bounded next_progress steps_storage \
             drain_start; do
  code_grep "^(public )?theorem $claim " 'Linger/Terminal/Proofs/Replay.lean' > /dev/null \
    || fail "replay claim $claim disappeared"
done
for claim in followingCap_front followingCap_frame followingCap_iff; do
  code_grep "^theorem $claim " Linger/Session/Proofs/Buf.lean >/dev/null \
    || fail "shared buffer allowance claim $claim disappeared"
done
code_grep '^theorem onMsg_attach_snapshot ' 'Linger/Session/Proofs/Session.lean' > /dev/null \
  || fail "the attach snapshot theorem disappeared"
code_grep '^theorem onMsg_attach_already ' 'Linger/Session/Proofs/Session.lean' > /dev/null \
  || fail "the repeated-attach refusal theorem disappeared"
code_grep '^[[:space:]]+effs [+][+] [[][.]replay c[.]id [(]Replay[.]start s[.]vt[)][]] [+][+]$' 'Linger/Session.lean' > /dev/null \
  || fail "attach no longer captures its resulting snapshot"
code_grep '^[[:space:]]+replay : Option Replay[.]Plan := none$' 'Linger/Session/Shell/Daemon.lean' > /dev/null \
  || fail "each connection must retain one optional replay cursor"
code_grep '^[[:space:]]+after : Buf := [.]empty$' 'Linger/Session/Shell/Daemon.lean' > /dev/null \
  || fail "following output bypasses the proved byte buffer"
code_grep '^[[:space:]]+[|] [.]replay id plan => do$' 'Linger/Session/Shell/Daemon.lean' > /dev/null \
  || fail "the runtime no longer receives the captured replay plan"
code_grep '^[[:space:]]+match ← flushConn [{] c with replay := some plan [}] with$' 'Linger/Session/Shell/Daemon.lean' > /dev/null \
  || fail "the runtime no longer executes the captured replay plan"
! code_grep 'Replay[.]start|Render[.]restore' 'Linger/Session/Shell/Daemon.lean' \
  || fail "the daemon must consume the captured cursor without constructing another repaint"
code_grep '^[[:space:]]+match Replay[.]next Linger[.]Session[.]outputChunk plan with$' 'Linger/Session/Shell/Daemon.lean' > /dev/null \
  || fail "replay advancement no longer uses the proved output chunk"
code_grep '^def replayFrameCap : Nat := Linger[.]Session[.]outputChunk [+] [(]Wire[.]encode [(][.]output [[][]][)][)][.]length$' 'Linger/Session/Shell/Daemon.lean' > /dev/null \
  || fail "replay reservation no longer includes the wire encoder's frame overhead"
code_grep '^[[:space:]]+let cap := followingCap outbufCap replayFrameCap [(]owedLen c[.]out[)]$' 'Linger/Session/Shell/Daemon.lean' > /dev/null \
  || fail "following output no longer shares the front buffer allowance"
code_grep '^[[:space:]]+bufEnqueue [(]outbufCap - owedLen c[.]after[)] [.]empty$' 'Linger/Session/Shell/Daemon.lean' > /dev/null \
  || fail "replay frames no longer account for following output debt"

# A logically closed peer still owns its transport until it drains or expires.
# It therefore counts towards admission, and ordinary polls must retire it
# before taking the fd snapshot. Deadlines use Nat and the same grace constant
# as shutdown. A repeated close cannot buy another grace period.
code_grep '^[[:space:]]+closeBy : Option Nat := none$' 'Linger/Session/Shell/Daemon.lean' > /dev/null \
  || fail "transport close deadlines no longer use Nat"
[ "$(code_count '^[[:space:]]+let deadline := [(]← monotonicMs[)] [+] drainTimeoutMs$' 'Linger/Session/Shell/Daemon.lean')" -eq 2 ] \
  || fail "ordinary close and shutdown must share the Nat drain deadline"
code_grep '^[[:space:]]+if c[.]closeBy[.]any [(]now ≥ ·[)] then$' 'Linger/Session/Shell/Daemon.lean' > /dev/null \
  || fail "retired transport expiry no longer checks its fixed deadline"
code_grep '^[[:space:]]+return [(]rt[.]setConn [{] c with closeBy := some deadline [}], true[)]$' 'Linger/Session/Shell/Daemon.lean' > /dev/null \
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
' Linger/Session/Shell/Daemon.lean \
  || fail "repeated-close guard or expire-before-poll-snapshot ordering changed"
code_grep '^[[:space:]]+timeout := min timeout [(]deadline - now[)]$' 'Linger/Session/Shell/Daemon.lean' > /dev/null \
  || fail "ordinary polling ignores close deadlines"
code_grep '^[[:space:]]+let accepting := rt[.]conns[.]length < maxClients && rt[.]acceptAfter[.]all [(]now ≥ ·[)]$' 'Linger/Session/Shell/Daemon.lean' > /dev/null \
  || fail "listener admission must count every transport and honor its retry deadline"
code_grep '^[[:space:]]+#[[][(]if accepting then POLLIN else 0[)],' 'Linger/Session/Shell/Daemon.lean' > /dev/null \
  || fail "listener polling no longer uses the admission guard"
code_grep '^[[:space:]]+for _ in List[.]range [(]maxClients - rt[.]conns[.]length[)] do$' 'Linger/Session/Shell/Daemon.lean' > /dev/null \
  || fail "accept budget no longer includes retired transports"
[ "$(code_count '^[[:space:]]+let polled := rt[.]conns$' 'Linger/Session/Shell/Daemon.lean')" -eq 2 ] \
  || fail "ordinary and shutdown polling must each freeze their fd set"
[ "$(code_count '^[[:space:]]+for c in polled do$' 'Linger/Session/Shell/Daemon.lean')" -eq 2 ] \
  || fail "ordinary fd construction and readiness must use the same frozen connections"
code_grep '^[[:space:]]+let fds := [(]polled[.]map [(]·[.]fd[)][)][.]toArray$' 'Linger/Session/Shell/Daemon.lean' > /dev/null \
  || fail "shutdown fd list diverged from its frozen connections"
code_grep '^[[:space:]]+for [(]c, i[)] in polled[.]zipIdx do$' 'Linger/Session/Shell/Daemon.lean' > /dev/null \
  || fail "shutdown readiness no longer indexes the frozen connection list"
code_grep '^[[:space:]]+rt ← drainConns rt$' 'Linger/Session/Shell/Daemon.lean' > /dev/null \
  || fail "serve no longer drains accepted bytes after exit"

# A client read failure is local to that peer. The close frame cannot prove an
# IO catch exists: tie errors and EOF to the same fd retirement and pure event.
# Every retirement goes through Rt.closeConn, so its body is tied too: it closes
# the fd, then forgets that transport alone.
# Linger.Session.Suites.Robust closes an unread reply and requires the original shell to run again.
code_grep '^theorem step_closed_frame ' Linger/Session/Proofs/Session.lean >/dev/null \
  || fail "the complete client-close frame disappeared"
daemon_code="$(awk '{ $1 = $1; printf "%s ", $0 }' Linger/Session/Shell/Daemon.lean)"
printf '%s\n' "$daemon_code" | CG_RE='(^|[[:space:]])let received ← try read c[.]fd 65536 catch _ => pure none match received with [|] some bs => if bs[.]size > 0 then events := events [+][+] [[][.]bytes c[.]fd[.]toNat bs[.]toList[]] [|] none => rt ← rt[.]closeConn c[.]fd events := events [+][+] [[][.]closed c[.]fd[.]toNat[]]([[:space:]]|$)' awk "$CODE_AWK" >/dev/null \
  || fail "client read errors must close only that peer through the proved transition"
printf '%s\n' "$daemon_code" | CG_RE='(^|[[:space:]])def Rt[.]closeConn [(]rt : Rt[)] [(]fd : UInt32[)] : IO Rt := do close fd return [{] rt with conns := rt[.]conns[.]filter [(]·[.]fd != fd[)] [}]([[:space:]]|$)' awk "$CODE_AWK" >/dev/null \
  || fail "Rt.closeConn must close the fd before it forgets only that connection"
# A session without a command runs Env.shellOf's program, which an unset or empty
# SHELL makes sh (shellOf_absent). Linger.Session.Suites.Agent creates sessions with both.
printf '%s\n' "$daemon_code" | CG_RE='(^|[[:space:]])let shell := Linger[.]Os[.]Env[.]shellOf [(]← IO[.]getEnv "SHELL"[)] let [(]prog, args[)] := match argv with [|] [[][]] => [(][(]shell, #[[][]][)] : String × Array String[)]([[:space:]]|$)' awk "$CODE_AWK" >/dev/null \
  || fail "a session without a command bypasses Env.shellOf"

# Descriptor exhaustion must suspend admission without stopping existing work.
# The live fixture exhausts real descriptors; gates pin the retry and fd cleanup.
code_grep '^def acceptRetryMs : Nat := [1-9][0-9]*$' 'Linger/Session/Shell/Daemon.lean' > /dev/null \
  || fail "admission retry must wait a positive duration"
printf '%s\n' "$daemon_code" | CG_RE='(^|[[:space:]])if let some retryAt := rt[.]acceptAfter then if now < retryAt then timeout := min timeout [(]retryAt - now[)]([[:space:]]|$)' awk "$CODE_AWK" >/dev/null \
  || fail "admission retry no longer bounds the next poll deadline"
code_grep '^[[:space:]]+rt := [{] rt with acceptAfter := some [(][(]← monotonicMs[)] [+] acceptRetryMs[)] [}]$' 'Linger/Session/Shell/Daemon.lean' > /dev/null \
  || fail "admission failures must renew their retry deadline"
printf '%s\n' "$daemon_code" | CG_RE='(^|[[:space:]])try setNonblock fd catch err => close fd throw err([[:space:]]|$)' awk "$CODE_AWK" >/dev/null \
  || fail "failed client setup must release its accepted descriptor"
printf '%s\n' "$daemon_code" | CG_RE='(^|[[:space:]])rt := [{] rt with conns := rt[.]conns [+][+] [[][{] fd [}][]], acceptAfter := none [}]([[:space:]]|$)' awk "$CODE_AWK" >/dev/null \
  || fail "successful admission must clear the failure latch"

# Recovery diagnostics must not throw a second IO error. The robust suite
# injects both the operation failure and a failing stderr write.
printf '%s\n' "$daemon_code" | CG_RE='(^|[[:space:]])def report [(]message : String[)] : IO Unit := do try IO[.]eprintln message catch _ => pure [(][)]([[:space:]]|$)' awk "$CODE_AWK" >/dev/null \
  || fail "daemon diagnostics must contain write failures"
[ "$(code_count 'IO[.]eprintln|IO[.]eprint|IO[.]getStderr' 'Linger/Session/Shell/Daemon.lean')" -eq 1 ] \
  || fail "daemon diagnostics must go through the non-throwing reporter"

# The shared driver proves feedback order, termination and invariant preservation.
# Its IO adapter must forward the actual state and retain the returned state/exit.
for claim in feedMsgs_after_close feedMsgs_after_exit; do
  code_grep "^theorem $claim " 'Linger/Session/Proofs/Session.lean' > /dev/null \
    || fail "decoded command stopping claim $claim disappeared"
done
for claim in effects_in_order run_execution run_total_safe handle_feedback_keeps_alive run_exited; do
  code_grep "^theorem $claim " 'Linger/Session/Proofs/Driver.lean' > /dev/null \
    || fail "shared driver claim $claim disappeared"
done
printf '%s\n' "$daemon_code" | CG_RE='(^|[[:space:]])def pump [(]rt : Rt[)] [(]evs : List Event[)] : IO Rt := do let result ← Driver[.]run executeEffect [{] st := rt[.]st, world := rt, exiting := rt[.]exiting [}] evs return [{] result[.]world with st := result[.]st, exiting := result[.]exiting [}]' awk "$CODE_AWK" >/dev/null \
  || fail "daemon pump must use the proved driver with its actual state and exit flag"
code_grep '^private def executeEffect [(]st : State[)] [(]rt : Rt[)] : [(]eff : Effect Plan[)] → IO [(]Rt × Driver[.]Reply eff[)]$' 'Linger/Session/Shell/Daemon.lean' > /dev/null \
  || fail "effect interpreter must implement the driver's dependent reply type"
code_grep '^[[:space:]]+rt[.]saveCkpt st$' 'Linger/Session/Shell/Daemon.lean' > /dev/null \
  || fail "checkpoint interpreter must save the driver's current state"

# An info answer can span several frames. The pure producer proves the bound;
# keep the IO accumulator on that same policy rather than a copied number.
code_grep '^theorem onMsg_info_bounded ' 'Linger/Session/Proofs/Session.lean' > /dev/null \
  || fail "the info producer's framing theorem disappeared"
code_grep '^abbrev infoReplyCap : Nat := Linger[.]Session[.]infoReplyCap$' 'Linger/Session/Shell/Inventory.lean' > /dev/null \
  || fail "the inventory's info policy diverged from the proved producer"
code_grep '^[[:space:]]+Linger[.]Session[.]Buf[.]bufOffer infoReplyCap acc [(]ByteArray[.]mk payload[.]toArray[)]$' 'Linger/Session/Shell/Inventory.lean' > /dev/null \
  || fail "the info accumulator no longer uses the shared byte policy"

# All session verbs consume the same exact target parser. Fuzzy matching stays
# in the interactive picker. SSH joins a command string, so the actual transport
# must consume the proved quoting function and inherit stdin for binary input.
for claim in check_eq_some_iff check_no_alias; do
  code_grep "^theorem $claim " Linger/Target/Proofs/Name.lean >/dev/null \
    || fail "exact-name contract disappeared: $claim"
done
for claim in targetValid_iff parseTarget_exact parseTarget_name_valid shellQuote_roundtrip command_argv \
             targetArgs_targetOperands targetArgs_option_ne targetArgs_option; do
  code_grep "^theorem $claim " Linger/Target/Proofs/Remote.lean >/dev/null \
    || fail "command target, operand or shell quoting contract disappeared: $claim"
done
# Every attach or capture argv linger builds for itself places its target with
# Remote.targetOperands, which Remote.targetArgs reads back exactly (targetArgs_targetOperands).
# A literal attach argv passes a name starting with - as an option. "attach" may begin
# a list, array or cons only in the command parser's pattern and in Picker.attachArgs,
# tied above.
attach_words="$(code_grep '"attach"[[:space:]]*(,|[]]|::)' 'Linger/*/Shell.lean' 'Linger/*/Shell/*' \
  | sed 's/^\([^:]*\):[0-9]*:[[:space:]]*/\1: /')"
[ "$attach_words" = "$(printf '%s\n' \
    'Linger/App/Shell.lean: | "attach" :: rest | "a" :: rest =>' \
    'Linger/Selector/Shell.lean: ("attach" :: (if readOnly then ["--read-only"] else []) ++')" ] \
  || fail "a literal attach argv: build it with Picker.attachArgs, whose operands come from Remote.targetOperands: $attach_words"
! code_grep 'Linger[.]Selector[.]Fuzzy|Name[.]sanitize' Linger/App/Shell.lean Linger/Session/Shell/Client.lean \
  || fail "noninteractive command lookup must not fuzzy-match or rewrite a name"
code_grep '^[[:space:]]+Linger[.]Target[.]Remote[.]targetValid target = true ∧ target ∉ candidates := by$' Linger/Selector/Proofs/Picker.lean >/dev/null \
  || fail "selector creation and command arguments no longer share the target grammar"
for verb in attach run send detach kill info capture resize get set unset clear; do
  code_grep "^[[:space:]]+withTarget \"$verb\" " Linger/App/Shell.lean >/dev/null \
    || fail "session command bypassed the common exact target boundary: $verb"
done
for tie in \
  'match Linger[.]Target[.]Remote[.]parseTarget target with [|] none => invalidTarget [|] some parsed => runTarget verb parsed args localAction options' \
  'let some targets := names[.]mapM Linger[.]Target[.]Remote[.]parseTarget [|] invalidTarget let mut rc : UInt32 := 0 for target in targets do rc := max rc [(]← runTarget "wait" target [[]] cmdWait[)]' \
  'let interactive := verb == "attach" if interactive && [(]![(]← stdinIsTty[)] [|][|] ![(]← [(]← IO[.]getStdout[)][.]isTty[)][)] then' \
  'let operands := if verb == "attach" [|][|] verb == "capture" then Linger[.]Target[.]Remote[.]targetOperands target[.]name else [[]target[.]name[]]' \
  'IO[.]Process[.]spawn [{] cmd := "ssh", args := #[[]if interactive then "-t" else "-T", "--", host, Linger[.]Target[.]Remote[.]command verb [(]options [+][+] operands [+][+] args[)][]], stdin := [.]inherit [}] try child[.]wait finally if interactive then writeAll stdoutFd [(]ByteArray[.]mk Linger[.]Terminal[.]Render[.]leaveAnsi[.]toArray[)]' \
  'let readOnly := args[.]head[?] == some "--read-only" let args := if readOnly then args[.]tail else args let some [(]name, cmd[)] := Linger[.]Target[.]Remote[.]targetArgs args [|]' \
  'let history := args[.]head[?] == some "--history" let args := if history then args[.]tail else args let some [(]name, [[][]][)] := Linger[.]Target[.]Remote[.]targetArgs args [|]' \
  'withTarget "attach" name cmd [(]cmdAttach · cmd readOnly[)] [(]if readOnly then [[]"--read-only"[]] else [[][]][)]' \
  'withTarget "capture" name [[][]] [(]cmdRead · [(]if history then [.]history else [.]screen[)] [(]if history then Linger[.]Terminal[.]Render[.]history else Linger[.]Terminal[.]Render[.]screenText[)][)] [(]if history then [[]"--history"[]] else [[][]][)]'; do
  printf '%s\n' "$cli_code" | CG_RE="(^|[[:space:]])$tie([[:space:]]|$)" awk "$CODE_AWK" >/dev/null \
    || fail "command transport lost exact targets, argv, stdin or terminal ownership: $tie"
done
[ "$(code_count '^[[:space:]]+writeAll stdoutFd [(]ByteArray[.]mk Linger[.]Terminal[.]Render[.]leaveAnsi[.]toArray[)]$' Linger/App/Shell.lean)" -eq 1 ] \
  || fail "remote SSH termination no longer establishes canonical handback"

# Lifetime ownership covers two resources: the socket namespace and the saved
# state namespace. The model assumes stable lock inodes and exclusive flock;
# these IO ties and Linger.Session.Suites.Identity check acquisition before use and release after
# cleanup. A connected daemon's failure must never fall back to older saved data.
for claim in reachable_protected owner_holds_lock at_most_one_owner claim_free; do
  code_grep "^theorem $claim " Linger/Session/Proofs/Claim.lean >/dev/null \
    || fail "resource ownership contract disappeared: $claim"
done
paths_code="$(awk '{ $1 = $1; printf "%s ", $0 }' Linger/Session/Shell/Paths.lean)"
for tie in \
  'match Linger[.]Target[.]Name[.]check name with [|] some name => return name [|] none => throw' \
  'let name ← checkName name ensureDir dir let path := s!"[{]dir[}]/[{]name[}][{]suffix[}]" checkSpelling path return path' \
  'def socketPath [(]name : String[)] : IO String := do namedPath [(]← socketDir[)] name "[.]sock"' \
  'def ckptPath [(]name : String[)] : IO String := do namedPath [(]← stateDir[)] name "[.]ckpt"' \
  'def lockPath [(]name : String[)] : IO String := do namedPath [(]← socketDir[)] name "[.]lock"' \
  'def stateLockPath [(]name : String[)] : IO String := do namedPath [(][(]← stateDir[)] [+][+] "/[.]locks"[)] name "[.]lock"' \
  'def logPath [(]name : String[)] : IO String := do namedPath [(][(]← stateDir[)] [+][+] "/logs"[)] name "[.]log"' \
  'def withLockRetrying [{]α : Type[}] [(]path : String[)] [(]retry : IO Bool[)] [(]action : IO α[)] : IO α := do let mut fd ← Linger[.]Os[.]Shell[.]flock path while fd < 0 do unless ← retry do break fd ← Linger[.]Os[.]Shell[.]flock path if fd < 0 then throw [(]IO[.]userError s!"session is owned by another process [(][{]path[}][)]"[)] try checkSpelling path action finally Linger[.]Os[.]Shell[.]close fd[.]toUInt64[.]toUInt32' \
  'def withLock [{]α : Type[}] [(]path : String[)] [(]action : IO α[)] : IO α := withLockRetrying path [(]pure false[)] action' \
  'def withSessionLockRetrying [{]α : Type[}] [(]name : String[)] [(]retry : IO Bool[)] [(]action : IO α[)] : IO α := do withLockRetrying [(]← lockPath name[)] retry do withLockRetrying [(]← stateLockPath name[)] retry action' \
  'def withSessionLock [{]α : Type[}] [(]name : String[)] [(]action : IO α[)] : IO α := withSessionLockRetrying name [(]pure false[)] action'; do
  printf '%s\n' "$paths_code" | CG_RE="(^|[[:space:]])$tie([[:space:]]|$)" awk "$CODE_AWK" >/dev/null \
    || fail "session paths or lifetime locking bypassed their contract: $tie"
done
# A listing row takes its name verbatim from the socket filename (`rowFields_name`), so
# both listings pass every directory entry through the exact name check.
for tie in \
  'private def listNames [(]dir suffix : String[)] : IO [(]List String[)] := do ensureDir dir return [(]← System[.]FilePath[.]readDir dir[)][.]toList[.]filterMap fun e => [(]e[.]fileName[.]dropSuffix[?] suffix[)][.]bind [(]Linger[.]Target[.]Name[.]check ·[.]toString[)]' \
  'def listSocketNames : IO [(]List String[)] := do listNames [(]← socketDir[)] "[.]sock"' \
  'def listCkptNames : IO [(]List String[)] := do listNames [(]← stateDir[)] "[.]ckpt"'; do
  printf '%s\n' "$paths_code" | CG_RE="(^|[[:space:]])$tie([[:space:]]|$)" awk "$CODE_AWK" >/dev/null \
    || fail "session listing must check every directory entry with Name.check: $tie"
done
! code_grep 'removeFile|rename' Linger/Session/Shell/Paths.lean \
  || fail "lock path construction and acquisition must never unlink or replace a lock inode"
printf '%s\n' "$client_code" | CG_RE='(^|[[:space:]])try Paths[.]checkSpelling path return some fd catch err => close fd throw err([[:space:]]|$)' awk "$CODE_AWK" >/dev/null \
  || fail "successful connects must reject case-folded aliases and close on failure"
printf '%s\n' "$daemon_code" | CG_RE='(^|[[:space:]])IO Unit := do let deadline := [(]← monotonicMs[)] [+] claimWaitMs let reported ← IO[.]mkRef false let retry := claimRetry name [(]← Paths[.]socketPath name[)] deadline reported Paths[.]withSessionLockRetrying name retry do ignoreSighup let saved ← loadCkpt([[:space:]]|$)' awk "$CODE_AWK" >/dev/null \
  || fail "daemon recovery and lifetime must execute inside both ownership locks"
# An offline reader holds both locks briefly, so the daemon's startup claim retries a
# held lock for a bounded, positive time, and stops at once when a live daemon answers
# on the socket. A retry is asked only after a failed attempt. Every other acquisition
# is withLock or withSessionLock, one attempt each, and only the claim names a retrying
# acquisition, so no reader can pass a retry by position. The Claim model reads each
# failed attempt as an unchanged step. Linger.Session.Suites.Robust holds an offline capture's locks
# while run starts the session, and checks that a claim finding both free logs no wait.
code_grep '^private def claimWaitMs : Nat := [1-9][0-9]*$' 'Linger/Session/Shell/Daemon.lean' > /dev/null \
  || fail "the startup claim must wait a positive, fixed time"
printf '%s\n' "$daemon_code" | CG_RE='(^|[[:space:]])if [(]← monotonicMs[)] ≥ deadline then return false let live ← unixConnect sockPath if live ≥ 0 then close live[.]toUInt64[.]toUInt32 return false([[:space:]]|$)' awk "$CODE_AWK" >/dev/null \
  || fail "the startup claim must stop at its deadline and when a live daemon answers"
retrying="$(code_grep '(^|[^[:alnum:]_])with(Session)?LockRetrying([^[:alnum:]_]|$)' 'Linger/*' Main.lean \
  | awk -F: '$1 != "Linger/Session/Shell/Paths.lean" { print $1 }')"
[ "$retrying" = 'Linger/Session/Shell/Daemon.lean' ] \
  || fail "only the daemon's startup claim may retry a held lock: ${retrying:-no retrying claim}"
for tie in \
  'finally close listenFd try IO[.]FS[.]removeFile sockPath catch _ => pure [(][)][[:space:]]+end Linger[.]Session[.]Shell[.]Daemon' \
  'finally for c in rt[.]conns do close c[.]fd try if !rt[.]reaped then if ← alive rt[.]childPid then'; do
  printf '%s\n' "$daemon_code" | CG_RE="(^|[[:space:]])$tie([[:space:]]|$)" awk "$CODE_AWK" >/dev/null \
    || fail "daemon resource cleanup escaped its ownership lifetime: $tie"
done
for tie in \
  'requestStatus name result [|] none => Paths[.]withSessionLock name do match ← Resume[.]loadCkpt name with [|] some [(]vt, _, _[)] => writeAll stdoutFd [(]ByteArray[.]mk [(]render vt[)][.]toArray[)]' \
  'if readOnly then match ← Client[.]connect name with [|] some fd => Client[.]attach name fd summaryText true [|] none => let checkpoint ← Paths[.]withSessionLock name [(]Resume[.]loadCkpt name[)] match checkpoint with [|] some [(]vt, _, _[)] => Client[.]viewSaved name vt'; do
  printf '%s\n' "$cli_code" | CG_RE="(^|[[:space:]])$tie([[:space:]]|$)" awk "$CODE_AWK" >/dev/null \
    || fail "offline reading or listing bypassed ownership: $tie"
done
tie='let available ← try Paths[.]withSessionLock name [(]pure true[)] catch _ => pure false'
printf '%s\n' "$inventory_code" | CG_RE="(^|[[:space:]])$tie([[:space:]]|$)" awk "$CODE_AWK" >/dev/null \
  || fail "offline reading or listing bypassed ownership: $tie"
# Saved viewing consumes the bounded, faithful replay cursor. The original
# snapshot survives every resize, and the immutable load precedes terminal IO.
# Linger.Session.Suites.Watch observes input discard, lock release, exact replay and handback.
for tie in \
  'let mut lastSize : Option [(]UInt32 × UInt32[)] := none while true do let size ← winsizeGet stdinFd if lastSize != some size then let cols := if size[.]1 == 0 then snapshot[.]colCount else size[.]1[.]toNat let rows := if size[.]2 == 0 then snapshot[.]rowCount else size[.]2[.]toNat' \
  'let view := if snapshot[.]colCount == cols && snapshot[.]rowCount == rows then snapshot else snapshot[.]resize cols rows let mut repaint := Linger[.]Terminal[.]Replay[.]start view repeat match Linger[.]Terminal[.]Replay[.]next 65536 repaint with [|] none => break [|] some [(]bytes, next[)] => if !bytes[.]isEmpty then writeAll stdoutFd [(]ByteArray[.]mk bytes[.]toArray[)] repaint := next' \
  'let title := Linger[.]Display[.]Title[.]compose name view[.]windowTitle [(]String[.]singleton [(]Linger[.]Display[.]Status[.]icon [.]resumable[)][)] Linger[.]Terminal[.]Title[.]maxChars writeAll stdoutFd [(]ByteArray[.]mk [(]Linger[.]Terminal[.]Title[.]update view title[)][.]toArray[)]' \
  'if [(]splitDetach bytes true[)][.]2 then return [.]detached return [.]detached finally try writeAll stdoutFd [(]ByteArray[.]mk Linger[.]Terminal[.]Render[.]leaveAnsi[.]toArray[)] finally termRestore stdinFd saved'; do
  printf '%s\n' "$client_code" | CG_RE="(^|[[:space:]])$tie([[:space:]]|$)" awk "$CODE_AWK" >/dev/null \
    || fail "saved viewer bypassed bounded replay, snapshot preservation or terminal ownership: $tie"
done
printf '%s\n' "$import_code" | CG_RE='(^|[[:space:]])if row[.]lookup "state" == some "resumable" then Paths[.]withSessionLock name do let some [(]_, cwd, _[)] ← Resume[.]loadCkpt name [|] throw' awk "$CODE_AWK" >/dev/null \
  || fail "exporter must establish offline ownership before reading saved state"

# `onMsg_resizePty_agrees` connects every emitted pty size to the resulting
# emulator's effective dimensions. IO is outside the theorem: keep the effect
# interpreter forwarding those exact dimensions, in order. Both ends are
# checked so deleting the claim cannot silently leave a decorative runtime tie.
code_grep '^theorem onMsg_resizePty_agrees ' 'Linger/Session/Proofs/Session.lean' > /dev/null \
  || fail "the session-to-pty geometry correspondence theorem disappeared"
code_grep '^[[:space:]]+[|] [.]resizePty cols rows =>' 'Linger/Session/Shell/Daemon.lean' > /dev/null \
  || fail "review the pty effect interpreter against onMsg_resizePty_agrees"
code_grep '^[[:space:]]+winsizeSet rt[.]ptyFd cols rows$' 'Linger/Session/Shell/Daemon.lean' > /dev/null \
  || fail "the pty interpreter no longer forwards the proved dimensions in order"

# The elapsed-time theorems use Nat. Keep the actual monotonic source and the
# daemon tick on that representation; narrowing here is invisible to the proofs.
code_grep '^theorem step_tick_before_interval ' 'Linger/Session/Proofs/Session.lean' > /dev/null \
  || fail "the no-early-checkpoint theorem disappeared"
code_grep '^theorem step_tick_checkpoint_elapsed ' 'Linger/Session/Proofs/Session.lean' > /dev/null \
  || fail "the checkpoint elapsed-time theorem disappeared"
code_grep '^def monotonicMs : IO Nat := IO[.]monoMsNow$' 'Linger/Os/Shell.lean' > /dev/null \
  || fail "the monotonic clock no longer forwards Lean's Nat clock directly"
code_grep '^[[:space:]]+let now ← monotonicMs$' 'Linger/Session/Shell/Daemon.lean' > /dev/null \
  || fail "the daemon tick no longer reads the monotonic clock"
code_grep "^[[:space:]]+rt ← pump rt' [(]events [+][+] [[][.]tick now[]][)]$" 'Linger/Session/Shell/Daemon.lean' > /dev/null \
  || fail "the daemon no longer forwards the monotonic value to the proved tick"

# The daemon boots from Session.bootVt, the term the resume theorems quantify over.
# Theorems/Contracts.lean ties the model side: resumeVt is bootVt over loadBytes, by rfl.
code_grep '^[[:space:]]+let vt0 := Linger[.]Session[.]bootVt [(]restore[.]map [(]·[.]1[)][)]$' 'Linger/Session/Shell/Daemon.lean' > /dev/null \
  || fail "Daemon.serve no longer boots from Session.bootVt, which liveReachableVt_resumeVt covers"

# Read-only attachment's client-side guards (pin-the-gaps item 1). Read-only
# is enforced DAEMON-side: the 0x0 attach geometry sets `sizer := false` and
# `onMsg .input`/`onMsg .resize` then drop a non-sizer's traffic
# (`onMsg_input_readonly`). So these two `!readOnly` call sites are defence in
# depth and a pty test CANNOT see them — remove either and not one observable
# byte changes. That makes a grep the only honest oracle, the same species as
# SHIM_CAP above; faking it as a pty assertion would be decoration.
# `Linger/Session/Suites/Watch.lean` covers guard A (the 0x0 attach), which IS observable.
code_grep 'if size != lastSize && !readOnly' 'Linger/Session/Shell/Client.lean' > /dev/null \
  || fail "Client.attach lost its read-only resize guard (a watcher would fight the user's size)"
code_grep 'if !out.isEmpty && !readOnly' 'Linger/Session/Shell/Client.lean' > /dev/null \
  || fail "Client.attach lost its read-only input guard (a watcher would forward keystrokes)"
code_grep 'sendMsg fd [(][.]attach 0 0[)]' 'Linger/Session/Shell/Client.lean' > /dev/null \
  || fail "Client.attach no longer marks a read-only client with a 0x0 attach (the wire's only read-only bit)"
# The detach key follows Env.detachEnabled: always in a read-only view, whose saved
# form passes that value, true, directly (detachEnabled_readOnly), and for writable
# attach only while LINGER_NO_DETACH_KEY is unset. Linger.Session.Suites.Watch and Linger.Session.Suites.Attach observe both.
printf '%s\n' "$client_code" | CG_RE='(^|[[:space:]])let detachEnabled := Linger[.]Os[.]Env[.]detachEnabled readOnly [(]← IO[.]getEnv "LINGER_NO_DETACH_KEY"[)]([[:space:]]|$)' awk "$CODE_AWK" >/dev/null \
  || fail "attach bypasses Env.detachEnabled, which keeps the detach key in read-only views"
code_grep '^[[:space:]]+let [(]out, detach[)] := splitDetach bs detachEnabled$' Linger/Session/Shell/Client.lean >/dev/null \
  || fail "attach no longer splits input with its detach policy"

# The checkpoint decoder must not grow its forge back (`specs/archive/vt-toolkit.md` Step 2).
# `Linger/Session/Checkpoint.lean` keeps a PERMANENT `import all Linger.Terminal.Vt`: `wVt` reads
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
code_grep '(^|[^`[:alnum:]_.])Vt[.]ofDecoded ' 'Linger/Session/Checkpoint.lean' > /dev/null \
  || fail "Linger/Session/Checkpoint.lean no longer decodes through Vt.ofDecoded (a corrupt checkpoint could carry a zero column count)"
FORGE='(^|[^`[:alnum:]_])(cols|rows|grid|bot|tabs|pstate|u8need|u8acc) *:='
! code_grep "$FORGE" 'Linger/Session/Checkpoint.lean' \
  || fail "a Vt field is assigned in Linger/Session/Checkpoint.lean — the decoder forge is back; go through Vt.ofDecoded, which validates"

# Extensional reader theorems cannot distinguish reject-before-expansion from
# expand-then-reject. The latter passed every semantic check in the audit, and
# generated C confirmed that it allocated first. Pin these short guarded bodies
# and rVtB's prefix through its first row read, for the byte-array readers the
# runtime decodes with (`loadBytes_eq` is extensional); the list readers are private
# and only proofs and fixtures run them. Ignore layout, but inventory every region
# so a missing declaration or terminator cannot pass.
awk '
  BEGIN {
    want["rListB"] = "let(n,j)←rNatBbiifmaxCount.all(funlimit=>n≤limit)thenrListAuxBrnbjelsenone"
    want["rRLEB"] = "let(groups,j)←rListB(rPairBrNatBr)bilettotal:=groups.foldl(funng=>n+g.1)0ifmaxLength.all(funlimit=>total≤limit)thensome(expandB(Array.emptyWithCapacitytotal)groups,j)elsenone"
    want["rVtB"] = "let(cols,i)←rNatBbilet(rows,i)←rNatBbiifcols!=clampDimcols||rows!=clampDimrowsthennoneelsedolet(grid,i)←rListB(funbytesj=>rRowBbytesj(somecols))bi(somerows)"
  }
  /^def (rListB|rRLEB|rVtB) / {
    split($0, fields, " "); name = fields[2]
    seen[name]++; body = ""; collecting = 0
  }
  name != "" {
    line = $0
    if (!collecting) {
      if (!sub(/^.*(:= do|:= fun l => do|:= fun b i => do)/, "", line)) next
      collecting = 1
    }
    gsub(/[[:space:]]/, "", line)
    body = body line
    if ((name ~ /^rVt/ && index(line, "let(grid,") > 0) ||
        (name !~ /^rVt/ && line == "none")) {
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
  }' Linger/Session/Checkpoint.lean >&2 || fail "checkpoint allocation guard changed"
# The six bounds the byte-array readers forward.
for bound in \
  'rRLEB rCellB b i maxLength' \
  'let [(]rows, j[)] ← rListB rRowB b j maxRows' \
  'let [(]rows, j[)] ← rListB [(]fun bytes j => rRowB bytes j maxCols[)] bytes j maxRows' \
  'let [(]tabs, i[)] ← rListB rBoolB b i [(]some cols[)]' \
  'let [(]sb, i[)] ← rRingB b i [(]some sbCap[)]' \
  'let [(]altGrid, i[)] ← rAltB b i [(]some cols[)] [(]some rows[)]'; do
  code_grep "^[[:space:]]+$bound\$" 'Linger/Session/Checkpoint.lean' > /dev/null \
    || fail "a byte-array checkpoint reader stopped forwarding its bound: $bound"
done
# The checkpoint hooks are `IO`, so no theorem sees them use the proved codec: write the
# session's terminal and labels, read through the observers the headline theorems name,
# through `saveBytes` (`saveBytes_eq`), and return what `loadBytes` read from the file's bytes
# (`loadBytes_eq`).
resume_code="$(awk '{ $1 = $1; printf "%s ", $0 }' Linger/Session/Shell/Resume.lean)"
for tie in \
  'let ck : Ckpt Linger[.]Terminal[.]Vt[.]Vt := [{] vt := st[.]terminal, cwd, labels := st[.]labelList [}] let bytes := saveBytes ck' \
  'match loadBytes bytes with [|] some ck => return some [(]ck[.]vt, ck[.]cwd, ck[.]labels[)]'; do
  printf '%s\n' "$resume_code" | CG_RE="(^|[[:space:]])$tie([[:space:]]|$)" awk "$CODE_AWK" >/dev/null \
    || fail "checkpoint hooks bypassed the proved codec: $tie"
done

# Test-orchestrator safety. The pty suites isolate themselves by LINGER_DIR; an
# unscoped process-name kill reaches real sessions outside that directory. A skipped
# required regression is not a pass, and an executable Python snippet is still a
# second-language dependency even when embedded in a Lean string rather than tracked
# as a .py file. These are syntactic runtime ties, so the source gate is the oracle.
! code_grep '(^|[^[:alnum:]_])(pkill|killall)([^[:alnum:]_]|$)' 'scripts/verify.sh' 'Verify/*' 'Linger/*/Suites/*' \
  || fail "a test orchestrator kills by process name — suites may terminate only processes they created"
# A process-GROUP selector is the same hazard wearing a pid. POSIX reads `kill 0` as
# "every process in my group" and `kill -N` as group N, so one of these in a test
# script signals the harness, the agent running it, and whatever shell shares that
# group — which is exactly what happened on 2026-09-15, from `kill 0 15` inside
# `lingertest`. Scoped to the shell and the shim, because that is where nothing else
# stops it: from Lean the call goes through `Linger.Os.Shell.checkPid`, which rejects 0
# and every value that casts to a negative `pid_t` — a mechanism, not a grep — and
# `Linger/Os/Suites/Shim.lean`'s `kill 0 15` is that mechanism's regression test, so including
# Lean here would flag the assertion instead of the hazard. `kill -0 $pid` (the
# liveness probe) is a signal flag, not a target, and is deliberately not matched.
! code_grep 'kill([[:space:]]+-[A-Za-z0-9]+)*[[:space:]]+(--[[:space:]]+)?(0|-[0-9]+)([^0-9]|$)' \
    'scripts/*.sh' 'c/shim.c' 'recipes/*' \
  || fail "a signal targets process group 0 or a negative pid — name the pid the suite created"
! code_grep '["]python([0-9.]*)' 'Verify/*' 'Linger/*/Suites/*' \
  || fail "a suite executes embedded Python — use the suites binary as the child probe"
! code_grep 'IO[.]println[[:space:]]+"PASS[[:space:]].*skip' 'Verify/*' 'Linger/*/Suites/*' \
  || fail "a suite counts a skipped required check as PASS"
! code_grep 'expect[[:space:]]+[(]?true[)]?([[:space:]]|$)' 'Verify/*' 'Linger/*/Suites/*' \
  || fail "a suite asserts a constant true; a skipped check is not a PASS"
# Temporary paths follow two rules, each implemented once per language. Scratch without
# sockets goes under `${TMPDIR:-/tmp}`: that expansion in shell, `Verify.Harness.tempRoot`,
# `IO.FS.withTempDir` or `IO.FS.createTempDir` in Lean. A directory that will hold a Unix
# socket goes under `/tmp` whatever TMPDIR says, through `Verify.Harness.socketRoot` or
# `socket_root` in scripts/verify.sh: macOS caps a socket path at 104 bytes, and its TMPDIR
# alone takes about 49. So the test orchestration spells a temporary root only in those
# three definitions and in the expansion. Linger/Session/Suites/Paths.lean and Linger/Display/Suites/Overview.lean are exempt:
# they assert the product's documented defaults (Linger/Session/Shell/Paths.lean). The match
# also covers `/private/tmp`, `/var/tmp` and `/private/var/tmp`, and only where a path
# starts, not a component such as `$dir/tmp`. Each hit is read again with every expansion
# blanked out, because an ERE cannot exclude one context.
tmp_re='(^|[^[:alnum:]_.~)}])(/private(/var)?|/var)?[/]tmp([^[:alnum:]_]|$)'
tmp_hits="$(code_grep "$tmp_re" 'scripts/*.sh' .github/workflows/ci.yml Verify/Main.lean 'Verify/*.lean' 'Linger/*/Suites/*.lean' \
  | sed 's/[$][{]TMPDIR:-[/]tmp[}]/TMPDIR/g' | CG_RE="$tmp_re" awk "$CODE_AWK" \
  | sed 's/^[^:]*:[0-9]*://' | awk -F: '$1 != "Linger/Session/Suites/Paths.lean" && $1 != "Linger/Display/Suites/Overview.lean"')"
# The helpers are compared by content, with the root itself spelled `[/]tmp`, so these
# lines cannot match the gate that reads them.
tmp_got="$(printf '%s\n' "$tmp_hits" | sed 's/^\([^:]*\):[0-9]*:[[:space:]]*/\1: /; s#[/]tmp#[/]tmp#g')"
tmp_want="$(printf '%s\n' \
  'Verify/Harness.lean: return System.FilePath.mk (((← IO.getEnv "TMPDIR").filter (!·.isEmpty)).getD "[/]tmp")' \
  'Verify/Harness.lean: def socketRoot : System.FilePath := "[/]tmp"' \
  'scripts/verify.sh: socket_root=[/]tmp')"
[ "$tmp_got" = "$tmp_want" ] || {
  printf '  temporary roots other than the TMPDIR expansion:\n%s\n' \
    "$(printf '%s\n' "$tmp_hits" | sed 's/^/    /')" >&2
  printf '  want exactly the helpers:\n%s\n' "$(printf '%s\n' "$tmp_want" | sed 's/^/    /')" >&2
  fail "a hard-coded temporary root: put scratch under TMPDIR (the shell expansion, or Verify.Harness.tempRoot) and a socket directory under Verify.Harness.socketRoot or scripts/verify.sh's socket_root"; }
# A socket directory moved under the expansion or `tempRoot` passes that check, and fails
# only where TMPDIR is long, as on macOS, which CI does not run on every push. So each
# socket directory the suites and the verifier create is tied to its helper: every
# suite's state directory (`Env.make`), Interop's fixture root and the sentinel session's.
code_grep '^[[:space:]]+[|] none => [(]socketRoot / s!"linger-[{]slug[}]-[{]pid[}]"[)][.]toString$' \
  Verify/Harness.lean >/dev/null || fail "Env.make no longer roots each suite's state directory at Verify.Harness.socketRoot"
code_grep 'cmd := "mktemp", args := #[[]"-d", [(]socketRoot / "linger-i-XXXXXX"[)][.]toString[]]' \
  Linger/Import/Suites/Interop.lean >/dev/null || fail "Linger.Import.Suites.Interop no longer creates its fixture root under Verify.Harness.socketRoot"
code_grep '^sentinel_dir="[$]socket_root/linger-verify-sentinel-[$][$]"$' scripts/verify.sh >/dev/null \
  || fail "the verifier's sentinel directory is no longer under scripts/verify.sh's socket_root"
# `lean_lib Verify` has no glob (Verify/Coverage.lean's census needs the built program), so
# `./lake build suites` is the only build of the suites suites, under Verify/ and each component's
# Suites/, and it builds only the import closure of Verify/Main.lean, the suites root: a module
# outside it is never built, and none of its suites can run. Walk that closure forwards
# over the import lines; each suite module but Coverage and lingertest's root, the shim
# smoke test, must be in it.
suite_unreached="$(module_imports Verify/Main.lean 'Verify/*' 'Linger/*/Suites/*' \
| awk -F: -v files="$(git ls-files 'Verify/*.lean' 'Linger/*/Suites/*.lean' | tr '\n' ' ')" "$IMPORT_AWK"'
  { mod = import_mod($3); gsub(/[.]/, "/", mod)
    n++; src[n] = $1; dst[n] = mod ".lean" }
  END {
    q[1] = "Verify/Main.lean"; reached[q[1]] = 1; qn = 1
    for (qi = 1; qi <= qn; qi++)
      for (i = 1; i <= n; i++)
        if (src[i] == q[qi] && !(dst[i] in reached)) {
          reached[dst[i]] = 1; qn++; q[qn] = dst[i] }
    k = split(files, F, " ")
    for (j = 1; j <= k; j++)
      if (F[j] != "Verify/Coverage.lean" && F[j] != "Linger/Os/Suites/Shim.lean" &&
          !(F[j] in reached)) printf "%s ", F[j] }')"
[ -z "$suite_unreached" ] \
  || fail "outside the import closure of Verify/Main.lean, so './lake build suites' never elaborates them: ${suite_unreached% }"
# Every registered suite but the opt-in remote-live runs in the verifier: Verify.Main.suites
# names exactly the suites that scripts/verify.sh passes to `suites --suites`, read from those
# commands with their continuation lines joined.
registered="$(awk '/^def suites :/ { on = 1 } on { sub(/--.*/, ""); print } on && /[]][[:space:]]*$/ { exit }' Verify/Main.lean \
  | grep -oE '[(]"[^"]+"' | tr -d '("' | grep -vx 'remote-live' | sort)"
verified="$(awk '
  { cmd = cmd $0 }
  /\\$/ { sub(/\\$/, " ", cmd); next }
  cmd ~ /^[.]\/[.]lake\/build\/bin\/suites --suites[[:space:]]/ {
    sub(/^[.]\/[.]lake\/build\/bin\/suites --suites[[:space:]]+/, "", cmd)
    sub(/[[:space:]]*[|][|].*/, "", cmd)
    n = split(cmd, w, " ")
    for (k = 1; k <= n; k++) { name = w[k]; sub(/:[0-9]+$/, "", name); print name } }
  { cmd = "" }' scripts/verify.sh | sort)"
[ -n "$registered" ] && [ "$registered" = "$verified" ] \
  || fail "Verify.Main.suites less remote-live ($(printf '%s' "$registered" | tr '\n' ' ')) differs from the suites scripts/verify.sh runs ($(printf '%s' "$verified" | tr '\n' ' '))"

# Program and test sources stay Lean; pre-commit is an external framework.
# `scripts/` holds the shell verifier, while `Verify/` holds the executable suites.
if git ls-files '*.py' | grep -q .; then
  git ls-files '*.py'
  fail "a .py file is tracked; the suites and the coverage gate are Lean (see Verify/)"
fi

# Avoid the Tests/tests collision on case-insensitive filesystems and keep
# production modules under the project namespace.
git ls-files 'Tests/*' 'Linger/*/Tests/*' | grep -qvE '\.lean$' \
  && fail "a non-Lean file under a Tests/ directory (orchestration belongs in scripts/)" || true
git ls-files 'scripts/*' | grep -qvE '\.sh$' \
  && fail "a non-shell file under scripts/ (Lean suites belong in Verify/)" || true
git ls-files 'tests/*' 'Tools/*' 'Manager/*' 'Tests/*' 'Linger/Core/*' 'Linger/Runtime/*' \
    'Linger/Tools/*' 'Linger/Manager/*' | grep -q . \
  && fail "legacy directory: use scripts/, or a component under Linger/" || true

# Every declaration name cited in backticks must resolve to a declaration, in THEOREMS.md
# and in every tracked `.lean` file, comments included. This is gated rather than
# reviewed because reviewing it produced a FALSE CLEAN: the one-off check run in step 8
# grepped each name with `git grep -w`, which matches prose and comments, so
# `scrollbackAnsi_le`, which THEOREMS.md and two code comments named and nothing then
# declared, satisfied it. A doc that promises a theorem is unfalsifiable until something
# looks for the declaration, so this looks for `theorem|lemma|def|abbrev`.
#
# Basenames, because a citation is written unqualified while the declaration sits in a
# namespace; a qualified citation such as `Wire.decode_encode_chunked` is checked by its
# basename too. CamelCase names (types, structures) and file/section names are skipped:
# the target here is the `snake_case` claim names, which is what a reader would try to
# look up. Empty extraction is rejected so the check cannot pass without citations.
# Two lists hold names cited but not declared in Lean here: claims a comment states are
# absent, which must stay undeclared, and names from C, the Lean toolchain or GitHub,
# plus one lemma-name prefix. Every listed name must still be cited.
cite_absent='mmap_id_gridAnsi sb_csiDispatch_any load_legacy_save save_no_legacy'
cite_foreign="lean_chmod lean_io_process_get_pid pid_t tty_do_resize \
  native_decide bv_decide lean_exe workflow_dispatch org_ foldl_append"
cite_scan() {                                # file:line:basename per backticked snake_case name
  { grep -noE '`[A-Za-z][A-Za-z0-9_.]*`' THEOREMS.md | sed 's/^/THEOREMS.md:/'
    git grep -noE '`[A-Za-z][A-Za-z0-9_.]*`' -- '*.lean'; } \
  | awk -F: '{ name = $3; gsub(/`/, "", name); base = name; sub(/.*[.]/, "", base)
      if (name !~ /[.](md|lean|sh)$/ && ((name ~ /^[a-z]/ && name ~ /_/) || base ~ /^[a-z][A-Za-z0-9]*_/))
        print $1 ":" $2 ":" base }'
}
thm_cites="$(cite_scan | awk -F: '$1 == "THEOREMS.md" { print $3 }' | sort -u)"
[ -n "$thm_cites" ] \
  || fail "no declaration citations found in THEOREMS.md"
thm_decls="$(git grep -hoE '^ *(public )?(private )?(theorem|lemma|def|abbrev) [A-Za-z][A-Za-z0-9_.]*' \
  -- '*.lean' | sed 's/.*[[:space:]]//; s/.*[.]//' | sort -u)"
# Verify/Coverage.lean backs each renderer and replay reference with the claims covering
# it; those resolve too. The rows are counted, so a row the extraction misses fails.
emitter_claims="$(awk '
  /^def emitters / { on = 1 }
  on { text = text " " $0 }
  on && /[)][]]/ { on = 0 }
  END {
    while (match(text, /[(]"[^"]*"[[:space:]]*,[[:space:]]*"[^"]*"[[:space:]]*[)]/)) {
      row = substr(text, RSTART, RLENGTH); text = substr(text, RSTART + RLENGTH); rows++
      sub(/^[(]"[^"]*"[[:space:]]*,[[:space:]]*"/, "", row); sub(/"[[:space:]]*[)]$/, "", row)
      if (row == "type abbreviation") continue
      n = split(row, part, " / ")
      for (k = 1; k <= n; k++) {
        name = part[k]; sub(/^component of /, "", name)
        if (name ~ /^[A-Za-z][A-Za-z0-9_.]*$/) sub(/.*[.]/, "", name)
        print "Verify/Coverage.lean:emitters:" name } }
    print "#rows " rows }' Verify/Coverage.lean)"
[ "$(printf '%s\n' "$emitter_claims" | sed -n 's/^#rows //p')" = 28 ] \
  || fail "Verify/Coverage.lean's emitter table no longer reads as its 28 rows"
{ printf '%s\n' "$thm_decls" '#cites'; cite_scan; printf '%s\n' "$emitter_claims" | grep -v '^#rows '; } \
| CITE_ABSENT="$cite_absent" CITE_FOREIGN="$cite_foreign" awk -F: '
  BEGIN { n = split(ENVIRON["CITE_ABSENT"], L, " "); for (i = 1; i <= n; i++) absent[L[i]] = 1
          n = split(ENVIRON["CITE_FOREIGN"], L, " "); for (i = 1; i <= n; i++) foreign[L[i]] = 1 }
  !cites { if ($0 == "#cites") cites = 1; else declared[$0] = 1; next }
  ($3 in absent) || ($3 in foreign) { cited[$3] = 1; next }
  !($3 in declared) { printf "  %s:%s cites `%s`, which is declared nowhere\n", $1, $2, $3; bad = 1 }
  END {
    for (name in absent) if (name in declared) {
      printf "  `%s` is declared, but a comment states that it is absent\n", name; bad = 1 }
    for (name in absent) if (!(name in cited)) {
      printf "  `%s` is listed as absent but nothing cites it\n", name; bad = 1 }
    for (name in foreign) if (!(name in cited)) {
      printf "  `%s` is listed as foreign but nothing cites it\n", name; bad = 1 }
    exit bad }' >&2 \
  || fail "a cited declaration does not exist — repoint the citation, or list a claim stated as absent in cite_absent"
# Each theorem THEOREMS.md cites is restated in Theorems/Contracts.lean and closed by
# `with_reducible exact` of that theorem, so weakening its statement fails the build.
# The Proofs column also names theorems by qualified name, such as `Good.feed`.
thm_proofs="$(awk -F'|' '/^[|]/ { print $(NF - 1) }' THEOREMS.md \
  | grep -oE '`[A-Za-z][A-Za-z0-9_.]*`' | tr -d '`')"
{ code_grep 'with_reducible exact ' Theorems/Contracts.lean \
    | sed 's/.*with_reducible exact //; s/[^[:alnum:]_.].*//'
  printf '%s\n' '#cites' "$thm_cites" "$thm_proofs"; } \
| awk '
  !cites { if ($0 == "#cites") cites = 1; else pinned[++n] = $0; next }
  NF && !($0 in seen) { seen[$0] = 1; ok = 0
    for (i = 1; i <= n; i++) {
      p = pinned[i]
      if (p == $0 || substr(p, length(p) - length($0)) == "." $0) ok = 1 }
    if (!ok) { printf "  THEOREMS.md cites `%s`, which no with_reducible exact pins\n", $0; bad = 1 } }
  END { exit bad }' >&2 \
  || fail "Theorems/Contracts.lean does not restate every theorem THEOREMS.md cites"

# The CI matrix. macOS came off the per-push path on 2026-09-15 for a cost reason
# measured in SCRATCHPAD.md — not repeated here, because that figure was copied into
# seven files and had already started to rot — but the decision reaches the matrix
# through a `fromJSON` job output, and actionlint does NOT
# check it — verified by mistyping it deliberately, which actionlint accepted. Two
# ways that goes wrong silently: someone simplifies the matrix to ubuntu only and
# macOS is never checked again, or drops the schedule and it never runs. Neither is
# a Lean property, so this is the same species of oracle as SHIM_CAP.
ci_yml='.github/workflows/ci.yml'
# The runtime tie, and the load-bearing one: `Verify/Ci.lean` tests
# `scripts/ci-runners.sh`, and no Lean can see whether the workflow actually CALLS it.
# Re-inline the decision as a `case` in the YAML and the suite would keep passing
# against a script nothing runs. Same species as the `Buf` gate above.
#
# Match the INVOCATION, not the path: the first version of this grep looked for
# `ci-runners.sh` anywhere in the file, and the workflow's own comment names the
# script — so it passed with the call replaced by an inline `echo`. Break-verified
# after the fix.
grep -qE '(^|[^[:alnum:]_])sh[[:space:]]+scripts/ci-runners[.]sh' "$ci_yml" \
  || fail "$ci_yml: the runner decision is not a call to scripts/ci-runners.sh — Verify/Ci.lean would then be testing a script CI does not use"
[ -n "$(git ls-files -- scripts/ci-runners.sh)" ] \
  || fail "scripts/ci-runners.sh is not tracked — the workflow calls it, so a local-only copy passes here and fails in CI"
grep -qE '^ *os: [$][{][{] fromJSON[(]needs[.]gates[.]outputs[.]os[)] [}][}]$' "$ci_yml" \
  || fail "$ci_yml: the verify matrix must use the tested runner decision through needs.gates.outputs.os"
# Verify.Ci exercises Lake's invalidation and cached warnings, so the real verifier builds
# with the same flags. Semantic lint needs the dynamically imported program too, so the
# shared lint driver follows that complete build rather than running another hook stack.
awk '
  /^[.]\/lake --rehash --wfail build / { build = NR }
  /^[.]\/lake lint / { lint = NR }
  END { exit !(build && lint > build) }
' scripts/verify.sh \
  || fail "scripts/verify.sh: the complete --rehash --wfail build exercised by Verify.Ci must precede the shared Lake lint driver"
# Verify.Ci tests the actual input key. Both the lookup and successful receipt must
# use it; no prefix restore may turn merely similar inputs into verified ones.
[ -n "$(git ls-files -- scripts/ci-inputs.sh)" ] \
  || fail "scripts/ci-inputs.sh is not tracked"
[ "$(grep -cF 'key="$(sh scripts/ci-inputs.sh)"' "$ci_yml")" -eq 2 ] \
  || fail "$ci_yml: lookup and receipt must both use the tested verification key"
awk '
  /uses: actions\/cache\/restore@/ { receipt = 1; next }
  receipt && /^[[:space:]]+- name:/ { receipt = 0 }
  receipt && /restore-keys:/ { exit 1 }
  receipt && /key: passed-v1-/ { exact++ }
  /^[[:space:]]+run: [.]\/lake test$/ { full = NR }
  /^[[:space:]]+id: receipt$/ { record = NR }
  /uses: actions\/cache\/save@/ { save = NR }
  END { if (!(exact == 1 && full && record > full && save > record)) exit 1 }
' "$ci_yml" \
  || fail "$ci_yml: completed verification needs an exact receipt, saved only after the full verifier"
grep -qF "if: success() && runner.os == 'Linux'" "$ci_yml" \
  || fail "$ci_yml: record verification only after success"
grep -qF "if: success() && steps.receipt.outputs.key != ''" "$ci_yml" \
  || fail "$ci_yml: only a successful receipt may be saved"
grep -qF "if: needs.gates.outputs.verified != 'true'" "$ci_yml" \
  || fail "$ci_yml: only a completed verification may replace the full verifier"
# A scheduled month without commits gets no runners. A matrix over `[]` is an error, so the
# verify job must skip it rather than fail every quiet month.
grep -qF "needs.gates.outputs.os != '[]'" "$ci_yml" \
  || fail "$ci_yml: the verify job must skip a run with no runners"
awk '
  /if: steps.verified.outputs.cache-hit == .true./ { reuse = 1 }
  reuse && /^[[:space:]]+sh scripts\/gates[.]sh$/ { checked = 1 }
  END { exit !checked }
' "$ci_yml" \
  || fail "$ci_yml: reused verification must still run current source gates"
grep -qE '^[[:space:]]+run: sh scripts/hygiene[.]sh$' "$ci_yml" \
  || fail "$ci_yml: source hygiene must use the shared native checks"
grep -qE '^[[:space:]]+entry: sh scripts/lint[.]sh$' .pre-commit-config.yaml \
  || fail ".pre-commit-config.yaml: run the shared lint script exercised by Verify.Hygiene"
# The real suites must use the same isolated runner whose failure, signal and
# assertion-count contracts Verify.Ci exercises.
awk '/^say "[0-9]+[.] live suites / { live=1 }
  live && /^[.]\/[.]lake\/build\/bin\/suites --suites[[:space:]]/ { found=1 }
  END { exit !found }' scripts/verify.sh \
  || fail "scripts/verify.sh: run live suites through the tested --suites entry point"
grep -qE '^ +- cron:' "$ci_yml" \
  || fail "$ci_yml: no schedule — the monthly cron is when CI runs at all"
grep -q 'workflow_dispatch' "$ci_yml" \
  || fail "$ci_yml: no workflow_dispatch — a commit touching c/shim.c needs a way to ask for macOS without waiting for the monthly run"
# Suite fixed-sleep ratchet: a wait for something to appear polls its readiness
# signal (`waitFor`, `Client.awaitText`); the sleeps left are negative-assertion
# windows, fixture pacing, poll intervals and waits not yet converted. Both ratchets count
# the suites suites, under Verify/ and each component's Suites/, but not lingertest's shim smoke
# test, which they never counted.
SUITE_SLEEP_CAP=34
es_n="$(code_count 'IO[.]sleep([^[:alnum:]_]|$)' 'Verify/*' 'Linger/*/Suites/*' \
  ':!Linger/Os/Suites/Shim.lean')"
[ "$es_n" -le "$SUITE_SLEEP_CAP" ] \
  || fail "suite fixed sleeps grew to $es_n (cap $SUITE_SLEEP_CAP); poll a readiness signal with waitFor"
# Fixed drain windows: drain/drainStr with a literal deadline read for that long
# whatever arrives. Positive waits poll with Client.awaitText/awaitNeedle; the windows
# left are negative assertions, discards, stream sync points and positive reads not
# yet converted.
SUITE_DRAIN_CAP=64
ed_n="$(code_count '(^|[^[:alnum:]_.])drain(Str)?[[:space:]]+[^[:space:]]+[[:space:]]+[0-9]' 'Verify/*' \
  'Linger/*/Suites/*' ':!Linger/Os/Suites/Shim.lean')"
[ "$ed_n" -le "$SUITE_DRAIN_CAP" ] \
  || fail "suite fixed drain windows grew to $ed_n (cap $SUITE_DRAIN_CAP); wait for a positive condition with awaitText"

printf 'gates OK — purity, the OS and unsafe surfaces, the Vt friend set, the runtime ties, documentation contracts, and the ratchets\n'
