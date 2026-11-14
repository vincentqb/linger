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

# The proofs, read from the tree: linger's `Theorems/` and each component's `Proofs/`, and each
# package's `Proofs` and `Solution`. Deliberate word splitting below: no tracked path in this tree
# has a space. Pure code's own rules, no IO, no `partial`, no `sorry` and only the standard axioms,
# are the challenge library's, which each build's audit applies by role.
proof_paths="$(git ls-files -- 'Theorems/*.lean' 'Linger/*/Proofs/*.lean' \
  'packages/*/*/Proofs.lean' 'packages/*/*/Proofs/*.lean' 'packages/*/*/Solution.lean')"
[ -n "$proof_paths" ] || fail "no proof modules found"

# Termination is proved everywhere, never asserted with the keyword: the library allows
# `partial` in WorldCode and tooling, and this tree nowhere.
! code_grep '(^|[^[:alnum:]_])partial def([^[:alnum:]_]|$)' '*.lean' \
  || fail "partial def: use structural or well-founded recursion, or a do-block loop"
# Options come only from lakefile.lean, whose declarations are pinned below, and from
# scripts/verify.sh's flags: an option set in a file overrides both, and options such as
# `debug.skipKernelTC`, `warningAsError`, `autoImplicit` or a raised `maxHeartbeats` or
# `synthInstance.maxHeartbeats` weaken a check instead of meeting it.
! code_grep '(^|[^[:alnum:]_])set_option([^[:alnum:]_]|$)' '*.lean' \
  || fail "set_option in a Lean file: options belong in lakefile.lean, and a raised limit means restructuring"
# Fuel makes a recursion total by cutting it off, so the claims hold of a truncation.
! code_grep '[(]fuel[[:space:]]*:' '*.lean' \
  || fail "a fuel parameter: recurse on the data or a decreasing measure"
# A predicate preserved by each step is preserved by the fold: one `invariant_foldl`.
# shellcheck disable=SC2086
! code_grep '[(][a-z][A-Za-z0-9]*_foldl f hf as [(]f v a[)][)][.]trans [(]hf v a[)]' $proof_paths \
  || fail "hand-rolled fold-preservation lemma: derive it from invariant_foldl"
# The build proves both fuzz claims; this keeps them in place at their full ranges.
for c in '^example : failing 400 = [[][]] := by native_decide$' \
         '^example : failingDeep 150 = [[][]] := by native_decide$'; do
  code_grep "$c" packages/terminal/Terminal/Tests/Fuzz.lean >/dev/null || fail "fuzz claim weakened or disabled: $c"
done
# A CSI count reaches 65535, so every repeat it drives goes through Vt.repeatAtMost, which
# clamps it by the screen (repeatAtMost_eq_repeat). A loop counting `a1`, an `arg` or a
# stage's count `n` itself lets one CSI 65535 S fill the history ring with blank rows.
csi_loop='(List[.]range|Array[.]range|Nat[.]fold|Nat[.]repeat[[:space:]]+[[:alnum:]_.]+)[[:space:]]+'
csi_count='([(][^)]*[^[:alnum:]_.]|[(])?(a1|n)([^[:alnum:]_]|$)|[(][^)]*[.]arg([^[:alnum:]_]|$)'
! code_grep "$csi_loop($csi_count)" packages/terminal/Terminal/CoreCode/Vt.lean \
  || fail "a loop counts a CSI parameter directly: route it through Vt.repeatAtMost, which clamps it by the screen"
# ECH's span is the one other loop a count sizes. Its clamp to the screen's width shows in
# no result, since cells past the row are skipped either way, so this pins it at the call;
# without it one CSI 65535 X runs 65535 iterations.
code_grep '^[[:space:]]+v[.]eraseRowSpan v[.]cursor[.]y v[.]cursor[.]x [(]min [(]v[.]cursor[.]x [+] n[)] v[.]cols[)]$' \
  packages/terminal/Terminal/CoreCode/Vt.lean >/dev/null || fail "ECH lost its clamp: its span must end at min (v.cursor.x + n) v.cols"
# the OS surface stays where AGENTS.md says it is: the attribute in any form, including
# `@[never_extract, extern "f"]` and `attribute [extern "f"] g`
[ "$(code_grep '(^|[^[:alnum:]_])extern([^[:alnum:]_]|$)' '*.lean' | awk -F: '!seen[$1]++ { print $1 }' | tr -d ' ')" = "packages/os/Os/WorldSpec.lean" ] \
  || fail "extern declarations outside packages/os/Os/WorldSpec.lean"
# The os WorldSpec declares foreign functions and the world claim of the waits, and nothing else:
# no Lean body, no wrapper.
! code_grep '^[[:space:]]*(private[[:space:]]+)?(def|abbrev|theorem|instance|structure|inductive)[[:space:]]' \
    packages/os/Os/WorldSpec.lean \
  || fail "packages/os/Os/WorldSpec.lean holds a Lean definition: wrappers and checks belong in packages/os/Os/WorldCode.lean"
# Each binding is private, and packages/os/Os/WorldCode.lean wraps it (its one importer is pinned
# with the import closures below), so a caller reaches the shim only through a wrapper.
! code_grep '^[[:space:]]*(public[[:space:]]+)?opaque[[:space:]]' packages/os/Os/WorldSpec.lean \
  || fail "packages/os/Os/WorldSpec.lean declares a public binding: keep it private and wrap it in packages/os/Os/WorldCode.lean"
# `unsafe` and `@[implemented_by]` — the Lean-side twin of the `@[extern` gate just
# above, and the only route that makes the theorems false OF THE SHIPPED BINARY rather
# than of some value inside it. Measured here, in
# `packages/terminal/Terminal/Proofs/Render/Ends.lean`, on v4.34.0-rc2:
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
# `unsafeBaseIO`, `unsafePerformIO`, …) instead of the single name the exhibit above
# uses. `implemented_by` is unanchored for the same reason: `@[implemented_by f]` and
# `attribute [implemented_by f] g` both set it.
#
# DECLINED: adding `opaque`. Measured: most `opaque` hits over tracked `.lean` are
# actual `@[extern` declarations in `packages/os/Os/WorldSpec.lean`, so the gate could
# only ever read "opaque outside the boundary". What that would catch is not a forge:
# with no `@[extern]` and no `@[implemented_by]` the compiler emits no value at all, so
# `opaque x : Vt` is a liveness hazard, not an implementation that disagrees with the
# model. The remaining uses are mostly the English word in unbackticked prose, which
# `code_grep` keeps, so the helper does not make it cheaper either.
! code_grep '(^|[^[:alnum:]_])(unsafe|implemented_by)' '*.lean' \
  || fail "unsafe / @[implemented_by] in Lean — the compiled program may then disagree with every theorem about it (see the comment on this gate)"
[ "$(git ls-files '*.c' '*.h')" = packages/os/c/shim.c ] || fail "more than one C file"
# The shim returns -errno and errno numbers differ by platform: 918c671's
# `r == -111` meant ECONNREFUSED only on Linux.
! code_grep '(==|!=)[[:space:]]*[(]?-([2-9]|[1-9][0-9]+)([^0-9]|$)' 'Linger/*/WorldCode.lean' 'Linger/*/WorldCode/*' \
    'packages/os/Os/WorldCode.lean' 'packages/os/Os/WorldCode/*' \
    'Verify/*' 'Linger/*/Suites/*' \
  || fail "a negative literal comparison looks like an errno number: compare the sign, or classify the errno in packages/os/c/shim.c"
# Lean/libuv may have worker threads when the application forks. The child
# paths and the four helpers they run, which report a failure, reset what the
# program would inherit and execute it, must not allocate, format through
# stdio, mutate the environment, or use execvp's libc internals. Inventory the
# regions as well: deleting a marker must fail rather than checking nothing.
# This is a source guard for the listed calls, not a whole-program safety proof.
awk '
  /^static void (spawn_fail|close_from_3|spawn_reset|exec_search)\(/ { helper = 1; helpers++ }
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
    if (helpers != 4 || children != 2) {
      print "  fork guard expected four helpers and two child blocks, saw " helpers ", " children
      failed = 1
    }
    exit failed
  }' packages/os/c/shim.c >&2 || fail "fork child call boundary changed"
# The only external Lean dependency is the Lean Software Challenge library, pinned to a commit;
# the others are this checkout's own packages, each required by path from packages/<name>, and
# `first`, which linger requires first and whose build directory is linger's own: a workspace
# looks for a module in its dependencies' builds, the first required last, before its own, and
# each package names its challenge `Challenge`, as linger does, so once a package was built on its
# own, its `Challenge` would otherwise stand in for linger's in linger's audit and comparator.
checkout_packages="$(git ls-files 'packages/*/lakefile.lean' | awk -F/ '{ print $2 }' | sort -u)"
[ -n "$checkout_packages" ] || fail "no package under packages/"
[ "$(code_grep '^[[:space:]]*require ' 'lakefile.lean' | sed 's/^[^:]*:[0-9]*:[[:space:]]*//' | sort)" \
    = "$( { printf 'require first from "first"\nrequire software_challenge from git\n'
            for p in $checkout_packages; do printf 'require %s from "packages/%s"\n' "$p" "$p"; done; } \
          | sort)" ] \
  || fail "lakefile.lean may require only first, the challenge library, from git, and each package under packages/, by path"
[ "$(code_grep '^[[:space:]]*require ' 'lakefile.lean' | sed -n '1s/^[^:]*:[0-9]*:[[:space:]]*//p')" \
    = 'require first from "first"' ] \
  || fail "lakefile.lean must require first before anything else, so that linger's build comes first on its search path"
[ "$(code_grep '^package ' first/lakefile.lean | sed 's/^[^:]*:[0-9]*://')" \
    = 'package first where buildDir := "../.lake/build"' ] \
  && [ -z "$(code_grep '^(@[[][^]]*[]][[:space:]]*)?(require|lean_lib|lean_exe|target|extern_lib|script)[[:space:]]' first/lakefile.lean)" ] \
  || fail "first/lakefile.lean must declare only a package whose build directory is linger's"
lake_packages="$(tr -d ' \n' < lake-manifest.json | grep -o '"packages":\[[^]]*\]')"
[ "$(printf '%s' "$lake_packages" | grep -o '"name":"[^"]*"' | sort | tr '\n' ' ')" \
    = "$( { printf '"name":"first"\n"name":"software_challenge"\n'
            for p in $checkout_packages; do printf '"name":"%s"\n' "$p"; done; } | sort | tr '\n' ' ')" ] \
  && printf '%s' "$lake_packages" | grep -q '"url":"https://github.com/vincentqb/lean-software-challenge"' \
  && printf '%s' "$lake_packages" | grep -qE '"inputRev":"[0-9a-f]{40}"' \
  && printf '%s' "$lake_packages" \
    | grep -qF '"type":"path","scope":"","name":"first","manifestFile":"lake-manifest.json","inherited":false,"dir":"first"' \
  || fail "lake-manifest may list only first, by path, software_challenge, pinned to a commit, and this checkout's packages"
for p in $checkout_packages; do
  printf '%s' "$lake_packages" \
    | grep -qF "\"type\":\"path\",\"scope\":\"\",\"name\":\"$p\",\"manifestFile\":\"lake-manifest.json\",\"inherited\":false,\"dir\":\"packages/$p\"" \
    || fail "lake-manifest.json must take package $p by path from packages/$p"
done
for manifest in packages/*/lake-manifest.json; do
  pkg_packages="$(tr -d ' \n' < "$manifest" | grep -o '"packages":\[[^]]*\]')"
  [ "$(printf '%s' "$pkg_packages" | grep -o '"rev":"[0-9a-f]*"')" = "$(printf '%s' "$lake_packages" | grep -o '"rev":"[0-9a-f]*"')" ] \
    && tr -d ' \n' < "$manifest" | grep -q '"packagesDir":"../../.lake/packages"' \
    || fail "$manifest must pin software_challenge to linger's commit, in linger's packages"
done
# The audit stays a default target, and the verifier builds every default target: CI starts
# from a fresh checkout, so a default target missing from that list is never built there.
default_targets="$(code_grep '^@[[]default_target[]]' lakefile.lean \
  | sed 's/^[^:]*:[0-9]*:@[[]default_target[]][[:space:]]*//' | awk '{ print $2 }')"
printf '%s\n' "$default_targets" | grep -qx audit \
  || fail "the Lean Software Challenge audit is no longer a default target"
verify_build="$(awk '
  /^[.][/]lake --rehash --wfail build / { on = 1 }
  on { words = words " " $0; if ($0 !~ /[\\]$/) { print words; exit } }' scripts/verify.sh \
  | sed 's/>.*//; s/[\\]//g' | tr -s ' \t' '\n\n')"
[ -n "$verify_build" ] || fail "scripts/verify.sh lost its build command"
for default_target in $default_targets; do
  printf '%s\n' "$verify_build" | grep -qx "$default_target" \
    || fail "scripts/verify.sh does not build the default target $default_target"
done

# Import gates read the module header: `module_imports` gives its import lines, and
# `import_closure <file> <imports>` pins a module's exact imports, so that taking one out, as adding
# one, is a reviewable edit here. The challenge library's audit already holds every module to its
# role's imports (`CoreCode` imports only `CoreSpec` and `CoreCode`, and so on), and a package
# imports nothing of linger's, so these pin what roles do not: which pure modules a policy reads.
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
# Named targets must build the promised roots, not just happen to succeed.
# Read declaration lines through code_grep, then compare their verbatim Name
# literals: multiple backticks on a roots line are Lean syntax, not prose.
library_decl() {                             # `lean_lib $1` with its indented fields
  lake_decl lean_lib "$1"
}
lake_decl() {                                # `$1 $2` (`package linger`) with its indented fields
  code_grep '.' lakefile.lean \
    | sed 's/^[^:]*:[0-9]*://' \
    | awk -v kind="$1" -v name="$2" '
        /^--/ { next }
        /^(@[[][^]]*[]][[:space:]]+)?[a-z_]+[[:space:]]/ {
          sub(/^@[[][^]]*[]][[:space:]]+/, ""); active = ($1 == kind && $2 == name)
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
[ "$(library_decl Linger)" = "lean_lib Linger where leanOptions := implementationOptions " ] \
  || fail "the Linger library lost implementationOptions: $(library_decl Linger)"
# The checks of linger's world claims are a default target, so the audit counts them: the Checks
# library builds exactly each component's `WorldCode/Checks.lean`, which no program module imports.
checks_want="$(git ls-files -- 'Linger/*/WorldCode/Checks.lean' | sed 's/[.]lean$//; s#/#.#g' \
  | awk '{ printf "%s.one `%s", (NR > 1 ? ", " : ""), $0 }')"
[ -n "$checks_want" ] || fail "no module holds linger's checks"
[ "$(library_decl Checks)" = "lean_lib Checks where globs := #[$checks_want] leanOptions := implementationOptions " ] \
  || fail "the Checks library must build exactly each WorldCode/Checks.lean: $(library_decl Checks)"
checks_imported="$(module_imports '*/CoreSpec*.lean' '*/CoreCode*.lean' '*/WorldSpec*.lean' \
    '*/WorldCode*.lean' Linger.lean | awk -F: "$IMPORT_AWK"'
  import_mod($3) ~ /[.]WorldCode[.]Checks$/ { print "  " $1 ": " $3 }')"
[ -z "$checks_imported" ] || {
  printf '%s\n' "$checks_imported" >&2
  fail "a module of the program imports a module of checks, whose code would then ship in linger"; }
[ "$(git grep -c 'def implementationOptions : Array LeanOption := #\[⟨`linter.missingDocs, true⟩\]$' -- lakefile.lean)" = lakefile.lean:1 ] \
  || fail "implementationOptions no longer enables linter.missingDocs"
# Each package under packages/ builds with linger's options and its own audit, and shares the
# checkout's packages, so its code meets the same bar and building it alone fetches nothing.
for p in $checkout_packages; do
  pkg="packages/$p"
  grep -qx "package $p where" "$pkg/lakefile.lean" || fail "$pkg/lakefile.lean does not declare package $p"
  for opt in '⟨`autoImplicit, false⟩' '⟨`relaxedAutoImplicit, false⟩' '⟨`warningAsError, true⟩' \
      '⟨`linter.extra.unreachableTactic, true⟩' '⟨`linter.redundantVisibility, true⟩' \
      '⟨`linter.extra.unnecessarySeqFocus, true⟩' 'packagesDir := "../../.lake/packages"' \
      'def implementationOptions : Array LeanOption := #[⟨`linter.missingDocs, true⟩]' \
      '@[default_target] target audit pkg : Unit := do'; do
    grep -qF "$opt" "$pkg/lakefile.lean" || fail "$pkg/lakefile.lean lost $opt"
  done
  for file in Challenge.lean owned.lock lake-manifest.json lean-toolchain .lean-fmt.toml; do
    [ -n "$(git ls-files -- "$pkg/$file")" ] || fail "$pkg has no tracked $file"
  done
  cmp -s lean-toolchain "$pkg/lean-toolchain" || fail "$pkg/lean-toolchain differs from linger's"
  cmp -s .lean-fmt.toml "$pkg/.lean-fmt.toml" || fail "$pkg/.lean-fmt.toml differs from linger's"
done
# With `set_option` banned, the package's options and these declarations' fields are every
# option a module is built with, so each declaration that can carry options is pinned.
[ "$(lake_decl package linger)" = "package linger where leanOptions := #[⟨\`autoImplicit, false⟩, ⟨\`relaxedAutoImplicit, false⟩, ⟨\`warningAsError, true⟩, ⟨\`linter.extra.unreachableTactic, true⟩, ⟨\`linter.redundantVisibility, true⟩, ⟨\`linter.extra.unnecessarySeqFocus, true⟩] " ] \
  || fail "the package options changed: $(lake_decl package linger)"
[ "$(library_decl Verify)" = "lean_lib Verify where " ] \
  || fail "the Verify library gained fields: $(library_decl Verify)"
for exe in "linger \`Linger.App.WorldCode.Main" "lingertest \`Linger.Os.Suites.Shim" "suites \`Verify.Main"; do
  [ "$(lake_decl lean_exe "${exe% *}")" = "lean_exe ${exe% *} where root := ${exe#* } " ] \
    || fail "the ${exe% *} executable must declare only its root: $(lake_decl lean_exe "${exe% *}")"
done
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
module_imports packages/terminal/Terminal/Proofs/Vt.lean 'packages/terminal/Terminal/Proofs/Vt/*' packages/terminal/Terminal/Proofs/Mediation.lean packages/terminal/Terminal/Proofs/Title.lean \
  packages/terminal/Terminal/Proofs/Replay.lean packages/terminal/Terminal/Proofs/Render.lean 'packages/terminal/Terminal/Proofs/Render/*' \
| awk -F: "$IMPORT_AWK"'
  { mod = import_mod($3)
    if (mod !~ /^(Terminal[.](CoreCode[.](Vt|Render|Mediation|Title|Replay)|CoreSpec)|Terminal[.]Proofs[.]((Vt|Render)([.][[:alnum:]_]+)*|Mediation|Title|Replay)|Init[.]Data[.]String[.]Legacy)$/) {
      print "  " $0; bad = 1
    }
  }
  END { exit bad }' >&2 || fail "the VT proofs import outside the standalone library boundary"

# Entry and manager policies have explicit, small import closures. `main`
# composes their executors with the session backend. The session library never
# imports them, even through an intermediate module: every library import stays in
# the closure that the check after `Linger.lean`'s list below declares.
import_closure Linger/Import/CoreSpec.lean ''
import_closure Linger/Import/CoreCode/Resurrect.lean 'public import Linger.Import.CoreSpec;import Linger.Target.CoreCode.Name;import Linger.Display.CoreCode.Status;public import Terminal.CoreCode.Vt;public import Linger.Session.CoreSpec;'
import_closure Linger/Selector/CoreCode/Key.lean 'public import Linger.Selector.CoreSpec;public import Input.CoreSpec;'
import_closure Linger/Selector/CoreCode/Fetch.lean 'public import Linger.Selector.CoreSpec;'
import_closure Linger/Selector/CoreSpec.lean ''
import_closure packages/fuzzy/Fuzzy/CoreCode.lean 'public import Fuzzy.CoreSpec;'
import_closure packages/fuzzy/Fuzzy/CoreSpec.lean ''
import_closure Linger/Selector/CoreCode/Picker.lean 'import Input.CoreCode;public import Linger.Selector.CoreSpec;import Fuzzy.CoreCode;import Linger.Target.CoreCode.Name;import Linger.Display.CoreCode.Listing;public import Linger.Display.CoreSpec;import Linger.Display.CoreCode.Status;import Linger.Target.CoreCode.Remote;import Terminal.CoreCode.Vt;import Terminal.CoreCode.Render;import Linger.Display.CoreCode.View;'
import_closure Linger/Display/CoreCode/View.lean 'public import Linger.Display.CoreSpec;import Linger.Display.CoreCode.Status;'
import_closure Linger/Display/CoreSpec.lean ''
import_closure Linger/Display/CoreCode/Status.lean 'public import Linger.Display.CoreSpec;'
import_closure packages/input/Input/CoreCode.lean 'public import Input.CoreSpec;'
import_closure packages/input/Input/CoreSpec.lean ''
import_closure packages/input/Input/Proofs.lean 'public import Input.CoreCode;import all Input.CoreCode;'
import_closure packages/os/Os/CoreSpec.lean ''
import_closure packages/os/Os/CoreCode/Wait.lean ''
import_closure Linger/App/CoreCode/Entry.lean 'public import Linger.App.CoreSpec;import Linger.Target.CoreSpec;import Linger.Target.CoreCode.Remote;'
import_closure Linger/App/CoreSpec.lean 'public import Linger.Os.CoreSpec;public import Linger.Session.CoreSpec;'
import_closure Linger/Target/CoreCode/Name.lean 'import Linger.Target.CoreSpec;'
import_closure Linger/Target/CoreCode/Remote.lean 'import Linger.Target.CoreCode.Name;public import Linger.Target.CoreSpec;'
import_closure Linger/Display/CoreCode/Title.lean 'import Linger.Target.CoreCode.Name;'
import_closure Linger/Os/CoreCode/Env.lean ''
# The answers every command gives sit in the bottom layer and depend on nothing above it.
import_closure Linger/Os/CoreSpec.lean ''
import_closure Linger/Os/CoreCode/Answer.lean 'public import Linger.Os.CoreSpec;'
import_closure packages/os/Os/WorldSpec.lean 'import SoftwareChallenge.Commands;'
# packages/os/Os/WorldCode.lean is the one module that sees the private bindings: the one module
# that imports all of Os.WorldSpec. Others import it plainly, for the world claim it states.
[ "$(module_imports '*.lean' | awk -F: "$IMPORT_AWK"'
    $3 ~ /import[[:space:]]+all[[:space:]]/ && import_mod($3) == "Os.WorldSpec" && !seen[$1]++ { print $1 }')" \
    = "packages/os/Os/WorldCode.lean" ] \
  || fail "a module other than packages/os/Os/WorldCode.lean imports all of Os.WorldSpec, whose bindings are private"
# `import all` transits (see the Vt friend set below), so `import all Os.WorldCode` would
# grant the private bindings it wraps: every other module imports it plainly.
shell_all="$(module_imports '*.lean' | awk -F: "$IMPORT_AWK"'
  $3 ~ /import[[:space:]]+all[[:space:]]/ && import_mod($3) == "Os.WorldCode" { print "  " $0 }')"
[ -z "$shell_all" ] || {
  printf '%s\n' "$shell_all" >&2
  fail "import all Os.WorldCode grants the private bindings of Os.WorldSpec: import it plainly"; }
import_closure packages/os/Os/WorldCode/Command.lean 'import Os.WorldCode;'
import_closure Linger/Import/WorldCode.lean 'public import Linger.Os.CoreSpec;import Linger.Os.CoreCode.Answer;import Linger.Import.CoreCode.Resurrect;import Linger.Session.CoreCode.Checkpoint;import Os.WorldCode;import Linger.Display.CoreCode.Listing;import Linger.Session.WorldCode.Paths;import Linger.Session.WorldCode.Resume;import Linger.Session.WorldCode.Inventory;import Os.WorldCode.Command;import Linger.Target.CoreCode.Remote;import Linger.Selector.WorldCode;import Linger.Selector.CoreCode.Picker;import Std.Async.System;import Linger.Os.CoreCode.Env;'
import_closure Linger/Selector/WorldCode.lean \
  'public import Linger.Selector.CoreSpec;public import Linger.Os.CoreSpec;import Linger.Os.CoreCode.Answer;import Linger.Selector.CoreCode.Picker;import Os.WorldCode;import Linger.Target.CoreCode.Remote;import Terminal.CoreCode.Title;import Os.WorldCode.Command;import Linger.Display.CoreCode.View;import Std.Data.HashMap.Basic;import Linger.Display.CoreCode.Status;import Linger.Selector.CoreCode.Key;import Linger.Selector.CoreCode.Fetch;import Input.CoreCode;import Linger.Os.CoreCode.Env;'
import_closure Linger/App/WorldCode/Main.lean \
  'import Linger.Os.CoreCode.Answer;import Linger.App.WorldCode;import Linger.App.CoreCode.Entry;import Linger.Selector.WorldCode;import Linger.Import.WorldCode;'
# `lean_lib Linger` builds the umbrella's closure, so this list is what `./lake build`
# checks of the session library.
import_closure Linger.lean "$(printf 'public import %s;' Linger.Session.CoreCode.Buf \
  Linger.Session.CoreCode.Wire Terminal.CoreCode.Vt Linger.Target.CoreCode.Name \
  Linger.Session.CoreCode Linger.Session.CoreCode.Driver Linger.Session.CoreCode.Checkpoint \
  Linger.Target.CoreCode.Remote Linger.Display.CoreCode.Listing Linger.Display.CoreCode.Status \
  Linger.Display.CoreCode.Title Linger.Display.CoreCode.View Linger.Os.CoreCode.Env \
  Linger.Session.WorldCode.Paths Linger.Session.WorldCode.Daemon Linger.Session.WorldCode.Client \
  Linger.Session.WorldCode.Inventory Linger.App.CoreCode.Commands Linger.App.WorldCode \
  Linger.Session.WorldCode.Resume)"
module_imports ':(glob)Linger/Session/*.lean' 'Linger/Session/CoreCode/*' 'Linger/Session/WorldCode/*' \
    packages/os/Os/WorldCode/Command.lean Linger/App/WorldCode.lean packages/os/Os/WorldSpec.lean packages/os/Os/WorldCode.lean \
    Linger/Os/CoreCode/Env.lean Linger/Target/CoreCode/Name.lean Linger/Target/CoreCode/Remote.lean Linger/Display/CoreCode/Status.lean \
    Linger/Display/CoreCode/Title.lean Linger/Display/CoreCode/Listing.lean packages/terminal/Terminal/CoreCode/Vt.lean \
    packages/terminal/Terminal/CoreCode/Render.lean packages/terminal/Terminal/CoreCode/Mediation.lean packages/terminal/Terminal/CoreCode/Title.lean \
    packages/terminal/Terminal/CoreCode/Replay.lean Linger.lean \
| awk -F: "$IMPORT_AWK"'
  { mod = import_mod($3)
    if (mod !~ /^(Linger[.](Session|Os|Target|Display)[.][[:alnum:]_.]+|Terminal[.][[:alnum:]_.]+|Os[.][[:alnum:]_.]+|Linger[.]App[.](WorldCode|CoreSpec|CoreCode[.](Commands|Wait|Recovery|Capture))|Std[.]Async[.](System|Signal))$/ \
        && mod != "SoftwareChallenge.Commands") {
      print "  " $0; bad = 1
    }
  }
  END { exit bad }' >&2 || fail "the session library imports outside its declared closure"

# Components depend downward only, as AGENTS.md's layout lists them: a module imports
# modules of its own component or of a lower layer, never a peer's or a higher one's.
# Suites run the composed program and may import any component. A component this table
# does not name fails, so a new one has to be placed before it can import anything.
component_layers='Os:0 Target:0 Display:1 Session:2 Selector:2 Import:3 App:4'
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

# Headline theorems. The challenge library reads Challenge.lean: the build writes comparator.json
# from it, the audit holds it to holes and theorems and each headline to a kill marked
# `@[kills headline]`, and `./lake comparator` checks that Theorems.Solution proves the same
# statements. What the audit does not see is outside linger, which it trusts: so a statement's
# meaning rests on no package's code either, as a spec module imports, from anywhere, only spec
# modules, a CoreSpec or WorldSpec one, and the library's syntax, and none of them all of one.
spec_imports_bad="$(module_imports 'Linger/*/CoreSpec*.lean' 'Linger/*/WorldSpec*.lean' \
| awk -F: "$IMPORT_AWK"'
  function role(mod,    n, i, part) {
    n = split(mod, part, ".")
    for (i = 1; i <= n; i++) if (part[i] ~ /^(CoreSpec|CoreCode|WorldSpec|WorldCode)$/) return part[i]
    return "" }
  { mod = import_mod($3); r = role(mod)
    if ($3 ~ /import[[:space:]]+all[[:space:]]/ \
        || (r != "CoreSpec" && r != "WorldSpec" && mod != "SoftwareChallenge.Commands"))
      print "  " $0 }')"
[ -z "$spec_imports_bad" ] || {
  printf '%s\n' "$spec_imports_bad" >&2
  fail "a spec module imports code: it may import only CoreSpec and WorldSpec modules, and SoftwareChallenge.Commands"; }
[ "$(library_decl Challenge)" = "lean_lib Challenge where leanOptions := #[⟨\`warn.sorry, false⟩] " ] \
  || fail "the Challenge library may silence only its sorry warnings: $(library_decl Challenge)"
! grep -qE '^@[[]default_target[]][[:space:]]+lean_lib Challenge' lakefile.lean \
  || fail "the Challenge library proves nothing; keep it out of the default targets"

# Pure route proofs do not observe terminal IO or inspect `main`'s call sites, so these ties
# keep its dispatch on the proved route; Linger.App.Suites.Manager,
# Linger.Import.Suites.Recipes and Linger.Import.Suites.Interop exercise it in subprocesses.
# Every route gives an answer, which `main` binds as one `Linger.Os.Answer`, so each executor
# returns one, and the process exits only with that answer's code (`code_documented`).
# Fold layout whitespace for `main`'s small dispatch. Reuse the backtick-aware
# matcher below, so quoted prose cannot stand in for these call sites.
entry_code="$(awk '{ $1 = $1; printf "%s ", $0 }' Linger/App/WorldCode/Main.lean)"
for tie in \
  'def main [(]args : List String[)] : IO UInt32 := do let answer : Linger[.]Os[.]Answer ← try match Linger[.]App[.]Entry[.]route args with' \
  '[|] [.]selector readOnly => Linger[.]Selector[.]Shell[.]run [(]← IO[.]appPath[)][.]toString readOnly' \
  '[|] [.]tmux rest => Linger[.]Import[.]Shell[.]run [(]← IO[.]appPath[)][.]toString rest' \
  '[|] [.]session argv => Linger[.]App[.]Shell[.]main argv' \
  '[|] [.]malformed => IO[.]eprintln "linger: malformed encoded command line" pure [.]usage' \
  'catch e => IO[.]eprintln s!"linger: [{]e[}]" pure [.]notDone return answer[.]code'; do
  printf '%s\n' "$entry_code" | CG_RE="(^|[[:space:]])$tie([[:space:]]|$)" awk "$CODE_AWK" >/dev/null \
    || fail "entry point bypassed its proved route or fixed IO boundary: $tie"
done
[ "$(code_count '(^|[^[:alnum:]_.])return([^[:alnum:]_]|$)' Linger/App/WorldCode/Main.lean)" -eq 1 ] \
  || fail "Linger/App/WorldCode/Main.lean returns other than through its one exit, the code of its route's answer"

# Every exit is an answer: `main` exits with the code of the answer its route gives (above), and
# the executors it routes to answer in `Linger.Os.Answer`, the selector and the tmux interchange
# as the session commands do. So in the command shells a function that yields a process status,
# one declared to return an answer, or a `UInt32` or `UInt8` as `main` and `IO.Process.exit` take,
# returns no literal number; `IO.Process.exit` takes only an answer's code; and a daemon reports
# why a program did not start with an answer's code, which its command exits with. Other numbers
# in the shells, as durations, sizes and descriptors, are no status and pass.
# shellcheck disable=SC2016  # $0 below is awk's record; single quotes are the point
STATUS_AWK='
# The type after the last top-level colon of a declaration header, up to its top-level ":=",
# which sets `assigned`; brackets and braces nest as parentheses do.
function result(header,    n, i, c, depth, colon) {
  n = length(header); depth = 0; colon = 0; assigned = 0
  for (i = 1; i <= n; i++) {
    c = substr(header, i, 1)
    if (c == "(" || c == "[" || c == "{") depth++
    else if (c == ")" || c == "]" || c == "}") depth--
    else if (depth == 0 && c == ":") {
      if (substr(header, i + 1, 1) == "=") { assigned = 1; return substr(header, colon + 1, i - colon - 1) }
      colon = i } }
  return colon ? substr(header, colon + 1) : "" }
function settle(type) {
  gsub(/[[:space:]]+/, " ", type); sub(/^ /, "", type); sub(/ $/, "", type)
  yields = type ~ /^(IO|BaseIO) (Answer|Os[.]Answer|Linger[.]Os[.]Answer|UInt32|UInt8)$/; open = 0 }
FNR == 1 { open = 0; yields = 0; header = "" }
# A command in column 0 ends the declaration before it, and a definition begins one, whose header
# runs to its top-level ":=" or its first match alternative. Other lines in column 0, as those
# of a doc comment or a string literal, continue what they are in.
/^([/]-|@[[]|#|((private|protected|public|noncomputable|partial|unsafe|meta)[[:space:]]+)*(def|abbrev|instance|theorem|lemma|opaque|axiom|example|structure|inductive|class|section)([[:space:]]|$)|(namespace|end|mutual)([[:space:]]|$)|(open|variable)[[:space:]])/ {
  open = 0; yields = 0; header = ""
  if ($0 ~ /^(@[[][^]]*[]][[:space:]]*)*((private|protected|public|noncomputable|partial|unsafe)[[:space:]]+)*(def|abbrev|instance)([[:space:]]|$)/)
    open = 1 }
open && header != "" && /^[[:space:]]*[|]/ { settle(result(header)) }
open { header = header " " $0; type = result(header); if (assigned) settle(type) }
yields { print FILENAME ":" FNR }'
shell_paths="$(git ls-files -- 'Linger/*/WorldCode.lean' 'Linger/*/WorldCode/*')"
[ -n "$shell_paths" ] || fail "no command shells found"
# shellcheck disable=SC2086  # one tracked path per word
status_lines="$(awk "$STATUS_AWK" $shell_paths /dev/null)"
# The reader must find what `main` and the two executors below the command line yield.
for entry in 'Linger/App/WorldCode/Main.lean:^def main ' 'Linger/Selector/WorldCode.lean:^def run ' 'Linger/Import/WorldCode.lean:^def run '; do
  entry_line="$(grep -n "${entry#*:}" "${entry%%:*}" | cut -d: -f1)"
  printf '%s\n' "$status_lines" | grep -qx "${entry%%:*}:${entry_line:-none}" \
    || fail "the reader of the shell headers no longer finds the process status that ${entry%%:*} yields"
done
status_bad="$(
  { printf '%s\n' "$status_lines" '#literals'
    code_grep '(^|[^[:alnum:]_.])(return|pure)[[:space:]]+[(]*-?[0-9]' 'Linger/*/WorldCode.lean' 'Linger/*/WorldCode/*' || true; } \
  | awk -F: '!literals { if ($0 == "#literals") literals = 1; else yields[$0] = 1; next }
      ($1 ":" $2) in yields { print "  " $0 }'
  code_grep '(^|[^[:alnum:]_.])IO[.]Process[.]exit([^[:alnum:]_]|$)' 'Linger/*/WorldCode.lean' 'Linger/*/WorldCode/*' \
  | awk '{ rest = substr($0, index($0, "IO.Process.exit") + 15)
      if (rest !~ /[.]code([^[:alnum:]_]|$)/ || rest ~ /^[[:space:](]*-?[0-9]/) print "  " $0 }'
  code_grep '[.]failed[[:space:]]+[(]*-?[0-9]' 'Linger/*/WorldCode.lean' 'Linger/*/WorldCode/*' | sed 's/^/  /')"
[ -z "$status_bad" ] || {
  printf '%s\n' "$status_bad" >&2
  fail "a literal exit status in a command shell: answer with a Linger.Os.Answer and exit with its code"; }

# The proof covers the returned parser/plan values. These call-site gates make
# bypassing them a reviewable change; IO tests check preflight/failure ordering
# and actual argv. As with the runtime ties below, this is not an IO theorem.
code_grep '^[[:space:]]+IO[.]eprintln s!"linger tmux [{]command[}]: [{]diagnostic [(]toString e[)][}]"$' Linger/Import/WorldCode.lean >/dev/null \
  || fail "tmux commands no longer display the proved control-free diagnostic"
code_grep '^[[:space:]]+let content ← IO[.]FS[.]readFile path$' Linger/Import/WorldCode.lean >/dev/null \
  || fail "tmux catalog no longer reads the complete resolved save before parsing"
code_grep '^[[:space:]]+let panes ← IO[.]ofExcept [(]parseSave home content[)]$' Linger/Import/WorldCode.lean >/dev/null \
  || fail "tmux catalog no longer consumes the proved whole-save parser"
code_grep '^[[:space:]]+for pane in plan existing panes do$' Linger/Import/WorldCode.lean >/dev/null \
  || fail "importer no longer iterates the proved import plan"
import_code="$(awk '{ $1 = $1; printf "%s ", $0 }' Linger/Import/WorldCode.lean)"
# An import only writes: it names no command that would start a session's program.
! code_grep '"(resume|start)"' Linger/Import/WorldCode.lean \
  || fail "the importer starts a program; an import writes checkpoints only"
printf '%s\n' "$import_code" | CG_RE='(^|[[:space:]])[|] "import" => importSave executable paths[.]head[?]; return [.]done([[:space:]]|$)' awk "$CODE_AWK" >/dev/null \
  || fail "importer no longer forwards the entry point executable"
code_grep '^[[:space:]]+let listing ← IO[.]Process[.]output [{] cmd := executable, args := #[[]"ls", "--porcelain"[]] [}]$' Linger/Import/WorldCode.lean >/dev/null \
  || fail "importer no longer lists with the supplied executable"
# Native listing observes the caller's checkpoint namespace, including its
# no-HOME `/tmp` fallback. Only those fields reach the checked serializer.
printf '%s\n' "$import_code" | CG_RE='(^|[[:space:]])private def writeSave [(]path : String[)] [(]capture : IO [(]List [(]String × String[)][)] := snapshot[)] : IO Unit := do let fields ← capture let content ← IO[.]ofExcept [(]renderSave fields[)] publish path content([[:space:]]|$)' awk "$CODE_AWK" >/dev/null \
  || fail "exporter bypasses the current native snapshot, checked serializer or exclusive publication"
printf '%s\n' "$import_code" | CG_RE='(^|[[:space:]])[|] _ => writeSave [(]paths[.]headD ""[)]; return [.]done([[:space:]]|$)' awk "$CODE_AWK" >/dev/null \
  || fail "export command bypasses its native snapshot"
# Both views consume the same ordered catalog. Display strings are scrubbed;
# action fields have string-literal framing so display cleanup cannot retarget them.
# Acceptance must use the displayed snapshot, then pass its exact validated
# record to the shared creation executor. A suite checks the save-refresh race.
for tie in \
  'let save ← readSave origin home file let rows := catalogRows save[.]content save[.]panes' \
  'let value := if [[]"directory", "session", "window", "pane", "title", "command", "saved-command", "window-title"[]][.]contains key then value[.]quote else diagnostic value' \
  'Os[.]Shell[.]writeAll Os[.]Shell[.]stdoutFd [(]ByteArray[.]mk [(]Linger[.]Display[.]Listing[.]terminalListing withColor none rows[)][.]toArray[)]' \
  'let save ← readSave origin home file createPanes executable origin save[.]panes [(]readArchive save[.]path[)]' \
  'let path ← savePath origin home file let stops ← Os[.]Shell[.]watch Os[.]Shell[.]handbackSignals try while true do match ← Linger[.]Selector[.]Shell[.]choose executable [(]some path[.]toString[)] [(]stopped := stops[.]heard[)] with' \
  '[|] [.]attach target displayed => unless displayed[.]candidates[.]contains target do throw [(]IO[.]userError "selected pane was absent from the displayed save"[)] let row := displayed[.]row target' \
  'let some dir := [(]row[.]lookup "directory"[)][.]bind fun value => [(]Lean[.]Syntax[.]decodeStrLit value[)][.]filter [(]·[.]quote == value[)] [|] throw [(]IO[.]userError "selected pane has no directory"[)]' \
  'let some pane := selectedPane target dir line details [|] throw [(]IO[.]userError "invalid selected pane"[)]' \
  'createPanes executable origin [[]pane[]] archive let child ← IO[.]Process[.]spawn [{] cmd := executable, args := Linger[.]Selector[.]Shell[.]attachArgs pane[.]name, cwd := some [(]System[.]FilePath[.]mk pane[.]dir[)] [}] discard child[.]wait if ← stops[.]heard then return [.]interrupted' \
  'let panes := panes[.]map [(]preparePane content panes[)]' \
  'let archive ← if [(]plan existing panes[)][.]isEmpty then pure none else archive for pane in plan existing panes do let contents ← capturedPane archive pane discard <[|] seedPane pane contents' \
  'preflight origin panes let listing ← IO[.]Process[.]output [{] cmd := executable, args := #[[]"ls", "--porcelain"[]] [}]'; do
  printf '%s\n' "$import_code" | CG_RE="(^|[[:space:]])$tie([[:space:]]|$)" awk "$CODE_AWK" >/dev/null \
    || fail "tmux browser lost its catalog, displayed selection or preflight contract: $tie"
done
# Captures belong to the adjacent latest save only. Freeze their revision across
# display and acceptance, read the exact proved member to stdout, then publish
# the proved checkpoint while owning both identity locks, whole and durably as a
# daemon's saves are (`Os.Shell.replaceFile`). No saved command is run.
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
  'then return false Os[.]Shell[.]replaceFile path [(]Linger[.]Session[.]Checkpoint[.]saveBytes [(]checkpoint pane contents[)][)] return true' \
  'pending[.]set [(]some [(]← Command[.]startLimited "tar" args limit[)][)] let deadline := [(]← Os[.]Shell[.]monotonicMs[)] [+] 5000' \
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
  'let deadline := [(]← Os[.]Shell[.]monotonicMs[)] [+] 1000 repeat' \
  'unless ← Os[.]Shell[.]nap deadline 10 do break throw [(]IO[.]userError "tmux configuration query timed out; pass a save file explicitly"[)]' \
  'finally Command[.]stop pending' \
  'match file with [|] some path => pure path [|] none => if let some dir[[:space:]]*← configuredDirectory then' \
  'let path := System[.]FilePath[.]mk path return if path[.]isAbsolute then path else origin / path' \
  'let path ← IO[.]FS[.]realPath save let metadata ← path[.]metadata let content ← IO[.]FS[.]readFile path'; do
  printf '%s\n' "$import_code" | CG_RE="(^|[[:space:]])$tie([[:space:]]|$)" awk "$CODE_AWK" >/dev/null \
    || fail "tmux discovery lost its explicit path, polling deadline or child cleanup: $tie"
done

# Selector and decoder proofs concern pure values. Tie each IO consumer to the
# proved function, build attach argv from Remote.targetOperands and retain an
# immutable poll snapshot. A native visit queries remote hosts only when Picker.fetch, fed every
# key and every listing it starts, says remote rows are due (fetch_follows_events): when it opens,
# and at once after the refresh key, which also clears and redraws the screen: the next paint is a
# whole frame, as after a resize. Its other listings list local rows alone and keep the last full
# listing's remote rows (withRemote_row_local, withRemote_row_remote), and the header gives their
# age (Picker.ageParts) from the start of the listing that fetched them, as of each listing, so
# no timer of its own repaints it.
# Linger.App.Suites.Manager drives the terminal lifetime, failure paths, cadence and handoff itself.
for tie in \
  'let listed ← IO[.]ofExcept [(]Linger[.]Selector[.]Picker[.]parseSnapshot result[.]stdout[)]' \
  'let incoming := if full then listed else listed[.]withRemote lastFull' \
  'let mut state := Linger[.]Selector[.]Picker[.]init [[]] [(]!savedTmux && !readOnly[)]' \
  'let mut decoder := Input[.]init' \
  'let mut remoteDue := true' \
  'remoteDue := Linger[.]Selector[.]Picker[.]fetch remoteDue [(][.]key key[)]' \
  'full := savedTmux [|][|] remoteDue' \
  'remoteDue := Linger[.]Selector[.]Picker[.]fetch remoteDue [.]list' \
  'let fds := #[[]stdinFd[]]' \
  'let events := #[[]POLLIN[]]' \
  'let ready ← poll fds events 50' \
  'writeAll stdoutFd [(]ByteArray[.]mk Linger[.]Selector[.]Picker[.]enterAnsi[.]toArray[)]' \
  'writeAll stdoutFd [(]ByteArray[.]mk [(]Terminal[.]Title[.]ansi "linger"[)][.]toArray[)]' \
  'writeAll stdoutFd [(]ByteArray[.]mk Linger[.]Selector[.]Picker[.]exitAnsi[.]toArray[)]' \
  'writeAll stdoutFd [(]ByteArray[.]mk [(]Terminal[.]Title[.]ansi ""[)][.]toArray[)]' \
  'discard child[.]wait' \
  'let child ← IO[.]Process[.]spawn [{] cmd := executable, args := attachArgs target readOnly [}]'; do
  code_grep "^[[:space:]]+$tie$" Linger/Selector/WorldCode.lean >/dev/null \
    || fail "manager bypassed a proved value or fixed IO boundary: $tie"
done
picker_code="$(awk '{ $1 = $1; printf "%s ", $0 }' Linger/Selector/WorldCode.lean)"
# Pin traversal through shared row pieces, frame insertion and complete metadata
# replacement. Computing rows or refreshed state without consuming them is
# insufficient. The loop seams fix the frame, poll/decode/step, then refresh ordering.
# A completed snapshot must not replace the target underneath an unread key.
# Preserve byte order and consume both decoder results through the proved
# application binding before dispatch.
for tie in \
  'for byte in bytes do let [(]next, emitted[)] := Input[.]feed decoder byte decoder := next keys := keys [+][+] [(]emitted[.]filterMap Linger[.]Selector[.]Key[.]ofInput[)][.]toArray else if Input[.]pending decoder && [(]← monotonicMs[)] - lastInput ≥ 150 then let [(]next, emitted[)] := Input[.]flush decoder decoder := next keys := [(]emitted[.]filterMap Linger[.]Selector[.]Key[.]ofInput[)][.]toArray for key in keys do' \
  'let incomingStatuses := statusesOf incoming let ordered := Linger[.]Display[.]View[.]sort [(]incomingStatuses[.]getD · [.]unknown[)] incoming[.]candidates let next := if loaded then Linger[.]Selector[.]Picker[.]refresh state ordered incoming[.]descriptions else [{] [(]Linger[.]Selector[.]Picker[.]init ordered state[.]allowCreate[)] with query := state[.]query, descriptions := incoming[.]descriptions [}] let atHome := incoming[.]atHome home let now ← monotonicMs let age := fetched[.]map fun start => [(]now - start[)] / 1000 dirty := dirty [|][|] !loaded [|][|] next != state [|][|] atHome != snapshot [|][|] age != remoteAge state := next snapshot := atHome statuses := incomingStatuses remoteAge := age loaded := true nextListing := [(]← monotonicMs[)] [+] 1000' \
  'while true do let current ← winsizeGet stdoutFd if dirty [|][|] current != size then let rows := Linger[.]Selector[.]Picker[.]frameRows state snapshot [(]statuses[.]getD · [.]unknown[)] loaded withColor savedTmux remoteAge current[.]1[.]toNat current[.]2[.]toNat let frame := match shown with [|] some before => if current == size then Linger[.]Selector[.]Picker[.]update before rows else Linger[.]Selector[.]Picker[.]frame state snapshot [(]statuses[.]getD · [.]unknown[)] loaded withColor savedTmux remoteAge current[.]1[.]toNat current[.]2[.]toNat [|] none => Linger[.]Selector[.]Picker[.]frame state snapshot [(]statuses[.]getD · [.]unknown[)] loaded withColor savedTmux remoteAge current[.]1[.]toNat current[.]2[.]toNat if !frame[.]isEmpty then writeAll stdoutFd [(]ByteArray[.]mk frame[.]toArray[)] shown := some rows size := current dirty := false let ready ← poll fds events 50' \
  'for key in keys do remoteDue := Linger[.]Selector[.]Picker[.]fetch remoteDue [(][.]key key[)] if key == [.]refresh then shown := none dirty := true if !loaded && key == [.]accept then continue match Linger[.]Selector[.]Picker[.]step state key with [|] [.]stay next => dirty := dirty [|][|] next != state state := next [|] [.]attach target [|] [.]create target => return [.]attach target snapshot [|] [.]cancel => return [.]cancel if let some result[[:space:]]*← Os[.]Shell[.]Command[.]poll pending then' \
  'if full then lastFull := listed fetched := if savedTmux then none else some started let incoming := if full then listed else listed[.]withRemote lastFull' \
  'nextListing := [(]← monotonicMs[)] [+] 1000 if [(]← pending[.]get[)][.]isNone && [(]remoteDue [|][|] [(]← monotonicMs[)] ≥ nextListing[)] then full := savedTmux [|][|] remoteDue remoteDue := Linger[.]Selector[.]Picker[.]fetch remoteDue [.]list let args := if full then fullArgs else #[[]"ls", "--porcelain"[]] started ← monotonicMs pending[.]set [(]some [(]← Os[.]Shell[.]Command[.]start executable args[)][)] return [.]cancel finally' \
  'finally Os[.]Shell[.]Command[.]stop pending [(]if savedTmux then 0 else 1000[)]' \
  'let fullArgs := if savedTmux then #[[]"tmux", "ls", "--porcelain"[]] [+][+] save[.]toArray else #[[]"ls", "-r", "--porcelain"[]]' \
  'match ← choose executable [(]readOnly := readOnly[)] [(]stopped := stops[.]heard[)] with' \
  'let ready ← poll fds events 50 if ← stopped then return [.]interrupted' \
  'IO Linger[.]Os[.]Answer := do let stops ← watch handbackSignals try while true do' \
  'discard child[.]wait if ← stops[.]heard then return [.]interrupted return [.]done finally stops[.]stop' \
  'def attachArgs [(]target : String[)] [(]readOnly : Bool := false[)] : Array String := [(]"attach" :: [(]if readOnly then [[]"--read-only"[]] else [[][]][)] [+][+] Linger[.]Target[.]Remote[.]targetOperands target[)][.]toArray'; do
  printf '%s\n' "$picker_code" | CG_RE="(^|[[:space:]])$tie([[:space:]]|$)" awk "$CODE_AWK" >/dev/null \
    || fail "manager lost its selection, refresh, process ownership or attach contract: $tie"
done
# Work follows events (fetch_follows_events): no clock decides a remote query. Whether a listing
# queries remote hosts is set only where it starts and only from what Picker.fetch says of the
# events since the chooser opened.
[ -z "$(code_grep '(^|[^[:alnum:]_.])(full|remoteDue)[[:space:]]*:=' Linger/Selector/WorldCode.lean \
    | grep -v -F -e 'let mut full := true' -e 'full := savedTmux || remoteDue' \
      -e 'let mut remoteDue := true' -e 'remoteDue := Linger.Selector.Picker.fetch remoteDue ')" ] \
  || fail "the chooser decides a remote query outside Picker.fetch, which only its opening and the refresh key make due"
# Terminal loops and remote discovery own helpers through this one executor. Reap only
# after both pipes close; clear ownership before a reader error can throw.
# Cancellation can first request cooperative cleanup. It always force-retires
# the isolated group before reaping its reserved leader PID, then joins both
# readers even when termination or reaping throws.
command_code="$(awk '{ $1 = $1; printf "%s ", $0 }' packages/os/Os/WorldCode/Command.lean)"
for tie in \
  'IO[.]Process[.]spawn [{] cmd := executable, args, stdin := [.]null, stdout := [.]piped, stderr := [.]piped, setsid := true [}] let stdout ← IO[.]asTask child[.]stdout[.]readToEnd Task[.]Priority[.]dedicated let stderr ← IO[.]asTask child[.]stderr[.]readToEnd Task[.]Priority[.]dedicated return [{] child, stdout, stderr [}]' \
  'IO[.]Process[.]spawn [{] cmd := executable, args, stdin := [.]null, stdout := [.]piped, stderr := [.]piped, setsid := true [}] let stdout ← IO[.]asTask [(]readLimited child[.]stdout limit[)] Task[.]Priority[.]dedicated let stderr ← IO[.]asTask [(]readLimited child[.]stderr [(]64 [*] 1024[)][)] Task[.]Priority[.]dedicated return [{] child, stdout, stderr [}]' \
  'let chunk ← handle[.]read 4096 if chunk[.]isEmpty then break if !exceeded && bytes[.]size [+] chunk[.]size ≤ limit then bytes := bytes [+][+] chunk else exceeded := true' \
  'if exceeded then throw [(]IO[.]userError s!"command output exceeds [{]limit[}] bytes"[)] let some text := String[.]fromUTF8[?] bytes [|] throw [(]IO[.]userError "command output is not UTF-8"[)] return text' \
  'def poll [(]pending : IO[.]Ref [(]Option Job[)][)] : IO [(]Option IO[.]Process[.]Output[)] := do if let some job[[:space:]]*← pending[.]get then if [(]← IO[.]hasFinished job[.]stdout[)] && [(]← IO[.]hasFinished job[.]stderr[)] then if let some exitCode[[:space:]]*← job[.]child[.]tryWait then pending[.]set none let stdout ← IO[.]ofExcept [(]← IO[.]wait job[.]stdout[)] let stderr ← IO[.]ofExcept [(]← IO[.]wait job[.]stderr[)] return some [{] exitCode, stdout, stderr [}] return none' \
  'if let some job[[:space:]]*← pending[.]get then pending[.]set none try try try if graceMs > 0 then Os[.]Shell[.]kill job[.]child[.]pid 15 let deadline := [(]← Os[.]Shell[.]monotonicMs[)] [+] graceMs repeat if [(]← IO[.]hasFinished job[.]stdout[)] && [(]← IO[.]hasFinished job[.]stderr[)] then break unless ← Os[.]Shell[.]nap deadline 5 do break finally retireGroup job finally discard job[.]child[.]wait finally discard <[|] IO[.]wait job[.]stdout discard <[|] IO[.]wait job[.]stderr' \
  'private def retireGroup [(]job : Job[)] : IO Unit := do try job[.]child[.]kill catch err => match err with [|] [.]permissionDenied [.][.] [|] [.]noSuchThing [.][.] => Os[.]Shell[.]kill job[.]child[.]pid 9 [|] _ => throw err'; do
  printf '%s\n' "$command_code" | CG_RE="(^|[[:space:]])$tie([[:space:]]|$)" awk "$CODE_AWK" >/dev/null \
    || fail "owned command lost its process or pipe lifetime contract: $tie"
done

# Pure rendering and summary claims cannot see CLI/terminal IO. Pin the actual
# consumers: validated host order, one shared row, palette-only badge styling,
# and color only where Env.withColor allows it. A host that does not answer in time is one `?`
# record, its `host` with the status no answer gives. Prompt sampling shares one reply deadline; a
# busy nonblocking connect remains unknown and cannot authorize stale-socket removal.
cli_code="$(awk '{ $1 = $1; printf "%s ", $0 }' Linger/App/WorldCode.lean)"
for tie in \
  'match Linger[.]Target[.]Remote[.]checkHosts hosts with [|] [.]ok l => return l[.]map fun host => [(]host, Linger[.]Target[.]Remote[.]transportFor config host[)] [|] [.]error e => throw [(]IO[.]userError e[)]' \
  'for [(][(]host, _[)], output[)] in remotes[.]zip remote[.]toList do match output with [|] none => rows := rows [+][+] [[][[][(]"host", host[)], [(]"status", Linger[.]Display[.]Status[.]name [.]unknown[)][]][]] [|] some output => for row in Linger[.]Target[.]Remote[.]parse output do' \
  '[|] some [(]porcelain, remoteFlag[)] => cmdList porcelain [(]← resolveRemotes remoteFlag[)]' \
  'let withColor := Linger[.]Os[.]Env[.]withColor [(]← [(]← IO[.]getStdout[)][.]isTty[)] [(]← IO[.]getEnv "NO_COLOR"[)] [(]← IO[.]getEnv "TERM"[)] let named := rows[.]map fun info => match info[.]lookup "name", info[.]lookup "host" with [|] none, some host => [(]"name", "@" [+][+] host[)] :: info [|] _, _ => info let ordered := Linger[.]Display[.]View[.]sort [(]fun info => Linger[.]Display[.]Status[.]ofName [(][(]info[.]lookup "status"[)][.]getD ""[)][)] named let width ← humanWidth let home ← accountHome writeAll stdoutFd [(]ByteArray[.]mk [(]Linger[.]Display[.]Listing[.]terminalListing withColor width [(]ordered[.]map [(]Linger[.]Display[.]Listing[.]atHome home[)][)][)][.]toArray[)]' \
  'def summaryText : IO String := do let rows ← localRows [(]some [(][(]← monotonicMs[)] [+] 250[)][)] [(]statusOnly := true[)] return Linger[.]Display[.]Status[.]summary [(]rows[.]map fun info => Linger[.]Display[.]Status[.]ofName [(][(]info[.]lookup "status"[)][.]getD "unknown"[)][)]' \
  'def cmdSummary : IO Answer := do let summary ← summaryText if !summary[.]isEmpty then IO[.]println summary return [.]done' \
  'match ← connectUpsert name cmd with [|] [.]ok fd => attachSpoken name fd false' \
  '[|] [[]"ls", "--summary"[]] [|] [[]"list", "--summary"[]] [|] [[]"l", "--summary"[]] => cmdSummary'; do
  printf '%s\n' "$cli_code" | CG_RE="(^|[[:space:]])$tie([[:space:]]|$)" awk "$CODE_AWK" >/dev/null \
    || fail "listing or prompt bypassed its shared policy: $tie"
done
# An attach, writable or watching, goes only to a daemon that says in an info answer on the
# attach's own connection, within the one-shot reply budget, that it speaks this version's
# protocol (`admits_level`); the chooser runs `linger attach`. Linger.Session.Suites.Attach checks
# the refusals against older daemons' answers and against silence.
tie='let heard ← [(]Inventory[.]readInfo fd [(]some [(][(]← monotonicMs[)] [+] Client[.]replySilenceMs[.]toNatClampNeg[)][)][)][.]toBaseIO let level := [(]heard[.]toOption[.]bind [(]·[.]lookup "protocol"[)][)][.]bind String[.]toNat[?] if Linger[.]Session[.]Wire[.]admits level then return [.]ok [(]← Client[.]attach name fd summaryText readOnly[)] close fd'
printf '%s\n' "$cli_code" | CG_RE="(^|[[:space:]])$tie([[:space:]]|$)" awk "$CODE_AWK" >/dev/null \
  || fail "an attach bypasses its daemon's protocol level (Wire.admits): $tie"
[ "$(code_count 'Client[.]attach([^[:alnum:]_]|$)' Linger/App/WorldCode.lean)" -eq 1 ] \
  || fail "Client.attach is called outside attachSpoken, which first asks the daemon's protocol level"
# `linger help` lists the exit statuses from the vocabulary every command answers in
# (`code_documented`, `listed_once`), one line per answer of linger's own.
printf '%s\n' "$cli_code" | CG_RE='(^|[[:space:]])Answer[.]legend[.]map [(]" +" [+][+] ·[)][)]([[:space:]]|$)' awk "$CODE_AWK" >/dev/null \
  || fail "linger help no longer lists the exit statuses from Answer.legend"
# The session inventory the listing, the prompt summary, `get` and the importer share.
inventory_code="$(awk '{ $1 = $1; printf "%s ", $0 }' Linger/Session/WorldCode/Inventory.lean)"
for tie in \
  'if let some deadline := stopAt then if [(]← monotonicMs[)] ≥ deadline then return some [(][.]error [(]IO[.]userError "overview deadline reached"[)][)] match ← connect stopAt[.]isSome with [|] none => if stopAt[.]isSome && retainUnavailable then return some [(][.]error [(]IO[.]userError "overview connection unavailable"[)][)] return none [|] some fd => try let info ← [(]readInfo fd stopAt[)][.]toBaseIO return some info finally close fd' \
  'Client[.]sendMsg fd [.]info let deadline := stopAt[.]getD [(][(]← monotonicMs[)] [+] 2000[)]' \
  'while go && [(]← monotonicMs[)] < deadline do let remaining := deadline - [(]← monotonicMs[)] let revs ← poll #[[]fd[]] #[[]POLLIN[]] [(]Int32[.]ofNat [(]min 100 remaining[)][)]' \
  'queryWith [(]Client[.]connect name ·[)] stopAt retainUnavailable' \
  'IO[.]asTask [(]queryWith [(]connectListed listed ·[)] [(]some deadline[)] retainUnavailable[)]' \
  'let infos ← queryInfos asked deadline stopAt[.]isSome' \
  'let free ← try listed[.]withLock [(]pure true[)] catch _ => pure false return if free then none else some seen' \
  'for [(]listed, result[)] in asked[.]zip infos do let name := listed[.]name match result with [|] some info => confirmedLive := confirmedLive [+][+] [[]name[]] rows := rows [+][+] [[]liveRow name [(]info[.]toOption[.]getD [[][]][)][]] [|] none => if ![(]← removeStaleSocket listed[)] then'; do
  printf '%s\n' "$inventory_code" | CG_RE="(^|[[:space:]])$tie([[:space:]]|$)" awk "$CODE_AWK" >/dev/null \
    || fail "listing or prompt bypassed its shared policy: $tie"
done
# Environment policies decide unset and empty values for every input. The runtime
# reads SHELL and LINGER_NO_DETACH_KEY once each, and HOME once for remote hosts, into
# their policies. An unset or empty HOME configures no remote hosts
# (remotesFile_eq_none_iff): a fallback such as world-writable `/tmp` would let another
# account choose them, and a suite cannot create `/tmp/.config`. The remotes file's lines mean
# what `Remote.config` reads them as, or refuse the whole file, and `remoteConfig` alone reads it.
printf '%s\n' "$cli_code" | CG_RE='(^|[[:space:]])match Linger[.]Os[.]Env[.]remotesFile [(]← IO[.]getEnv "HOME"[)] with [|] none => pure [[][]] [|] some path => if ← System[.]FilePath[.]pathExists path then pure [(][(]← IO[.]FS[.]readFile path[)][.]splitOn([[:space:]]|$)' awk "$CODE_AWK" >/dev/null \
  || fail "remote configuration bypasses Env.remotesFile, which reads no file for an unset or empty HOME"
printf '%s\n' "$cli_code" | CG_RE='(^|[[:space:]])else pure [[][]] match Linger[.]Target[.]Remote[.]config lines with [|] [.]ok config => return config [|] [.]error e => throw [(]IO[.]userError e[)]([[:space:]]|$)' awk "$CODE_AWK" >/dev/null \
  || fail "remote configuration bypasses Remote.config, which reads each line of the remotes file as one meaning"
[ "$(code_count 'Env[.]remotesFile' 'Linger/*.lean' ':!Linger/*/Suites/*' ':!Linger/*/Proofs/*' ':!Linger/*/Tests/*' ':!Linger/Os/CoreCode/Env.lean')" -eq 1 ] \
  || fail "the remotes file is read outside remoteConfig, which reads it through Env.remotesFile and Remote.config"
for var in SHELL LINGER_NO_DETACH_KEY; do
  [ "$(code_count "getEnv \"$var\"" 'Linger/*' 'packages/*')" -eq 1 ] \
    || fail "$var is read more than once or not at all; read it once, into its Env policy"
done
# Linger colors its own listings exactly where Env.withColor allows it (withColor_iff): `ls`,
# `tmux ls` and the chooser each read whether standard output is a terminal, NO_COLOR and TERM
# once, into it. A NO_COLOR of any nonempty value turns color off, as no-color.org says, and an
# unset, empty or `dumb` TERM names no terminal that takes escape sequences.
# Linger.App.Suites.Manager runs each with NO_COLOR unset, empty and set and with TERM unset,
# empty and `dumb`, and `ls` and `tmux ls` redirected.
color_read='let withColor := Linger[.]Os[.]Env[.]withColor [(]← [(]← IO[.]getStdout[)][.]isTty[)] [(]← IO[.]getEnv "NO_COLOR"[)] [(]← IO[.]getEnv "TERM"[)]'
for code in "$cli_code" "$import_code" "$picker_code"; do
  printf '%s\n' "$code" | CG_RE="(^|[[:space:]])$color_read([[:space:]]|$)" awk "$CODE_AWK" >/dev/null \
    || fail "ls, tmux ls or the chooser colors its output outside Env.withColor: $color_read"
done
for var in NO_COLOR TERM; do
  [ "$(code_count "getEnv \"$var\"" 'Linger/*' 'packages/*')" -eq 3 ] \
    || fail "$var is read other than once for each of ls, tmux ls and the chooser, into Env.withColor"
done
# Discovery keeps bounded ownership until completion. Remote signal handlers
# are installed before spawning the transports' isolated groups, so cancelling the chooser
# reaches those groups through its listing helper. Each host's listing runs through its query
# command, then the encoded words of `ls --porcelain` (`Remote.argv`). Linger.Target.Suites.Remote
# checks overlap, output order, slot reuse, shared deadlines and descendant cleanup.
for tie in \
  'for signal in [[]Std[.]Async[.]Signal[.]sigterm, [.]sigint, [.]sighup[]] do let waiter ← Std[.]Async[.]Signal[.]Waiter[.]mk signal true try let task ← waiter[.]wait signals[.]modify [(]·[.]push [(]waiter, task[)][)] catch e => waiter[.]stop throw e let deadline := [(]← monotonicMs[)] [+] remoteQueryTimeoutMs' \
  'for [(]_, signal[)] in ← signals[.]get do if [(]← signal[.]getState[)] == [.]finished then return none if [(]← monotonicMs[)] ≥ deadline then break' \
  'while next < hosts[.]size && [(]← jobs[.]get[)][.]size < remoteQueryLimit && [(]← monotonicMs[)] < deadline do' \
  'if let cmd :: args := Linger[.]Target[.]Remote[.]argv hosts[[]index[]]![.]2 "ls" [[]"--porcelain"[]] then pending[.]set [(]some [(]← Command[.]start cmd args[.]toArray[)][)]' \
  'finally for [(]_, pending[)] in ← jobs[.]get do try Command[.]stop pending catch _ => pure [(][)] for [(]waiter, _[)] in ← signals[.]get do waiter[.]stop' \
  'let task ← IO[.]asTask localRows Task[.]Priority[.]dedicated try let remote ← listRemotes remotes[.]toArray let locals ← IO[.]ofExcept [(]← IO[.]wait task[)] pure [(]locals, remote[)] finally discard <[|] IO[.]wait task'; do
  printf '%s\n' "$cli_code" | CG_RE="(^|[[:space:]])$tie([[:space:]]|$)" awk "$CODE_AWK" >/dev/null \
    || fail "discovery lost its bounded task or process ownership: $tie"
done
for tie in \
  'while next < names[.]size && [(]← pending[.]get[)][.]size < localQueryLimit && [(]← monotonicMs[)] < deadline do' \
  'let some listed := names[[]index[]][?] [|] break let task ← IO[.]asTask [(]queryWith [(]connectListed listed ·[)] [(]some deadline[)] retainUnavailable[)] Task[.]Priority[.]dedicated' \
  'finally for [(]_, task[)] in ← pending[.]get do discard <[|] IO[.]wait task'; do
  printf '%s\n' "$inventory_code" | CG_RE="(^|[[:space:]])$tie([[:space:]]|$)" awk "$CODE_AWK" >/dev/null \
    || fail "discovery lost its bounded task or process ownership: $tie"
done
code_grep '^[[:space:]]+let r ← unixConnect path nonblocking$' Linger/Session/WorldCode/Client.lean >/dev/null \
  || fail "status connect lost its nonblocking boundary"

# Title writes use the bounded, control-free encoder and the existing VT
# observer. Observe raw application bytes only, reassert repeated OSC titles,
# and defer every injected title until the parser and UTF-8 decoder are idle.
# Attention is sampled in the client's process, one task at a time, and an
# outstanding sample is joined after the socket closes. Linger.Display.Suites.Title checks that an
# idle client reaps no children and that detach joins a held sample.
client_code="$(awk '{ $1 = $1; printf "%s ", $0 }' Linger/Session/WorldCode/Client.lean)"
for tie in \
  'let mut observer := Terminal[.]Vt[.]Vt[.]init 1 1' \
  'while !leaving do if let some task[[:space:]]*← pending[.]get then if ← IO[.]hasFinished task then pending[.]set none let fresh := match ← IO[.]wait task with [|] [.]ok text => text [|] [.]error _ => String[.]singleton [(]Linger[.]Display[.]Status[.]icon [.]unknown[)] titleDirty := titleDirty [|][|] fresh != summary summary := fresh nextSummary := [(]← monotonicMs[)] [+] 1000 if [(]← pending[.]get[)][.]isNone && [(]← monotonicMs[)] ≥ nextSummary then pending[.]set [(]some [(]← IO[.]asTask sample Task[.]Priority[.]dedicated[)][)] let revs ← poll #[[]stdinFd, fd[]] #[[]POLLIN, POLLIN[]] 200' \
  'writeAll stdoutFd [(]ByteArray[.]mk payload[.]toArray[)] observer := observer[.]observe payload receivedOutput := true' \
  'if receivedOutput && titleDirty && !leaving then let title := Linger[.]Display[.]Title[.]compose name observer[.]windowTitle summary Terminal[.]Title[.]maxChars let bytes := Terminal[.]Title[.]update observer title if !bytes[.]isEmpty then writeAll stdoutFd [(]ByteArray[.]mk bytes[.]toArray[)] titleDirty := false' \
  'try writeAll stdoutFd [(]ByteArray[.]mk Terminal[.]Render[.]leaveAnsi[.]toArray[)] finally termRestore stdinFd saved return result finally stops[.]stop close fd' \
  'def attach [(]name : String[)] [(]fd : UInt32[)] [(]sample : IO String[)] [(]readOnly : Bool := false[)] : IO Outcome := do let pending ← IO[.]mkRef [(]none : Option [(]Task [(]Except IO[.]Error String[)][)][)] try converse name fd sample readOnly pending finally if let some task[[:space:]]*← pending[.]get then discard <[|] IO[.]wait task'; do
  printf '%s\n' "$client_code" | CG_RE="(^|[[:space:]])$tie([[:space:]]|$)" awk "$CODE_AWK" >/dev/null \
    || fail "attached title lost its observer, sampler or handback contract: $tie"
done
# SIGTERM, SIGHUP and SIGINT (`Os.Shell.handbackSignals`) end an attach, and a view of a saved
# session, as a detach does: they are caught before raw mode, and the next poll round leaves the
# loop, so the terminal is handed back on the same path. Linger.Session.Suites.Attach sends each.
for tie in \
  'IO Outcome := do let stops ← watch handbackSignals try let detachEnabled' \
  'let revs ← poll #[[]stdinFd, fd[]] #[[]POLLIN, POLLIN[]] 200 if ← stops[.]heard then result := [.]interrupted leaving := true continue' \
  'IO Outcome := do let stops ← watch handbackSignals let saved ← termRaw stdinFd try' \
  'let ready ← poll fds events 200 if ← stops[.]heard then return [.]interrupted'; do
  printf '%s\n' "$client_code" | CG_RE="(^|[[:space:]])$tie([[:space:]]|$)" awk "$CODE_AWK" >/dev/null \
    || fail "an attached client ends on a signal other than as a detach does: $tie"
done
! code_grep 'IO[.]Process|Command[.]|spawnDetached|spawnPty|appPath' Linger/Session/WorldCode/Client.lean \
  || fail "the attach client starts processes; it samples title attention in its own process"
[ "$(code_count 'observer := observer[.]observe' Linger/Session/WorldCode/Client.lean)" -eq 1 ] \
  || fail "title observer must consume application output exactly once"
[ "$(code_count '(^|[[:space:]])observer([[:space:]]+:[^=]*)?[[:space:]]*(:=|←)' Linger/Session/WorldCode/Client.lean)" -eq 2 ] \
  || fail "title observer may only initialize once and consume application output"
awk '
  /receivedOutput := true/ { output = 1; next }
  output && /^[[:space:]]*--/ { next }
  output { if ($0 !~ /^[[:space:]]*titleDirty := true$/) bad = 1; output = 0; checked++ }
  END { exit (checked != 1 || bad) }
' Linger/Session/WorldCode/Client.lean \
  || fail "repeated application titles no longer trigger reassertion"

# The `Vt` friend set — who may forge a `Vt`. `import all M` grants M's OWN all-access
# set, including whatever M has all-access to, so **`import all` TRANSITS** and
# `git grep -l 'import all Terminal.Vt'` is NOT an enumeration of the friend set.
# Measured in the real position, not a scratch file: one added
# `import all Terminal.Render` in `Linger/Session/WorldCode/Client.lean` plus a five-field
# `{ cols := 0, rows := 0, grid := #[], … }` gives `./lake build linger` exit 0 AND
# `sh scripts/gates.sh` exit 0. Two hops is the same: `import all Linger.Display.Proofs.Listing` from
# a file holding neither `import all Terminal.Vt` nor `import all Terminal.Render`
# compiles the identical forge. As with the toolkit's import closure above, the compiler
# consents, so a grep is the only possible oracle: without one, joining the friend set
# would cost one line that nothing objected to, and `private` on 20 fields would be worth
# one line of anyone's diff.
#
# CLOSURE, not edges. Transit follows `import all` edges ONLY (measured:
# `import all Linger.Session` — a plain `public import`er of `Vt` — does not
# transit, and neither does the `Linger` umbrella, whose imports are all `public`), so
# the closure over those edges IS the friend set and nothing else can widen it. Gating
# the edges instead would mean recording all of them, though few matter, and
# would fire on every legitimate rewire of the `packages/terminal/Terminal/Proofs/Render/*` chain — noise on the
# common change, which is how a gate stops being read.
#
# The permitted region is an EXACT file list plus the proof and fixture directories,
# `Theorems/` and each component's `Proofs/` and `Tests/`, and that split is by
# edit frequency: commits add a `.lean` under those more often than
# one beside `Vt`, and few of those join the closure. So a per-file list over
# `Theorems/**` would be edited reflexively, while the core list changes rarely, which
# is what makes it a checkpoint. The proof and fixture directories are friends BY
# DECLARATION (see `packages/terminal/Terminal/CoreCode/Vt.lean`, "## Every door"), and a component's `Tests/` deliberately forges invalid
# states in its negative fixtures, so listing its files one by one would gate a
# non-property. Everything else is outside and fail-closed — `Verify/**`, each component's
# `Suites/`, `Linger/App/WorldCode/Main.lean`, every shell and the other component modules. Replay joins only
# to read shared immutable rows.
# The suites are outside deliberately: a pty suite asserts on bytes the real binary
# emitted, so a forged `Vt` there would be an assertion about a state the binary cannot
# reach — the very bug the seal exists to prevent.
#
# EXACT means both directions, as with the toolkit lists above: a recorded friend
# that stops reaching `Vt` fails too, so a future step taking a friend import out is a
# reviewable edit here rather than a silent one. No cardinality number is recorded: a
# count is blind to identity, so it would pass one friend swapped for another.
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
VT_FRIEND_EXACT='packages/terminal/Terminal/CoreCode/Vt.lean packages/terminal/Terminal/CoreCode/Render.lean packages/terminal/Terminal/CoreCode/Mediation.lean Linger/Session/CoreCode/Checkpoint.lean packages/terminal/Terminal/CoreCode/Replay.lean'
VT_FRIEND_DIRS='Theorems/'
VT_FRIEND_RE='^(Linger/[^/]+|packages/terminal/Terminal)/(Proofs|Tests)/|^packages/terminal/Terminal/Solution[.]lean$'
code_grep "$VT_ALL_RE" '*.lean' \
| awk -F: -v seed='packages/terminal/Terminal/CoreCode/Vt.lean' -v exact="$VT_FRIEND_EXACT" -v dirs="$VT_FRIEND_DIRS" \
    -v friend_re="$VT_FRIEND_RE" \
    "$IMPORT_AWK"'
  BEGIN { ne = split(exact, E, " "); nd = split(dirs, D, " ") }
  { tgt = import_mod($3); gsub(/[.]/, "/", tgt)
    if (tgt ~ /^Terminal[/]/) tgt = "packages/terminal/" tgt
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
      printf "  %s has all-access to Terminal.Vt -- its private fields, its\n", f
      printf "  private constructor and Vt.ofDecoded -- by this chain of import all:\n"
      for (cur = f; cur != seed; cur = dst[via[cur]])
        printf "    %s:%s:%s\n", src[via[cur]], ln[via[cur]], raw[via[cur]] }
    for (j = 1; j <= ne; j++)
      if (!(E[j] in inset)) { bad++
        printf "  %s is a RECORDED friend that no longer reaches Terminal.Vt", E[j]
        printf " (renamed, moved, or its import all went)\n" }
    if (bad > 0) printf "  permitted: %s -- plus anything under: %s, or matching %s\n", exact, dirs, friend_re
    exit (bad == 0 ? 0 : 1) }' >&2 \
  || fail "the Terminal.Vt friend set changed (import all TRANSITS: it re-grants whatever the imported module itself has all-access to)"

# shim-size ratchet: the C trust boundary must not grow silently. This
# number only ever goes DOWN without discussion; raising it is a
# deliberate, reviewable act — the checkpoint for "does this genuinely
# need a syscall wrapper, or does Lean core already have it?". 26: a pty's
# foreground group (tcgetpgrp) and a process's words, which macOS keeps only
# behind sysctl, as a row shows what runs in a session; Lean core has neither.
SHIM_CAP=26
shim_n="$(code_count 'LEAN_EXPORT' 'packages/os/c/shim.c')"
[ "$shim_n" -le "$SHIM_CAP" ] \
  || fail "shim grew to $shim_n wrappers (cap $SHIM_CAP); justify the new syscall and bump the cap"

# The runtime keeps no byte queue of its own. `Linger/Session/CoreCode/Buf.lean` owns the two
# kinds of long-lived queue -- their caps, their drop and cut policies, and the
# removal of written prefixes (`Linger/Session/Proofs/Buf.lean`) -- and the runtime shells
# (the session's, the CLI and command jobs) are `IO`,
# so NO theorem can see that the daemon calls those functions rather than
# open-coding the same sums. Without this grep the Buf theorems are arithmetic
# about a value nothing forces the runtime to use. A source-tree property cannot
# be a theorem, so it is a gate, in the same spirit as SHIM_CAP above: evadeable
# by deliberately writing something new, not by reverting a fix.
# On the commit before Buf landed these three found 5 hits (Conn.out, Rt.ptyIn,
# the CLI's info-reply accumulator, and two .extract compactions). `code_grep` prints
# the hits, so each regex is spelled once: two copies of a pattern is two things to
# keep in step.
! code_grep '^[[:space:]]+[a-zA-Z_]+ : ByteArray' 'Linger/App/WorldCode.lean' 'packages/os/Os/WorldCode/Command.lean' 'Linger/Session/WorldCode/*' \
  || fail "a ByteArray field in a runtime shell (use Linger.Session.Buf, which is proved)"
! code_grep 'mut [a-zA-Z_]+ : ByteArray' 'Linger/App/WorldCode.lean' 'packages/os/Os/WorldCode/Command.lean' 'Linger/Session/WorldCode/*' \
  || fail "an accumulating ByteArray local in a runtime shell (use Linger.Session.Buf: it is capped)"
! code_grep '[.]extract([^[:alnum:]_]|$)' 'Linger/App/WorldCode.lean' 'packages/os/Os/WorldCode/Command.lean' 'Linger/Session/WorldCode/*' \
  || fail "buffer arithmetic in a runtime shell (Buf.bufAdvance owns it, and is proved)"

# The cursor proofs describe pure values. These ties keep the runtime on the
# captured snapshot, bounded advances and shared byte allowance. The delivery
# suite separately observes framing, prior/replay/live ordering and exit tails.
code_grep '^[[:space:]]+effs [+][+] focusEffects typist before s [+][+] [[][.]replay c[.]id [(]Replay[.]start s[.]vt[)][]] [+][+]$' 'Linger/Session/CoreCode.lean' > /dev/null \
  || fail "attach no longer captures its resulting snapshot"
code_grep '^[[:space:]]+replay : Option Replay[.]Plan := none$' 'Linger/Session/WorldCode/Daemon.lean' > /dev/null \
  || fail "each connection must retain one optional replay cursor"
code_grep '^[[:space:]]+after : Buf := [.]empty$' 'Linger/Session/WorldCode/Daemon.lean' > /dev/null \
  || fail "following output bypasses the proved byte buffer"
code_grep '^[[:space:]]+[|] [.]replay id plan => do$' 'Linger/Session/WorldCode/Daemon.lean' > /dev/null \
  || fail "the runtime no longer receives the captured replay plan"
code_grep '^[[:space:]]+match ← flushConn [{] c with replay := some plan [}] with$' 'Linger/Session/WorldCode/Daemon.lean' > /dev/null \
  || fail "the runtime no longer executes the captured replay plan"
! code_grep 'Replay[.]start|Render[.]restore' 'Linger/Session/WorldCode/Daemon.lean' \
  || fail "the daemon must consume the captured cursor without constructing another repaint"
code_grep '^[[:space:]]+match Replay[.]next Linger[.]Session[.]outputChunk plan with$' 'Linger/Session/WorldCode/Daemon.lean' > /dev/null \
  || fail "replay advancement no longer uses the proved output chunk"
code_grep '^def replayFrameCap : Nat := Linger[.]Session[.]outputChunk [+] [(]Wire[.]encode [(][.]output [[][]][)][)][.]length$' 'Linger/Session/WorldCode/Daemon.lean' > /dev/null \
  || fail "replay reservation no longer includes the wire encoder's frame overhead"
code_grep '^[[:space:]]+let cap := followingCap outbufCap replayFrameCap [(]owedLen c[.]out[)]$' 'Linger/Session/WorldCode/Daemon.lean' > /dev/null \
  || fail "following output no longer shares the front buffer allowance"
code_grep '^[[:space:]]+bufEnqueue [(]outbufCap - owedLen c[.]after[)] [.]empty$' 'Linger/Session/WorldCode/Daemon.lean' > /dev/null \
  || fail "replay frames no longer account for following output debt"

# A logically closed peer still owns its transport until it drains or expires.
# It therefore counts towards admission, and ordinary polls must retire it
# before taking the fd snapshot. Deadlines use Nat and the same grace constant
# as shutdown. A repeated close cannot buy another grace period.
code_grep '^[[:space:]]+closeBy : Option Nat := none$' 'Linger/Session/WorldCode/Daemon.lean' > /dev/null \
  || fail "transport close deadlines no longer use Nat"
[ "$(code_count '^[[:space:]]+let deadline := [(]← monotonicMs[)] [+] drainTimeoutMs$' 'Linger/Session/WorldCode/Daemon.lean')" -eq 2 ] \
  || fail "ordinary close and shutdown must share the Nat drain deadline"
code_grep '^[[:space:]]+if c[.]closeBy[.]any [(]now ≥ ·[)] then$' 'Linger/Session/WorldCode/Daemon.lean' > /dev/null \
  || fail "retired transport expiry no longer checks its fixed deadline"
code_grep '^[[:space:]]+return [(]rt[.]setConn [{] c with closeBy := some deadline [}], true[)]$' 'Linger/Session/WorldCode/Daemon.lean' > /dev/null \
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
' Linger/Session/WorldCode/Daemon.lean \
  || fail "repeated-close guard or expire-before-poll-snapshot ordering changed"
code_grep '^[[:space:]]+deadlines := deadline :: deadlines$' 'Linger/Session/WorldCode/Daemon.lean' > /dev/null \
  || fail "ordinary polling ignores close deadlines"
# A daemon sleeps until its earliest deadline, or for an event however long that takes when it
# holds none (`poll_wakes`, over the world claim `Poll.Sleeps`, which its check and the quiet suite test):
# the round's one poll waits `Session.pollTimeout` of the deadlines it gathered.
printf '%s\n' "$(awk '{ $1 = $1; printf "%s ", $0 }' Linger/Session/WorldCode/Daemon.lean)" \
  | CG_RE='(^|[[:space:]])let timeout := Linger[.]Session[.]pollTimeout now deadlines let accepting := .* let revs ← poll fds evts timeout([[:space:]]|$)' awk "$CODE_AWK" >/dev/null \
  || fail "a daemon's poll waits other than Session.pollTimeout of its deadlines"
code_grep '^[[:space:]]+let accepting := rt[.]conns[.]length < maxClients && rt[.]acceptAfter[.]all [(]now ≥ ·[)]$' 'Linger/Session/WorldCode/Daemon.lean' > /dev/null \
  || fail "listener admission must count every transport and honor its retry deadline"
code_grep '^[[:space:]]+#[[][(]if accepting then POLLIN else 0[)],' 'Linger/Session/WorldCode/Daemon.lean' > /dev/null \
  || fail "listener polling no longer uses the admission guard"
code_grep '^[[:space:]]+for _ in List[.]range [(]maxClients - rt[.]conns[.]length[)] do$' 'Linger/Session/WorldCode/Daemon.lean' > /dev/null \
  || fail "accept budget no longer includes retired transports"
[ "$(code_count '^[[:space:]]+let polled := rt[.]conns$' 'Linger/Session/WorldCode/Daemon.lean')" -eq 2 ] \
  || fail "ordinary and shutdown polling must each freeze their fd set"
[ "$(code_count '^[[:space:]]+for c in polled do$' 'Linger/Session/WorldCode/Daemon.lean')" -eq 2 ] \
  || fail "ordinary fd construction and readiness must use the same frozen connections"
code_grep '^[[:space:]]+let fds := [(]polled[.]map [(]·[.]fd[)][)][.]toArray$' 'Linger/Session/WorldCode/Daemon.lean' > /dev/null \
  || fail "shutdown fd list diverged from its frozen connections"
code_grep '^[[:space:]]+for [(]c, i[)] in polled[.]zipIdx do$' 'Linger/Session/WorldCode/Daemon.lean' > /dev/null \
  || fail "shutdown readiness no longer indexes the frozen connection list"
code_grep '^[[:space:]]+rt ← drainConns rt$' 'Linger/Session/WorldCode/Daemon.lean' > /dev/null \
  || fail "serve no longer drains accepted bytes after exit"

# A client read failure is local to that peer. The close frame cannot prove an
# IO catch exists: tie errors and EOF to the same fd retirement and pure event.
# Every retirement goes through Rt.closeConn, so its body is tied too: it closes
# the fd, then forgets that transport alone.
# Linger.Session.Suites.Robust closes an unread reply and requires the original shell to run again.
daemon_code="$(awk '{ $1 = $1; printf "%s ", $0 }' Linger/Session/WorldCode/Daemon.lean)"
printf '%s\n' "$daemon_code" | CG_RE='(^|[[:space:]])let received ← try read c[.]fd 65536 catch _ => pure none match received with [|] some bs => if bs[.]size > 0 then events := events [+][+] [[][.]bytes c[.]fd[.]toNat bs[.]toList[]] [|] none => rt ← rt[.]closeConn c[.]fd events := events [+][+] [[][.]closed c[.]fd[.]toNat[]]([[:space:]]|$)' awk "$CODE_AWK" >/dev/null \
  || fail "client read errors must close only that peer through the proved transition"
printf '%s\n' "$daemon_code" | CG_RE='(^|[[:space:]])def Rt[.]closeConn [(]rt : Rt[)] [(]fd : UInt32[)] : IO Rt := do close fd return [{] rt with conns := rt[.]conns[.]filter [(]·[.]fd != fd[)] [}]([[:space:]]|$)' awk "$CODE_AWK" >/dev/null \
  || fail "Rt.closeConn must close the fd before it forgets only that connection"
# A session runs exactly the program and words it was given (`Start.programOf`, the
# `programOf_exact` headline), and without a command Env.shellOf's program, which an unset or
# empty SHELL makes sh (shellOf_absent). Linger.Session.Suites.Agent creates sessions with both.
printf '%s\n' "$daemon_code" | CG_RE='(^|[[:space:]])let [(]prog, args[)] := Start[.]programOf [(]Linger[.]Os[.]Env[.]shellOf [(]← IO[.]getEnv "SHELL"[)][)] argv([[:space:]]|$)' awk "$CODE_AWK" >/dev/null \
  || fail "a session's program bypasses Start.programOf or Env.shellOf"
# The program reads the session's variables as `Start.environment` sets them (`start_runs`, over
# the world claim `Spawn.Runs`, which its check and the agent and resume suites test), and starts
# without what `Start.reset` resets (`start_clean`, over the world claim `Spawn.Clean`, which its
# check and the agent suite test); a program that cannot start reports `Start.failureStatus`
# (`failureStatus_exact`); and `info` reports the start as `Start.metadata` says
# (`metadata_dirs`). The daemon asks the operating system with exactly these.
for tie in \
  'trySpawnPty [(]UInt32[.]ofNat [(]Terminal[.]Vt[.]clampDim vt0[.]colCount[)][)] [(]UInt32[.]ofNat [(]Terminal[.]Vt[.]clampDim vt0[.]rowCount[)][)] cwd prog args [(][(]Start[.]environment name[)][.]toArray[.]map fun [(]key, value[)] => s!"[{]key[}]=[{]value[}]"[)] [(]resetOf Start[.]reset[)]' \
  'private def resetOf [(]reset : Linger[.]Session[.]Spawn[.]Reset[)] : SpawnReset := [{] dispositions := reset[.]dispositions, mask := reset[.]mask, descriptors := reset[.]descriptors [}]' \
  'req[.]tell [(][.]failed [(]Start[.]failureStatus failure[)] why[.]toUTF8[.]toList[)]' \
  'private def failureOf : SpawnFailure → Linger[.]Session[.]Spawn[.]Failure [|] [.]directory why => [.]directory why [|] [.]notFound why => [.]notFound why [|] [.]notRunnable why => [.]notRunnable why' \
  'if let [.]error reported := spawned then record[.]restore previous let failure := failureOf reported' \
  'State[.]boot vt0 [(][(]restore[.]map [(]·[.]2[)][)][.]getD [[][]][)] [(]Start[.]metadata name [(]toString pid[)] [(]toString created[)] [(]String[.]intercalate " " [(]prog :: args[.]toList[)][)] cwd [(]saved[.]map fun [(]_, dir, _[)] => dir[)][)]'; do
  printf '%s\n' "$daemon_code" | CG_RE="(^|[[:space:]])$tie([[:space:]]|$)" awk "$CODE_AWK" >/dev/null \
    || fail "a session starts outside Start.environment, Start.reset, Start.failureStatus or Start.metadata: $tie"
done
# A session's end sends its program and the rest of the program's terminal session the signals
# of `Session.ending`, SIGHUP and then SIGKILL (`ending_clean`, over the world claim
# `Signal.Ends`, which its check and the attach suite test), both while the program is unreaped. A stop
# that cannot send a signal reports it and sends the next all the same.
for tie in \
  'for [(]sig, ms[)] in Linger[.]Session[.]ending do if ← ended then break try kill pid sig catch err => report s!"[^"]*" try discard <[|] signalSession pid sig catch err => report s!"[^"]*" if ← within ms 10 ended then break' \
  'for [(]sig, ms[)] in Linger[.]Session[.]ending do if ← gone then return discard <[|] signalSession pid sig if ← within ms 50 gone then return'; do
  printf '%s\n' "$daemon_code" | CG_RE="(^|[[:space:]])$tie([[:space:]]|$)" awk "$CODE_AWK" >/dev/null \
    || fail "a session's processes end other than by Session.ending: $tie"
done
# A kill reaches the same ending as a program's own end (`step_kill_stops`,
# `step_ended_reports`): the stop runs `Session.ending` and answers how the program ended, which
# the driver hands back to the session as `.stopped`.
printf '%s\n' "$daemon_code" | CG_RE='(^|[[:space:]])[|] [.]stopProgram => do let outcome ← stopProgram rt return [(][{] rt with ending := some outcome [}], outcome[)]([[:space:]]|$)' awk "$CODE_AWK" >/dev/null \
  || fail "the daemon stops a program other than by Session.ending, or keeps how it ended from the session"
code_grep '^[[:space:]]+[|] [.]stopProgram, outcome => [[][.]stopped outcome[]]$' 'Linger/Session/CoreCode/Driver.lean' > /dev/null \
  || fail "the driver no longer hands a stopped program's end back to the session"
# A stop signal to the daemon reaches the session as its event (`step_signal_saves`): the signal
# pipe carries it, and the first stop signal a round heard is the session's event, before the
# program's end when it came first (`Session.stopOf`); the end record the session asks for
# (`Effect.record`) is the one the daemon writes as it gives the name up. Linger.Session.Suites.Resume
# sends SIGTERM to a daemon and reads what it left.
for tie in \
  'let signals ← match ← signalPipe[.]toBaseIO with' \
  'if watchEnd && revs[[]2[]]! &&& [(]POLLIN [|][|][|] POLLHUP [|][|][|] POLLERR[)] != 0 then asked := true if let [.]ok [(]some bytes[)][[:space:]]*← [(]read [(]rt[.]signals[.]getD closedFd[)] 65536[)][.]toBaseIO then heard := bytes[.]toList' \
  'match Linger[.]Session[.]stopOf heard with [|] some [(]signal, true[)] => events := events [+][+] [.]signal signal :: ended [|] some [(]signal, false[)] => events := events [+][+] ended [+][+] [[][.]signal signal[]] [|] none => events := events [+][+] ended return [(]rt, events[)]' \
  '[|] [.]record r => do return [(][{] rt with final := some r [}], [(][)][)]'; do
  printf '%s\n' "$daemon_code" | CG_RE="(^|[[:space:]])$tie([[:space:]]|$)" awk "$CODE_AWK" >/dev/null \
    || fail "a stop signal ends a daemon other than as the session's event, or its end record is not the session's: $tie"
done
# A daemon's checkpoint saves and record writes start on a thread of their own, as
# `Session.Offloop.ask` decides (`offloop_coalesces`): while one runs, a later one waits in place
# of any that waited, so a slow disk holds up no answer and writes never queue.
printf '%s\n' "$daemon_code" | CG_RE='(^|[[:space:]])def Offloop[.]ask [(]w : Offloop[)] [(]write : IO Unit[)] : IO Offloop := do match Linger[.]Session[.]Offloop[.]ask w write with [|] [(]w, none[)] => return w [|] [(]w, some write[)] => return [{] w with running := some [(]← IO[.]asTask write Task[.]Priority[.]dedicated[)] [}]([[:space:]]|$)' awk "$CODE_AWK" >/dev/null \
  || fail "an off-loop write starts other than as Session.Offloop.ask decides, on a thread of its own"
# Every wait sleeps through `Os.Shell.nap`, as `Os.Wait.next` decides (`wait_ends`, over the world
# claim `Wait.Lasts`, which its check tests): at least 1 ms and at most its step, never past its
# deadline, and `false` once that has passed, when the wait reports what it missed. The one wait
# with no deadline that sleeps, `start` or `resume` waiting on a daemon that took the request's
# ticket, sleeps through `Os.Shell.pause`. No timer task stands in for a deadline. The program
# is every module but proofs, tests, suites and checks, which run apart from it.
sleeps="$(code_grep '(^|[^A-Za-z0-9_.])IO[.]sleep([^A-Za-z0-9_]|$)' 'Linger/*.lean' 'packages/*.lean' \
  | grep -v -e '^Linger/[^/]*/Proofs/' -e '^Linger/[^/]*/Tests/' -e '^Linger/[^/]*/Suites/' \
      -e '^packages/[^/]*/[^/]*/Proofs/' -e '^packages/[^/]*/[^/]*/Tests/' -e '^packages/[^/]*/[^/]*/Suites/' \
      -e '/WorldCode/Checks[.]lean:' \
  | cut -d: -f1 | sort | uniq -c | awk '{ printf "%s:%s ", $2, $1 }')"
[ "$sleeps" = "packages/os/Os/WorldCode.lean:2 " ] \
  || fail "a wait sleeps outside Os.Shell.nap and Os.Shell.pause: $sleeps"
code_grep '^[[:space:]]+match Os[.]Wait[.]next deadline step [(]← monotonicMs[)] with$' \
  packages/os/Os/WorldCode.lean >/dev/null \
  || fail "Os.Shell.nap sleeps other than as Os.Wait.next decides"
[ "$(code_count '(^|[^A-Za-z0-9_.])pause [0-9]' 'Linger/*.lean')" -eq 1 ] \
  && code_grep '^[[:space:]]+pause 10$' Linger/App/WorldCode.lean >/dev/null \
  || fail "a wait with no deadline sleeps other than where start and resume wait on their daemon"
# A resume runs in its saved directory, else in a nonempty HOME, else nowhere
# (resumeDir_absent): the daemon reads HOME for it into Env.resumeDir, and the resume suite
# runs it with HOME unset and empty.
printf '%s\n' "$daemon_code" | CG_RE='(^|[[:space:]])match Linger[.]Os[.]Env[.]resumeDir [(]← IO[.]getEnv "HOME"[)] dir [(]← System[.]FilePath[.]isDir dir[)] with([[:space:]]|$)' awk "$CODE_AWK" >/dev/null \
  || fail "a resume chooses its directory outside Env.resumeDir"

# Descriptor exhaustion must suspend admission without stopping existing work.
# The live fixture exhausts real descriptors; gates pin the retry and fd cleanup.
code_grep '^def acceptRetryMs : Nat := [1-9][0-9]*$' 'Linger/Session/WorldCode/Daemon.lean' > /dev/null \
  || fail "admission retry must wait a positive duration"
printf '%s\n' "$daemon_code" | CG_RE='(^|[[:space:]])if let some retryAt := rt[.]acceptAfter then if now < retryAt then deadlines := retryAt :: deadlines([[:space:]]|$)' awk "$CODE_AWK" >/dev/null \
  || fail "admission retry no longer bounds the next poll deadline"
code_grep '^[[:space:]]+rt := [{] rt with acceptAfter := some [(][(]← monotonicMs[)] [+] acceptRetryMs[)] [}]$' 'Linger/Session/WorldCode/Daemon.lean' > /dev/null \
  || fail "admission failures must renew their retry deadline"
printf '%s\n' "$daemon_code" | CG_RE='(^|[[:space:]])try setNonblock fd catch err => close fd throw err([[:space:]]|$)' awk "$CODE_AWK" >/dev/null \
  || fail "failed client setup must release its accepted descriptor"
printf '%s\n' "$daemon_code" | CG_RE='(^|[[:space:]])rt := [{] rt with conns := rt[.]conns [+][+] [[][{] fd [}][]], acceptAfter := none [}]([[:space:]]|$)' awk "$CODE_AWK" >/dev/null \
  || fail "successful admission must clear the failure latch"

# Recovery diagnostics must not throw a second IO error. The robust suite
# injects both the operation failure and a failing stderr write.
printf '%s\n' "$daemon_code" | CG_RE='(^|[[:space:]])def report [(]message : String[)] : IO Unit := do try IO[.]eprintln message catch _ => pure [(][)]([[:space:]]|$)' awk "$CODE_AWK" >/dev/null \
  || fail "daemon diagnostics must contain write failures"
[ "$(code_count 'IO[.]eprintln|IO[.]eprint|IO[.]getStderr' 'Linger/Session/WorldCode/Daemon.lean')" -eq 1 ] \
  || fail "daemon diagnostics must go through the non-throwing reporter"

# The shared driver proves feedback order, termination and invariant preservation.
# Its IO adapter must forward the actual state and retain the returned state/exit.
printf '%s\n' "$daemon_code" | CG_RE='(^|[[:space:]])def pump [(]rt : Rt[)] [(]evs : List Event[)] : BaseIO Rt := do let result ← Driver[.]run executeEffect [{] st := rt[.]st, world := rt, exiting := rt[.]exiting [}] evs return [{] result[.]world with st := result[.]st, exiting := result[.]exiting [}]' awk "$CODE_AWK" >/dev/null \
  || fail "daemon pump must use the proved driver with its actual state and exit flag"
code_grep '^private def perform [(]st : State[)] [(]rt : Rt[)] : [(]eff : Effect Plan[)] → IO [(]Rt × Driver[.]Reply eff[)]$' 'Linger/Session/WorldCode/Daemon.lean' > /dev/null \
  || fail "effect interpreter must implement the driver's dependent reply type"
# The executor the driver runs answers every effect and raises nothing (`run_total_safe`, over
# the world claim `Driver.Responds`, which its check and the delivery suite test): `BaseIO` has no error to
# raise, and an error `perform` raises all the same is reported and answered as its effect's
# failure.
printf '%s\n' "$daemon_code" | CG_RE='(^|[[:space:]])private def executeEffect [(]st : State[)] [(]rt : Rt[)] [(]eff : Effect Plan[)] : BaseIO [(]Rt × Driver[.]Reply eff[)] := [(]perform st rt eff[)][.]catchExceptions fun err => do discard <[|] [(]report s!"[^"]*"[)][.]toBaseIO failed rt eff([[:space:]]|$)' awk "$CODE_AWK" >/dev/null \
  || fail "the driver's effect executor must answer every effect with its reply and raise nothing"
for tie in \
  '[|] [.]checkpoint => do return [(][{] rt with saves := ← rt[.]saves[.]ask [(]rt[.]saveCkpt st[)] [}], false[)]' \
  '[|] some write => return [(][{] running := some [(]← IO[.]asTask write Task[.]Priority[.]dedicated[)] [}], some ended[)]' \
  'let seen := rt[.]st[.]seen if rt[.]published == some seen then return rt let records ← rt[.]records[.]ask [(]rt[.]saveRecord [(][.]running [(]some seen[)][)][)]' \
  'rt ← flushPty rt if !rt[.]exiting then rt ← publish rt latest[.]set rt'; do
  printf '%s\n' "$daemon_code" | CG_RE="(^|[[:space:]])$tie([[:space:]]|$)" awk "$CODE_AWK" >/dev/null \
    || fail "checkpoint and record writes must carry the driver's current state, on a thread of their own: $tie"
done

# An info answer can span several frames. The pure producer proves the bound;
# keep the IO accumulator on that same policy rather than a copied number.
code_grep '^abbrev infoReplyCap : Nat := Linger[.]Session[.]infoReplyCap$' 'Linger/Session/WorldCode/Inventory.lean' > /dev/null \
  || fail "the inventory's info policy diverged from the proved producer"
code_grep '^[[:space:]]+Linger[.]Session[.]Buf[.]bufOffer infoReplyCap acc [(]ByteArray[.]mk payload[.]toArray[)]$' 'Linger/Session/WorldCode/Inventory.lean' > /dev/null \
  || fail "the info accumulator no longer uses the shared byte policy"

# All session verbs consume the same exact target parser. Fuzzy matching stays
# in the interactive picker. A remote verb runs through its host's transport, which the remotes
# file gives it or else ssh (`Remote.transportFor`), and the argv `Remote.targetArgv` builds: the
# transport's attach or query command, then the proved encoder's plain words, which every
# transport delivers as they are (`Transport.Delivers`, `transport_exact`) and every shell passes
# on (`Shell.Literal`); stdin is inherited for binary input.
# Every attach or capture argv linger builds for itself places its target with
# Remote.targetOperands, which Remote.targetArgs reads back exactly (targetArgs_targetOperands).
# A literal attach argv passes a name starting with - as an option. "attach" may begin
# a list, array or cons only in the command parser's pattern and in Picker.attachArgs,
# tied above.
attach_words="$(code_grep '"attach"[[:space:]]*(,|[]]|::)' 'Linger/*/WorldCode.lean' 'Linger/*/WorldCode/*' \
  | sed 's/^\([^:]*\):[0-9]*:[[:space:]]*/\1: /')"
[ "$attach_words" = "$(printf '%s\n' \
    'Linger/App/WorldCode.lean: | "attach" :: rest | "a" :: rest =>' \
    'Linger/Selector/WorldCode.lean: ("attach" :: (if readOnly then ["--read-only"] else []) ++')" ] \
  || fail "a literal attach argv: build it with Picker.attachArgs, whose operands come from Remote.targetOperands: $attach_words"
! code_grep '(^|[^A-Za-z0-9_.])Fuzzy[.]|Name[.]sanitize' Linger/App/WorldCode.lean Linger/Session/WorldCode/Client.lean \
  || fail "noninteractive command lookup must not fuzzy-match or rewrite a name"
code_grep '^[[:space:]]+Linger[.]Target[.]Remote[.]targetValid target = true ∧ target ∉ candidates := by$' Linger/Selector/Proofs/Picker.lean >/dev/null \
  || fail "selector creation and command arguments no longer share the target grammar"
for verb in attach start resume send detach kill info capture resize get set unset clear; do
  code_grep "^[[:space:]]+withTarget \"$verb\" " Linger/App/WorldCode.lean >/dev/null \
    || fail "session command bypassed the common exact target boundary: $verb"
done
for tie in \
  'match Linger[.]Target[.]Remote[.]parseTarget target with [|] none => invalidTarget [|] some parsed => runTarget verb parsed args localAction options' \
  'let some targets := names[.]mapM Linger[.]Target[.]Remote[.]parseTarget [|] invalidTarget let deadline ← limit[.]mapM' \
  'answer ← runTarget "wait" target [[]] [(]cmdWait deadline[)] options' \
  'let [(]heard, why[)] ← hear name silenceMs match Wait[.]decide deadline heldSince [(]← monotonicMs[)] heard with' \
  'heldSince := since if let some first := since then discard <[|] nap [(]first [+] Wait[.]heldNameMs[)] 20' \
  'let interactive := verb == "attach" if interactive && [(]![(]← stdinIsTty[)] [|][|] ![(]← [(]← IO[.]getStdout[)][.]isTty[)][)] then' \
  'let transport := Linger[.]Target[.]Remote[.]transportFor [(]← remoteConfig[)] host match Linger[.]Target[.]Remote[.]targetArgv transport verb options target[.]name args with' \
  '[|] cmd :: argv => let child ← IO[.]Process[.]spawn [{] cmd, args := argv[.]toArray, stdin := [.]inherit [}] try return [.]program [(]← child[.]wait[)] finally if interactive then writeAll stdoutFd [(]ByteArray[.]mk Terminal[.]Render[.]leaveAnsi[.]toArray[)]' \
  'let readOnly := args[.]head[?] == some "--read-only" let args := if readOnly then args[.]tail else args let some [(]name, cmd[)] := Linger[.]Target[.]Remote[.]targetArgs args [|]' \
  'let history := args[.]head[?] == some "--history" let args := if history then args[.]tail else args let some [(]name, [[][]][)] := Linger[.]Target[.]Remote[.]targetArgs args [|]' \
  'withTarget "attach" name cmd [(]cmdAttach · cmd readOnly[)] [(]if readOnly then [[]"--read-only"[]] else [[][]][)]' \
  'withTarget "capture" name [[][]] [(]cmdRead · [(]if history then [.]history else [.]screen[)] [(]if history then Terminal[.]Render[.]history else Terminal[.]Render[.]screenText[)][)] [(]if history then [[]"--history"[]] else [[][]][)]'; do
  printf '%s\n' "$cli_code" | CG_RE="(^|[[:space:]])$tie([[:space:]]|$)" awk "$CODE_AWK" >/dev/null \
    || fail "command transport lost exact targets, argv, stdin or terminal ownership: $tie"
done
[ "$(code_count '^[[:space:]]+writeAll stdoutFd [(]ByteArray[.]mk Terminal[.]Render[.]leaveAnsi[.]toArray[)]$' Linger/App/WorldCode.lean)" -eq 1 ] \
  || fail "a remote attach's end no longer establishes canonical handback"
# Reaching a host is the transport's (`Transport.Delivers`): the program names ssh only as the
# transport of a host the remotes file gives no command (`Remote.ssh`), and runs no option of its.
[ "$(code_grep '"ssh"' 'Linger/*.lean' ':!Linger/*/Suites/*' ':!Linger/*/Proofs/*' ':!Linger/*/Tests/*' \
    ':!Linger/*/WorldCode/Checks.lean' 'packages/*.lean' | sed -E 's/^([^:]+):[0-9]+:[[:space:]]*/\1: /')" \
    = 'Linger/Target/CoreCode/Remote.lean: { query := ["ssh", "-T", "--", host], attach := ["ssh", "-t", "--", host] }' ] \
  || fail "the program runs ssh outside Remote.ssh, the transport of a host the remotes file gives no command"

# Lifetime ownership covers two resources: the socket namespace and the saved
# state namespace. The model takes the operating system's lock contract as the world claim
# `Claim.Exclusive`, which its check and Linger.Session.Suites.Robust test, and linger's decision to act as
# an owner as `Claim.enters`, which every two-lock acquisition asks before it acts; these IO ties
# and Linger.Session.Suites.Identity check acquisition before use and release after cleanup. A
# connected daemon's failure must never fall back to older saved data.
paths_code="$(awk '{ $1 = $1; printf "%s ", $0 }' Linger/Session/WorldCode/Paths.lean)"
for tie in \
  'match Linger[.]Target[.]Name[.]check name with [|] some name => return name [|] none => throw' \
  'if listed then return s!"[{]dir[}]/[{]name[}][{]suffix[}]" let name ← checkName name ensureDir dir let path := s!"[{]dir[}]/[{]name[}][{]suffix[}]" checkSpelling path return path' \  'def namedPath [(]dir name suffix : String[)] : IO String := pathIn dir name suffix false' \
  'def socketPath [(]name : String[)] : IO String := do namedPath [(]← socketDir[)] name "[.]sock"' \
  'def ckptPath [(]name : String[)] : IO String := do namedPath [(]← stateDir[)] name "[.]ckpt"' \
  'def lockPath [(]name : String[)] : IO String := do namedPath [(]← socketDir[)] name "[.]lock"' \
  'def stateLockPath [(]name : String[)] : IO String := do namedPath [(][(]← stateDir[)] [+][+] "/[.]locks"[)] name "[.]lock"' \
  'def logPath [(]name : String[)] : IO String := do namedPath [(][(]← stateDir[)] [+][+] "/logs"[)] name "[.]log"' \
  'def acquire [(]path : String[)] [(]retry : IO Bool[)] [(]listed : Bool[)] : IO [(]Option UInt32[)] := do let mut fd ← Os[.]Shell[.]flock path while fd < 0 do unless ← retry do break fd ← Os[.]Shell[.]flock path if fd < 0 then return none let held := fd[.]toUInt64[.]toUInt32 unless listed do try checkSpelling path catch err => Os[.]Shell[.]close held throw err return some held' \
  'def withLockRetrying [{]α : Type[}] [(]path : String[)] [(]retry : IO Bool[)] [(]action : IO α[)] [(]listed : Bool := false[)] : IO α := do let some fd ← acquire path retry listed [|] throw [(]IO[.]userError s!"session is owned by another process [(][{]path[}][)]"[)] try action finally Os[.]Shell[.]close fd' \
  'def withOwnership [{]α : Type[}] [(]socket : String[)] [(]checkpoint : IO String[)] [(]retry : IO Bool[)] [(]listed : Bool[)] [(]action : IO α[)] : IO α := do let held ← acquire socket retry listed try let [(]state, refused[)] ← match held with [|] none => pure [(]none, socket[)] [|] some _ => do let path ← checkpoint pure [(]← acquire path retry listed, path[)] try unless Claim[.]enters held[.]isSome state[.]isSome do throw [(]IO[.]userError s!"session is owned by another process [(][{]refused[}][)]"[)] action finally if let some fd := state then Os[.]Shell[.]close fd finally if let some fd := held then Os[.]Shell[.]close fd' \  'def Listed[.]withLock [{]α : Type[}] [(]n : Listed[)] [(]action : IO α[)] : IO α := do withLockRetrying [(]← pathIn [(]← socketDir[)] n[.]name "[.]lock" true[)] [(]pure false[)] action [(]listed := true[)]' \  'def Listed[.]withSessionLock [{]α : Type[}] [(]n : Listed[)] [(]action : IO α[)] : IO α := do withOwnership [(]← pathIn [(]← socketDir[)] n[.]name "[.]lock" true[)] [(]do let locks := [(]← stateDir[)] [+][+] "/[.]locks" ensureDir locks pathIn locks n[.]name "[.]lock" true[)] [(]pure false[)] true action' \
  'def withLock [{]α : Type[}] [(]path : String[)] [(]action : IO α[)] : IO α := withLockRetrying path [(]pure false[)] action' \
  'def withSessionLockRetrying [{]α : Type[}] [(]name : String[)] [(]retry : IO Bool[)] [(]action : IO α[)] : IO α := do withOwnership [(]← lockPath name[)] [(]stateLockPath name[)] retry false action' \
  'def withSessionLock [{]α : Type[}] [(]name : String[)] [(]action : IO α[)] : IO α := withSessionLockRetrying name [(]pure false[)] action'; do
  printf '%s\n' "$paths_code" | CG_RE="(^|[[:space:]])$tie([[:space:]]|$)" awk "$CODE_AWK" >/dev/null \
    || fail "session paths or lifetime locking bypassed their contract: $tie"
done
# A listing row takes its name verbatim from the socket filename (`rowFields_name`), so
# both listings pass every directory entry through the exact name check.
for tie in \
  'private def listNames [(]dir suffix : String[)] : IO [(]List Listed[)] := do ensureDir dir return [(]← System[.]FilePath[.]readDir dir[)][.]toList[.]filterMap fun e => [(][(]e[.]fileName[.]dropSuffix[?] suffix[)][.]bind [(]Linger[.]Target[.]Name[.]check ·[.]toString[)][)][.]map [(]⟨·⟩[)]' \
  'def listSocketNames : IO [(]List Listed[)] := do listNames [(]← socketDir[)] "[.]sock"' \
  'def listCkptNames : IO [(]List Listed[)] := do listNames [(]← stateDir[)] "[.]ckpt"'; do
  printf '%s\n' "$paths_code" | CG_RE="(^|[[:space:]])$tie([[:space:]]|$)" awk "$CODE_AWK" >/dev/null \
    || fail "session listing must check every directory entry with Name.check: $tie"
done
! code_grep 'removeFile|rename' Linger/Session/WorldCode/Paths.lean \
  || fail "lock path construction and acquisition must never unlink or replace a lock inode"
printf '%s\n' "$client_code" | CG_RE='(^|[[:space:]])try Paths[.]checkSpelling path return some fd catch err => close fd throw err([[:space:]]|$)' awk "$CODE_AWK" >/dev/null \
  || fail "successful connects must reject case-folded aliases and close on failure"
printf '%s\n' "$daemon_code" | CG_RE='(^|[[:space:]])IO Unit := do let deadline := [(]← monotonicMs[)] [+] claimWaitMs let reported ← IO[.]mkRef false let retry := claimRetry name [(]← Paths[.]socketPath name[)] deadline reported Paths[.]withSessionLockRetrying name retry do ignoreSighup let sockPath ← Paths[.]socketPath name([[:space:]]|$)' awk "$CODE_AWK" >/dev/null \
  || fail "daemon recovery and lifetime must execute inside both ownership locks"
# A start takes a name only by Start.plan, decided holding the name, and never loads a checkpoint;
# a resume runs only a saved session's program, by Start.resumePlan, or nothing. Every other
# daemon starts from what the name's checkpoint holds as `Recovery.decide` says (`recovery_exact`),
# holding the name: a refusal starts nothing over a checkpoint that does not decode, and the
# command's daemon, the offline readers and an attach whose daemon refused all ask it of the
# file's bytes. Linger.Session.Suites.Resume writes damaged checkpoints at a saved session's path.
for tie in \
  'if let some req := start then let saved ← System[.]FilePath[.]pathExists [(]← Paths[.]ckptPath name[)] if resume then match Start[.]resumePlan live saved with' \
  'else match Start[.]plan live saved with' \
  'let recovered ← if start[.]isSome && !resume then pure [(][.]ok none[)] else recover !resume if let [.]error [(]status, why[)] := recovered then match start with [|] some req => req[.]tell [(][.]failed status why[.]toUTF8[.]toList[)] [|] none => report s!"linger: session .[{]name[}]. did not start: [{]why[}]" return let saved := recovered[.]toOption[.]join'; do
  printf '%s\n' "$daemon_code" | CG_RE="(^|[[:space:]])$tie([[:space:]]|$)" awk "$CODE_AWK" >/dev/null \
    || fail "a start took a name outside Start.plan, or a resume started anything but a saved session: $tie"
done
for tie in \
  'private def recoverFor [(]name : String[)] [(]create : Bool[)] : IO Daemon[.]Recovered := do match Linger[.]App[.]Recovery[.]decide create [(]← Resume[.]readCkpt name[)] with [|] [.]fresh => return [.]ok none [|] [.]resume ck => return [.]ok [(]some [(]ck[.]vt, ck[.]cwd, ck[.]labels[)][)] [|] [.]refuse answer =>' \
  'match Linger[.]App[.]Recovery[.]decide true file with [|] [.]refuse answer => return some answer'; do
  printf '%s\n' "$cli_code" | CG_RE="(^|[[:space:]])$tie([[:space:]]|$)" awk "$CODE_AWK" >/dev/null \
    || fail "a command started from a checkpoint other than as Recovery.decide says: $tie"
done
[ "$(code_count '[(]recoverFor name[)]' Linger/App/WorldCode.lean)" -eq 3 ] \
  || fail "every daemon a command begins, for attach, start and resume, recovers through recoverFor"
! code_grep '(^|[^[:alnum:]_])loadBytes([^[:alnum:]_]|$)' Linger/App/WorldCode.lean Linger/Session/WorldCode/Resume.lean \
  || fail "a command decodes a checkpoint itself: ask Recovery.decide, which never takes bytes that do not decode for no checkpoint"
# A request's answer is true (`start_answer_true`). The command makes the request's ticket before
# it begins the daemon. The daemon takes it once, before its first report and at the commit point
# just before its socket listens, and starts nothing when the command took it (`Start.proceeds`);
# it reports only holding it. The command takes it once its bounded wait has run out, and then
# answers that nothing starts; otherwise it waits for the daemon's report, and says the program
# runs only by `Start.answer`. Linger.Session.Suites.Resume checks both sides.
for tie in \
  'if let some req := start then unless Start[.]proceeds [(]← req[.]take[)] do return let listenFd ← unixListen sockPath'; do
  printf '%s\n' "$daemon_code" | CG_RE="(^|[[:space:]])$tie([[:space:]]|$)" awk "$CODE_AWK" >/dev/null \
    || fail "a daemon reached its commit point without taking its request's ticket: $tie"
done
[ "$(code_count 'req[.]take|Start[.]proceeds|unixListen' Linger/Session/WorldCode/Daemon.lean)" -eq 2 ] \
  || fail "a daemon takes its request's ticket and listens only at its one commit point"
for tie in \
  'private def takeTicket [(]report : String[)] : IO Bool := do try IO[.]FS[.]removeFile [(]ticketPath report[)] return true catch _ => return false' \
  'let take : IO Bool := do if let some held← took[.]get then return held let held ← takeTicket report took[.]set [(]some held[)] return held let tell [(]r : Linger[.]Session[.]Start[.]Report[)] : IO Unit := do if ← take then writeReport report r return [{] take, tell [}]' \
  'IO[.]FS[.]withFile [(]ticketPath report[)] [.]writeNew fun _ => pure [(][)] try spawnDetached [(]← IO[.]appPath[)][.]toString ⟨args⟩ log catch err => discard <[|] takeTicket report throw err' \
  'if bounded then unless ← nap deadline 10 do if ← takeTicket report then return [.]took true bounded := false else pause 10' \
  'match Linger[.]Session[.]Start[.]answer [(]waited matches [.]took _[)] [(]waited matches [.]told [(]some [.]started[)][)], waited with [|] [.]started, _ => return [.]done [|] [.]notStarted,' \
  'let runs := waited matches [.]told [(]some [.]started[)] [|][|] waited matches [.]told [(]some [.]running[)] match Linger[.]Session[.]Start[.]answer [(]waited matches [.]took _[)] runs, waited with [|] [.]started, [.]told [(]some [.]started[)] => do sayMoved name return [.]done [|] [.]started, _ => return [.]done [|] [.]notStarted,' \
  'let pid ← beginRequest report log [(][[]"__start", report, name, cwd[]] [+][+] argv[)] startStatus name log [(]← awaitReport pid report[)]' \
  'let pid ← beginRequest report log [[]"__resume", report, name, cwd[]] resumeStatus name log [(]← awaitReport pid report[)]'; do
  printf '%s\n' "$cli_code" | CG_RE="(^|[[:space:]])$tie([[:space:]]|$)" awk "$CODE_AWK" >/dev/null \
    || fail "start or resume answered without its request's ticket: $tie"
done
[ "$(code_count 'takeTicket report' Linger/App/WorldCode.lean)" -eq 4 ] \
  || fail "only the daemon's take-once, a failed begin and the command's wait take a request's ticket"
# An offline reader holds both locks briefly, while it loads and renders, so the daemon's
# startup claim retries a held lock for a bounded, positive time, and stops at once when a live
# daemon answers on the socket. A retry is asked only after a failed attempt. Every other
# acquisition is withLock or withSessionLock, one attempt each, and only the claim names a
# retrying acquisition, so no reader can pass a retry by position. The Claim model reads each
# failed attempt as an unchanged step. Linger.Session.Suites.Robust holds both of a name's locks
# while resume starts the session, as an offline reader does, and checks that a claim finding
# both free logs no wait.
code_grep '^private def claimWaitMs : Nat := [1-9][0-9]*$' 'Linger/Session/WorldCode/Daemon.lean' > /dev/null \
  || fail "the startup claim must wait a positive, fixed time"
printf '%s\n' "$daemon_code" | CG_RE='(^|[[:space:]])if [(]← monotonicMs[)] ≥ deadline then return false let live ← unixConnect sockPath if live ≥ 0 then close live[.]toUInt64[.]toUInt32 return false([[:space:]]|$)' awk "$CODE_AWK" >/dev/null \
  || fail "the startup claim must stop at its deadline and when a live daemon answers"
retrying="$(code_grep '(^|[^[:alnum:]_])with(Session)?LockRetrying([^[:alnum:]_]|$)' 'Linger/*' \
  | awk -F: '$1 != "Linger/Session/WorldCode/Paths.lean" { print $1 }')"
[ "$retrying" = 'Linger/Session/WorldCode/Daemon.lean' ] \
  || fail "only the daemon's startup claim may retry a held lock: ${retrying:-no retrying claim}"
for tie in \
  'finally close listenFd try IO[.]FS[.]removeFile sockPath catch _ => pure [(][)][[:space:]]+end Linger[.]Session[.]Shell[.]Daemon' \
  'finally let rt ← latest[.]get for c in rt[.]conns do close c[.]fd let outcome ← stopProgram rt let rt ← settleRecord rt try record[.]save [(]rt[.]final[.]getD [(][.]ended outcome[)][)]' \
  'let previous ← record[.]load record[.]save [(][.]running none[)] let spawned ← try trySpawnPty'; do
  printf '%s\n' "$daemon_code" | CG_RE="(^|[[:space:]])$tie([[:space:]]|$)" awk "$CODE_AWK" >/dev/null \
    || fail "daemon resource cleanup escaped its ownership lifetime: $tie"
done
# A name's end record and a session's checkpoint, a daemon's or an imported one, are replaced
# whole and durably (`Os.Shell.replaceFile`): a temporary sibling made private, written and
# flushed, renamed over the file, and the directory flushed, the protocol the world claims
# `Record.Kept` (`record_answer`) and `Disk.Durable` (`crash_resumes`) take the file system to
# honor. The agent suite reads records after their sessions end, the resume suite reads both
# after a daemon killed while it saves, and the interop suite reads an imported checkpoint.
record_code="$(awk '{ $1 = $1; printf "%s ", $0 }' Linger/Session/WorldCode/Record.lean)"
for tie in \
  'def save [(]name : String[)] [(]record : Linger[.]Session[.]Record[)] : IO Unit := do Os[.]Shell[.]replaceFile [(]← Paths[.]recordPath name[)] [(]ByteArray[.]mk [(]Linger[.]Session[.]Record[.]encode record[)][.]toArray[)]' \
  '[|] some bytes => Os[.]Shell[.]replaceFile path [(]ByteArray[.]mk bytes[.]toArray[)]'; do
  printf '%s\n' "$record_code" | CG_RE="(^|[[:space:]])$tie([[:space:]]|$)" awk "$CODE_AWK" >/dev/null \
    || fail "an end record is written other than whole and durably, through Os.Shell.replaceFile: $tie"
done
os_shell_code="$(awk '{ $1 = $1; printf "%s ", $0 }' packages/os/Os/WorldCode.lean)"
printf '%s\n' "$os_shell_code" | CG_RE='(^|[[:space:]])def replaceFile [(]path : String[)] [(]bytes : ByteArray[)] : IO Unit := do let tmp := path [+][+] "[.]tmp" IO[.]FS[.]withFile tmp [.]write fun handle => do IO[.]Prim[.]setAccessRights tmp 0o600 handle[.]write bytes let _ ← fsyncPath tmp IO[.]FS[.]rename tmp path let dir := [(][(]System[.]FilePath[.]mk path[)][.]parent[.]map [(]·[.]toString[)][)][.]getD "" let _ ← fsyncPath [(]if dir[.]isEmpty then "[.]" else dir[)] [(]directory := true[)]([[:space:]]|$)' awk "$CODE_AWK" >/dev/null \
  || fail "Os.Shell.replaceFile no longer makes its temporary file private and flushes it before its rename and the directory after it"
[ "$(code_count 'IO[.]FS[.]rename' 'Linger/Session/WorldCode/*')" -eq 0 ] \
  || fail "a session file is renamed into place outside Os.Shell.replaceFile, which flushes it"
# `capture` of a saved session takes the steps of `Capture.plan` (`capture_waits_unlocked`), each
# from an `acquire` to the next `release` inside one `withSessionLock`, as `Capture.work` reads
# them: it loads and renders holding both locks and writes once it has let them go. The robust
# suite resumes a session while a capture of it waits on a pipe nobody reads.
for tie in \
  'private def runHolding [(]name : String[)] [(]plan : List Linger[.]App[.]Capture[.]Step[)] [(]run : Linger[.]App[.]Capture[.]Step → IO Unit[)] : IO Unit := do let mut held : Option [(]Array Linger[.]App[.]Capture[.]Step[)] := none for step in plan do match step, held with [|] [.]acquire, none => held := some #[[][]] [|] [.]release, some inside => Paths[.]withSessionLock name [(]inside[.]forM run[)] held := none [|] [.]acquire, some _ [|] [.]release, none => pure [(][)] [|] step, some inside => held := some [(]inside[.]push step[)] [|] step, none => run step if let some inside := held then Paths[.]withSessionLock name [(]inside[.]forM run[)]' \
  'requestStatus name result [|] none => let file ← IO[.]mkRef [(]none : Option ByteArray[)] let shown ← IO[.]mkRef [(]Shown[.]refusal [.]notFound [(]← refusalText name [.]notFound[)][)] let answer ← IO[.]mkRef Answer[.]failed runHolding name Linger[.]App[.]Capture[.]plan fun [|] [.]load => do file[.]set [(]← Resume[.]readCkpt name[)] [|] [.]render => do match Linger[.]App[.]Recovery[.]decide false [(]← file[.]get[)] with [|] [.]resume ck => shown[.]set [(][.]session [(]render ck[.]vt[)][)]' \
  '[|] [.]write => do match ← shown[.]get with [|] [.]session bytes => writeAll stdoutFd [(]ByteArray[.]mk bytes[.]toArray[)] answer[.]set [.]done [|] [.]refusal said why => IO[.]eprintln s!"linger: [{]why[}]" answer[.]set said [|] [.]acquire [|] [.]release => pure [(][)] answer[.]get' \
  'if readOnly then match ← Client[.]connect name with [|] some fd => attachSpoken name fd true [|] none => match ← visitOffline name true with' \
  'let [(]steps, record, file[)] ← Paths[.]withSessionLock name do let record ← [(]Record[.]load name[)][.]toBaseIO let steps := Linger[.]App[.]Recovery[.]visit readOnly record[.]toOption[.]join if steps == [[][.]resume[]] then return [(]steps, record, none[)] return [(]steps, record, ← Resume[.]readCkpt name[)]' \
  'Paths[.]withSessionLock name do if [(]← Resume[.]readCkpt name[)][.]map [(]·[.]data[)] == some shown[.]data then Resume[.]dropCkpt name'; do
  printf '%s\n' "$cli_code" | CG_RE="(^|[[:space:]])$tie([[:space:]]|$)" awk "$CODE_AWK" >/dev/null \
    || fail "offline reading or listing bypassed ownership: $tie"
done
tie='let record ← try listed[.]withSessionLock [(]some <[$]> [(]Record[.]loadListed listed[)][.]toBaseIO[)] catch _ => pure none'
printf '%s\n' "$inventory_code" | CG_RE="(^|[[:space:]])$tie([[:space:]]|$)" awk "$CODE_AWK" >/dev/null \
  || fail "offline reading or listing bypassed ownership: $tie"
# Saved viewing consumes the bounded, faithful replay cursor. The original
# snapshot survives every resize, and the immutable load precedes terminal IO.
# Linger.Session.Suites.Watch observes input discard, lock release, exact replay and handback.
for tie in \
  'let mut lastSize : Option [(]UInt32 × UInt32[)] := none while true do let size ← winsizeGet stdinFd if lastSize != some size then let cols := if size[.]1 == 0 then snapshot[.]colCount else size[.]1[.]toNat let rows := if size[.]2 == 0 then snapshot[.]rowCount else size[.]2[.]toNat' \
  'let view := if snapshot[.]colCount == cols && snapshot[.]rowCount == rows then snapshot else snapshot[.]resize cols rows let mut repaint := Terminal[.]Replay[.]start view repeat match Terminal[.]Replay[.]next 65536 repaint with [|] none => break [|] some [(]bytes, next[)] => if !bytes[.]isEmpty then writeAll stdoutFd [(]ByteArray[.]mk bytes[.]toArray[)] repaint := next' \
  'let title := Linger[.]Display[.]Title[.]compose name view[.]windowTitle [(]String[.]singleton [(]Linger[.]Display[.]Status[.]icon status[)][)] Terminal[.]Title[.]maxChars writeAll stdoutFd [(]ByteArray[.]mk [(]Terminal[.]Title[.]update view title[)][.]toArray[)]' \
  'if [(]splitDetach bytes true[)][.]2 then return [.]detached return [.]detached finally try writeAll stdoutFd [(]ByteArray[.]mk Terminal[.]Render[.]leaveAnsi[.]toArray[)] finally termRestore stdinFd saved'; do
  printf '%s\n' "$client_code" | CG_RE="(^|[[:space:]])$tie([[:space:]]|$)" awk "$CODE_AWK" >/dev/null \
    || fail "saved viewer bypassed bounded replay, snapshot preservation or terminal ownership: $tie"
done
printf '%s\n' "$import_code" | CG_RE='(^|[[:space:]])if row[.]lookup "state" == some "resumable" then Paths[.]withSessionLock name do let some saved := [(]← Resume[.]readCkpt name[)][.]bind Linger[.]Session[.]Checkpoint[.]loadBytes [|] throw' awk "$CODE_AWK" >/dev/null \
  || fail "exporter must establish offline ownership before reading saved state"

# `onMsg_resizePty_agrees` connects every emitted pty size to the resulting
# emulator's effective dimensions. IO is outside the theorem: keep the effect
# interpreter forwarding those exact dimensions, in order.
code_grep '^[[:space:]]+[|] [.]resizePty cols rows =>' 'Linger/Session/WorldCode/Daemon.lean' > /dev/null \
  || fail "review the pty effect interpreter against onMsg_resizePty_agrees"
code_grep '^[[:space:]]+winsizeSet rt[.]ptyFd cols rows$' 'Linger/Session/WorldCode/Daemon.lean' > /dev/null \
  || fail "the pty interpreter no longer forwards the proved dimensions in order"

# The elapsed-time theorems use Nat. Keep the actual monotonic source and the
# daemon tick on that representation; narrowing here is invisible to the proofs.
code_grep '^def monotonicMs : IO Nat := IO[.]monoMsNow$' 'packages/os/Os/WorldCode.lean' > /dev/null \
  || fail "the monotonic clock no longer forwards Lean's Nat clock directly"
code_grep '^[[:space:]]+let now ← monotonicMs$' 'Linger/Session/WorldCode/Daemon.lean' > /dev/null \
  || fail "the daemon tick no longer reads the monotonic clock"
code_grep "^[[:space:]]+rt ← pump rt' [(]events [+][+] [[][.]tick now[]][)]$" 'Linger/Session/WorldCode/Daemon.lean' > /dev/null \
  || fail "the daemon no longer forwards the monotonic value to the proved tick"

# The daemon boots from Session.bootVt, the term the resume theorems quantify over:
# `resume_restores` (Challenge.lean, part 7) states the resume over `bootVt` itself.
code_grep '^[[:space:]]+let vt0 := Linger[.]Session[.]bootVt [(]restore[.]map [(]·[.]1[)][)]$' 'Linger/Session/WorldCode/Daemon.lean' > /dev/null \
  || fail "Daemon.serve no longer boots from Session.bootVt, which resume_restores covers"

# Read-only attachment's client-side guards. Read-only
# is enforced DAEMON-side: the attach carries the mode, `onMsg .attach` records it
# whatever the size, and `onMsg .input`/`onMsg .resize` then drop a watcher's
# keystrokes and never let it size the session (`onMsg_input_readonly`). So these
# two `!readOnly` call sites are defence in depth and a pty test CANNOT see them —
# remove either and not one observable byte changes. That makes a grep the only
# honest oracle, the same species as SHIM_CAP above; faking it as a pty assertion
# would be decoration. `Linger/Session/Suites/Watch.lean` covers guard A (the mode
# the attach carries), which IS observable.
code_grep 'if size != lastSize && !readOnly' 'Linger/Session/WorldCode/Client.lean' > /dev/null \
  || fail "Client.attach lost its read-only resize guard (a watcher would fight the user's size)"
code_grep 'if !out.isEmpty && !readOnly' 'Linger/Session/WorldCode/Client.lean' > /dev/null \
  || fail "Client.attach lost its read-only input guard (a watcher would forward keystrokes)"
code_grep '^[[:space:]]+let mode : Linger[.]Session[.]Mode := if readOnly then [.]readOnly else [.]writable$' 'Linger/Session/WorldCode/Client.lean' > /dev/null \
  && code_grep '^[[:space:]]+sendMsg fd [(][.]attach mode cols rows[)]$' 'Linger/Session/WorldCode/Client.lean' > /dev/null \
  || fail "Client.attach no longer sends the mode its caller asked for (the wire's only read-only bit)"
# The detach key follows Env.detachEnabled: always in a read-only view, whose saved
# form passes that value, true, directly (detachEnabled_readOnly), and for writable
# attach only while LINGER_NO_DETACH_KEY is unset. Linger.Session.Suites.Watch and Linger.Session.Suites.Attach observe both.
printf '%s\n' "$client_code" | CG_RE='(^|[[:space:]])let detachEnabled := Linger[.]Os[.]Env[.]detachEnabled readOnly [(]← IO[.]getEnv "LINGER_NO_DETACH_KEY"[)]([[:space:]]|$)' awk "$CODE_AWK" >/dev/null \
  || fail "attach bypasses Env.detachEnabled, which keeps the detach key in read-only views"
code_grep '^[[:space:]]+let [(]out, detach[)] := splitDetach bs detachEnabled$' Linger/Session/WorldCode/Client.lean >/dev/null \
  || fail "attach no longer splits input with its detach policy"

# The checkpoint decoder must not grow its forge back.
# `Linger/Session/CoreCode/Checkpoint.lean` keeps a PERMANENT `import all Terminal.Vt`: `wVt` reads
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
code_grep '(^|[^`[:alnum:]_.])Vt[.]ofDecoded ' 'Linger/Session/CoreCode/Checkpoint.lean' > /dev/null \
  || fail "Linger/Session/CoreCode/Checkpoint.lean no longer decodes through Vt.ofDecoded (a corrupt checkpoint could carry a zero column count)"
FORGE='(^|[^`[:alnum:]_])(cols|rows|grid|bot|tabs|pstate|u8need|u8acc) *:='
! code_grep "$FORGE" 'Linger/Session/CoreCode/Checkpoint.lean' \
  || fail "a Vt field is assigned in Linger/Session/CoreCode/Checkpoint.lean — the decoder forge is back; go through Vt.ofDecoded, which validates"

# Extensional reader theorems cannot distinguish reject-before-expansion from
# expand-then-reject. The latter passed every semantic check, and
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
  }' Linger/Session/CoreCode/Checkpoint.lean >&2 || fail "checkpoint allocation guard changed"
# The six bounds the byte-array readers forward.
for bound in \
  'rRLEB rCellB b i maxLength' \
  'let [(]rows, j[)] ← rListB rRowB b j maxRows' \
  'let [(]rows, j[)] ← rListB [(]fun bytes j => rRowB bytes j maxCols[)] bytes j maxRows' \
  'let [(]tabs, i[)] ← rListB rBoolB b i [(]some cols[)]' \
  'let [(]sb, i[)] ← rRingB b i [(]some sbCap[)]' \
  'let [(]altGrid, i[)] ← rAltB b i [(]some cols[)] [(]some rows[)] [(]version == 1[)]'; do
  code_grep "^[[:space:]]+$bound\$" 'Linger/Session/CoreCode/Checkpoint.lean' > /dev/null \
    || fail "a byte-array checkpoint reader stopped forwarding its bound: $bound"
done
# The checkpoint hooks are `IO`, so no theorem sees them use the proved codec: write the
# session's terminal and labels, read through the observers the headline theorems name,
# through `saveBytes` (`saveBytes_eq`), replacing the file whole and durably, and hand the file's
# bytes to `Recovery.decide`, which decodes them with `loadBytes` (`recovery_exact`).
resume_code="$(awk '{ $1 = $1; printf "%s ", $0 }' Linger/Session/WorldCode/Resume.lean)"
for tie in \
  'let ck : Ckpt Terminal[.]Vt[.]Vt := [{] vt := st[.]terminal, cwd, labels := st[.]labelList [}] let bytes := saveBytes ck Os[.]Shell[.]replaceFile path bytes' \
  'if ![(]← System[.]FilePath[.]pathExists path[)] then return none try return some [(]← IO[.]FS[.]readBinFile path[)]'; do
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
# stops it: from Lean every process binding takes the proof `Os.Shell.checkPid`
# returns, which it gives for no 0 and no value that casts to a negative `pid_t` (a type,
# not a grep), and `Linger/Os/Suites/Shim.lean`'s `kill 0 15` is that mechanism's
# regression test, so including Lean here would flag the assertion instead of the hazard.
# `kill -0 $pid` (the
# liveness probe) is a signal flag, not a target, and is deliberately not matched.
! code_grep 'kill([[:space:]]+-[A-Za-z0-9]+)*[[:space:]]+(--[[:space:]]+)?(0|-[0-9]+)([^0-9]|$)' \
    'scripts/*.sh' 'packages/os/c/shim.c' 'recipes/*' \
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
# they assert the product's documented defaults (Linger/Session/WorldCode/Paths.lean). The match
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
# `lean_lib Verify` has no glob (Verify/Coverage.lean reads the built program), so
# `./lake build suites` is the only build of the suites suites, under Verify/ and each component's
# Suites/, and it builds only the import closure of Verify/Main.lean, the suites root: a module
# outside it is never built, and none of its suites can run. Walk that closure forwards
# over the import lines; each suite module but Coverage and lingertest's root, the shim smoke
# test, must be in it.
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
# Every registered suite but the opt-in remote-live and perf runs in the verifier: Verify.Main.suites
# names exactly the suites that scripts/verify.sh passes to `suites --suites`, read from those
# commands with their continuation lines joined, each as `<suite>:<checks>` or
# `<suite>:<checks>:<skips>`.
registered="$(awk '/^def suites :/ { on = 1 } on { sub(/--.*/, ""); print } on && /[]][[:space:]]*$/ { exit }' Verify/Main.lean \
  | grep -oE '[(]"[^"]+"' | tr -d '("' | grep -vxE 'remote-live|perf' | sort)"
verified="$(awk '
  { cmd = cmd $0 }
  /\\$/ { sub(/\\$/, " ", cmd); next }
  cmd ~ /^[.]\/[.]lake\/build\/bin\/suites --suites[[:space:]]/ {
    sub(/^[.]\/[.]lake\/build\/bin\/suites --suites[[:space:]]+/, "", cmd)
    sub(/[[:space:]]*[|][|].*/, "", cmd)
    n = split(cmd, w, " ")
    for (k = 1; k <= n; k++) { name = w[k]; sub(/:.*$/, "", name); print name } }
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

# A module's role is the first component of its name that is `CoreSpec`, `CoreCode`,
# `WorldSpec` or `WorldCode`, and the audit holds each role to its rules; any other module is
# tooling, held to none of them, which no program module can import. So each module of a
# component or a package has its role right below the component or the package's root, or is a
# proof, a test, a suite or a package's solution, and no module of the program is tooling by a
# misplaced name.
layout_bad="$( { git ls-files -- 'Linger/*.lean' | awk -F/ '{ print $3 "\t" $0 }'
    git ls-files -- 'packages/*/*/*.lean' | awk -F/ '{ print $4 "\t" $0 }'; } \
  | awk -F'\t' '$1 !~ /^(CoreSpec|CoreCode|WorldSpec|WorldCode|Proofs|Tests|Suites)([.]lean)?$/ \
      && $1 != "Solution.lean" { print "  " $2 }')"
[ -z "$layout_bad" ] || {
  printf '%s\n' "$layout_bad" >&2
  fail "a module has no role below its component: name it <component>/<role>/..., or move it under Proofs/, Tests/ or Suites/"; }

# Every declaration name cited in backticks must resolve to a declaration, in every tracked
# `.lean` file, comments included. This is gated rather than reviewed because reviewing it
# produced a FALSE CLEAN: a one-off check grepped each name with
# `git grep -w`, which matches prose and comments, so `scrollbackAnsi_le`, which a document
# and two code comments named and nothing then declared, satisfied it. A doc that promises a
# theorem is unfalsifiable until something looks for the declaration, so this looks for
# `theorem|lemma|def|abbrev`.
#
# Basenames, because a citation is written unqualified while the declaration sits in a
# namespace; a qualified citation such as `Wire.decode_encode_chunked` is checked by its
# basename too. CamelCase names (types, structures) and file/section names are skipped:
# the target here is the `snake_case` claim names, which is what a reader would try to
# look up. Two lists hold names cited but not declared in Lean here: claims a comment states
# are absent, which must stay undeclared, and names from C, the Lean toolchain or GitHub,
# plus one lemma-name prefix. Every listed name must still be cited, so an extraction that
# finds nothing fails too.
cite_absent='mmap_id_gridAnsi sb_csiDispatch_any load_legacy_save save_no_legacy'
cite_foreign="lean_chmod lean_io_process_get_pid pid_t tty_do_resize close_range \
  native_decide lean_exe workflow_dispatch org_ foldl_append"
cite_scan() {                                # file:line:basename per backticked snake_case name
  git grep -noE '`[A-Za-z][A-Za-z0-9_.]*`' -- '*.lean' \
  | awk -F: '{ name = $3; gsub(/`/, "", name); base = name; sub(/.*[.]/, "", base)
      if (name !~ /[.](md|lean|sh)$/ && ((name ~ /^[a-z]/ && name ~ /_/) || base ~ /^[a-z][A-Za-z0-9]*_/))
        print $1 ":" $2 ":" base }'
}
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
[ "$(printf '%s\n' "$emitter_claims" | sed -n 's/^#rows //p')" = 31 ] \
  || fail "Verify/Coverage.lean's emitter table no longer reads as its 31 rows"
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

# The CI matrix. macOS runs only when `scripts/ci-runners.sh` asks for it, for the cost
# reason that script states, and the decision reaches the matrix through a `fromJSON`
# job output, which actionlint does NOT check — verified by mistyping it deliberately,
# which actionlint accepted. Two ways that goes wrong silently: someone simplifies the
# matrix to ubuntu only and macOS is never checked again, or drops the schedule and it
# never runs. Neither is a Lean property, so this is the same species of oracle as
# SHIM_CAP.
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
  || fail "$ci_yml: no workflow_dispatch — a commit touching packages/os/c/shim.c needs a way to ask for macOS without waiting for the monthly run"
# Suite fixed-sleep ratchet: a wait for something to appear polls its readiness
# signal (`waitFor`, `Client.awaitText`); the sleeps left are negative-assertion
# windows, fixture pacing, poll intervals and waits not yet converted. Both ratchets count
# the suites suites, under Verify/ and each component's Suites/, but not lingertest's shim smoke
# test, which they never counted.
# The quiet suite adds three negative-assertion windows: a daemon must stay asleep, and a poll
# with no timeout must keep waiting, and only time passing without an event can show either.
SUITE_SLEEP_CAP=37
es_n="$(code_count 'IO[.]sleep([^[:alnum:]_]|$)' 'Verify/*' 'Linger/*/Suites/*' \
  ':!Linger/Os/Suites/Shim.lean')"
[ "$es_n" -le "$SUITE_SLEEP_CAP" ] \
  || fail "suite fixed sleeps grew to $es_n (cap $SUITE_SLEEP_CAP); poll a readiness signal with waitFor"
# Fixed drain windows: drain/drainStr with a literal deadline read for that long
# whatever arrives. Positive waits poll with Client.awaitText/awaitNeedle, and a read to the
# end of a client that exits drains under `hangMs`, which returns at its end of file; the
# windows left are negative assertions, discards, stream sync points and positive reads not
# yet converted.
SUITE_DRAIN_CAP=43
ed_n="$(code_count '(^|[^[:alnum:]_.])drain(Str)?[[:space:]]+[^[:space:]]+[[:space:]]+[0-9]' 'Verify/*' \
  'Linger/*/Suites/*' ':!Linger/Os/Suites/Shim.lean')"
[ "$ed_n" -le "$SUITE_DRAIN_CAP" ] \
  || fail "suite fixed drain windows grew to $ed_n (cap $SUITE_DRAIN_CAP); wait for a positive condition with awaitText"

# The program's timers, each with what bounds it. Work follows events: a wakeup no event paid
# for belongs only on this list, and every wait on it is bounded and says what it missed, so a
# loaded host slows linger down without hanging it. A new sleep, nap or poll joins the list with
# its bound, or waits on an event instead. Every bounded wait naps as `Os.Wait.next` decides
# (`wait_ends`); the one sleep with no deadline is `pause`, named below. The checks of the world
# claims are no part of the program: they run apart from it, and its modules never import them.
#   App/WorldCode: a started daemon's report, every 10 ms for at most startWaitMs (30 s), then, once
#     the daemon took the request's ticket, every 10 ms while it lives (`pause`); a spawned
#     daemon's socket, every 30 ms for socketWaitFloorMs (3 s), then while that daemon lives,
#     up to socketWaitCapMs (30 s); remote listings, every 5 ms for at most
#     remoteQueryTimeoutMs (3 s); `send -` wakes only for input, replies and closes; `wait`
#     looks at a held name every 20 ms for at most heldNameMs (8 s) from the look that first
#     found it so, as `Wait.decide` says, and `kill` for its release as long.
#   Import/WorldCode: tmux's configuration and a pane archive, every 10 ms for at most 1 s and 5 s.
#   packages/os, Os/WorldCode: `nap` and `pause`, the only sleeps; a full write's wait for its
#     descriptor to take more (`writeAll`), with no deadline, on its reader, as a blocking
#     write's; Os/WorldCode/Command: a stopped command's output, every 5 ms for its grace period.
#   Selector/WorldCode: the picker, every 50 ms while it is open, for keys, the escape deadline and
#     a listing each second.
#   Session/WorldCode/Client: a one-shot reply, until replySilenceMs (10 s) of silence; a saved view
#     and an attach, every 200 ms for a resize, and an attach's title sample once a second.
#   Session/WorldCode/Daemon: a write waiting on the disk says so after a second, looking every
#     10 ms; the loop, until an event or a deadline; the final drain, at most drainTimeoutMs
#     (3 s); stopping a program, in 10 ms steps for at most 2 s, and the rest of its session, in
#     50 ms steps for at most 2 s; a held startup claim, every 10 ms for at most claimWaitMs (1 s).
#   Session/WorldCode/Inventory: an info reply, until the request's deadline: replySilenceMs (10 s)
#     for the one an attach asks for its daemon's protocol level.
timers="$(code_grep '(IO[.]sleep [^[:space:]]|← poll [^[:space:]]|(^|[[:space:].])nap [^[:space:]]|(^|[[:space:]])pause [0-9])' 'Linger/*.lean' \
    ':!Linger/*/Suites/*' ':!Linger/*/Proofs/*' ':!Linger/*/Tests/*' ':!Linger/*/WorldCode/Checks.lean' \
    'packages/*.lean' ':!packages/*/Suites/*' ':!packages/*/Proofs/*' ':!packages/*/Tests/*' \
    ':!packages/*/WorldCode/Checks.lean' \
  | sed -E 's/^([^:]+):[0-9]+:[[:space:]]*/\1: /')"
expected_timers='Linger/App/WorldCode.lean: unless ← nap deadline 10 do
Linger/App/WorldCode.lean: pause 10
Linger/App/WorldCode.lean: unless ← nap (start + socketWaitCapMs) 30 do
Linger/App/WorldCode.lean: unless ← nap deadline 5 do
Linger/App/WorldCode.lean: let revs ← poll #[stdinFd, fd] #[POLLIN, POLLIN] (-1)
Linger/App/WorldCode.lean: discard <| nap (first + Wait.heldNameMs) 20
Linger/App/WorldCode.lean: unless ← nap deadline 20 do
Linger/Import/WorldCode.lean: unless ← Os.Shell.nap deadline 10 do
Linger/Import/WorldCode.lean: unless ← Os.Shell.nap deadline 10 do
Linger/Selector/WorldCode.lean: let ready ← poll fds events 50
Linger/Session/WorldCode/Client.lean: let revs ← poll #[fd] #[POLLIN] silenceMs
Linger/Session/WorldCode/Client.lean: let ready ← poll fds events 200
Linger/Session/WorldCode/Client.lean: let revs ← poll #[stdinFd, fd] #[POLLIN, POLLIN] 200
Linger/Session/WorldCode/Daemon.lean: unless ← nap tellAt 10 do
Linger/Session/WorldCode/Daemon.lean: unless ← nap deadline step do
Linger/Session/WorldCode/Daemon.lean: let revs ← poll fds evts timeout
Linger/Session/WorldCode/Daemon.lean: let revs ← poll fds (Array.replicate fds.size POLLOUT) (Int32.ofNat (min 100 (deadline - now)))
Linger/Session/WorldCode/Daemon.lean: nap deadline 10
Linger/Session/WorldCode/Inventory.lean: let revs ← poll #[fd] #[POLLIN] (Int32.ofNat (min 100 remaining))
packages/os/Os/WorldCode.lean: let _ ← poll #[fd] #[POLLOUT] (-1)
packages/os/Os/WorldCode.lean: def nap (deadline step : Nat) : IO Bool := do
packages/os/Os/WorldCode.lean: IO.sleep ms.toUInt32
packages/os/Os/WorldCode.lean: def pause (ms : Nat) : IO Unit := IO.sleep ms.toUInt32
packages/os/Os/WorldCode/Command.lean: unless ← Os.Shell.nap deadline 5 do'
[ "$timers" = "$expected_timers" ] \
  || fail "the program's timers changed; name each here with its bound, or wait on an event instead:
$timers"
# What the program writes to a terminal: every use of standard output's descriptor, each raw
# write with whose bytes it writes (the ties above and below pin each argument). Linger's own
# bytes are printers `writes_clean` (Challenge part 8) proves clean; the session's own are its
# output and the repaint of its screen. A new write joins this list, and the headline when its
# bytes are linger's own.
#   App/WorldCode: the handback after a remote command (`leaveAnsi`); `ls` (`terminalListing`), at
#     the terminal's width;
#     `capture` of a saved session (`screenText` or `history`, as `cmdRead`'s caller passes,
#     rendered at the plan's `render` step and written at its `write` step, tied above).
#   Import/WorldCode: `tmux ls` (`terminalListing`).
#   Selector/WorldCode: taking the terminal (`enterAnsi`) and naming it, the window size, the frame
#     (`frame`, the first, after a resize and on the refresh key, or the `update` between the
#     `frameRows` of two frames of one size), giving the terminal back (`exitAnsi`) and clearing
#     its title.
#   Session/WorldCode/Client: a one-shot reply, which is the daemon's `infoText`, `screenText` or
#     `history` in frames; a saved view's repaint (the session's), title (`Title.update`) and
#     handback; an attach's output (the session's), title and handback.
term_writes="$(code_grep 'stdoutFd' 'Linger/*.lean' \
    ':!Linger/*/Suites/*' ':!Linger/*/Proofs/*' ':!Linger/*/Tests/*' \
    'packages/*.lean' ':!packages/*/Suites/*' ':!packages/*/Proofs/*' ':!packages/*/Tests/*' \
  | sed -E 's/^([^:]+):[0-9]+:[[:space:]]*/\1: /')"
expected_term_writes='Linger/App/WorldCode.lean: writeAll stdoutFd (ByteArray.mk Terminal.Render.leaveAnsi.toArray)
Linger/App/WorldCode.lean: let (cols, _) ← winsizeGet stdoutFd
Linger/App/WorldCode.lean: writeAll stdoutFd
Linger/App/WorldCode.lean: writeAll stdoutFd (ByteArray.mk bytes.toArray)
Linger/Import/WorldCode.lean: Os.Shell.writeAll Os.Shell.stdoutFd
Linger/Selector/WorldCode.lean: writeAll stdoutFd (ByteArray.mk Linger.Selector.Picker.enterAnsi.toArray)
Linger/Selector/WorldCode.lean: writeAll stdoutFd (ByteArray.mk (Terminal.Title.ansi "linger").toArray)
Linger/Selector/WorldCode.lean: let current ← winsizeGet stdoutFd
Linger/Selector/WorldCode.lean: writeAll stdoutFd (ByteArray.mk frame.toArray)
Linger/Selector/WorldCode.lean: writeAll stdoutFd (ByteArray.mk Linger.Selector.Picker.exitAnsi.toArray)
Linger/Selector/WorldCode.lean: writeAll stdoutFd (ByteArray.mk (Terminal.Title.ansi "").toArray)
Linger/Session/WorldCode/Client.lean: writeAll stdoutFd (ByteArray.mk payload.toArray)
Linger/Session/WorldCode/Client.lean: writeAll stdoutFd (ByteArray.mk bytes.toArray)
Linger/Session/WorldCode/Client.lean: writeAll stdoutFd (ByteArray.mk (Terminal.Title.update view title).toArray)
Linger/Session/WorldCode/Client.lean: writeAll stdoutFd (ByteArray.mk Terminal.Render.leaveAnsi.toArray)
Linger/Session/WorldCode/Client.lean: writeAll stdoutFd (ByteArray.mk payload.toArray)
Linger/Session/WorldCode/Client.lean: writeAll stdoutFd (ByteArray.mk bytes.toArray)
Linger/Session/WorldCode/Client.lean: writeAll stdoutFd (ByteArray.mk Terminal.Render.leaveAnsi.toArray)
packages/os/Os/WorldCode.lean: def stdoutFd : UInt32 := 1'
[ "$term_writes" = "$expected_term_writes" ] \
  || fail "the program's terminal writes changed; name each here with whose bytes it writes:
$term_writes"
tie='[|] [.]output payload [|] [.]infoReply payload => writeAll stdoutFd [(]ByteArray[.]mk payload[.]toArray[)]'
printf '%s\n' "$client_code" | CG_RE="(^|[[:space:]])$tie([[:space:]]|$)" awk "$CODE_AWK" >/dev/null \
  || fail "a one-shot reply is written other than as the daemon's frames: $tie"
# No other way to write bytes to standard output: no literal descriptor, and no stream write in
# the program, whose files `Os.Shell.replaceFile` writes. A stream write is a call on a value,
# `handle.write`; a match arm `| .write` names a step or a decision.
! code_grep '(writeAll|write) (Os[.]Shell[.])?[0-9]' 'Linger/*.lean' \
    ':!Linger/*/Suites/*' ':!Linger/*/Proofs/*' ':!Linger/*/Tests/*' \
  || fail "a write names a descriptor by number; use stdoutFd and list the write above"
! code_grep '[[:alnum:]_)][.]write[[:space:](]' 'Linger/*.lean' \
    ':!Linger/*/Suites/*' ':!Linger/*/Proofs/*' ':!Linger/*/Tests/*' \
  || fail "a stream write could reach standard output: write files through Os.Shell.replaceFile"
# One command table: help prints it and every usage error quotes its command's row, so no usage
# text is written anywhere else.
! code_grep '"usage: linger' Linger/App/WorldCode.lean \
  || fail "a usage error bypasses the command table (Commands.usageLine)"
printf '%s\n' "$(awk '{ $1 = $1; printf "%s ", $0 }' Linger/App/WorldCode.lean)" \
  | CG_RE='(^|[[:space:]])private def usage : String := Linger[.]App[.]Commands[.]helpText([[:space:]]|$)' \
    awk "$CODE_AWK" >/dev/null \
  || fail "help no longer prints the command table"
# Every one-shot request is given up after replySilenceMs of silence; only `wait` passes its own
# budget, its deadline's, or none when it has none, since it waits for a program to end.
printf '%s\n' "$(awk '{ $1 = $1; printf "%s ", $0 }' Linger/Session/WorldCode/Client.lean)" \
  | CG_RE='(^|[[:space:]])def oneShot [(]name : String[)] [(]m : Msg[)] [(]untilDone : Bool := true[)] [(]silenceMs : Int32 := replySilenceMs[)] : IO [(]Option Drained[)] := do([[:space:]]|$)' \
    awk "$CODE_AWK" >/dev/null \
  || fail "a one-shot request must default to the reply silence budget"
[ "$(code_count 'silenceMs := ' 'Linger/App/*.lean' 'Linger/Session/WorldCode/*.lean')" -eq 1 ] \
  || fail "only wait may choose a one-shot request's silence budget"

printf 'gates OK — purity, the OS and unsafe surfaces, the Vt friend set, the runtime ties, declaration citations, and the ratchets\n'
