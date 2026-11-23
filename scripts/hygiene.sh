#!/bin/sh
# Read-only source hygiene shared by local hooks and CI. Bash 3.2 (macOS) suffices:
# NUL-delimited Git records keep spaces, tabs and newlines in paths intact.
if [ -z "${BASH_VERSION:-}" ]; then
  exec bash "$0" "$@"
fi
set -euo pipefail
export LC_ALL=C

cd "$(git rev-parse --show-toplevel)"
inventory="$(mktemp "${TMPDIR:-/tmp}/linger-hygiene.XXXXXX")"
trap 'rm -f "$inventory"' EXIT
# Keep this outside a pipeline/process substitution: an inventory failure must fail.
git ls-files --stage -z > "$inventory"

failed=0
fail() {
  printf 'hygiene: %s: %s\n' "$file" "$1" >&2
  failed=1
}

# A challenge, linger's `Challenge.lean` or a package's, holds only its statements, the one part
# of it anything checks, so it holds no comment: no `--` and no `/-` outside its string and
# character literals. This reads Lean's literals byte by byte; the shell's quotes cannot hold a
# single quote, so the program spells it `q`.
challenge_awk='
BEGIN { q = "\047" }
function complain() {
  printf "hygiene: %s:%d: comment in a challenge, which holds only statements\n",
    ENVIRON["HYGIENE_FILE"], line
  bad = 1
}
# A byte an identifier may end with, so that a quote after it is a prime, not a character.
function ident(ch) { return ch ~ /[[:alnum:]_!?]/ || ch == q }
# Move to byte `to`, counting the lines passed.
function skip(to,    span) {
  span = substr(src, i + 1, to - i); line += gsub(/\n/, "", span); i = to; prev = " "
}
{ src = src $0 "\n" }
END {
  n = length(src); line = 1; prev = " "
  for (i = 1; i <= n; i++) {
    c = substr(src, i, 1)
    if (c == "\"") {                         # a string: a backslash escapes the next byte
      for (j = i + 1; j <= n && substr(src, j, 1) != "\""; j++) if (substr(src, j, 1) == "\\") j++
      skip(j); continue
    }
    if (c == "r" && !ident(prev) && match(substr(src, i + 1, 256), /^#*"/)) {
      stop = "\"" substr(src, i + 1, RLENGTH - 1)   # a raw string ends at a quote and its hashes
      k = index(substr(src, i + 1 + RLENGTH), stop)
      if (k > 0) { skip(i + RLENGTH + k + length(stop) - 1); continue }
    }
    if (c == q && !ident(prev)) {            # a character: one escape, or one UTF-8 character
      if (substr(src, i + 1, 1) == "\\") {
        k = index(substr(src, i + 3, 10), q); body = substr(src, i + 1, k + 1); j = i + 2 + k
      } else { k = index(substr(src, i + 2, 4), q); body = substr(src, i + 1, k); j = i + 1 + k }
      if (k > 0 && body !~ /\n/ &&
          (length(body) == 1 || body ~ /^\\/ || body !~ /[[:print:][:cntrl:]]/)) {
        skip(j); continue
      }
    }
    if (c == "-" && substr(src, i + 1, 1) == "-") {   # a line comment
      complain(); skip(i + index(substr(src, i), "\n") - 2); continue
    }
    if (c == "/" && substr(src, i + 1, 1) == "-") {   # a block comment, which nests
      complain(); depth = 1
      for (j = i + 2; j <= n && depth > 0; j++)
        if (substr(src, j, 2) == "/-") { depth++; j++ }
        else if (substr(src, j, 2) == "-/") { depth--; j++ }
      skip(j - 1); continue
    }
    if (c == "\n") line++
    prev = c
  }
  exit bad
}'

while IFS= read -r -d '' entry; do
  metadata="${entry%%$'\t'*}"
  file="${entry#*$'\t'}"
  mode="${metadata%% *}"
  if [[ "${metadata##* }" != 0 ]]; then
    fail "unmerged index entry"
    continue
  fi
  case "$mode" in
    120000|160000) continue ;; # Symlinks and submodules are not source file contents.
    100644|100755) ;;
    *) fail "unsupported Git file mode"; continue ;;
  esac
  if [[ ! -f "./$file" || -L "./$file" ]]; then
    fail "tracked path is not a regular file"
    continue
  fi

  bytes="$(wc -c < "./$file")"
  if [[ "$bytes" -gt $((256 * 1024)) ]]; then
    fail "file exceeds 256 KiB"
    continue
  fi
  # read succeeds only on a NUL byte. Binary files retain the size check but
  # not text or shebang checks; no filename-extension allowlist can hide source.
  if IFS= read -r -d '' content < "./$file"; then
    continue
  fi
  if [[ "$mode" == 100755 && "$content" != '#!'* ]]; then
    fail "executable without shebang"
  elif [[ "$mode" == 100644 && "$content" == '#!'* ]]; then
    fail "shebang without executable mode"
  fi
  # The challenge library writes and rereads each owned.lock itself, without a final newline:
  # its layout is the library's, not this repository's to correct.
  if [[ -n "$content" && "$content" != *$'\n' && "${file##*/}" != owned.lock ]]; then
    fail "missing final newline"
  fi
  if [[ "$content" == *$'\n\n' ]]; then
    fail "extra trailing blank lines"
  fi
  if ! HYGIENE_FILE="$file" awk '
    function complain(message) {
      printf "hygiene: %s:%d: %s\n", ENVIRON["HYGIENE_FILE"], NR, message
      bad = 1
    }
    /\r/ { complain("carriage return") }
    /[[:space:]]$/ {
      if (!(ENVIRON["HYGIENE_FILE"] ~ /\.[mM][dD]$/ && /[^[:space:]]  $/))
        complain("trailing whitespace")
    }
    # Check the three conflict-marker forms, regardless of merge state.
    /^(<<<<<<<|=======|>>>>>>>)([[:space:]]|$)/ {
      complain("conflict marker")
    }
    END { exit bad }
  ' < "./$file" >&2; then
    failed=1
  fi
  if [[ "${file##*/}" == Challenge.lean ]] \
      && ! HYGIENE_FILE="$file" awk "$challenge_awk" < "./$file" >&2; then
    failed=1
  fi
done < "$inventory"

exit "$failed"
