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
  # This already-large append-only history passed the former added-files-only
  # size hook. Preserve that exception, but keep every text check below.
  if [[ "$file" != SCRATCHPAD.md && "$bytes" -gt $((256 * 1024)) ]]; then
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
  if [[ -n "$content" && "$content" != *$'\n' ]]; then
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
    # The immutable history contains standalone diff3 base labels.
    # Check the three conflict-marker forms, regardless of merge state.
    /^(<<<<<<<|=======|>>>>>>>)([[:space:]]|$)/ {
      complain("conflict marker")
    }
    END { exit bad }
  ' < "./$file" >&2; then
    failed=1
  fi
done < "$inventory"

exit "$failed"
