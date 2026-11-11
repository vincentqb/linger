#!/bin/sh
# Shared by `./lake lint`, pre-commit and the full verifier.
set -e
cd "$(dirname "$0")/.."

sh scripts/hygiene.sh
sh scripts/gates.sh
pre-commit validate-config

if command -v actionlint > /dev/null; then
  actionlint -shellcheck="" -pyflakes=""
else
  printf 'actionlint absent; workflow validation runs in CI — see AGENTS.md\n'
fi

if command -v lean-fmt > /dev/null; then
  # lean-fmt loads the Lake workspace, and Lake runs git in .lake/packages: a git hook's
  # GIT_DIR or GIT_INDEX_FILE would aim those commands at this repository.
  unset GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE
  # Private logs: concurrent checkouts lint at the same time.
  logs="$(mktemp -d "${TMPDIR:-/tmp}/linger-lint.XXXXXX")"
  trap 'rm -r "$logs"' EXIT
  lean-fmt format --check > "$logs/fmt.log" 2>&1 \
    || { cat "$logs/fmt.log" >&2; exit 1; }
  printf 'layout: %s\n' "$(head -1 "$logs/fmt.log")"
  lean-fmt check > "$logs/lint.log" 2>&1 \
    || { cat "$logs/lint.log" >&2; exit 1; }
  # Each package under packages/ is a workspace of its own to the formatter.
  for pkg in packages/*/; do
    [ -d "$pkg" ] || continue
    (cd "$pkg" && lean-fmt format --check && lean-fmt check) > "$logs/package.log" 2>&1 \
      || { cat "$logs/package.log" >&2; exit 1; }
    printf 'layout and lint of %s: OK\n' "${pkg%/}"
  done
  printf 'semantic lint: OK\n'
elif [ "${GITHUB_ACTIONS-}" = true ] && [ "${RUNNER_OS-}" = Linux ]; then
  printf 'the pinned formatter is missing from Linux CI\n' >&2
  exit 1
else
  printf 'lean-fmt absent; layout and semantic lint unchecked — see AGENTS.md\n'
fi
