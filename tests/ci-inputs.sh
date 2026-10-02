#!/bin/sh
# Identity of a completed verification, not a build-artifact cache key.
# Only work records are excluded; source gates still check their citations.
# Unknown file kinds are inputs. Paths and modes matter as well as content.
set -eu
export LC_ALL=C

set -- . ':(exclude)AGENTS.md' ':(exclude)SCRATCHPAD.md' \
  ':(glob,exclude)specs/**/*.md'

# The index supplies object IDs only after proving it matches the working inputs.
# Never issue a key for an untracked source, an unstaged edit or an empty census.
git diff --quiet -- "$@" || {
  echo 'verification inputs: unstaged changes' >&2
  exit 1
}
untracked="$(git ls-files --others --exclude-standard -- "$@")"
[ -z "$untracked" ] || {
  echo 'verification inputs: untracked files' >&2
  exit 1
}
inputs="$(git ls-files --stage -- "$@")"
[ -n "$inputs" ] || {
  echo 'verification inputs: empty inventory' >&2
  exit 1
}

# Image identity is part of the digest itself, so a hosted image update cannot
# borrow a success from its predecessor. E2E.Ci changes each field independently.
printf '%s\n' "${RUNNER_OS-}" "${RUNNER_ARCH-}" "${ImageOS-}" "${ImageVersion-}" \
  "$inputs" | git hash-object --stdin
