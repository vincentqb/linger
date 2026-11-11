#!/bin/sh
# Which runners the full gate needs, as a JSON array for a GitHub matrix.
#
#   sh scripts/ci-runners.sh <event_name> <ref> [<base>]   ->   ["ubuntu-latest", ...]
#
# A DELIBERATE NON-LEAN FILE, and the reason is the cost this exists to
# control: `.github/workflows/ci.yml`'s `gates` job compiles NOTHING, which is what
# makes it cheap, so its decision cannot be `./lake exe suites …` without putting a
# Lean build back into the cheap job. Shell is what a workflow step can call for
# free. It lives here rather than inlined in the YAML so `Verify/Ci.lean` can DRIVE it
# — an inline `case` can only be tested by a copy of itself, and this repo's rule is
# that a suite asserts against the code's own definitions, never a copy.
#
# The workflow runs on its monthly schedule and on manual dispatch. macOS costs several
# times more per billed minute (measurements are in git history), so it runs only when
# there is something new for it to learn:
#
#   workflow_dispatch  both        — someone asked, e.g. after touching packages/os/c/shim.c
#   schedule           both if the last WINDOW has commits, otherwise none (`[]`): the
#                      workflow then skips every check, because rebuilding an unchanged
#                      tree re-learns last month's answer
#   push to any tag    both        — no longer a trigger; kept so a restored trigger
#                                    behaves as before without a change here
#   push / PR          ubuntu, and macOS too if the diff from <base> to HEAD touches
#                      packages/os/c/shim.c or ./lake, or if <base> is empty, all zeros or not a fetched
#                      commit (a new branch, a force push); no longer triggers either
#
# WINDOW=32 days against a cron on the 1st of each month on purpose: the longest gap
# between runs is 31 days, and the extra day means a cron GitHub delays cannot open a
# gap where a commit is never tested. It costs at most one redundant run, and only for
# a commit landing on the boundary. Keep the two in step.
set -eu

WINDOW='32 days ago'

event="${1?usage: ci-runners.sh <event_name> <ref> [<base>]}"
ref="${2?usage: ci-runners.sh <event_name> <ref> [<base>]}"
base="${3-}"

run=yes
macos=no
case "$event" in
  workflow_dispatch)
    macos=yes
    ;;
  schedule)
    # Keep the assignment outside `if`: set -e must propagate a failed history
    # lookup, rather than treating its empty output as "no commits".
    # Verify.Ci drives recent, stale and unreadable histories against this script.
    commits="$(git log --since="$WINDOW" --format=%H)"
    if [ -n "$commits" ]; then
      macos=yes
    else
      run=no
    fi
    ;;
  push | pull_request)
    case "$ref" in
      refs/tags/*) macos=yes ;;
      *)
        if [ -z "$base" ] || [ "$base" = 0000000000000000000000000000000000000000 ] \
          || ! git cat-file -e "$base^{commit}" 2> /dev/null; then
          macos=yes
        else
          # Outside `if`, so set -e propagates a failed diff.
          changed="$(git diff --name-only "$base" HEAD -- packages/os/c/shim.c lake)"
          if [ -n "$changed" ]; then
            macos=yes
          fi
        fi
        ;;
    esac
    ;;
esac

if [ "$run" = no ]; then
  printf '[]\n'
elif [ "$macos" = yes ]; then
  printf '["ubuntu-latest", "macos-latest"]\n'
else
  printf '["ubuntu-latest"]\n'
fi
