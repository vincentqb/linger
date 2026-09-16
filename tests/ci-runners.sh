#!/bin/sh
# Which runners the full gate needs, as a JSON array for a GitHub matrix.
#
#   sh tests/ci-runners.sh <event_name> <ref>   ->   ["ubuntu-latest", ...]
#
# THE THIRD DELIBERATE NON-LEAN FILE, and the reason is the cost this exists to
# control: `.github/workflows/ci.yml`'s `gates` job compiles NOTHING, which is what
# makes it cheap, so its decision cannot be `./lake exe e2e …` without putting a
# Lean build back into the cheap job. Shell is what a workflow step can call for
# free. It lives here rather than inlined in the YAML so `E2E/Ci.lean` can DRIVE it
# — an inline `case` can only be tested by a copy of itself, and this repo's rule is
# that a suite asserts against the code's own definitions, never a copy.
#
# ubuntu always: every push gets the whole gate. macOS costs several times more per
# billed minute (the arithmetic is in the ci.yml header), so it runs only when there is
# something new for it to learn:
#
#   workflow_dispatch  always      — someone asked, e.g. after touching c/shim.c
#   push to any tag    always      — the workflow only triggers on `v*`, but this
#                                    script does not check the shape, so a broadened
#                                    trigger gets macOS without a change here
#   schedule           if commits  — rebuilding an unchanged tree re-learns last
#                                    week's answer at the expensive rate
#   push / PR          never
#
# WINDOW=8 days against a 7-day cron on purpose: the overlap means a cron GitHub
# delays cannot open a gap where a commit is never macOS-tested. It costs at most
# one redundant run, and only for a commit landing on the boundary. Keep the two in
# step — a monthly cron with an 8-day window would skip almost every month.
set -eu

WINDOW='8 days ago'

event="${1?usage: ci-runners.sh <event_name> <ref>}"
ref="${2?usage: ci-runners.sh <event_name> <ref>}"

macos=no
case "$event" in
  workflow_dispatch)
    macos=yes
    ;;
  schedule)
    # `git log --since` in the current repository. Quoting matters and has bitten:
    # an unquoted `--since=8 days ago` makes git read `days` as a revision and fail,
    # which — because the failure is empty output — would silently mean "no commits"
    # and macOS would never run again. `E2E/Ci.lean` drives this path against real
    # temporary repositories for exactly that reason.
    if [ -n "$(git log --since="$WINDOW" --format=%H)" ]; then
      macos=yes
    fi
    ;;
  push)
    case "$ref" in
      refs/tags/*) macos=yes ;;
    esac
    ;;
esac

if [ "$macos" = yes ]; then
  printf '["ubuntu-latest", "macos-latest"]\n'
else
  printf '["ubuntu-latest"]\n'
fi
