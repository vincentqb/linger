#!/bin/sh
# Forward-written session state, run by the PreCompact hook.
#
# Compaction keeps what the summarizer judged relevant and drops the rest, so the
# nuance it eats is exactly what is NOT already on disk. Everything durable here
# is already committed or in SCRATCHPAD.md/specs/ — what a compaction genuinely
# loses is the *volatile* part: which commit we were on, what was uncommitted, and
# which round was in flight. This writes those three, deterministically, with no
# model involvement, so a post-compaction agent re-grounds against facts rather
# than against a summary of facts.
#
# Cheap by design: no network, no writes outside .claude/, nothing destructive.
# AGENTS.md is re-injected after a compaction on its own (CLAUDE.md @-includes
# it), so the spec pointers do not need repeating here — only what AGENTS.md
# cannot know.
# No `set -e`: this is a convenience snapshot, and a hook that fails is worse
# than a hook that is missing — it interrupts the thing it was meant to help.
cd "$(dirname "$0")/.." || exit 0
OUT=.claude/last-compact-state.md

{
  printf '# Session state at the last compaction\n\n'
  printf 'Written by `.claude/precompact-snapshot.sh` (PreCompact hook). Facts, not a\n'
  printf 'summary. Re-ground against `AGENTS.md` item 1 and the active spec, per\n'
  printf 'AGENTS.md; this file only carries what those two cannot know.\n\n'

  printf '## HEAD\n\n```\n'
  git --no-pager log --no-color --oneline -5 2>/dev/null || printf '(no git)\n'
  printf '```\n\n'

  printf '## Uncommitted at that moment\n\n```\n'
  if [ -n "$(git --no-pager status --porcelain 2>/dev/null)" ]; then
    git -c color.status=false --no-pager status --short 2>/dev/null
  else
    printf '(clean)\n'
  fi
  printf '```\n\n'

  printf '## Last worklog heading (the round that was in flight)\n\n```\n'
  grep -n '^## ' SCRATCHPAD.md 2>/dev/null | tail -3 || printf '(none)\n'
  printf '```\n\n'

  printf '## Live specs\n\n```\n'
  ls specs/*.md 2>/dev/null || printf '(none)\n'
  printf '```\n'
} > "$OUT"

printf 'precompact: wrote %s\n' "$OUT"
exit 0
