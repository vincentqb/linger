#!/bin/sh
# Collect the whole status board before clearing it; Ctrl-C exits.
if [ "$#" -ne 0 ]; then
    printf 'usage: lzs\n' >&2
    exit 2
fi
while :; do
    board=$(linger ls -r) || exit "$?"
    clear || exit "$?"
    printf '%s\n' "$board" || exit "$?"
    sleep 5 || exit "$?"
done
