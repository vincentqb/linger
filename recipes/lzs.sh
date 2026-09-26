#!/bin/sh
# Collect the whole status board before clearing it; Ctrl-C exits.
if [ "$#" -gt 2 ]; then
    printf 'usage: lzs [HOSTS [SECS]]\n' >&2
    exit 2
fi
hosts=${1-}
secs=${2:-5}
# Digits, at most one decimal point, and at least one nonzero digit.
case "$secs" in
    *[!0-9.]*|*.*.*) valid=false ;;
    *[1-9]*) valid=true ;;
    *) valid=false ;;
esac
if [ "$valid" = false ]; then
    printf 'lzs: SECS must be a positive number\n' >&2
    exit 2
fi
set -- ls -r
# Empty HOSTS retains the configured remote list.
if [ -n "$hosts" ]; then set -- "$@" "$hosts"; fi
while :; do
    board=$(linger "$@") || exit "$?"
    clear || exit "$?"
    printf '%s\n' "$board" || exit "$?"
    sleep "$secs" || exit "$?"
done
