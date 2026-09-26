#!/bin/sh
# Reconnect after SSH's transport-failure status; detach and normal exit stop.
# A remote command exiting 255 is indistinguishable from a transport failure.
if [ "$#" -ne 1 ] || [ -z "$1" ]; then
    printf 'usage: lza NAME[@HOST]\n' >&2
    exit 2
fi
while :; do
    linger attach "$1"
    attached=$?
    [ "$attached" -eq 255 ] || exit "$attached"
    sleep 2 || exit "$?"
done
