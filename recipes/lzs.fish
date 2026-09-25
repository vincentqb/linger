# A status board for the sessions you are NOT looking at. Your
# terminal's tabs can title a session but can't report on one with no
# tab open — and that is exactly when the status column says something
# you don't already know. Park this in one small tab and it covers the
# gap a remote multiplexer's in-band window list would fill.
# Redraw is build-then-clear so the table doesn't flicker; ^C exits.
function lzs --description 'live status board for local + remote sessions' \
             --argument-names hosts secs
    if test (count $argv) -gt 2
        printf 'usage: lzs [HOSTS [SECS]]\n' >&2
        return 2
    end
    test -n "$secs"; or set secs 5
    if not string match -rq '^([0-9]+(\.[0-9]*)?|\.[0-9]+)$' -- "$secs"; or not test "$secs" -gt 0
        printf 'lzs: SECS must be a positive number\n' >&2
        return 2
    end
    test -n "$hosts"; or set hosts
    while true
        # No host arg expands away to a bare -r, so hosts come from
        # ~/.config/linger/remotes; `lzs a,b` overrides that, and
        # `lzs '' 2` keeps the file.
        set -l board (linger ls -r $hosts)
        or return $status
        clear; or return $status
        printf '%s\n' $board; or return $status
        sleep "$secs"; or return $status
    end
end
