# A status board for the sessions you are NOT looking at. Your
# terminal's tabs can title a session but can't report on one with no
# tab open — and that is exactly when the status column says something
# you don't already know. Park this in one small tab and it covers the
# gap a remote multiplexer's in-band window list would fill.
# Redraw is build-then-clear so the table doesn't flicker; ^C exits.
function lzs --description 'live status board for local + remote sessions' \
             --argument-names hosts secs
    test -n "$secs"; or set secs 5
    while true
        # No host arg expands away to a bare -r, so hosts come from
        # ~/.config/linger/remotes; `lzs a,b` overrides that, and
        # `lzs '' 2` keeps the file (linger drops empty host entries).
        set -l board (linger ls -r $hosts)
        clear
        printf '%s\n' $board
        sleep $secs
    end
end
