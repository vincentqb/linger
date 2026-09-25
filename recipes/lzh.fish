# Turn ctrl-\ into a session switcher. linger has no prefix key, so a
# detach normally drops you at a shell; this wraps attach in a loop, so
# detaching pops the picker and you land in the next session instead.
# It crosses hosts — rows are name@host.
# Esc (or ctrl-c) exits with fzf's status; empty or multiple results also exit.
# `lzh work` starts attached; bare `lzh` starts at the picker.
function lzh --description 'attach; detach pops a picker instead of a shell'
    if test (count $argv) -gt 1
        printf 'usage: lzh [NAME[@HOST]]\n' >&2
        return 2
    end
    set -l name $argv[1]
    while true
        test -n "$name"; and linger attach "$name"
        # Drop the -r for local-only (skips one ssh round per host).
        set -l listing (linger ls -r --porcelain)
        or return $status
        set name (printf '%s\n' $listing | string replace -rf '^name\t([^\t]+)$' '$1' \
                  | fzf --no-multi --prompt 'session> ')
        or return $status
        test (count $name) -eq 1; and test -n "$name"; or return 1
    end
end
