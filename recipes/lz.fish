# Fuzzy-pick a session with fzf and attach — local rows plus (with a
# ~/.config/linger/remotes file) remote ones tagged name@host; `linger
# attach` ssh-es for the latter. Names come from --porcelain so an
# empty list offers nothing to pick (no stray "no sessions" row).
# Drop the -r for a faster, local-only picker.
# `lz` attaches once; `lz --loop [NAME[@HOST]]` optionally starts attached
# and returns to the picker after attach exits, including on failure.
# Esc (or ctrl-c) exits with fzf's status; empty or multiple results also exit.
function lz --description 'pick a session and attach; --loop picks again after attach exits'
    set -l loop 0
    set -l name
    set -l picker_args --no-multi
    if test (count $argv) -gt 0
        if test "$argv[1]" != --loop; or test (count $argv) -gt 2; or contains -- '' $argv
            printf 'usage: lz [--loop [NAME[@HOST]]]\n' >&2
            return 2
        end
        set loop 1
        set name $argv[2]
        set -a picker_args --prompt 'session> '
    end
    while true
        if test -n "$name"
            linger attach "$name"
            set -l attach_status $status
            test $loop -eq 1; or return $attach_status
        end
        set -l listing (linger ls -r --porcelain)
        or return $status
        set name (printf '%s\n' $listing | string replace -rf '^name\t([^\t]+)$' '$1' | fzf $picker_args)
        or return $status
        test (count $name) -eq 1; and test -n "$name"; or return 1
    end
end
