# Turn ctrl-\ into a session switcher. linger has no prefix key, so a
# detach normally drops you at a shell; this wraps attach in a loop, so
# detaching pops the picker and you land in the next session instead.
# It crosses hosts — rows are name@host.
# Esc (or ctrl-c) at the picker exits: fzf's nonzero status ends the loop.
# `lzh work` starts attached; bare `lzh` starts at the picker.
function lzh --description 'attach; detach pops a picker instead of a shell'
    set -l name $argv[1]
    while true
        test -n "$name"; and linger attach $name
        # Drop the -r for local-only (skips one ssh round per host).
        set name (linger ls -r --porcelain \
                  | awk -F '\t' '$1=="name"{print $2}' | fzf --prompt 'session> ')
        or break
    end
end
