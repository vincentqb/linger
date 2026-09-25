# Fuzzy-pick a session with fzf and attach — local rows plus (with a
# ~/.config/linger/remotes file) remote ones tagged name@host; `linger
# attach` ssh-es for the latter. Names come from --porcelain so an
# empty list offers nothing to pick (no stray "no sessions" row).
# Drop the -r for a faster, local-only picker.
function lz --description 'pick a session and attach'
    set -l listing (linger ls -r --porcelain)
    or return $status
    set -l name (printf '%s\n' $listing | string replace -rf '^name\t([^\t]+)$' '$1' | fzf --no-multi)
    or return $status
    test (count $name) -eq 1; and test -n "$name"; or return 1
    linger attach "$name"
end
