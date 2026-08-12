# Fuzzy-pick a session with fzf and attach — local rows plus (with a
# ~/.config/lzmx/remotes file) remote ones tagged name@host; `lzmx
# attach` ssh-es for the latter. Names come from --porcelain so an
# empty list offers nothing to pick (no stray "no sessions" row).
# Drop the -r for a faster, local-only picker.
function lz --description 'pick a session and attach'
    set -l name (lzmx ls -r --porcelain | awk -F '\t' '$1=="name"{print $2}' | fzf)
    and lzmx attach $name
end
