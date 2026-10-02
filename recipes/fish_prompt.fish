# Standard display: session · application title · attention; omit empty parts.
# This optional right prompt supplies only attention, after your existing context.
# Merge the calls last in an existing fish_right_prompt; leave fish_title alone.
# With no right prompt, use this as ~/.config/fish/functions/fish_right_prompt.fish.
function fish_right_prompt
    set -l last_status $status
    command -q linger
    and command linger status 2>/dev/null
    return $last_status
end
