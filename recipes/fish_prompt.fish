# Optional right prompt; merge the calls into an existing fish_right_prompt.
# With no right prompt, use this as ~/.config/fish/functions/fish_right_prompt.fish.
function fish_right_prompt
    set -l last_status $status
    command -q linger
    and command linger status 2>/dev/null
    return $last_status
end
