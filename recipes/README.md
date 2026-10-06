# Configuration recipes

[Install linger](../README.md) first. Merge these examples into your existing
configuration. Terminals need `linger` on PATH or an absolute executable path.

| Use | Example |
|---|---|
| Ghostty 1.2+ | [ghostty_config](ghostty_config) |
| kitty | [kitty.conf](kitty.conf) |
| WezTerm | [wezterm.lua](wezterm.lua) |
| Fish attention counts | [fish_prompt.fish](fish_prompt.fish) |
| SSH keepalives | [ssh_config](ssh_config) |

For a new Fish right prompt, save the example as
`~/.config/fish/functions/fish_right_prompt.fish`. For an existing prompt,
merge its calls at the end, preserving `$status` and your title hook.

Run `linger help` for session commands and `linger tmux help` for save interchange.
