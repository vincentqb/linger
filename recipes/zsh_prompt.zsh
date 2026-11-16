# Standard display: session · application title · attention; omit empty parts.
# This optional right prompt supplies only attention, after your existing context.
# Source it once from ~/.zshrc, after any RPROMPT you set; leave your title hooks alone.
# It samples on each prompt through precmd and keeps the last command's status.
linger_attention_sample() {
  local last_status=$?
  linger_attention=
  (( $+commands[linger] )) && linger_attention=$(command linger ls --summary 2>/dev/null)
  return $last_status
}
autoload -Uz add-zsh-hook
add-zsh-hook precmd linger_attention_sample
setopt prompt_subst
RPROMPT+='${linger_attention}'
