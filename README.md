# linger

Persistent terminal sessions for Linux and macOS.

Install [elan](https://github.com/leanprover/elan) and clang (on Linux also
binutils `ar`), then run from this checkout:

```sh
./lake build
mkdir -p ~/.local/bin
ln -sf "$PWD/.lake/build/bin/linger" ~/.local/bin/linger
export PATH="$HOME/.local/bin:$PATH"
linger attach work
```

Press **Ctrl-\\** to detach; run the same command to reattach.
`linger --help` lists commands, the statuses a session shows and the exit codes.
[Configuration recipes](recipes/README.md).

## Command endings

A shell that marks its prompts and commands with OSC 133 reports each command's ending: until
you look, `linger ls` shows the command and its status, as `make test: exit 2`, and
`linger ls NAME --porcelain` reports them as `lastcmd` and `lastexit`. fish marks them by itself;
for zsh, add to `~/.zshrc`:

```zsh
autoload -Uz add-zsh-hook
_linger_precmd() { print -n "\e]133;D;$?\a\e]133;A\a" }
_linger_preexec() { print -nf '\e]133;C;cmdline=%q\a' -- "$1" }
add-zsh-hook precmd _linger_precmd
add-zsh-hook preexec _linger_preexec
```

A command's ending is no session status: `✓` and `✗` stay for the session's own program.

## Upgrades

`linger upgrade [name...]`, run by a newer linger, moves each named live session, or every one,
onto it: its daemon replaces its own image with that binary, keeping its process, its program,
its terminal and every connection, so the program and attached clients see nothing happen. A
daemon an older linger started cannot do this; it keeps running, as does one whose new binary
cannot take the session over, and `upgrade` says why.

## Names

`linger rename old new` gives a session a new name; its program, terminal, clients, waiters and
status stay as they were, and so does `LINGER_SESSION`, which holds the session's ID, fixed when
the session was created. A new session's ID is its name; a name whose ID a renamed session still
holds gets a fresh one. `rename` refuses a name a live, saved or ended session has, and a session
an older linger started until `linger upgrade` moves it onto this one.

## Remote hosts

Every command takes a `name@host` target, and `linger ls -r` and the chooser also list the
sessions of the hosts in `~/.config/linger/remotes`. Each line names a host, then the command
that runs linger there, as you would type it before `linger`. A line that is only a host reaches
it with `ssh -T` (`ssh -t` for an attach). An attach needs a terminal at the far end, so a line
may give the attach its own command after a `|`:

```
devbox
box   docker exec -i box | docker exec -it box
pod   kubectl exec -i pod -- | kubectl exec -it pod --
far   ssh -T -- far | mosh far --
```

Blanks separate words, which are never quoted or expanded. A line whose first word starts with
`#` is a comment. A host that does not answer within 3 s lists as `?`. The chooser lists remote
hosts when it opens and when you press Ctrl-L, which also redraws the screen, and its header says
how long ago it listed them, as `remote 12s`.
