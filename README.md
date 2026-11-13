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
`linger help` lists commands, the statuses a session shows and the exit codes.
[Configuration recipes](recipes/README.md).

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
hosts when it opens and when you press Ctrl-R.
