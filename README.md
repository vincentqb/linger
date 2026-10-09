# linger

Persistent terminal sessions for Linux and macOS. Programs keep running when
you detach or disconnect.

Install [elan](https://github.com/leanprover/elan) and clang (on Linux also
binutils `ar`), then build from this checkout:

```sh
./lake build
mkdir -p ~/.local/bin
ln -sf "$PWD/.lake/build/bin/linger" ~/.local/bin/linger
```

Add `~/.local/bin` to your PATH, then create or reattach to a session:

```sh
linger attach work
```

Press **Ctrl-\\** to detach; run the same command to reattach.
Run `linger help` for commands and options.

Optional [terminal, prompt and SSH configuration](recipes/README.md).
