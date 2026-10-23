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
`linger help` lists commands. [Configuration recipes](recipes/README.md).
