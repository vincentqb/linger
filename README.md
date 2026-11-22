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

## Waiting

`linger wait NAME...` waits for each session's program to end and exits with its status, as a
shell's `wait` does. It takes no time limit: `timeout 5 linger wait NAME` exits 124 when the
time runs out first, as `timeout` does, and leaves the session running.

## A Lean library

`Linger.App.Api` gives each command as a Lean function with typed arguments and results: what the
command found, whose answer is its exit status, and what it shows, a listing's records or a
capture's bytes. It works in the namespace its caller names, writes nothing to standard output or
standard error, tells what it says to its caller, and reaches a remote host only through a
transport its caller passes. Its `wait` takes a deadline, since a Lean caller cannot run
`timeout` around a call. The command line parses its words into such a request and renders the
reply.

## JSON-RPC

`linger serve` speaks linger's operations as JSON-RPC 2.0 on its standard input and output, one
JSON value a line, for a client that runs it as a child with pipes. The client sends `initialize`
with the `protocolVersion` it speaks (`"1"`), gets the version, `serverInfo` and the methods in
`capabilities`, and sends the `initialized` notification; before that every other request gets
error -32002. Each method is one command's request: `sessions/list` (optional `names`),
`session/start` (`name`, `program`, optional `args`), `session/resume`, `session/send` (`name`,
`data` in base64), `session/detach`, `session/kill`, `session/rename` (`name`, `new`),
`session/capture` (`name`, optional `history`), `session/resize` (`name`, `cols`, `rows`) and
`session/wait` (`name`). `sessions/subscribe` lists the sessions as `sessions/list` does and opens
a subscription named by its request's id: from then on `serve` lists them one second after its
last listing ended, and whenever its records differ from what the client was last told, read
without `idle` and `lastout`, the clock's readings, sends `sessions/changed` with that id, the
records that differ and the names that
went, the latest when the client reads late, never a backlog; `sessions/unsubscribe`
(`subscription`) closes it. A result carries the answer the command would exit with, as
`{"answer": "done", "code": 0}`, then what it shows: a listing's `records`, a capture's bytes in
base64 as `data`, how a session ended as `ending`, and what the command said as `said`, its last
32 lines, with `saidDropped` counting the rest. A
malformed line, an unknown method and wrong params get JSON-RPC's errors, with linger's answer in
their `data`. linger's own chooser reads the same records: it runs `ls --porcelain`, which prints
the listing `sessions/list` sends, each key and value clean text. `serve` reaches no remote host. Once its standard input ends, it answers the
requests it read and exits.

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

## tmux-resurrect saves

linger reads the latest tmux-resurrect save where tmux-resurrect keeps it, and never writes,
moves or deletes anything there. `linger ls` and the chooser list each of its panes as `~`,
`(saved by tmux)`, after your saved sessions, while linger has no session, checkpoint or ending
under the pane's name; `linger ls --porcelain` gives those rows the field `source`, `tmux`.
`linger attach NAME`, or `linger resume NAME`, starts a fresh shell in the pane's directory on
its saved screen, and never runs its saved command; a name that is already a session's stays
that session's. `linger kill NAME` hides the pane for good, recording the ending a kill leaves.
`linger ls --resurrect` writes your sessions' names and directories as a save, to standard output
only.

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
