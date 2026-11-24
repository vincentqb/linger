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
JSON value a line, for a client that runs it as a child with pipes. Every line either way is
canonical JSON, the format of [ExactJSON](https://github.com/vincentqb/lean-toml-json): no
whitespace outside strings, object keys in increasing code-point order, each key once, integers
in decimal with no leading zero, no `+` and no `-0`, and a string's characters as themselves but
`"`, `\` and those below U+0020, each with its one escape (`\"`, `\\`, `\b`, `\t`, `\n`, `\f`,
`\r`, otherwise `\u00` and two lowercase hexadecimal digits). linger's values hold no float, so a
number with a fraction or an exponent is none of its texts. A request reads
`{"id":1,"jsonrpc":"2.0","method":"sessions/list","params":{}}`; a line that is not canonical,
such as `{"jsonrpc":"2.0","id":1,…}`, gets error -32700 with no id and changes nothing, its `data`
linger's usage answer and the reason, at the character it stops being canonical:
`{"answer":"usage","code":2,"reason":"at character 20: the key \"id\" after \"jsonrpc\", where
canonical JSON lists keys in increasing order"}`. The client sends `initialize`
with the `protocolVersion` it speaks (`"1"`), gets the version, `serverInfo` and the methods in
`capabilities`, and sends the `initialized` notification; before that every other request gets
error -32002. Each method is one command's request: `sessions/list` (optional `names`),
`session/start` (`name`, `program`, optional `args`), `session/resume`, `session/send` (`name`,
`data` in base64), `session/detach`, `session/kill`, `session/rename` (`name`, `new`),
`session/capture` (`name`, optional `history`), `session/resize` (`name`, `cols`, `rows`),
`session/wait` (`name`) and `session/upgrade` (`name`). `sessions/subscribe` lists the sessions as `sessions/list` does and opens
a subscription named by its request's id: from then on `serve` lists them one second after its
last listing ended, and whenever its records differ from what the client was last told, read
without `idle` and `lastout`, the clock's readings, sends `sessions/changed` with that id, the
records that differ and the names that
went, the latest when the client reads late, never a backlog; `sessions/unsubscribe`
(`subscription`) closes it. A result carries the answer the command would exit with, as
`{"answer":"done","code":0}`, with what it shows: a listing's `records`, a capture's bytes in
base64 as `data`, how a session ended as `ending`, and what the command said as `said`, its last
32 lines, with `saidDropped` counting the rest. An
unknown method and wrong params get JSON-RPC's errors, with linger's answer in their `data`.
`ls --porcelain` prints exactly the records `sessions/list` sends, one canonical JSON object a line,
each key and value clean text, and linger's own chooser reads them so. A `name@host` session reaches its
host's `serve`, as on the command line. Once its standard input ends, it answers the requests it
read and exits.

A client with no terminal of its own follows a session's terminal as rows. `session/screen`
(`name`) attaches to the session read-only, as `attach --read-only` does, and answers with its
screen: `rows`, each `{"line": 3, "text": "...", "spans": [[5, {"fg": 1, "bold": true}], ...]}`,
whose text is what `capture` prints for that row and whose spans are runs of `[length, pen]`
over its characters, a pen giving `fg` and `bg` (a palette index or `"#rrggbb"`) when not the
default and each of `bold`, `dim`, `italic`, `underline`, `blink`, `reverse` and `strike` that is
set; the `cursor`, `{"x", "y", "visible"}`; and the window `title`. From then on, after the session
writes, `session/screen/changed` brings the client's copy to the screen: the `rows` that changed,
the numbers of the lines `removed` when the screen shrinks, and the `cursor` and `title` when they
changed, the latest when the client reads late, never a backlog. `session/history` (`name`) sends
`session/history/changed` with the `lines` that scrolled off the top of the screen since its last
update, in the same form, and how many it `dropped` before them, at most 1000 between two
updates. Each update names its subscription, the id of the request that opened it, and the last,
when the session ends, carries `closed` with the answer its ending gives; `sessions/unsubscribe`
closes either, and a connection holds at most 16.

A client that is a terminal attaches to a session as `linger attach` does. `session/attach`
(`name`, optional `readOnly` and `command`) attaches, writable unless `readOnly`, starting the
session under the name with `command`, or the shell, when none holds it, and with no size of its
own until the client gives one; it answers `done`, and from then on
`session/output` (`subscription`, `data`) carries in base64 exactly the bytes the session's daemon
sends an attach client: the synchronized repaint, then the output as it comes. `session/input`
(`subscription`, `data` in base64) types into the session, `session/resize` (`subscription`,
`cols`, `rows`) gives it the client's size, and `session/detach` (`subscription`) ends the attach;
the session runs on. When the session ends, the last update carries `closed` with the answer its
ending gives. Every session `linger attach` reaches, `session/attach` reaches as it does: a saved
session is resumed and streams; an ended one's stream is its final screen's repaint, then `closed`
with how its program ended, and the session is discarded, its ending kept for `wait` and `ls`; a
read-only attach of a saved one shows its screen until the client detaches, and keeps it saved;
and a `name@host` session streams from its host's `session/attach`. A client that stops reading is
cut off as an attach client is: `serve` stops reading the daemon while 64 KiB wait for the client,
the daemon closes the connection once it owes the client its cap, and the last update carries
`closed`.

## Upgrades

`linger upgrade [name...]`, run by a newer linger, moves each named live session, or every one,
onto it: its daemon replaces its own image with that binary, keeping its process, its program,
its terminal and every connection, so the program and attached clients see nothing happen. A
daemon an older linger started cannot do this; it keeps running, as does one whose new binary
cannot take the session over, and `upgrade` says why. `linger attach NAME` does the same first,
saying nothing, when the session's daemon was built at an earlier step than the attaching linger,
as `ls NAME --porcelain` reports in `build`, or reports no build, and can hand its session over;
a daemon that refuses keeps running, and the attach says why on one line before it attaches. A
read-only attach, `ls`, the chooser and `capture` never upgrade.

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
it with `ssh -T`:

```
devbox
box   docker exec -i box
pod   kubectl exec -i pod --
```

Blanks separate words, which are never quoted or expanded. A line whose first word starts with
`#` is a comment. Every command on a remote session runs `linger serve` on its host through its
command and calls the method of its request there, as any client of `serve` does, with every
argument in JSON, so no shell reads any of them: what the command finds, shows and says is what the
host's linger answered, each line it said prefixed with the host. An attach is linger's own attach
client, conversing with the host's `session/attach`: the detach key, the title, the synchronized
repaint and the handback are the same as for a local session, and the far end needs no terminal.
`ls -r` calls `sessions/list` of each host and lists the records it returns, each named
`name@host`. A host that does not answer within 3 s lists as `?`; a host whose linger does not
speak `serve` is refused, `HOST runs a linger without serve; install a current linger there`, and
lists as `?` with that `reason` in `ls -r --porcelain`; so is one whose `serve` writes other JSON than
canonical, as a linger from before canonical JSON does, `HOST runs a linger whose serve does not
write canonical JSON (REASON); install a current linger there`. The chooser lists remote hosts when it
opens and when you press Ctrl-L, which also redraws the screen, and its header says how long ago
it listed them, as `remote 12s`.
