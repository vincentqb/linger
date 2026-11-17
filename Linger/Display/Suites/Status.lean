module

public import Verify.Harness

public section

/-! # Linger.Display.Suites.Status — the status column, the unread mechanism end to end

`unseen` is a property of the SESSION — new lines entered its history while nobody was
watching — so the two transitions that matter are: attaching marks a session seen, and lines
that enter the history while detached mark it unread again; this pins them against the
rendered porcelain rather than against the internals. A session is `⣷` only while its program
declares progress (`checkDeclared`), and a line rewritten in place or a title adds no line
(`checkRedraw`). An ask is the same kind of property: a bell or a
notification with nobody watching makes the session list `⚑`, first, until someone looks
(`checkAsks`).

The comparisons are against the `Status` constructors (through `Env.status`, which
reads `ofName`) and against `Status.icon` itself, so renaming a state is a compile
error rather than an assertion passing against a column that no longer exists.
`Linger.Session.Suites.Watch` covers the one transition this suite never exercises:
`linger attach --read-only` also marks a session seen. -/

namespace Linger.Display.Suites.Status

open Verify.Harness
open Linger.Display.Status (Status)

/-- `linger ls --summary` against `waiting`'s state dir, under `hangMs`, which only a hang
outlasts: the exit code (`none` once it had to be killed), elapsed milliseconds and stdout. -/
private def summaryWithin (waiting : Env) : IO (Option UInt32 × Nat × String) := do
  let start ← Os.Shell.monotonicMs
  let command ←
    IO.Process.spawn
        { cmd := waiting.bin, args := #["ls", "--summary"], env := waiting.procEnv,
          stdout := .piped, stderr := .null }
  let code ← waitOrKill command hangMs
  return (code, (← Os.Shell.monotonicMs) - start, ← command.stdout.readToEnd)

/-- The reply window `ls --summary` gives its peers, in milliseconds: `summaryText` in
`Linger.App.Shell`. -/
def summaryWindowMs : Nat := 250

/-- How many peers never answer in `checkDeadline`: enough that waiting out the reply window
once per peer would take ten seconds. -/
def stalledPeers : Nat := 40

/-- How many summaries `checkDeadline` may ask for to see the responsive peer counted once: a
loaded host can keep that peer, a process of its own, from answering within one window. -/
def summaryRuns : Nat := 5

/-- `summaryWithin` against fresh fake daemons at the sockets `names` in `waiting`'s state dir:
`ready` answers, and the rest send a plausible partial reply and never finish it. A fake daemon
ends after two conversations, so each summary gets its own, at the paths the previous ones left. -/
private def summaryAmong (waiting : Env) (names : Array String) (ready : String) :
    IO (Option UInt32 × Nat × String) := do
  let self ← IO.appPath
  for name in names do
    for path in [s!"{waiting.dir}/{name}.sock", s!"{waiting.dir}/{name}.ready"] do
      if ← System.FilePath.pathExists path then
        IO.FS.removeFile path
  let servers : Array (IO.Process.Child { stdout := .null, stderr := .null }) ←
    names.mapM fun name =>
        IO.Process.spawn
          { cmd := self.toString,
            args :=
              #["--info-server", s!"{waiting.dir}/{name}.sock", s!"{waiting.dir}/{name}.ready",
                if name == ready then "failed-info" else "timeout"],
            stdout := .null, stderr := .null }
  try
    for name in names do
      unless ← waitFor patienceMs (System.FilePath.pathExists s!"{waiting.dir}/{name}.ready") do
        throw (IO.userError s!"status info server {name} did not become ready")
    summaryWithin waiting
  finally
    for server in servers do
      reapOrKill server 0

/-- Stalled sockets precede a responsive peer and follow it. One sampling window covers the
entire snapshot; incomplete and unqueried peers stay unknown. Four stalled peers are fake
daemons that send a plausible partial reply and never finish it; the rest are listeners that
never accept, whose connections the kernel queues. The responsive peer sorts after the four, so
a summary that waited for each peer in turn would reach it only after a second, and would end
only after `stalledPeers` reply windows, ten seconds. The bound is half that: no load makes
waiting in turn quicker, and one shared window would have to stretch twentyfold to reach it.
The summary runs up to `summaryRuns` times, each against fresh fake daemons, until one counts
the responsive peer, and every run must end within the bound. A summary that asked the peers one
at a time within the shared window would count it in no run: each run's four stalled peers take
the whole window first. -/
def checkDeadline (e : Env) : IO Unit := do
  let waiting := { e with dir := s!"{e.dir}/waiting" }
  IO.FS.createDirAll waiting.dir
  let unfinished := #["first", "second", "third", "fourth"]
  let ready := "zz-ready"
  -- `zz-ready` sorts before `zzz-…`, and after the four unfinished peers.
  let quiet :=
    (List.range (stalledPeers - unfinished.size)).toArray.map fun i =>
      s!"zzz-{if i < 10 then "0" else ""}{i}"
  let listeners ← IO.mkRef (#[] : Array UInt32)
  try
    for name in quiet do
      listeners.modify (·.push (← Os.Shell.unixListen s!"{waiting.dir}/{name}.sock"))
    let serialMs := stalledPeers * summaryWindowMs
    let counted :=
      s!"1{Linger.Display.Status.icon .exitedBad} {stalledPeers}{Linger.Display.Status.icon .unknown}\n"
    let mut shared := true
    let mut slowest := 0
    let mut outputs : Array String := #[]
    for _ in List.range summaryRuns do
      let (code, elapsed, output) ← summaryAmong waiting (unfinished.push ready) ready
      shared := shared && code == some 0 && elapsed < serialMs / 2
      slowest := max slowest elapsed
      outputs := outputs.push output
      if output == counted then
        break
    expect shared
        s!"prompt shares one reply deadline across {stalledPeers} stalled peers (at most \
          {slowest} ms in {outputs.size} runs; one window per peer would take {serialMs} ms)"
    let seen := ", ".intercalate (outputs.toList.map fun output => s!"{output.trimAscii}")
    expect (outputs.contains counted)
        s!"a responsive peer behind stalled peers completes within the shared deadline in one of \
          {outputs.size} runs ({seen})"
    let retained ←
      (unfinished.push ready ++ quiet).allM fun name =>
          System.FilePath.pathExists s!"{waiting.dir}/{name}.sock"
    expect retained "prompt leaves unanswered peers' sockets in place"
  finally
    for listener in ← listeners.get do
      Os.Shell.close listener

/-- Fill a listener without accepting. A reply timeout cannot help a blocking
connect here; the sampling command must decline the connection promptly. Nonblocking
connects fill the queue without timing: each one is queued until the queue is full, and the
next is refused at once, so the fixture knows it is full rather than guessing from a connect
that is slow. A summary that connected blocking would wait until this check closes the
listener, past `hangMs`. -/
def checkBacklog (e : Env) : IO Unit := do
  let waiting := { e with dir := s!"{e.dir}/backlog" }
  IO.FS.createDirAll waiting.dir
  let path := s!"{waiting.dir}/full.sock"
  let listener ← Os.Shell.unixListen path
  let queued ← IO.mkRef (#[] : Array UInt32)
  try
    let mut refused := false
    for _ in List.range 1024 do
      let fd ← Os.Shell.unixConnect path true
      if fd < 0 then
        refused := true
        break
      queued.modify (·.push fd.toUInt64.toUInt32)
    let held := (← queued.get).size
    let (code, elapsed, output) ← summaryWithin waiting
    expect (refused && held > 0)
        s!"fixture fills the pending Unix connection queue ({held} queued, then refused)"
    expect (code == some 0) s!"prompt does not wait for a full Unix connection queue ({elapsed} ms)"
    expect (output == s!"1{Linger.Display.Status.icon .unknown}\n")
        "busy connection counts as unknown"
    expect (← System.FilePath.pathExists path)
        "prompt retains a busy listener without claiming its name lock"
  finally
    Os.Shell.close listener
    for fd in ← queued.get do
      Os.Shell.close fd

/-- Whether `linger ls --summary` comes to print `expected` within `patienceMs`: a daemon writes
what it sees to its name's end record on a thread of its own, a moment after it sees it. -/
private def summaryBecomes (e : Env) (expected : String) : IO Bool :=
  waitFor patienceMs do
    let (code, text, _) ← e.cli #["ls", "--summary"]
    return code == 0 && text == expected

/-- The glyph a session whose program asks for you lists with. -/
private def asksGlyph : String := String.singleton (Linger.Display.Status.icon Status.asks)

/-- The porcelain name of that status. -/
private def asksName : String := Linger.Display.Status.name Status.asks

/-- The row of session `name` in a plain `linger ls`, or `""` when none lists it. -/
private def rowOf (e : Env) (name : String) : IO String := do
  let rows ← lines <$> e.out #["ls"]
  return (rows.find? fun row => (row.splitOn " ").getD 1 "" == name).getD ""

/-- Whether session `name`'s history comes to show `marker` within `patienceMs`: what its program
printed before the marker has reached its daemon. Reading the history is an export, not a look,
so it leaves an ask as it was. -/
private def printed (e : Env) (name marker : String) : IO Bool :=
  waitFor patienceMs (return has (← e.out #["capture", "--history", name]) marker)

/-- Send the lines `lines`, joined by newlines, as one datagram to the socket `NOTIFY_SOCKET`
names, as `sd_notify` does: exit 0 once it was sent whole, 1 when it was not, and 2 with no
`NOTIFY_SOCKET`. The notification check's program runs it when the host has no
`systemd-notify`. -/
def notifyProbe (lines : List String) : IO UInt32 := do
  let some path ← IO.getEnv "NOTIFY_SOCKET" | return 2
  return if ← Os.Shell.dgramSend path ("\n".intercalate lines).toUTF8 then 0 else 1

/-- A program says it is ready, and gives its status, through the socket its `NOTIFY_SOCKET`
names, as systemd's services do (`notify_exact`): `systemd-notify --ready --status=hi`, or, on a
host without it, the suite's own sender, makes `ls NAME --porcelain` say `ready true` and
`status_text hi`, and a row with no title show the status as its caption. The same words printed
to the terminal say nothing. The socket is a file of the live session alone: it is there while
the session runs, and gone once a kill ends it. -/
def checkNotify (e : Env) : IO Unit := do
  let sender ←
    if
        (←
              IO.Process.output
                  { cmd := "sh", args := #["-c", "command -v systemd-notify"] }).exitCode ==
          0 then
      pure "systemd-notify --ready --status=hi"
    else
      pure s!"{shellQuote (← IO.appPath).toString} --notify READY=1 STATUS=hi"
  let _ ← e.cli #["start", "notifier", "sh", "-c", s!"{sender}; echo sent-$((1+1)); exec sleep 100"]
  let sent ← printed e "notifier" "sent-2"
  let ready ← waitFor patienceMs (return (← e.info "notifier" "ready") == some "true")
  let status ← e.info "notifier" "status_text"
  let row ← rowOf e "notifier"
  expect (sent && ready && status == some "hi" && has row " hi ")
      s!"a program that notifies is ready with its status, which its row shows: {status} {row}"
  let _ ←
    e.typeIn "printer" #["printf", "'READY=1\\nSTATUS=printed\\n'", "&&", "echo", "p-$((1+1))"]
  let printedOut ← printed e "printer" "p-2"
  expect
      (printedOut && (← e.info "printer" "ready") == some "false" &&
        (← e.info "printer" "status_text").isNone)
      "what a program prints to its terminal says nothing of its readiness"
  let socket := s!"{e.dir}/notifier.notify"
  let live ← System.FilePath.pathExists socket
  e.killAll #["notifier", "printer"]
  let gone ← waitFor patienceMs (return !(← System.FilePath.pathExists socket))
  expect (live && gone) "the notification socket is the live session's, gone once it ends"

/-- What a program owns comes from its own output alone (`step_owned`): a client that types the
sequences that would title its window, post a notification, ring the bell and mark a command, to a
program that does not echo them, changes none of what it owns, and the program writing the same
sequences does. The program reads every line it is sent and answers `synced` to one, so the check
reads the fields once it has read what came before. -/
def checkInputUnowned (e : Env) : IO Unit := do
  let marks :=
    "\x1b]2;owned-title\x07\x1b]9;owned-notice\x07\x07\x1b]133;C;cmdline_url=owned-cmd\x07" ++
      "\x1b]133;D;3\x07"
  let script :=
    s!"stty -echo; echo ready-$((1+1)); while read -r line; do \
      case \"$line\" in sync) echo synced-$((1+1));; emit) printf '%s' {shellQuote marks};; \
      esac; done"
  let _ ← e.cli #["start", "typed", "sh", "-c", script]
  let ready ← printed e "typed" "ready-2"
  let _ ← e.cli #["send", "typed", marks ++ "\n"]
  let _ ← e.cli #["send", "typed", "sync\n"]
  let synced ← printed e "typed" "synced-2"
  let fields ← records <$> e.out #["ls", "--porcelain", "--", "typed"]
  let untouched :=
    ["title", "notice", "lastcmd", "lastexit"].all (fun k => fields.lookup k |>.isNone) &&
      fields.lookup "status" != some (Linger.Display.Status.name .asks)
  expect (ready && synced && untouched) s!"a client's input sets nothing the program owns: {fields}"
  let _ ← e.cli #["send", "typed", "emit\n"]
  let titled ← waitFor patienceMs (return (← e.info "typed" "title") == some "owned-title")
  let fields ← records <$> e.out #["ls", "--porcelain", "--", "typed"]
  expect
      (titled && fields.lookup "notice" == some "owned-notice" &&
        fields.lookup "lastcmd" == some "owned-cmd" &&
        fields.lookup "lastexit" == some "3" &&
        fields.lookup "status" == some (Linger.Display.Status.name .asks))
      s!"the program's own output sets each of them: {fields}"
  e.killAll #["typed"]

/-- A program asks for you when it rings the bell or posts a desktop notification, OSC 9 or
OSC 777, and its session lists `⚑`, first, until someone looks: an attach, or output while a
client is attached. A notification's text is in `info`, the porcelain and the row. Each marker a
command prints is computed by the shell, so the echo of the typed command cannot show it. -/
def checkAsks (e : Env) : IO Unit := do
  let _ ← e.typeIn "a-out" #["seq", "100", "&&", "echo", "out-$((1+1))"]
  let _ ← e.typeIn "z-bell" #["printf", "'\\a'", "&&", "echo", "bell-$((1+1))"]
  let rang ← printed e "z-bell" "bell-2"
  expect (rang && (← e.field "z-bell" "status") == some asksName)
      "a program that rings the bell asks for you"
  let unread ← printed e "a-out" "out-2"
  let rows := lines (← e.out #["ls"])
  expect
      (unread && rows.length == 2 && (rows.headD "").startsWith s!"{asksGlyph} z-bell" &&
        [Status.wantsYou, .working].any fun st =>
          (rows.getD 1 "").startsWith s!"{Linger.Display.Status.icon st} a-out")
      s!"a session that asks lists first, before one with unseen output: {rows}"
  let _ ← waitFor patienceMs (return (← e.status "a-out") == Status.wantsYou)
  expect (← summaryBecomes e (Linger.Display.Status.summary [.asks, .wantsYou] ++ "\n"))
      "summary counts the ask with its own glyph"
  let _ ← e.typeIn "n9" #["printf", "'\\033]2;fix parser\\007'"]
  let _ ← e.cli #["send", "n9", "printf '\\033]9;edit src/Foo.lean?\\007' && echo n9-$((1+1))\n"]
  let posted ← printed e "n9" "n9-2"
  expect
      (posted && (← e.info "n9" "notice") == some "edit src/Foo.lean?" &&
        (← e.field "n9" "notice") == some "edit src/Foo.lean?")
      "an OSC 9 notification's text is in info and the porcelain"
  let row ← rowOf e "n9"
  expect (row.startsWith s!"{asksGlyph} n9" && has row "fix parser  edit src/Foo.lean?")
      s!"the row shows the notification's text right after the caption: {row}"
  let _ ←
    e.typeIn "n777"
        #["printf", "'\\033]777;notify;Claude;needs you\\033\\\\'", "&&", "echo", "n777-$((1+1))"]
  let posted ← printed e "n777" "n777-2"
  expect
      (posted && (← e.field "n777" "status") == some asksName &&
        (← e.info "n777" "notice") == some "Claude: needs you")
      "an OSC 777 notification asks, with its title and body"
  let _ ← e.typeIn "prog" #["printf", "'\\033]9;4;1;50\\007'", "&&", "echo", "prog-$((1+1))"]
  let reported ← printed e "prog" "prog-2"
  let quiet := (← e.field "prog" "status") != some asksName && (← e.info "prog" "notice").isNone
  let _ ← e.cli #["send", "prog", "printf '\\033]9;done\\033\\\\'\n"]
  let notified ← waitFor patienceMs (return (← e.info "prog" "notice") == some "done")
  expect (reported && quiet && notified && (← e.field "prog" "status") == some asksName)
      "a ConEmu progress report (OSC 9;4) asks nothing, and a notification after it does"
  let asked := (← e.field "n9" "status") == some asksName
  let c ← e.spawn #["attach", "n9"] 80 24
  let _ ← waitFor patienceMs (return (← e.info "n9" "clients") == some "1")
  c.detach
  let _ ← waitFor patienceMs (return (← e.info "n9" "clients") == some "0")
  c.bye (sendDetach := false)
  expect
      (asked && (← e.field "n9" "status") != some asksName && (← e.info "n9" "notice").isNone &&
        !has (← rowOf e "n9") "edit src/Foo.lean?")
      "attaching clears the ask and its text"
  let _ ← e.typeIn "seen-bell" #["true"]
  let watcher ← e.spawn #["attach", "seen-bell"] 80 24
  let _ ← waitFor patienceMs (return (← e.info "seen-bell" "clients") == some "1")
  let _ ← e.cli #["send", "seen-bell", "printf '\\a' && echo seen-$((1+1))\n"]
  let shown ← watcher.awaitNeedle "seen-2"
  watcher.detach
  let _ ← waitFor patienceMs (return (← e.info "seen-bell" "clients") == some "0")
  watcher.bye (sendDetach := false)
  let unasked := (← e.field "seen-bell" "status") != some asksName
  let _ ← e.cli #["send", "seen-bell", "printf '\\a'\n"]
  let away ← waitFor patienceMs (return (← e.field "seen-bell" "status") == some asksName)
  expect (shown && unasked && away)
      "a bell while a client is attached leaves no ask, and one after it leaves does"
  e.killAll #["a-out", "z-bell", "n9", "n777", "prog", "seen-bell"]

/-- A `/bin/sh` command that prints the OSC 133 mark `body`, ended by BEL. -/
private def mark (body : String) : String := s!"printf '\\033]133;{body}\\007'"

/-- What `info` and the porcelain report of session `name`'s last command's ending since a look:
its command line and its exit status, each in both. -/
private def endingOf (e : Env) (name : String) :
    IO (Option String × Option String × Option String × Option String) := do
  return (← e.info name "lastcmd", ← e.info name "lastexit", ← e.field name "lastcmd",
      ← e.field name "lastexit")

/-- Nothing reported of a command's ending. -/
private def untold : Option String × Option String × Option String × Option String :=
  (none, none, none, none)

/-- A shell that marks its commands with OSC 133 reports each command's ending: a `D` after a
`C` with nobody attached is told in `info`, the porcelain and the row, with the command line the
`C` gave, URL-encoded or quoted as `printf %q` quotes it, and the status the `D` gave, until
someone looks; a later `C` replaces it, a `D` with no `C` since the last `D` or `A` tells
nothing, and the session's status stays its own. The session's shell is `/bin/sh`, which prints
the marks with `printf`; each marker a command prints is computed by the shell, so the echo of
the typed command cannot show it. -/
def checkEndings (e : Env) : IO Unit := do
  let _ ←
    e.typeIn "mk"
        #[s!"{mark "A;click_events=1"}; {mark "B"}; {mark "C;cmdline_url=make%%20test"}; (exit 2); \
            printf '\\033]133;D;%s\\007' $?; {mark "D;5"}; {mark "A"}; echo mk-$((1+1))"]
  let ran ← printed e "mk" "mk-2"
  let told ← endingOf e "mk"
  expect (ran && told == (some "make test", some "2", some "make test", some "2"))
      s!"a command that ends with 2 while nobody watches is in info and the porcelain, and a D \
        with no C after it tells nothing: {told}"
  let row ← rowOf e "mk"
  expect (has row "make test: exit 2") s!"the row shows the command line and its exit status: {row}"
  let status ← e.status "mk"
  expect (status == Status.idle)
      s!"a command's ending leaves the session's own status: {Linger.Display.Status.name status}"
  let before ← endingOf e "mk"
  let c ← e.spawn #["attach", "mk"] 80 24
  let _ ← waitFor patienceMs (return (← e.info "mk" "clients") == some "1")
  c.detach
  let _ ← waitFor patienceMs (return (← e.info "mk" "clients") == some "0")
  c.bye (sendDetach := false)
  expect
      (before.1 == some "make test" && (← endingOf e "mk") == untold &&
        !has (← rowOf e "mk") "exit")
      "attaching clears the ending"
  let _ ←
    e.cli
        #["send", "mk",
          s!"{mark "C;cmdline=make\\\\ check\\\\;\\\\ ls"}; (exit 1); \
            printf '\\033]133;D;%s\\007' $?; echo mk-$((2+2))\n"]
  let quoted ← printed e "mk" "mk-4"
  let checked ← endingOf e "mk"
  expect (quoted && checked == (some "make check; ls", some "1", some "make check; ls", some "1"))
      s!"a command line quoted as printf %q quotes it is read unquoted: {checked}"
  let _ ← e.cli #["send", "mk", s!"{mark "C;cmdline_url=sleep%%201"}; echo mk-$((3+3))\n"]
  let replaced ← printed e "mk" "mk-6"
  expect (replaced && checked.1.isSome && (← endingOf e "mk") == untold)
      "a later C replaces an ending nobody saw"
  let _ ← e.cli #["send", "mk", s!"{mark "A"}; {mark "D;0"}; echo mk-$((4+4))\n"]
  let prompted ← printed e "mk" "mk-8"
  expect (prompted && (← endingOf e "mk") == untold) "a D with no C since the last A tells nothing"
  let _ ← e.typeIn "plain" #["(exit 3);", "echo", "plain-$((1+1))"]
  let plain ← printed e "plain" "plain-2"
  expect (plain && (← endingOf e "plain") == untold && !has (← rowOf e "plain") "exit")
      "a shell that marks nothing reports no ending"
  e.killAll #["mk", "plain"]

/-- How many times a status check reads a session's status while its program holds still. -/
def statusSamples : Nat := 10

/-- Session `name`'s status, read back to back at least `statusSamples` times and over at least
`spanMs`, so the reads cover that much of its program's time. -/
private def sampleStatus (e : Env) (name : String) (spanMs : Nat) : IO (List Status) := do
  let start ← Os.Shell.monotonicMs
  let mut read := []
  while read.length < statusSamples || (← Os.Shell.monotonicMs) < start + spanMs do
    read := read ++ [← e.status name]
  return read

/-- The names of statuses, as the porcelain gives them. -/
private def names (statuses : List Status) : List String := statuses.map Linger.Display.Status.name

/-- A program that declares itself busy with ConEmu's progress report, `OSC 9;4;3`, the
indeterminate state, reads `⣷` at every sample while it sleeps, whatever time passes, and once it
clears the report with `OSC 9;4;0` it reads quiet at every sample, as `progress` says. Each marker
the program prints is computed by the shell, so the echo of the typed command cannot show it. -/
def checkDeclared (e : Env) : IO Unit := do
  let _ ←
    e.typeIn "decl"
        #["printf", "'\\033]9;4;3;\\007'", "&&", "echo", "busy-$((1+1))", "&&", "sleep", "12", "&&",
          "printf", "'\\033]9;4;0;\\007'", "&&", "echo", "done-$((1+1))", "&&", "sleep", "60"]
  let busy ← printed e "decl" "busy-2"
  let progress ← e.info "decl" "progress"
  let during ← sampleStatus e "decl" 6000
  expect (busy && progress == some "indeterminate" && during.all (· == .working))
      s!"a program that declared itself busy reads working while it sleeps: {progress} \
        {names during}"
  let cleared ← printed e "decl" "done-2"
  let progress ← e.info "decl" "progress"
  let after ← sampleStatus e "decl" 3000
  expect (cleared && progress == some "none" && after.all (· == .idle))
      s!"a program that cleared its report reads idle, with no flips: {progress} {names after}"
  e.killAll #["decl"]

/-- Each state a program declares has its own status, held until it reports another: an error,
`OSC 9;4;2`, reads `!`, running with an error, which the summary counts, a pause, `OSC 9;4;4`, reads
`⣤`, and removing the report reads quiet. -/
def checkStates (e : Env) : IO Unit := do
  let report (state : Nat) : Array String := #["printf", s!"'\\033]9;4;{state};\\007'", "&&"]
  let _ ←
    e.typeIn "states"
        (report 2 ++ #["echo", "failed-$((1+1))", "&&", "sleep", "8", "&&"] ++ report 4 ++
          #["echo", "paused-$((2+2))", "&&", "sleep", "8", "&&"] ++
          report 0 ++
          #["echo", "cleared-$((3+3))", "&&", "sleep", "60"])
  let failed ← printed e "states" "failed-2"
  let errored ← sampleStatus e "states" 2500
  let counted ← summaryBecomes e (Linger.Display.Status.summary [.errored] ++ "\n")
  expect (failed && errored.all (· == .errored) && counted)
      s!"a program that declared an error reads running-error, counted by the summary: \
        {names errored}"
  let paused ← printed e "states" "paused-4"
  let held ← sampleStatus e "states" 2500
  let progress ← e.info "states" "progress"
  expect (paused && progress == some "paused" && held.all (· == .paused))
      s!"a program that declared a pause reads paused until it reports another state: {progress} \
        {names held}"
  let cleared ← printed e "states" "cleared-6"
  let quiet ← sampleStatus e "states" 1000
  expect (cleared && quiet.all (· == .idle)) s!"removing the report reads idle: {names quiet}"
  e.killAll #["states"]

/-- A program that only rewrites one line in place, with a carriage return, and animates its
window title, as an idle agent's status line and a working agent's spinner do, never reads `⣷`,
`⣿` or `⚑`: no line enters its history and it declares nothing. -/
def checkRedraw (e : Env) : IO Unit := do
  let _ ←
    e.typeIn "redraw"
        #["i=0;", "while", "[", "$i", "-lt", "40", "];", "do", "printf", "'\\r t-%s'",
          "$((i+100));", "printf", "'\\033]0;spin %s\\007'", "$i;", "sleep", "0.2;", "i=$((i+1));",
          "done;", "echo;", "echo", "redrawn-$((1+1));", "sleep", "60"]
  let started ← printed e "redraw" "t-10"
  let during ← sampleStatus e "redraw" 4000
  let finished ← printed e "redraw" "redrawn-2"
  expect (started && finished && during.all (· == .idle))
      s!"a line rewritten in place and an animated title read idle: {names during}"
  e.killAll #["redraw"]

/-- A program that prints a hundred lines with nobody attached, more than the screen holds, puts
new lines in its history: it reads `⣿` at every sample, whatever time passes, until an attach. -/
def checkLines (e : Env) : IO Unit := do
  let _ ← e.typeIn "lines" #["seq", "100", "&&", "echo", "lines-$((1+1))", "&&", "sleep", "60"]
  let printedAll ← printed e "lines" "lines-2"
  let unread ← sampleStatus e "lines" 4000
  let c ← e.spawn #["attach", "lines"] 80 24
  let _ ← waitFor patienceMs (return (← e.info "lines" "clients") == some "1")
  c.detach
  let _ ← waitFor patienceMs (return (← e.info "lines" "clients") == some "0")
  c.bye (sendDetach := false)
  let seen ← e.status "lines"
  expect (printedAll && unread.all (· == .wantsYou) && seen == .idle)
      s!"a hundred lines with nobody attached read wants-you until an attach: {names unread} \
        then {Linger.Display.Status.name seen}"
  e.killAll #["lines"]

/-- The status suite: attaching marks a session seen and detached output marks it unread. -/
def run : IO UInt32 :=
  Env.suite "status" fun e => do
    let (emptyCode, empty, _) ← e.cli #["ls", "--summary"]
    expect (emptyCode == 0 && empty.isEmpty) "empty attention summary prints nothing"
    -- a long-lived child, so nothing exits under us and the row stays classifiable
    -- as idle/wants-you rather than exited-ok, after more lines than the screen holds, which
    -- enter its history
    let _ ← e.typeIn "st" #["seq", "100", "&&", "sleep", "60"]
    -- a settling time, so that `behind` below counts all the output the shell will print
    IO.sleep 1500
    -- 1. a session nobody has watched, that has produced output, is unread
    expect (← waitFor patienceMs (return (← e.status "st") == Status.wantsYou))
        "unwatched output reads wants-you"
    let unread := s!"1{Linger.Display.Status.icon Status.wantsYou}\n"
    let before ← e.field "st" "behind"
    expect (← summaryBecomes e unread) "summary counts unread with the shared glyph"
    expect ((← e.field "st" "behind") == before) "summary does not acknowledge unread output"
    -- 2. attaching marks it seen: detach with no further output and it is idle.
    let c ← e.spawn #["attach", "st"] 80 24
    let _ ← waitFor patienceMs (return (← e.info "st" "clients") == some "1")
    c.detach
    let _ ← waitFor patienceMs (return (← e.info "st" "clients") == some "0")
    c.bye (sendDetach := false)
    expect ((← e.status "st") == Status.idle) "attach marks the session seen"
    expect (← summaryBecomes e "") "idle session does not clutter the summary"
    -- 3. output while detached makes it unread again
    -- the line is echoed by the terminal under the bottom of a full screen, so it enters the history
    let _ ← e.cli #["send", "st", "echo later\n"]
    expect (← waitFor patienceMs (return (← e.status "st") == Status.wantsYou))
        "output while away reads wants-you"
    -- `behind` is `toString (Session.behind s)`, a decimal `Nat`, so parse it
    -- rather than compare the string to "0": `!= "0"` also passes on a field that
    -- stopped being a number at all.
    let behind := ((← e.field "st" "behind").getD "0").toNat?.getD 0
    expect (behind > 0) "behind counts unseen output"
    -- 4. the human column renders one glyph for it — `Status.icon`'s own glyph,
    -- which is what `Listing.humanRow` puts at the head of the row.
    let human ← e.out #["ls"]
    expect (has human (String.singleton (Linger.Display.Status.icon Status.wantsYou)))
        "human listing shows the wants-you glyph"
    -- A real daemon retires when its child exits. Exercise a completed info
    -- reply carrying that exit field without racing the daemon's retirement.
    let self ← IO.appPath
    let failedServer ←
      IO.Process.spawn
          { cmd := self.toString,
            args :=
              #["--info-server", s!"{e.dir}/failed.sock", s!"{e.dir}/failed.ready", "failed-info"],
            stdout := .null, stderr := .null }
    try
      unless ← waitFor patienceMs (System.FilePath.pathExists s!"{e.dir}/failed.ready") do
        throw (IO.userError "failed info server did not become ready")
      let failed := (← e.status "failed") == Status.exitedBad
      let mixed :=
        s!"1{Linger.Display.Status.icon Status.wantsYou} 1{Linger.Display.Status.icon Status.exitedBad}\n"
      expect (failed && (← summaryBecomes e mixed))
          "summary keeps unread output and a reported failed exit distinct"
    finally
      reapOrKill failedServer 0
      -- a daemon removes its socket when it ends; the fixture's own is removed here
      try
        IO.FS.removeFile s!"{e.dir}/failed.sock"
      catch _ =>
        pure ()
    -- a record is read only while its daemon holds the name: a daemon killed before it could say
    -- how its program ended is counted as not answering, not from what it last wrote
    let program := ((← e.info "st" "pid").bind (·.toNat?)).map UInt32.ofNat
    let daemon ← e.daemonPid "st"
    for pid in [daemon, program] do
      if let some pid := pid then
        try
          Os.Shell.kill pid 9
        catch _ =>
          pure ()
    let unanswered := s!"1{Linger.Display.Status.icon Status.unknown}\n"
    expect (daemon.isSome && program.isSome && (← summaryBecomes e unanswered))
        "a summary counts a killed daemon as not answering, not from what it last wrote"
    e.killAll #["st"]
    checkInputUnowned e
    checkNotify e
    checkAsks e
    checkDeclared e
    checkRedraw e
    checkLines e
    checkStates e
    checkEndings e
    checkDeadline e
    checkBacklog e

end Linger.Display.Suites.Status
