module

public import Verify.Harness

public section

/-! # Linger.Display.Suites.Status — the status column, the unread mechanism end to end

`unseen` is a property of the SESSION — output arrived while nobody was watching —
so the two transitions that matter are: attaching marks a session seen, and output
while detached marks it unread again. Both go through the counter pair in
`Session.State` (`outSeq`/`lookSeq`), and this pins them against the rendered
porcelain rather than against the internals. An ask is the same kind of property: a bell or a
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
  let _ ← e.typeIn "a-out" #["echo", "out-$((1+1))"]
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
  expect (status == Status.wantsYou || status == .working)
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

/-- How many times `checkSteady` reads a steady program's status. -/
def steadySamples : Nat := 6

/-- A program that redraws once a second, as `top` does, keeps one status, `⣷`, between its
redraws, and goes quiet once it stops. The program reads its own session's status each time,
right after the second it sleeps between two outputs, when the latest output is oldest: a working
window of a second has let it go quiet by then, and the session would flip between `⣷` and `⣿` on
every redraw. Its reads go to a file, never to its terminal, so a read is no output. -/
def checkSteady (e : Env) : IO Unit := do
  let samples := s!"{e.dir}/steady-samples"
  -- the suite's own state directory and tmux source, whatever the session's environment holds
  let env :=
    " ".intercalate (e.procEnv.toList.filterMap fun (k, v) => v.map fun v => s!"{k}={shellQuote v}")
  let read :=
    s!"env {env} {shellQuote e.bin} ls --porcelain -- steady | grep '^status' >> {shellQuote samples}"
  let _ ←
    e.typeIn "steady"
        #[s!"i=0; while [ $i -lt {steadySamples} ]; do printf 'redraw\\n'; sleep 1; {read}; \
            i=$((i+1)); done; echo steady-$((1+1))"]
  let finished ←
    waitFor (patienceMs + steadySamples * 2000)
        (return has (← e.out #["capture", "--history", "steady"]) "steady-2")
  let read ← (lines <$> readText samples) <|> pure []
  let working := s!"status\t{Linger.Display.Status.name .working}"
  expect (finished && read.length == steadySamples && read.all (· == working))
      s!"a program that prints once a second stays working between its redraws: {read}"
  let quiet ← waitFor patienceMs (return [Status.wantsYou, .idle].contains (← e.status "steady"))
  expect (finished && quiet) "a steady program that stops goes quiet"
  e.killAll #["steady"]

/-- The status suite: attaching marks a session seen and detached output marks it unread. -/
def run : IO UInt32 :=
  Env.suite "status" fun e => do
    let (emptyCode, empty, _) ← e.cli #["ls", "--summary"]
    expect (emptyCode == 0 && empty.isEmpty) "empty attention summary prints nothing"
    -- a long-lived child, so nothing exits under us and the row stays classifiable
    -- as idle/wants-you rather than exited-ok
    let _ ← e.typeIn "st" #["sh", "-c", "sleep 60"]
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
    let _ ← e.cli #["send", "st", "echo", "later"]
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
    checkAsks e
    checkSteady e
    checkEndings e
    checkDeadline e
    checkBacklog e

end Linger.Display.Suites.Status
