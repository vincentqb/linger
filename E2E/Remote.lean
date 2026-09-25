module

public import E2E.Harness
public import Linger.Core.Remote
public import Linger.Core.Name
public import Linger.Runtime.Cli

public section

/-! # E2E.Remote — remote sessions over ssh, against a FAKE `ssh` on PATH

Ported from `tests/remote_test.py`. `linger -r <hosts>` folds each host's sessions
into the local overview (by running `ssh <host> linger ls --porcelain`), tolerates
an unreachable host, and refuses a duplicate host. `linger attach name@host` execs
`ssh -t -- <host> linger attach <name>`. Hostile remote output must not inject a
path or escape bytes into the local listing.

WHY A FAKE `ssh`, AND HOW. The suite is hermetic — no network, no second machine,
no keys. A short `/bin/sh` script named `ssh` goes FIRST on `PATH`, logs its argv,
answers `ls`/`attach` for a reachable host and exits 255 for a dead one. That turns
the argv linger hands to ssh, which is what this suite is really about, into an
artefact on disk. Three parts of the delivery are all load-bearing: the
option-stripping loop, so the script finds the destination whether it was called
with `-t --` (`cmdAttach`) or with four `-o` pairs (`listRemote`); the exec bit, or
`PATH` lookup never finds it; and fakebin being first, or a real `ssh` wins.
`Posix.chmod` already existed (`Paths.ensureDir` uses it), so this costs no
syscall — `SHIM_CAP` does not move.

WHAT THE PORT TIGHTENED:

* the duplicate-host rejection is asked of `Remote.checkHosts` itself instead of
  substring-matched as `'more than once'` AND `'dev-a'` — one derived string
  covers both of the Python's conjuncts, and moving the wording now fails the
  check instead of passing it;
* the hostile name's expected form is `Name.sanitize hostileName`, not the literal
  `_._.._etc_passwd` the Python spelled out beside it;
* `remote-work@dev-a` is additionally read out of `ls --porcelain` through
  `records` as a `name` RECORD, not as a substring loose in the human listing. The
  porcelain is what a peer's own `-r` parses, so that is where the `@host` tag has
  to be well formed; the same reader now also proves no row's name ends `@dead`;
* the ssh argv check STRIPS the option prefix off the logged line and compares the
  tail to a list. That is what the Python's
  `-t (-o \S+ )*(--\s+)?dev-a linger attach remote-work` regex approximated —
  except the tail comparison pins the whole remote command, where the regex pinned
  a prefix of it and would have passed on `… linger attach remote-work-2`.

TWO THINGS DELIBERATELY DROPPED. The Python's `plain()` stripped CSI sequences so
that `in` would work on decoded text; `hasBytes`/`hasText` read the pty's raw
bytes, so there is nothing to strip. And its `timeout=15` on the `-r` call is gone:
the only ssh here is the fake, which never blocks, and a real host that hangs is
bounded by `listRemote`'s own `-o ConnectTimeout=3` rather than by this suite. -/

namespace E2E.Remote

open E2E.Harness
open Linger.Posix (chmod kill)

/-! ## The fixture -/

def devHost : String := "dev-a"

/-- The fake `ssh` exits 255 for this one: a host that is down. -/
def deadHost : String := "dead"

/-- A `user@host` ssh target, so the `attach` split has more than one `@` to get
wrong. -/
def userHost : String := s!"me@{devHost}"

def goodName : String := "remote-work"

/-- The hostile record's name: a path, with a leading dot. `Name.sanitize` is what
defuses it, and the check below asks *it* what to expect. -/
def hostileName : String := "../../etc/passwd"

def attachMark : String := "FAKE-ATTACH-OK"

/-- The rejection `Remote.checkHosts` itself produces for a repeated host.

Derived rather than substring-matched: the Python asserted `'more than once'` and
`'dev-a'` as two conjuncts, and this one string is both — while also failing if the
wording moves. The `.ok` branch is a sentence stderr cannot contain, deliberately:
a validator that started ACCEPTING duplicates must FAIL this check, and an empty
needle would make `has` trivially true instead. -/
def dupMsg : String :=
  match Linger.Core.Remote.checkHosts [devHost, devHost] with
  | .error m => m
  | .ok _ => "checkHosts accepted a duplicate host"

/-- The fake `ssh`.

The ANSI injection is written `\033` for printf to decode rather than as the raw
ESC byte the Python's f-string left in the file — same byte on the wire (the
`E2E.Graphics` `printf '\033…'` precedent), and it keeps a control character out of
Lean source. The two record names come from the constants above, so the sanitize
expectation and the fixture cannot drift apart. The third `printf` is a line with
no tabs: `Remote.parseRecord` must drop the record, not the listing. -/
def fakeSsh (log : String) : String :=
  "#!/bin/sh\n" ++ s!"echo \"$@\" >> {log}\n" ++
    "# strip ssh options to find the destination and remote command\n" ++
    "while [ $# -gt 0 ]; do\n" ++
    "  case \"$1\" in\n" ++
    "    -o) shift 2 ;;\n" ++
    "    -t) shift ;;\n" ++
    "    --) shift; break ;;\n" ++
    "    *) break ;;\n" ++
    "  esac\n" ++
    "done\n" ++
    "host=\"$1\"; shift\n" ++
    s!"[ \"$host\" = \"{deadHost}\" ] && exit 255\n" ++
    "case \"$2\" in\n" ++
    "  ls)\n" ++
    s!"    printf 'name\\t{goodName}\\nstate\\tlive\\nclients\\t1\\ncmd\\tvim\\033[31mINJECT\\nlabel.env\\tprod\\n\\n'\n" ++
    s!"    printf 'name\\t{hostileName}\\nstate\\tresumable\\n\\n'\n" ++
    "    printf 'garbage line with no tabs\\n\\n'\n" ++
    "    ;;\n" ++
    "  attach) /bin/sh -c \"$*\"; sleep 5 ;;\n" ++
    "esac\n" ++
    "exit 0\n"

/-- SSH joins its remote argv into shell input. This stub records the arguments
that survive that shell, so logging SSH's own argv cannot hide an injection. -/
def fakeLinger : String :=
  "#!/bin/sh\n" ++ "printf '%s\\n' \"$@\" > \"$LINGER_REMOTE_ARGS\"\n" ++
    s!"printf '{attachMark}\\n'\n"

/-- Drop `-o value` pairs and the end-of-options `--`: the `(-o \S+ )*(--\s+)?`
half of the Python's regex. `--` terminates the strip, because that is what it
means. -/
def stripOpts : List String → List String
  | "-o" :: _ :: rest => stripOpts rest
  | "--" :: rest => rest
  | rest => rest

/-- One logged argv, minus its option prefix. `none` unless the line asked for a
tty, which is the `-t` anchor the regex opened with — `cmdAttach` must request one
or the remote `linger attach` gets no terminal and refuses. -/
def sshTail (line : String) : Option (List String) :=
  match (line.splitOn " ").filter (fun t => !t.isEmpty) with
  | "-t" :: rest => some (stripOpts rest)
  | _ => none

/-- Every tty-requesting argv the fake logged. A missing log reads as `[]`, so a
failure is a FAIL line rather than an exception that costs the `FAILURES:`
verdict. -/
def sshTails (log : String) : IO (List (List String)) := do
  if (← System.FilePath.pathExists (System.FilePath.mk log)) then
    let txt ← IO.FS.readFile (System.FilePath.mk log)
    return (txt.splitOn "\n").filterMap sshTail
  else
    return []

def run : IO UInt32 := do
  let e ← Env.make "remote"
  let mut f := 0
  -- ── the fake ssh: written, made executable, put first on PATH ──────────────
  let fakebin := (System.FilePath.mk e.dir) / "fakebin"
  IO.FS.createDirAll fakebin
  let log := ((System.FilePath.mk e.dir) / "ssh.log").toString
  let remoteArgs := (System.FilePath.mk e.dir) / "remote-args"
  let sshPath := fakebin / "ssh"
  IO.FS.writeFile sshPath (fakeSsh log)
  chmod sshPath.toString 0o755
  let lingerPath := fakebin / "linger"
  IO.FS.writeFile lingerPath fakeLinger
  chmod lingerPath.toString 0o755
  -- `:` is `os.pathsep`; fakebin FIRST so it shadows any real ssh. Both spellings
  -- are needed: the `-r` path spawns ssh from inside `linger`, inheriting the
  -- one-shot verb's environment, and the attach path `execvp`s ssh from the pty
  -- child, whose environment the fork carries.
  let path0 := (← IO.getEnv "PATH").getD "/usr/bin:/bin"
  let newPath := s!"{fakebin.toString}:{path0}"
  let procPath : Array (String × Option String) := #[("PATH", some newPath)]
  let ptyPath : Array String := #[s!"PATH={newPath}", s!"LINGER_REMOTE_ARGS={remoteArgs}"]
  let _ ← e.cliEnv procPath #["run", "localsess", "echo local-content"]
  IO.sleep 1000
  -- 1. a duplicate host is a hard error, reported before anything runs (no tty
  -- needed — argv validation precedes the connection attempts)
  let (drc, _, derr) ← e.cliEnv procPath #["-r", s!"{devHost},{devHost}"]
  f := f + (← expect (drc != 0 && has derr dupMsg) "duplicate -r host errors loudly")
  -- 2-7. the overview folds in the remote host's sessions (plain stdout, no tty:
  -- `IO.Process.output` hands the child a null stdin, the Python's DEVNULL)
  let (rrc, out, _) ← e.cliEnv procPath #["-r", s!"{devHost},{deadHost}"]
  let (_, pout, _) ← e.cliEnv procPath #["ls", "--porcelain", "-r", s!"{devHost},{deadHost}"]
  let recs := records pout
  let tag := s!"{goodName}@{devHost}"
  f := f + (← expect (rrc == 0) "`linger -r` exits cleanly")
  f := f + (← expect (has out "localsess") "local session listed alongside remotes")
  -- as a porcelain RECORD as well as in the human listing: the porcelain is what
  -- a peer's own `-r` reads back, so that is where the tag must be well formed
  f :=
    f +
      (← expect (has out tag && recs.contains ("name", tag)) "remote session listed with @host tag")
  -- the expected spelling comes from the sanitizer, not from a copy of its output
  f :=
    f +
      (←
        expect (has out (Linger.Core.Name.sanitize hostileName) && !has out "/etc/passwd")
            "hostile remote name is sanitized (no slashes, no leading dot)")
  f := f + (← expect (!has out "\x1b") "remote escape sequences are scrubbed from the listing")
  f :=
    f +
      (←
        expect
            (!has out s!"@{deadHost}" &&
              !recs.any (fun kv => kv.1 == "name" && kv.2.endsWith s!"@{deadHost}"))
            "unreachable host contributes no rows")
  -- 8+9. `attach name@host` execs `ssh -t -- host linger attach name`. Needs a
  -- tty, so this one is a pty spawn and not `cliEnv`.
  let c1 ← e.spawnEnv ptyPath #["attach", tag] 100 24
  let attached ← drain c1.fd 2000
  let tails ← sshTails log
  f := f + (← expect (hasText attached attachMark) "attach name@host reaches the remote attach")
  f :=
    f +
      (←
        expect (tails.contains [devHost, "linger", "attach", goodName])
            s!"remote attach ssh argv correct ({tails.filter (·.contains "attach")})")
  kill c1.pid 9
  c1.bye (sendDetach := false)
  -- 10. a `user@host` remote (multi-@) round-trips: the host is everything after
  -- the FIRST @, so `attach work@me@dev-a` execs ssh to `me@dev-a` and attaches
  -- `work` (session names never contain @ — sanitize reserves it, and
  -- `sanitize_no_at` is why that is safe to rely on)
  let c2 ← e.spawnEnv ptyPath #["attach", s!"{goodName}@{userHost}"] 100 24
  let _ ← drain c2.fd 2000
  let tails2 ← sshTails log
  f :=
    f +
      (←
        expect (tails2.contains [userHost, "linger", "attach", goodName])
            s!"user@host remote round-trips via first-@ split ({tails2.filter (·.contains userHost)})")
  kill c2.pid 9
  c2.bye (sendDetach := false)
  -- 11. a malformed target (empty host) is a loud error, not a silent local
  -- session. `Main` prints a caught `IO.userError` to stderr, which on a pty is
  -- the same terminal, so the message arrives in the drained bytes.
  let c3 ← e.spawnEnv ptyPath #["attach", "work@"] 100 24
  let bad ← drain c3.fd 1500
  f :=
    f +
      (←
        expect (hasText bad "malformed")
            "trailing @ errors loudly instead of creating a local session")
  kill c3.pid 9
  c3.bye (sendDetach := false)
  for (kind, name) in
    [("path", hostileName), ("separator", "work;printf REMOTE-INJECTED"),
      ("substitution", "work$(printf REMOTE-INJECTED)"), ("quotes", "work 'two words'"),
      ("newline", "work\nprintf REMOTE-INJECTED")] do
    IO.FS.writeFile remoteArgs ""
    let c ← e.spawnEnv ptyPath #["attach", s!"{name}@{devHost}"] 100 24
    let reply ← drain c.fd 2000
    let argv := lines (← IO.FS.readFile remoteArgs)
    f :=
      f +
        (←
          expect
              (argv == ["attach", Linger.Core.Name.sanitize name] && hasText reply attachMark &&
                !hasText reply "REMOTE-INJECTED")
              s!"remote attach sanitizes {kind} before shell interpretation")
    kill c.pid 9
    c.bye (sendDetach := false)
  f :=
    f +
      (←
        expect
            ([["--porcelain", "-r", s!"{devHost},{deadHost}"],
                  ["-r", s!"{devHost},{deadHost}", "--porcelain"],
                  ["--remote", s!"{devHost},{deadHost}", "--porcelain"]].all
              (fun args =>
                Linger.Runtime.Cli.parseLs args == some (true, some [devHost, deadHost])))
            "ls parses explicit hosts in either option order")
  f :=
    f +
      (←
        expect
            (Linger.Runtime.Cli.parseLs ["-r", "--porcelain"] == some (true, some []) &&
              Linger.Runtime.Cli.parseLs ["--porcelain", "--remote"] == some (true, some []) &&
              Linger.Runtime.Cli.parseLs ["-r", "--typo"] == none)
            "ls preserves an option after -r and rejects an unknown option")
  e.killAll #["localsess"]
  verdict e f

end E2E.Remote
