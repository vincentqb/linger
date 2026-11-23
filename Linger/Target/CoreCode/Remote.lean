module

import Linger.Target.CoreCode.Name
public import Linger.Target.CoreSpec

public section

/-! # Linger.Target.Remote — other machines' targets, transports and the remotes file

A session verb on a `name@host` target, and the overview (`linger ls -r`), reach the host through
its transport (`transportFor`), which runs `linger serve` there (`argv`): every word linger runs is
the transport's command and those two, and what a command asks of the host it writes as JSON-RPC on
the command's standard input, never as a word, so no shell reads it. A target is split at its
first `@` (`parseTarget`), its name validated without rewriting and its host kept verbatim. -/

namespace Linger.Target.Remote

/-- Drop C0 and C1 controls and DEL from untrusted text: `ls -r --porcelain`
prints a remote `cmd` verbatim, and `Client.replyText` prints a daemon's reason. -/
def scrub (s : String) : String :=
  String.ofList (s.toList.filter (fun c => c.toNat ≥ 32 && (c.toNat < 127 || c.toNat ≥ 160)))

/-- First host that appears more than once (for the error message). -/
def firstDupHost : List String → Option String
  | [] => none
  | h :: t => if t.contains h then some h else firstDupHost t

/-- Validate the `-r` host list. Two rejections, both **loud**, because each is a
configuration mistake with no valid meaning: a repeated host would double-query and
show duplicate rows, and a host with a control byte in it goes into a transport's argv, so
scrubbing it would connect somewhere the user did not name. Reject rather than
silently dedup or rewrite. The overview runs this *before* any connection is
attempted, so a bad list refuses immediately and names the offender. Pure; the `IO`
caller turns `.error` into `IO.userError`.

The message reports the offending host **scrubbed**: it is printed to a terminal,
and echoing the raw bytes back is how a hostile remotes file would inject an escape
sequence through the error path rather than the listing (`terminalListing` covers the
listing; this covers here). -/
def checkHosts (hosts : List String) : Except String (List String) :=
  match firstDupHost hosts with
  | some h => .error s!"remote host '{scrub h}' listed more than once"
  | none =>
    match hosts.find? (!hostClean ·) with
    | some h => .error s!"remote host '{scrub h}' contains a control character"
    | none => .ok hosts

/-- Exact local name and optional host. -/
structure Target where
  /-- The session name: everything before the first `@`. -/
  name : String
  /-- Everything after the first `@`, verbatim, or `none` without one. -/
  host : Option String
  deriving BEq, Repr

/-- One target grammar for command arguments, listed targets and selector creation.
The host is preserved verbatim, including a possible `user@host` suffix. -/
def targetValid (target : String) : Bool :=
  let parts := target.splitOn "@"
  let name := parts.headD ""
  !target.isEmpty && (Linger.Target.Name.accept name).isSome && hostClean target &&
    (parts.tail.isEmpty || !(String.intercalate "@" parts.tail).isEmpty)

/-- Split a target that `targetValid` accepts at its first `@`, and refuse any other
(`parseTarget_exact`). -/
def parseTarget (target : String) : Option Target :=
  if targetValid target then
    let parts := target.splitOn "@"
    some
      { name := parts.headD ""
        host := if parts.tail.isEmpty then none else some (String.intercalate "@" parts.tail) }
  else none

/-- A positional target after optional flags. `--` preserves option-like names;
everything after the target belongs to the command, without reinterpretation. -/
def targetArgs (args : List String) : Option (String × List String) :=
  match args with
  | "--" :: name :: rest => some (name, rest)
  | name :: rest => if name.startsWith "-" then none else some (name, rest)
  | [] => none

/-! ## Transports

A transport is a command that runs linger elsewhere (`Transport.Delivers`): linger runs its words,
then `linger serve`, and nothing else. -/

/-- The transport of a host the remotes file gives no command: ssh, with `-T`, since no command
wants a terminal at the far end, and `--` before the host, so that no host is read as an
option. -/
def ssh (host : String) : Transport := { command := ["ssh", "-T", "--", host] }

/-- **The argv that runs a host's `serve`**: its transport's command, then `linger serve`. -/
def argv (transport : Transport) : List String := transport.command ++ ["linger", "serve"]

/-! ## The remotes file

`$HOME/.config/linger/remotes` (`Env.remotesFile`) names the hosts `ls -r` lists and how linger
reaches each one, one host to a line. A line's words are its runs of characters between blanks,
none quoted, escaped or expanded, since what they mean is the transport's: the host, then the
command that runs linger there, as a command line would hold it before `linger`. A line that is
only a host reaches it with ssh (`ssh`), as such a line always did. An empty line, or one whose
first word starts with `#`, names nothing. -/

/-- A line's words: its runs of characters between blanks, which are ASCII whitespace. -/
def lineWords (line : String) : List String :=
  (line.splitToList Char.isWhitespace).filter (!·.isEmpty)

/-- The transport the words after a host name: ssh when there are none, else those words, every
one of them, as the command that runs linger there. -/
def transportOf (host : String) (rest : List String) : Transport :=
  if rest.isEmpty then ssh host else { command := rest }

/-- What one line of the remotes file says: nothing for an empty line or a comment, else its host
and the transport that reaches it. -/
def configLine (line : String) : Option (String × Transport) :=
  match lineWords line with
  | [] => none
  | host :: rest => if host.startsWith "#" then none else some (host, transportOf host rest)

/-- The remotes file's hosts, in order, each with its transport. A host listed twice or holding a
control character refuses the whole file (`checkHosts`), and so does a command word that holds a
control character: each is a mistake with no valid meaning, named, scrubbed, before any command
runs. -/
def config (lines : List String) : Except String (List (String × Transport)) := do
  let entries := lines.filterMap configLine
  let _ ← checkHosts (entries.map (·.1))
  match entries.find? (fun entry => !entry.2.command.all hostClean) with
  | some (host, _) =>
    .error s!"remote host '{scrub host}': a word of its command holds a control character"
  | none =>
    .ok entries

/-- The transport the remotes file gives `host`, or ssh for a host it does not name. -/
def transportFor (config : List (String × Transport)) (host : String) : Transport :=
  (config.lookup host).getD (ssh host)

end Linger.Target.Remote
