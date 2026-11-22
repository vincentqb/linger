module

public import Linger.App.CoreSpec
import Linger.App.CoreCode.Commands
import Linger.Os.CoreCode.Answer
import Linger.Target.CoreCode.Remote
import Terminal.CoreSpec

public section

/-! # Linger.App.Api — a command line as a request, and a request as what it does

**The model is the interface.** A command line names its operation by its command's word, the
row `Commands.lookup` finds, and `parse` reads the words after it as that operation's typed
`Request`, or as no request, a usage error; `plan` gives the transition the request takes, the
message it sends each session's daemon or the pure step it runs, which the command line's shell
and the Lean API execute and no other path does; and `answer` gives what the command exits with,
from what it found (`op_meaning`). -/

namespace Linger.App.Api

/-- The listing's options: an optional `--porcelain`, and either `-r` with its hosts or the names
of the sessions to list, in any order, every word after `--` a name, as `Remote.targetOperands`
places one that starts with `-`. `-r` followed by a `-`-prefixed token (or nothing) means "use the
file"; `-r hosts` is an explicit comma list. `none` on any other option, and on names with
`-r`. -/
def parseLs (args : List String) : Option (Bool × Option (List String) × List String) :=
  let rec go : List String → Option (Bool × Option (List String) × List String)
    | [] => some (false, none, [])
    | "--" :: names => some (false, none, names)
    | "--porcelain" :: rest => (go rest).map fun (_, r, n) => (true, r, n)
    | "-r" :: rest =>
      match rest with
      | h :: more =>
        if h.startsWith "-" then (go (h :: more)).map fun (p, _, n) => (p, some [], n)
        else (go more).map fun (p, _, n) => (p, some (h.splitOn ","), n)
      | [] => some (false, some [], [])
    | word :: rest =>
      if word.startsWith "-" then none else (go rest).map fun (p, r, n) => (p, r, word :: n)
  match go args with
  | some (_, some _, _ :: _) => none
  | parsed => parsed

/-- What `ls` reports for its options (`parseLs`): `--summary` or `--resurrect` alone, or a
listing of every session or of the named ones. -/
def parseView (args : List String) : Option View :=
  if args = ["--summary"] then some .summary
  else
    if args = ["--resurrect"] then some .resurrect
    else
      match parseLs args with
      | some (porcelain, hosts, []) => some (.every porcelain hosts)
      | some (porcelain, _, names) => some (.named porcelain names)
      | none => none

/-- A size the emulator keeps as it is, 1 to 1000, so that the pty cannot disagree with it. -/
def parseSize (text : String) : Option Nat :=
  match text.toNat? with
  | some n => if Terminal.Vt.clampDim n = n then some n else none
  | none => none

/-- An optional `flag`, then a target as `Remote.targetArgs` reads it, and the words after it. -/
def flagged (flag : String) (args : List String) : Bool × Option (String × List String) :=
  if args.head? = some flag then (true, Linger.Target.Remote.targetArgs args.tail)
  else (false, Linger.Target.Remote.targetArgs args)

/-- The words after an operation's command, read as that operation's request, or `none` for words
it does not take. -/
def parseOp : Commands.Op → List String → Option Request
  | .attach, args =>
    match flagged "--read-only" args with
    | (true, some (target, [])) => some (.attach true target [])
    | (false, some (target, command)) => some (.attach false target command)
    | _ => none
  | .list, args => (parseView args).map .list
  | .start, target :: program :: args => some (.start target program args)
  | .start, _ => none
  | .resume, [target] => some (.resume target)
  | .resume, _ => none
  | .send, target :: words =>
    if words = ["-"] then some (.send target .stdin)
    else if words = [] then none else some (.send target (.text words))
  | .send, [] => none
  | .detach, [target] => some (.detach target)
  | .detach, _ => none
  | .kill, [target] => some (.kill target)
  | .kill, _ => none
  | .rename, [target, new] => some (.rename target new)
  | .rename, _ => none
  | .capture, args =>
    match flagged "--history" args with
    | (history, some (target, [])) => some (.capture history target)
    | _ => none
  | .resize, [target, cols, rows] =>
    match parseSize cols, parseSize rows with
    | some cols, some rows => some (.resize target cols rows)
    | _, _ => none
  | .resize, _ => none
  | .wait, targets =>
    if targets = [] ∨ targets.any (·.startsWith "-") then none else some (.wait targets)
  | .upgrade, targets => some (.upgrade targets)
  | .serve, [] => some .serve
  | .serve, _ => none

/-- The request a session command line makes: its first word's command (`Commands.lookup`), and
the rest as that command's operation reads it (`parseOp`). -/
def parse : List String → Option Request
  | word :: args => (Commands.lookup word).bind fun command => parseOp command.op args
  | [] => none

/-- Why the words after an operation's command name no request, when its usage line alone does
not say it: a read-only attach given a command, or a size the emulator would clamp. -/
def complaint : Commands.Op → List String → Option String
  | .attach, "--read-only" :: args =>
    match Linger.Target.Remote.targetArgs args with
    | some (_, _ :: _) => some "read-only attach does not accept a command"
    | _ => none
  | .resize, [_, cols, rows] =>
    match cols.toNat?, rows.toNat? with
    | some _, some _ => some "size must be 1..1000 (the emulator clamps at 1000)"
    | _, _ => none
  | _, _ => none

/-- The transition a request takes: what its operation means, `Request.act`, the one definition
of it (`op_meaning`). -/
def plan (request : Request) : Act := request.act

/-- What a command answers, whose code is its exit status, for what it found: the answer true of
it, `Found.answer`, the one definition of it. -/
def answer (found : Found) : Os.Answer := found.answer

/-- The worse of two findings of one command's requests, as its exit status should tell: the one
whose answer has the higher code. -/
def worse (a b : Found) : Found := if (answer a).code < (answer b).code then b else a

/-- What the command line writes to standard error for what a command says: `linger: ` and the
text on a line of its own. -/
def Said.render (said : Said) : String :=
  (if said.fresh then "\r\n" else "") ++ "linger: " ++ said.text ++ "\n"

end Linger.App.Api
