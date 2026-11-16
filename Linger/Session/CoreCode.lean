module

public import Linger.Session.CoreCode.Wire
public import Linger.Session.CoreCode.Record
public import Terminal.CoreCode.Vt
public import Terminal.CoreCode.Replay
import Terminal.CoreCode.Mediation
import Terminal.CoreCode.Render

public section

/-! # Linger.Session — the daemon's brain, as data

One daemon = one session = one pty + one `Vt` + attached clients. This
module is the session's decision logic:
`step : State → Event → State × List (Effect Plan)`. The daemon
(`Linger/Session/WorldCode/Daemon.lean`) is a poll loop that turns fds into `Event`s and
`Effect`s into syscalls.

What `step` keeps:
* A session with zero clients still advances; detach never touches the screen; attach
  touches only the dimensions (resize).
* Clients ≤ `maxClients`, record fields ≤ `maxFields`, every stored wire decoder holds at most
  one frame and is not errored (a malformed peer is closed, not buffered), and the pty
  scanner stays within its caps: `Bounds`, which `run_total_safe` (`Challenge.lean`,
  part 5) keeps.
* An `unknown` message is refused and changes nothing (`onMsg_unknown`); the event that
  carries it answers only the refusal and keeps the terminal and the record's fields
  (`step_unknown_refused`, part 5).
-/

namespace Linger.Session

open Terminal
open Linger.Session.Wire (Msg)
open Terminal.Replay (Plan)

/-- Largest payload of one `output` or `infoReply` frame, 64 KiB, and the byte budget of
each replay step. -/
def outputChunk : Nat := 65536

/-- How a daemon ends its program and every other process of the program's terminal session: the
signals it sends, in order, each with the milliseconds it then waits for them to end. SIGHUP
first, as a terminal that hangs up sends, so a program can save its work, then SIGKILL to
whatever outlives a second of it. -/
def ending : List (UInt32 × Nat) := [(1, 1000), (9, 1000)]

/-- The signals that stop a daemon as the system stops linger at logout or shutdown, by number,
the same on Linux and macOS: SIGHUP, SIGINT, SIGQUIT and SIGTERM. -/
def stopSignals : List UInt8 := [1, 2, 3, 15]

/-- What a daemon makes of the bytes its signal pipe carried in one poll round, in the order they
came, each stop signal as its number and each child's end as 0: the first stop signal, if any, and
whether it came before every child's end, so that it ends the session even when the program also
ended in the round. -/
def stopOf (bytes : List UInt8) : Option (UInt8 × Bool) :=
  (bytes.find? stopSignals.contains).map fun signal =>
    (signal, !(bytes.takeWhile (!stopSignals.contains ·)).contains 0)

/-- How long a daemon lets a connection finish the bytes it owes once it closes it, and every
connection once the session has ended: one grace period for both. -/
def drainTimeoutMs : Nat := 3000

/-- How long a daemon's poll sleeps, from the time now and the deadlines the daemon holds: until
the earliest of them, at once for one already past, and for an event however long that takes,
`-1`, when it holds none. A deadline beyond `Int32`'s range of milliseconds, about 24.8 days,
waits the most a poll can, and the daemon then looks again. -/
def pollTimeout (now : Nat) (deadlines : List Nat) : Int32 :=
  (deadlines.min?.map fun due => Int32.ofNat (min (due - now) 2147483647)).getD (-1)

/-- What a daemon does with a write of one kind it asks for off its loop: while one runs, the new
write waits in place of any that waited, so writes never queue and the latest state is the one
that reaches the disk; otherwise it starts now, as the write this returns. -/
def Offloop.ask {R W : Type} (o : Offloop R W) (w : W) : Offloop R W × Option W :=
  if o.running.isSome then ({ o with waiting := some w }, none) else (o, some w)

/-- Maximum encoded info answer, shared by the producer and the CLI accumulator. -/
def infoReplyCap : Nat := 1048576

/-- The session's whole state, sealed: the bookkeeping fields, the unread counter among them,
and every helper that rewrites the state are `private`; the private fields make the anonymous
constructor private too — outside this module and its friends
(`Linger/Session/Proofs/Session.lean`, `Linger/Session/Tests/Session.lean`,
`Linger/App/Proofs/Wait.lean`, via `import all`) a `State` can only be `State.boot`ed
and `step`ped, never forged or field-poked, so
`run_wf`'s well-formedness is a fact about every state the daemon can possess
rather than about the states it politely constructs. `vt`, `fields` and
`metaKv` stay public-read: the checkpoint save hook (`Linger/Session/WorldCode/Resume.lean`) saves
the first two and finds the session's directory through the third. `scan` and `clients` are
public-read too, because the session bounds headline theorems state (`Linger.Session.Bounds`)
read them. -/
structure StateRec where
  /-- The emulator, fed every byte the child writes. -/
  vt : Vt.Vt
  /-- One bounded scanner owned by the PTY-facing virtual terminal. -/
  scan : Terminal.Mediation.Scan := .ground
  /-- The connected clients, in arrival order. -/
  clients : List Client := []
  /-- The fields of the session's record, at most `maxFields`: its description, which only
  `.describe` sets, and those a restored checkpoint holds, as a tmux import's provenance. -/
  fields : List (String × String) := []
  /-- name/pid/created/cwd…, set once by the runtime at boot. -/
  metaKv : List (String × String) := []
  private ended : Option Ending := none
  /-- Persistent screen or record changes since the last checkpoint? -/
  private dirty : Bool := false
  private lastCkptMs : Nat := 0
  /-- monotone attach counter, for size ownership. -/
  private attachSeq : Nat := 0
  /-- Monotone output counter: bumped once per pty-output event. A counter
  rather than a timestamp, so "has anything happened since you looked" is
  determined by the event list alone — `.tick` already carries time for the
  checkpoint clock, but this needs no tick to be *correct*, only to be
  reported. -/
  private outSeq : Nat := 0
  /-- The `outSeq` as of the last look: caught up on attach, on each output while a
  client is attached, and on capture. `outSeq > lookSeq` is "unread", which is a
  property of the **session**, not of a viewer — "last looked" is a session
  event, so no per-client bookkeeping is created for a one-off connection. -/
  private lookSeq : Nat := 0
  /-- Whether the program rang the bell or posted a desktop notification since the last look:
  `⚑`, which `info` reports as `asks`. Output with nobody attached raises it, as the mediator
  hears it, and every look clears it, as it catches `lookSeq` up. -/
  private asking : Bool := false
  /-- The text of the program's last notification since the last look, as the mediator heard
  it, which `info` reports as `notice`. Every look clears it with `asking`. -/
  private notice : Option (List UInt8) := none
  /-- The command the shell's last `C` mark started, with its command line, while no `D` or `A`
  has followed it, as the mediator heard the marks. -/
  private running : Option Mediation.Cmdline := none
  /-- The ending of the shell's last command that finished since the last look, which `info`
  reports as `lastcmd` and `lastexit`: output with nobody attached sets it as the shell's marks
  tell it, a later `C` replaces it, and every look clears it, as it catches `lookSeq` up. -/
  private finished : Option Finished := none
  /-- `outSeq` as of the previous `.tick`. Output since then is what the next tick records as
  the time of the last output (`lastOutMs`), so the output event itself needs no clock. -/
  private tickOutSeq : Nat := 0
  /-- Whether the last output arrived within `freshMs` of the latest tick: `⣷`, which `info`
  reports as `fresh`. -/
  private freshFlag : Bool := false
  /-- When the last output arrived, as the first tick after it saw it; `none` before any. -/
  private lastOutMs : Option Nat := none
  /-- What the daemon last read of the world, as it was about to answer; `none` before it read
  any. -/
  private observed : Option Observation := none

/-- The session's state, as the headline theorems name it: a definition over the sealed record
`StateRec`, because `Challenge.lean` declares the type as a hole the program fills. -/
abbrev State : Type := StateRec

/-- The session's terminal, as the headline theorems observe it. -/
def State.terminal (s : State) : Vt.Vt := s.vt

/-- The connected clients, in arrival order, as the headline theorems observe them. -/
def State.roster (s : State) : List Client := s.clients

/-- The fields of the session's record, as the headline theorems observe them. -/
def State.fieldList (s : State) : List (String × String) := s.fields

/-- The pty scanner's state, as the headline theorems observe it. -/
def State.scanner (s : State) : Mediation.Scan := s.scan

/-- What the session heard of its shell's commands, as the headline theorems observe it: the
command that runs and the ending of the last one that finished since the last look. -/
def State.commands (s : State) : Commands := { running := s.running, finished := s.finished }

-- No `deriving` clause at all. `Inhabited` would need `Inhabited Vt`, a public door out of
-- the `Vt` seal admitting a zero-column screen, and `Repr` would need `Repr Vt`, whose
-- absence is what makes the seal hide reads. A `State` has exactly one door, `State.boot`.

/-- The one public door into a `State`: a fresh or restored emulator, the
restored record fields, the boot-time metadata. Everything else a `State` ever holds
is `step`'s doing (the private fields above make the constructor private).

Restored fields are kept to the record's own and capped HERE: `.describe` enforces
`maxFields`, but `Checkpoint.loadBytes` is deliberately total on arbitrary bytes, so a corrupt
or forged checkpoint could carry any list, and a checkpoint an older linger saved holds the
labels it had, any key. Only `recordField`s are restored, and over the cap, the first
`maxFields` of them. `boot_wf` is the claim; composed with `run_wf`
(`run_boot_wf`), every state the daemon can hold is well-formed. -/
def State.boot (vt : Vt.Vt) (fields : List (String × String)) (metaKv : List (String × String)) :
    State := { vt, fields := (fields.filter (recordField ·.1)).take maxFields, metaKv }

/-- The emulator a daemon boots with: a restored checkpoint's, else a fresh 80×24 screen. -/
def bootVt (restored : Option Vt.Vt) : Vt.Vt := restored.getD (Vt.Vt.init 80 24)

/-- How long output counts as happening right now (`⣷`): from the tick that saw it. -/
def freshMs : Nat := 1000

/-- A `.describe` payload decoded as text. Invalid UTF-8 becomes `""`, which clears the
description: a corrupt payload sets no text it did not carry. -/
private def descriptionText (bs : List UInt8) : String :=
  String.fromUTF8? (ByteArray.mk bs.toArray) |>.getD ""

/-! ## Helpers -/

/-- Consecutive pieces of `n` elements, the last possibly shorter. A list of at most `n`
elements is one piece, as is any list when `n = 0`, so `[]` gives `[[]]`. -/
private def chunksOf {α : Type} (n : Nat) (l : List α) : List (List α) :=
  if _h : l.length ≤ n ∨ n = 0 then [l]
  else
    let rest := chunksOf n (l.drop n)
    l.take n :: rest
termination_by l.length
decreasing_by simp only [List.length_drop]; omega

/-- The record of the connection with this identifier, if it is connected. -/
def State.client? (s : State) (id : Nat) : Option Client := s.clients.find? (·.id == id)

/-- Replace the record that has `c`'s identifier with `c`; a record is never added. -/
private def State.setClient (s : State) (c : Client) : State :=
  { s with clients := s.clients.map (fun c' => if c'.id == c.id then c else c') }

/-- Remove the record of the connection with this identifier. -/
private def State.dropClient (s : State) (id : Nat) : State :=
  { s with clients := s.clients.filter (·.id != id) }

/-- The report a terminal sends a program that enabled focus reporting (private mode 1004) when
its window gains focus (`CSI I`) or loses it (`CSI O`). -/
def focusReport (focused : Bool) : List UInt8 := [0x1B, 0x5B, if focused then 0x49 else 0x4F]

/-- Whether someone can type into the session: a writable client is attached, whatever its size,
as a window has focus while it gets the keys. A watcher cannot type, so it never counts. -/
def State.focused (s : State) : Bool := s.clients.any (fun c => c.attached && c.mode == .writable)

/-- What a client that can type owes the program when it attaches or leaves, from focus `before`:
its focus report, when focus changed and the program enabled focus reporting. A watcher, which
cannot type, owes nothing (`typist` is false). -/
private def focusEffects (typist before : Bool) (s : State) : List (Effect Plan) :=
  if typist && before != s.focused && s.vt.getModes.focusEvents then
    [.writePty (focusReport s.focused)]
  else []

/-- One disconnect transition for EOF and malformed traffic. Decide whether
the last attacher needs a checkpoint before removing its record, and tell a program that
enabled focus reporting when the last client that could type leaves. The record the identifier
finds decides whether the leaver could type, as it does for every message. -/
private def closeClient (s : State) (id : Nat) : State × List (Effect Plan) :=
  let hadAttached := s.clients.any (fun c => c.id == id && c.attached)
  let s' := s.dropClient id
  let focus := focusEffects ((s.client? id).any (·.mode == .writable)) s.focused s'
  if s.dirty && hadAttached && s'.clients.all (fun c => !c.attached) then
    ({ s' with dirty := false }, focus ++ [.checkpoint])
  else (s', focus)

/-- Unread: output arrived while nobody was watching. What
`Status.wantsYou` is derived from — a property of the **session**, since
"last looked" is a session event rather than a viewer attribute, so a one-off
connection creates no state. A bell or a notification is output too, and the session then asks
(`asking`), which outranks it. -/
private def unseen (s : State) : Bool := s.lookSeq < s.outSeq

/-- How much arrived unseen — free from the counter, where a boolean would
have thrown it away. -/
private def behind (s : State) : Nat := s.outSeq - s.lookSeq

/-- What a session hears of its shell's commands in one mark, from what it heard before, the
command that runs and the last ending nobody saw: a prompt ends what ran, a `C` starts a command
and replaces that ending, and a `D` ends the command a `C` started, with its status, and is no
ending with none running. `Commands.hear` is what each mark means. -/
private def hearMark (heard : Option Mediation.Cmdline × Option Finished) :
    Mediation.Mark → Option Mediation.Cmdline × Option Finished
  | .prompt => (none, heard.2)
  | .input => heard
  | .runs cmdline => (some cmdline, none)
  | .finished status =>
    match heard.1 with
    | some cmdline => (none, some ⟨cmdline, status⟩)
    | none => heard

/-- What a tick at `now` observes: output since the previous tick makes `now` the time of the
last output, which stays fresh for `freshMs`. -/
private def State.ticked (s : State) (now : Nat) : State :=
  let lastOut := if s.tickOutSeq < s.outSeq then some now else s.lastOutMs
  { s with
    lastOutMs := lastOut, freshFlag := lastOut.any (now < · + freshMs), tickOutSeq := s.outSeq }

/-- When the session next needs a tick, if ever: when its checkpoint falls due while it has
unsaved changes, and when its last output stops being fresh. `none` when it needs neither, and
the daemon then waits only for events. -/
def State.nextTick (s : State) : Option Nat :=
  let save := if s.dirty then some (s.lastCkptMs + ckptIntervalMs) else none
  let stale := if s.freshFlag then s.lastOutMs.map (· + freshMs) else none
  match save, stale with
  | some a, some b => some (min a b)
  | a, none => a
  | none, b => b

/-- What the daemon sees of the output, which its name's end record publishes for a summary that
reads the record instead of asking: the `fresh`, `unseen` and `asks` that `info` reports
(`infoFields_seen`). -/
def State.seen (s : State) : Seen := ⟨s.freshFlag, unseen s, s.asking⟩

/-- How `info` reports an ending: `exit` holds the status a shell would report, and a field
only a signal or an unseen ending has says which those are, so two endings never read the
same (`outcomeFields_injective`). -/
def outcomeFields : Outcome → List (String × String)
  | .exited code => [("exit", toString code.toNat)]
  | .signaled signal =>
    [("exit", toString (Outcome.signaled signal).status.toNat), ("signal", toString signal.toNat)]
  | .unknown => [("exit", toString Outcome.unknown.status.toNat), ("outcome", "unknown")]

/-- How `info` reports how a session ended: its program's ending as `outcomeFields` reports it, or,
for a session a signal to its daemon saved, `saved` with that signal's number and no `exit`,
since its program has no status to report, so no saved session reads as an ending of its
program (`endingFields_injective`). -/
def endingFields : Ending → List (String × String)
  | .program outcome => outcomeFields outcome
  | .saved signal => [("saved", toString signal.toNat)]

/-- How `info` reports the title the session's program last gave its window: `title`, when it
gave a nonempty one. -/
def titleFields (title : String) : List (String × String) :=
  if title.isEmpty then [] else [("title", title)]

/-- A notification's text as UTF-8, as a window title is read: the longest of its bytes and the
bytes less one, two or three at the end that is UTF-8, since the mediator's cap may cut a
character short; `none` when none is. -/
def noticeText (bytes : List UInt8) : Option String :=
  [0, 1, 2, 3].findSome? fun cut =>
    String.fromUTF8? (ByteArray.mk (bytes.take (bytes.length - cut)).toArray)

/-- How `info` reports the program's last notification since the session was last looked at:
`notice`, its text (`noticeText`), when it has one that is not empty. -/
def noticeFields (notice : Option (List UInt8)) : List (String × String) :=
  match notice.bind noticeText with
  | some text => if text.isEmpty then [] else [("notice", text)]
  | none => []

/-- A command line as text, as a window title is read: the longest of its bytes and the bytes
less one, two or three at the end that is UTF-8, since a cap may cut a character short, followed
by `…` when that is not the whole command line; `none` when no text of it reads. -/
def cmdlineText (cmdline : Mediation.Cmdline) : Option String :=
  match
    [0, 1, 2, 3].findSome? fun cut =>
      (String.fromUTF8?
            (ByteArray.mk (cmdline.bytes.take (cmdline.bytes.length - cut)).toArray)).map
        fun text => (text, cut == 0) with
  | some (text, all) =>
    if text.isEmpty then none else some (if cmdline.whole && all then text else text ++ "…")
  | none => none

/-- How `info` reports the ending of the shell's last command since the session was last looked
at: `lastcmd`, its command line (`cmdlineText`), when one reads, and `lastexit`, the exit status
its `D` gave, when it gave one. -/
def finishedFields : Option Finished → List (String × String)
  | none => []
  | some f =>
    ((cmdlineText f.cmdline).map (("lastcmd", ·))).toList ++
      (f.status.map (("lastexit", toString ·))).toList

/-- How `info` reports the session's present, as the daemon last read it before it answered:
`idle`, the whole seconds since the program last wrote, and `lastout`, that time on the real-time
clock in seconds, once it wrote at all; `login` when the session's program is its login shell;
and the foreground of its terminal, `fg` its words joined by spaces, `fgpid` its process and
`fgdir` its directory, when the operating system reports one. -/
def presentFields (observed : Option Observation) (lastOutMs : Option Nat) :
    List (String × String) :=
  match observed with
  | none => []
  | some o =>
    (match lastOutMs with
      | some t =>
        [("idle", toString ((o.nowMs - t) / 1000)),
          ("lastout", toString (o.wallS - (o.nowMs - t) / 1000))]
      | none => []) ++
      (if o.login then [("login", "true")] else []) ++
      match o.foreground with
      | some fg =>
        [("fg", String.intercalate " " fg.argv), ("fgpid", toString fg.pid), ("fgdir", fg.dir)]
      | none => []

/-- The fields one listing record carries, as a named stage. Split out from
`infoText` because the framing below is only unambiguous if no field contains a
framing byte, and that is a claim about *these* — see `infoText_framing`. -/
def infoFields (s : State) : List (String × String) :=
  s.metaKv ++ [("clients", toString (s.roster.filter (·.attached)).length)]
    -- what a client needs before sending a request this daemon may not serve
    ++
    [("protocol", toString Wire.protocol), ("version", Terminal.Mediation.versionNumber),
      ("handoff", toString Handoff.version), ("renames", "true")]
    -- the observations `Status.classify` needs from the daemon; the rest
    -- (reachability, checkpoint loadability) only the caller can know
    ++
    [("unseen", toString (unseen s)), ("fresh", toString s.freshFlag), ("asks", toString s.asking),
      ("behind", toString (behind s))]
    -- what an agent needs to see the session:
    -- geometry + cursor for `capture`, `alt` for "a full-screen app is live",
    -- `outseq` as the change cursor ("re-capture only when it moved"). Values
    -- are read at reply time, so they are current as of this `.info`.
    ++
    [("cols", toString s.vt.colCount), ("rows", toString s.vt.rowCount),
      ("cursorx", toString s.vt.cursorPos.1), ("cursory", toString s.vt.cursorPos.2),
      ("alt", toString s.vt.inAlt), ("outseq", toString s.outSeq)] ++
    (match s.ended with
    | some ending => endingFields ending
    | none => []) ++
    titleFields s.vt.windowTitle ++
    noticeFields s.notice ++
    finishedFields s.commands.finished ++
    presentFields s.observed s.lastOutMs ++
    s.fields.filter (recordField ·.1)

/-- Frame the fields as `k` TAB `v` LF records.

**The two framing bytes are emitted structurally, and nothing else can produce
them.** Every character of a key or a value goes through `Render.textChar` and
`Render.utf8s`, which replace a C0 control — tab and newline included — with
U+FFFD, and a C1 control too, since `ls --porcelain` prints these records to a terminal. So
a description containing a newline shows a replacement
character instead of **forging an extra record**, and in particular cannot forge a
`status`/`state` pair that the listing would then display as a session's state.

Established here rather than at `.describe`, for the same reason `Render.gridAnsi`
establishes its own pen instead of trusting its callers: a guard at the emit site
needs no invariant about where the field came from, and it covers fields nobody has
added yet. `Status.name_clean` proves the *status* column carries no framing byte;
this is the same promise for every other column.

The records are built as `List UInt8` directly, not through a `String`: a `String` does not
reduce in the kernel, so no theorem could see its bytes, which is the argument in
`packages/terminal/Terminal/CoreCode/Render.lean`'s header. -/
def infoText (s : State) : List UInt8 :=
  (infoFields s).flatMap
    (fun (k, v) =>
      Render.utf8s (k.toList.map Render.textChar) ++ [0x09] ++
        Render.utf8s (v.toList.map Render.textChar) ++
        [0x0A])

/-- Whether a client sizes the session: attached, writable, and with a terminal that has a size.
A watcher never does, and nor does a terminal that has no size yet, whose 0 must not reach the
pty. -/
private def Client.sizes (c : Client) : Bool :=
  c.attached && c.mode == .writable && c.cols != 0 && c.rows != 0

/-- Resize the pty only on behalf of the size owner: of the clients that size the session, the
most recently attached (a watcher or an older mirror must not fight the active user's size). -/
private def sizeOwner (s : State) : Option Client :=
  (s.clients.filter (·.sizes)).foldl
    (fun best c =>
      match best with
      | none => some c
      | some b => if c.seq ≥ b.seq then some c else some b)
    none

/-- One geometry transition for attach, attached resize and control resize.
An exact or clamped same size preserves the whole emulator: resetting its
region and tabs without a winsize change would leave the child unaware.
A genuine change marks the screen dirty and sends the pty the emulator's
effective dimensions, never an unclamped wire value. -/
private def resize (s : State) (cols rows : UInt32) : State × List (Effect Plan) :=
  if
      (s.vt.colCount == cols.toNat && s.vt.rowCount == rows.toNat) ||
        (s.vt.colCount == Vt.clampDim cols.toNat && s.vt.rowCount == Vt.clampDim rows.toNat) then
    (s, [])
  else
    let vt := s.vt.resize cols.toNat rows.toNat
    ({ s with
        vt, dirty := true },
      [.resizePty (UInt32.ofNat vt.colCount) (UInt32.ofNat vt.rowCount)])

/-- Only the size owner applies its size, and only a real one. -/
private def resizeOwned (s : State) (c : Client) : State × List (Effect Plan) :=
  if c.sizes && (sizeOwner s).any (·.id == c.id) then resize s c.cols c.rows else (s, [])

/-- The control-resize decision (`linger resize`, from a NON-attached
connection). The size-owner rule extends rather than
bends: while an attached client sizes the session it always wins (refuse, loudly — a
silent drop would let an agent believe a size it never got); with nobody
sizing it there is nobody to fight, and the requested size applies. The
same-size branch leaves the emulator alone for the attach guard's reason:
`Vt.resize` resets the scroll region and tab ruler unconditionally, and at an
unchanged winsize no SIGWINCH nudges the child to re-establish them. Zero is refused: a zero
dimension is never a size. -/
private def controlResize (s : State) (c : Client) (cols rows : UInt32) :
    State × List (Effect Plan) :=
  if (sizeOwner s).isSome then
    (s, [.send c.id (.err "an attached client owns the size".toUTF8.toList)])
  else
    if cols == 0 || rows == 0 then (s, [.send c.id (.err "size must be nonzero".toUTF8.toList)])
    else
      let r := resize s cols rows
      (r.1, r.2 ++ [.send c.id .done])

/-- Send a byte payload as ≤ 64 KiB `output` frames (`Msg.WF`). -/
private def outputMsgs (id : Nat) (bytes : List UInt8) : List (Effect Plan) :=
  (chunksOf outputChunk bytes).map (fun c => .send id (.output c))

/-- Preflight the whole info answer before emitting any bytes. Accepted answers
are a stream of bounded byte chunks followed by `done`; records and UTF-8 may
cross frames, so consumers decode text only after joining the payloads.
Refusals carry no prefix or `done`, and the diagnostic is bounded too. -/
private def infoMsgs (id : Nat) (bytes : List UInt8) : List (Effect Plan) :=
  if bytes.length > infoReplyCap then
    [.send id (.err ("info reply exceeds the byte limit".toUTF8.toList.take outputChunk))]
  else (chunksOf outputChunk bytes).map (fun c => .send id (.infoReply c)) ++ [.send id .done]

/-- Broadcast presentation bytes to the attached clients.

The empty guard is load-bearing, not defensive tidiness: `chunksOf n [] = [[]]`,
so without it a chunk consisting *entirely* of an owned query — whose visible
bytes are empty by design — would push a zero-length `output` frame to every
attached client on every terminal query. The runtime raises `.ptyOut` only for a
non-empty read, so empty bytes come only from the mediator.
Pinned by `broadcast_empty` and by a Session fixture. -/
private def broadcast (s : State) (bytes : List UInt8) : List (Effect Plan) :=
  if bytes.isEmpty then []
  else s.clients.filter (·.attached) |>.flatMap (fun c => outputMsgs c.id bytes)

/-! ## Message handling (client → daemon) -/

/-- Handle one client message; one query per read is answered (`Client.answered`). A connection's
rights are its mode alone: a watcher, a client that attached read-only, may look and leave,
whatever its size: its keystrokes are dropped and its requests to disconnect every client, end
the session or describe it are refused. -/
private def onMsg (s : State) (c : Client) (m : Msg) : State × List (Effect Plan) :=
  match m with
  | .attach mode cols rows =>
    if c.attached then (s, [.send c.id (.err "already attached".toUTF8.toList)])
    else
      -- the rights are the mode asked for, whatever the size; a watcher mirrors output, and its
      -- keystrokes are dropped
      let typist := mode == .writable
      let before := s.focused
      let c :=
        { c with
          attached := true, mode, seq := s.attachSeq, cols, rows }
      let s :=
        { s.setClient c with
          attachSeq := s.attachSeq + 1, lookSeq := s.outSeq, asking := false, notice := none,
          finished := none }
      let (s, effs) := resizeOwned s c
      -- Capture here: feedMsgs can change the VT again before effects run.
      (s,
        effs ++ focusEffects typist before s ++ [.replay c.id (Replay.start s.vt)] ++
          (match s.ended with
          | some ending => ending.told.map (Effect.send c.id)
          | none => []))
  | .input bytes =>
    -- a watcher's keystrokes are dropped; a control connection (not attached, as `linger send`
    -- opens) is writable
    if c.mode == .readOnly then (s, []) else (s, [.writePty bytes])
  | .resize cols rows =>
    let c :=
      { c with
        cols, rows }
    let s := s.setClient c
    if c.attached then resizeOwned s c
    else
      if c.answered then (s, [.send c.id (.err "one request per read".toUTF8.toList)])
      else
        -- a control connection (`linger resize`): the named stage above owns
        -- the decision, and `controlResize_never_overrides` the invariant
        let c := { c with answered := true }
        controlResize (s.setClient c) c cols rows
  | .detachAll =>
    if c.mode == .readOnly then (s, [.send c.id (.err "read-only".toUTF8.toList)])
    else
      (s,
        (s.clients.filter (·.attached) |>.map (fun c' => Effect.close c'.id)) ++ [.send c.id .done])
  | .kill =>
    -- the program's end, which the runtime answers, ends the session (`.stopped`); the kill's
    -- connection closes, so nothing it sent after the kill takes effect
    if c.mode == .readOnly then (s, [.send c.id (.err "read-only".toUTF8.toList)])
    else (s, [.stopProgram, .close c.id])
  | .info =>
    if c.answered then (s, [.send c.id (.err "one request per read".toUTF8.toList)])
    else (s.setClient { c with answered := true }, infoMsgs c.id (infoText s))
  | .history =>
    if c.answered then (s, [.send c.id (.err "one request per read".toUTF8.toList)])
    else
      (s.setClient { c with answered := true },
        outputMsgs c.id (Render.history s.vt) ++ [.send c.id .done])
  | .screen =>
    -- `linger capture`: the grid only, plain text. Delivering the current
    -- screen IS a look, so it catches the read mark up and clears an ask and an
    -- ending — after a capture,
    -- "output arrived while nobody was watching" is false and `behind` counts
    -- from this moment. `.info` must never do this
    -- (`ls` polls every daemon; a listing that marks everything read destroys
    -- the status column) and `.history` stays an export, not an observation.
    if c.answered then (s, [.send c.id (.err "one request per read".toUTF8.toList)])
    else
      ({ s.setClient { c with answered := true } with
          lookSeq := s.outSeq, asking := false, notice := none, finished := none },
        outputMsgs c.id (Render.screenText s.vt) ++ [.send c.id .done])
  | .wait =>
    match s.ended with
    | some ending => (s, ending.told.map (Effect.send c.id))
    | none => (s.setClient { c with waiting := true }, [])
  | .describe text =>
    if c.mode == .readOnly then (s, [.send c.id (.err "read-only".toUTF8.toList)])
    else
      let text := descriptionText text
      let fields :=
        s.fields.filter (·.1 != "description") ++
          if text.isEmpty then [] else [("description", text)]
      if fields.length > maxFields then (s, [.send c.id (.err "too many fields".toUTF8.toList)])
      else
        ({ s with
            fields, dirty := true },
          [.send c.id .done])
  | .upgrade exe =>
    -- a watcher may not replace the daemon, nor may a client that streams the session; the
    -- runtime carries one upgrade out at a time and refuses the others it is asked for meanwhile
    if c.mode == .readOnly then (s, [.send c.id (.err "read-only".toUTF8.toList)])
    else
      if c.attached then (s, [.send c.id (.err "attached".toUTF8.toList)])
      else (s, [.upgrade c.id exe])
  -- daemon-to-client vocabulary arriving at the daemon is no request and is dropped;
  -- a tag this version does not know is a request it cannot serve, and is refused
  | .output _ | .exited _ | .ended _ | .saved _ | .infoReply _ | .done | .err _ => (s, [])
  | .unknown _ _ => (s, [.send c.id (.err "unknown message".toUTF8.toList)])

/-- How a session ends, whatever ended it: the scanner's pending bytes reach the attached clients,
every client attached or waiting hears how it ended (`Ending.told`), every connection closes, the
name's end record says how it ended, the session's last screen is saved and kept, or discarded,
as `keep` says, and the daemon exits. -/
private def conclude (s : State) (ending : Ending) (keep : Bool) : State × List (Effect Plan) :=
  let flushed := Terminal.Mediation.finish s.scanner
  let s :=
    { s with
      ended := some ending, scan := flushed.2 }
  let flush := broadcast s flushed.1
  let notify :=
    s.clients.filter (fun c => c.attached || c.waiting) |>.flatMap
      (fun c => ending.told.map (Effect.send c.id))
  let closes := s.clients.map (fun c => Effect.close c.id)
  (s,
    flush ++ notify ++ closes ++
      [.record ending.record, if keep then .checkpoint else .dropCheckpoint, .exit])

/-! ## The step function -/

/-- Fold decoded messages through `onMsg`, threading state + effects.
The client record is re-read each round (attach mutates it); a message
after a close for this sender or an exit stops affecting state, even before
the runtime executes those effects. Named so the preservation and stopping
theorems can target it. -/
private def feedMsgs (id : Nat) (msgs : List Msg) (acc : State × List (Effect Plan)) :
    State × List (Effect Plan) :=
  msgs.foldl
    (fun (acc : State × List (Effect Plan)) m =>
      if acc.2.contains (.close id) || acc.2.contains .exit then acc
      else
        match acc.1.client? id with
        | none => acc
        | some c' =>
          let r := onMsg acc.1 c' m
          (r.1, acc.2 ++ r.2))
    acc

/-- `feedMsgs` in time linear in the messages and effects. It checks the incoming
effects for a stop once and then only each message's own, and conses each
message's effects onto a reversed list, where `feedMsgs` rescans and copies every
effect so far for each message. -/
private def feedMsgsTR (id : Nat) (msgs : List Msg) (acc : State × List (Effect Plan)) :
    State × List (Effect Plan) :=
  let r :=
    msgs.foldl
      (fun (r : State × List (Effect Plan) × Bool) m =>
        if r.2.2 then r
        else
          match r.1.client? id with
          | none => r
          | some c' =>
            let out := onMsg r.1 c' m
            (out.1, out.2.reverseAux r.2.1, out.2.contains (.close id) || out.2.contains .exit))
      (acc.1, [], acc.2.contains (.close id) || acc.2.contains .exit)
  (r.1, acc.2 ++ r.2.1.reverse)

/-- `feedMsgs` and `feedMsgsTR` are the same function, so `step`, their only compiled
caller, runs the latter. Local, because a `@[csimp]` theorem must otherwise be public. -/
@[local csimp]
private theorem feedMsgs_eq_feedMsgsTR : @feedMsgs = @feedMsgsTR := by
  funext id msgs acc
  simp only [feedMsgs, feedMsgsTR]
  -- Related accumulators hold the same state, the incoming effects followed by
  -- the reversed ones, and a flag equal to the specification's stop test.
  refine
    (List.foldl_rel (r :=
        fun (b : State × List (Effect Plan)) (c : State × List (Effect Plan) × Bool) =>
        b = (c.1, acc.2 ++ c.2.1.reverse) ∧
          c.2.2 = (b.2.contains (.close id) || b.2.contains .exit))
        ⟨by simp, rfl⟩ ?_).1
  rintro m - b ⟨s, rev, stop⟩ ⟨rfl, hstop⟩
  dsimp only at hstop ⊢
  subst hstop
  split
  · exact ⟨rfl, rfl⟩
  · split
    · exact ⟨rfl, rfl⟩
    · rename_i hx _ _ _
      refine ⟨by simp, ?_⟩
      simp only [List.contains_append, Bool.not_eq_true, Bool.or_eq_false_iff] at hx ⊢
      simp only [hx, Bool.false_or]

/-- The daemon's transition: one event in, the next state and the effects to run. -/
def step (s : State) (ev : Event) : State × List (Effect Plan) :=
  match ev with
  | .connected id =>
    if s.clients.length ≥ maxClients then
      (s, [.send id (.err "too many clients".toUTF8.toList), .close id])
    else ({ s with clients := s.clients ++ [{ id }] }, [])
  | .bytes id chunk =>
    match s.client? id with
    | none => (s, []) -- late bytes from a dropped client
    | some c =>
      let (dec, msgs) := c.decoder.feed chunk
      if dec.errored then
        let (s, effs) := closeClient s id
        (s, .close id :: effs)
      else
        feedMsgs id msgs
          (s.setClient
              { c with
                decoder := dec, answered := false },
            [])
  | .closed id => closeClient s id
  | .ptyOut chunk =>
    -- output while a client is attached is a look: it is seen as it arrives, and a bell, a
    -- notification or a command's ending in it leaves nothing to tell
    let r := Terminal.Mediation.feed s.vt s.scan chunk
    ({ s with
        vt := r.vt, scan := r.scan, dirty := true, outSeq := s.outSeq + 1,
        lookSeq := if s.clients.any (·.attached) then s.outSeq + 1 else s.lookSeq,
        asking := !s.clients.any (·.attached) && (s.asking || r.asks),
        notice := if s.clients.any (·.attached) then none else r.notice.or s.notice,
        running := (r.marks.foldl hearMark (s.running, s.finished)).1,
        finished :=
          if s.clients.any (·.attached) then none
          else (r.marks.foldl hearMark (s.running, s.finished)).2 },
      (if r.replies.isEmpty then [] else [.writePty r.replies]) ++ broadcast s r.visible)
  | .childExited outcome =>
    -- an ended session is a result until someone sees it: told to an attached client, it is
    -- discarded as a kill discards it; with nobody attached its last screen is saved, until the
    -- first attach shows it
    conclude s (.program outcome) (!seenBy s.clients)
  | .stopped outcome =>
    -- a session the daemon stopped, as `kill` asks, ends the same way and is discarded
    conclude s (.program outcome) false
  | .signal signal =>
    -- the environment stopping linger, not the program ending: the daemon stops the program,
    -- then ends the same way, saving the screen the signal found, to resume
    let r := conclude s (.saved signal) true
    (r.1, .stopProgram :: r.2)
  | .tick now =>
    -- the activity fields are refreshed in both branches by one helper: a `let` before the
    -- `if` would hide the `if` from the proofs that `split` on this handler
    if s.dirty && now ≥ s.lastCkptMs + ckptIntervalMs then
      ({ s.ticked now with
          dirty := false, lastCkptMs := now },
        [.checkpoint])
    else (s.ticked now, [])
  | .observed observation => ({ s with observed := some observation }, [])
  | .checkpointFailed =>
    -- Keep the attempt time: retry at the next cadence, without needing more
    -- output and without spinning while storage remains unavailable.
    ({ s with dirty := true }, [])

/-- Removing a client can only take focus away. -/
private theorem focused_dropClient (s : State) (id : Nat) (h : (s.dropClient id).focused = true) :
    s.focused = true := by
  simp only [State.focused, State.dropClient, List.any_eq_true, List.mem_filter] at h ⊢
  obtain ⟨c, ⟨hc, _⟩, hf⟩ := h
  exact ⟨c, hc, hf⟩

/-- Disconnect feedback can request persistence and tell the program it lost focus, but cannot
create more transport work. Used by the driver's termination argument. -/
theorem closed_effects (s : State) (id : Nat) :
    ∀ eff ∈ (step s (.closed id)).2, eff = .checkpoint ∨ eff = .writePty (focusReport false) := by
  have hfocus :
    ∀ eff ∈ focusEffects ((s.client? id).any (·.mode == .writable)) s.focused (s.dropClient id),
      eff = .writePty (focusReport false) := by
    intro eff h
    unfold focusEffects at h
    split at h
    · rename_i hc
      simp only [List.mem_singleton] at h
      subst h
      cases hd : (s.dropClient id).focused
      · rfl
      · simp [focused_dropClient s id hd, hd] at hc
    · simp at h
  intro eff h
  simp only [step, closeClient] at h
  split at h
  · rcases List.mem_append.mp h with h | h
    · exact .inr (hfocus eff h)
    · simp only [List.mem_singleton] at h
      exact .inl h
  · exact .inr (hfocus eff h)

/-- A failed checkpoint marks the state dirty without immediately retrying. -/
theorem checkpointFailed_effects (s : State) : (step s .checkpointFailed).2 = [] := by rfl

/-- The end of a session the daemon stopped asks for no other stop. Used by the driver's
termination argument. -/
theorem stopped_effects (s : State) (outcome : Outcome) :
    ∀ eff ∈ (step s (.stopped outcome)).2, eff ≠ .stopProgram := by
  intro eff h hstop
  subst hstop
  simp only [step, conclude, broadcast, outputMsgs] at h
  split at h <;> simp at h

/-- Fold the supplied event trace through `step`, preserving effect order.
For the runtime this trace consists of the events actually consumed, including
effect feedback: `pump` stops before consuming any event after exit. `run` does
not model that queue or choose its stopping prefix. The state projection is
recursive, so preservation lifts directly from `step`. -/
def run (s : State) : List Event → State × List (Effect Plan)
  | [] => (s, [])
  | ev :: evs =>
    let r := step s ev
    let rest := run r.1 evs
    (rest.1, r.2 ++ rest.2)

end Linger.Session
