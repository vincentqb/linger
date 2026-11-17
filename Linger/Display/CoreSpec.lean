module

public import Terminal.CoreSpec

public section

/-! # What the status headline theorems mean

A session's status says what linger saw of it, in one glyph: the eight statuses, the observation
a listing row is classified from, and the legend line each status stands for, written as
predicates on that observation independently of the classifier that computes them. -/

namespace Linger.Display.Status

/-- Ten mutually exclusive states. A row shows the first that applies, in the order `?`, the
endings `✓` and `✗`, `~`, `⚑`, then the progress its program declared, `!`, `⣷` or `⣤`, a command
its shell's marks say runs, `⣷`, then `⣿`, `⣀`: a program waiting for you outranks one that says
how it is doing. -/
inductive Status where
  /-- `?` — no answer: the daemon did not answer, or the saved session could not be read. -/
  | unknown
  /-- `✗` — the program ended any other way: a nonzero exit, a signal, or an ending linger did
  not see. -/
  | exitedBad
  /-- `✓` — the program exited 0. It did its job. -/
  | exitedOk
  /-- `~` — no daemon, but a checkpoint is on disk whose program was interrupted before it
  ended: attach resumes it. -/
  | resumable
  /-- `⚑` — since the session was last looked at, its program rang the bell or posted a desktop
  notification, and it is still running: it asks for you. -/
  | asks
  /-- `!` — its program declared that an error stopped its progress, ConEmu's OSC `9;4` state 2,
  and it still runs: it needs you. -/
  | errored
  /-- `⣿` — new lines entered the session's history since it was last looked at, and its program
  neither asks nor says it is working. -/
  | wantsYou
  /-- `⣷` — its program says it is working: it declared progress under way, OSC `9;4` state 1 or
  3, or, declaring none, its shell's marks say a command runs. -/
  | working
  /-- `⣤` — its program declared its progress paused, ConEmu's OSC `9;4` state 4. -/
  | paused
  /-- `⣀` — nothing new since you last looked. -/
  | idle
  deriving DecidableEq, Repr, Inhabited

/-- What a row is classified from. Booleans the runtime computes, so the
classifier depends on nothing else — no clock, no filesystem. Each is a signal's: none is a guess
from timing. -/
structure Obs where
  /-- We got a trustworthy answer about this row. -/
  known : Bool := true
  /-- The session's socket is live. -/
  daemonUp : Bool := true
  /-- The status a shell reports for how the program ended, once it has: from the daemon while
  it ends, then from the name's end record, which a socket-less row reads. -/
  exit : Option Nat := none
  /-- The progress the program last declared, ConEmu's OSC `9;4`, `none` when it declared none
  or removed it. -/
  progress : Option Terminal.Mediation.Progress := none
  /-- The program's shell's marks say a command runs. -/
  running : Bool := false
  /-- New lines entered the session's history since it was last looked at (attach, output while
  attached, or capture). -/
  unseen : Bool := false
  /-- A bell or a desktop notification since the session was last looked at. -/
  asks : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- The legend, as predicates on an observation: the observation each status's line in
`linger help` describes. -/
@[expose]
def Is : Status → Obs → Prop
  | .unknown, o => o.known = false
  | .exitedOk, o => o.known = true ∧ o.exit = some 0
  | .exitedBad, o => o.known = true ∧ ∃ n, o.exit = some n ∧ n ≠ 0
  | .resumable, o => o.known = true ∧ o.exit = none ∧ o.daemonUp = false
  | .asks, o => o.known = true ∧ o.exit = none ∧ o.daemonUp = true ∧ o.asks = true
  | .errored, o =>
    o.known = true ∧ o.exit = none ∧ o.daemonUp = true ∧ o.asks = false ∧ o.progress = some .error
  | .working, o =>
    o.known = true ∧
      o.exit = none ∧
      o.daemonUp = true ∧
      o.asks = false ∧
      (o.progress = some .normal ∨
        o.progress = some .indeterminate ∨ o.progress = none ∧ o.running = true)
  | .paused, o =>
    o.known = true ∧ o.exit = none ∧ o.daemonUp = true ∧ o.asks = false ∧ o.progress = some .paused
  | .wantsYou, o =>
    o.known = true ∧
      o.exit = none ∧
      o.daemonUp = true ∧ o.asks = false ∧ o.progress = none ∧ o.running = false ∧ o.unseen = true
  | .idle, o =>
    o.known = true ∧
      o.exit = none ∧
      o.daemonUp = true ∧ o.asks = false ∧ o.progress = none ∧ o.running = false ∧ o.unseen = false

/-- A wrong classifier: the rule before asks, which lumps a bell and a notification in with the
rest of what a session shows, so a running session that asks shows another status. The headline that a bell
or a notification since the last look makes a running session ask is shown to reject it. -/
@[expose]
def lumped (classify : Obs → Status) (o : Obs) : Status := classify { o with asks := false }

end Linger.Display.Status

namespace Linger.Display.Listing

/-- Where a listing row came from. **A sum type rather than a handful of
`Bool`s on purpose.** The previous signature took `socketPresent`,
`answered` and `ckptLoadable` separately, and a caller passed a literal
`true` for `answered` — so "the daemon did not answer" became unreachable and
a busy session listed as a healthy idle one, even though the theorem about it
was correct. Booleans a caller has to get right are the hazard; each
constructor here carries exactly the facts its case has, so there is no
argument left to pass wrongly. -/
inductive Row where
  /-- A socket accepted the connection; `info` is whatever it replied (possibly
  nothing, if it was too busy). -/
  | live (info : List (String × String))
  /-- No socket, but a checkpoint file is there, and its end record does not say how its
  program ended: the session was interrupted, as by a reboot. -/
  | stale
  /-- No socket, a checkpoint, and an end record saying its program ended with this status, as
  a shell reports it: the session's result, nobody saw it end, until the first attach shows it
  or `kill` discards it. -/
  | ended (status : Nat)
  /-- No socket, and the saved session cannot be read: its end record, which says whether its
  program ended, cannot be read. A checkpoint that will not load would be one too, but the
  listing does not load checkpoints. -/
  | broken
  /-- From a peer's porcelain over ssh: whether the peer lists the session live,
  and the peer's own `status` name, read by `Status.ofName`. -/
  | remote (live : Bool) (peerStatus : String)
  /-- A socket whose daemon holds the name, read from the name's end record instead of asking:
  the progress the daemon last saw its program declare, whether its shell's marks said a command
  runs, new lines in its history since the session was last looked at, and a bell or a
  notification since then (`Session.Record.published`). -/
  | published (progress : Option Terminal.Mediation.Progress) (running unseen asks : Bool)
  deriving Repr

/-- The fields of a listing record a human row reads, each from its one source: the socket's
name; the status and how a saved session ended, from the caller and the name's end record;
`pid` and `cmd`, which tell a busy daemon or a peer's row; `source`, which marks a row a source
linger only reads, as a saved tmux pane's, gives; the description, which only the user
sets, as the field `description`; the title, which the session's program gave its window, the
status text it last gave through `sd_notify`, and the text of its last notification since the
session was last looked at; the command line and exit
status of the last command that finished since then, as its shell's marks reported them; the
login shell and the foreground program, its process and its directory, which the operating system
reports; the seconds since the program last wrote; and the watchers. No other field changes what
a human row shows. -/
@[expose]
def sources : List String :=
  ["name", "status", "state", "saved", "signal", "outcome", "exit", "pid", "cmd", "source",
    "description", "title", "status_text", "notice", "lastcmd", "lastexit", "login", "fg", "fgpid",
    "fgdir", "idle", "clients"]

/-- The fields a human row prints of, each as clean text: every field it reads (`sources`) but
the processes and the login flag, which only decide what it prints. -/
@[expose]
def shown : List String := sources.filter fun key => !["pid", "fgpid", "login"].contains key

/-- How a view lays out its rows, one field to a column: the name column's width, then the width of
each later column, the caption, the foreground program, its directory, the age and the watchers,
all in the display columns a terminal gives them. -/
structure Layout where
  /-- The name column's width: the widest name's. -/
  nameCol : Nat := 0
  /-- The widths of the columns after the name, in order. -/
  widths : List Nat := []
  deriving DecidableEq, BEq, Repr, Inhabited

/-- The display columns each part of a row laid out by `layout` takes: the glyph and a space, the
name column, then each later column with a space on each side, or nothing for a column no row
fills. -/
@[expose]
def Layout.spans (layout : Layout) : List Nat :=
  2 :: layout.nameCol :: layout.widths.map fun w => if w = 0 then 0 else w + 2

/-- The fields each cell after the name reads, in order: the caption, which says how a session
that is not running stands, the program's title or status text or a description an older linger
saved, a notification's text and how the last command ended; the foreground program, which the
caption may already name; its directory, which the caption may already hold; the age, which a
printing session lacks; and the watchers. -/
@[expose]
def cellSources : List (List String) :=
  [["status", "state", "saved", "signal", "outcome", "exit", "pid", "cmd", "source", "description",
      "title", "status_text", "notice", "lastcmd", "lastexit"],
    ["fg", "login", "fgpid", "pid", "cmd", "description", "title", "status_text"],
    ["fgdir", "description", "title", "status_text"], ["status", "idle"], ["clients"]]

/-- The name of the program a command line runs: its first word, after the word's last `/`. -/
@[expose]
def command (line : String) : String := (((line.splitOn " ").headD "").splitOn "/").getLast?.getD ""

end Linger.Display.Listing

namespace Linger.Display

/-- A character a terminal prints: neither a C0 control, DEL nor a C1 control. -/
@[expose]
def Printable (c : Char) : Prop :=
  0x20 ≤ c.toNat ∧ c.toNat ≠ 0x7F ∧ ¬(0x80 ≤ c.toNat ∧ c.toNat < 0xA0)

/-- A number's decimal digits, as bytes, most significant first. -/
@[expose]
def digits (n : Nat) : List UInt8 :=
  if n < 10 then [UInt8.ofNat (0x30 + n)] else digits (n / 10) ++ [UInt8.ofNat (0x30 + n % 10)]
termination_by n
decreasing_by omega

/-- One piece of what linger writes to a terminal on its own account: a character, a line
break or tab, or one of the control sequences linger uses. -/
inductive Piece where
  /-- A character, which must be printable. -/
  | text (c : Char)
  /-- Line feed. -/
  | lf
  /-- Carriage return. -/
  | cr
  /-- Horizontal tab. -/
  | tab
  /-- A control sequence: `ESC [`, `?` when it is private, numeric parameters separated by `;`,
  and a final byte. -/
  | csi (priv : Bool) (params : List Nat) (final : UInt8)
  /-- `ESC ] 2 ;`, a window title, `BEL`. -/
  | title (cs : List Char)
  /-- `ESC` and a final byte. -/
  | esc (final : UInt8)
  /-- `ESC (` or, for G1, `ESC )`, and `B`: ASCII in G0 or G1. -/
  | ascii (g1 : Bool)
  /-- Shift in (`SI`): select G0. -/
  | shiftIn
  /-- `ESC [ 0 SP q` (DECSCUSR 0): the terminal's own cursor shape. -/
  | shapeDefault
  /-- `ESC ] 9 ;`, a desktop notification's text, `ESC \`. -/
  | notify (cs : List Char)
  deriving DecidableEq, Repr

/-- A piece's bytes. -/
@[expose]
def Piece.bytes : Piece → List UInt8
  | .text c => String.utf8EncodeChar c
  | .lf => [0x0A]
  | .cr => [0x0D]
  | .tab => [0x09]
  | .csi priv params final =>
    [0x1B, 0x5B] ++ (if priv then [0x3F] else []) ++
      ((params.map digits).intersperse [0x3B]).flatten ++
      [final]
  | .title cs => [0x1B, 0x5D, 0x32, 0x3B] ++ cs.flatMap String.utf8EncodeChar ++ [0x07]
  | .esc final => [0x1B, final]
  | .ascii g1 => [0x1B, if g1 then 0x29 else 0x28, 0x42]
  | .shiftIn => [0x0F]
  | .shapeDefault => [0x1B, 0x5B, 0x30, 0x20, 0x71]
  | .notify cs => [0x1B, 0x5D, 0x39, 0x3B] ++ cs.flatMap String.utf8EncodeChar ++ [0x1B, 0x5C]

/-- The pieces linger may write. Text, titles and notifications are printable. A control sequence selects
graphic rendition (`m`), moves the cursor (`H`), sets the scroll region (`r`), erases the screen
but not its scrollback (`J` with parameters at most 2), resets a mode (`l`), or sets DEC private
mode 7 (autowrap), 25 (cursor shown), 1049 (alternate screen), 2004 (bracketed paste) or 2026
(synchronized update) (`h`).
An escape ends a string (`\`) or selects the keypad's numeric mode (`>`), and the cursor's shape
goes back to the terminal's own. No piece asks the terminal for a reply, resets it or erases its
scrollback, and bracketed paste is the one mode a piece sets that changes what the terminal
sends. -/
@[expose]
def Piece.Ok : Piece → Prop
  | .text c => Printable c
  | .csi priv params final =>
    (priv = false ∧
        (final = 0x6D ∨ final = 0x48 ∨ final = 0x72 ∨ (final = 0x4A ∧ ∀ n ∈ params, n ≤ 2))) ∨
      final = 0x6C ∨ (final = 0x68 ∧ priv = true ∧ ∀ n ∈ params, n ∈ [7, 25, 1049, 2004, 2026])
  | .title cs | .notify cs => ∀ c ∈ cs, Printable c
  | .esc final => final = 0x5C ∨ final = 0x3E
  | .lf | .cr | .tab | .ascii _ | .shiftIn | .shapeDefault => True

/-- Bytes made only of pieces linger may write. -/
@[expose]
def Clean (bytes : List UInt8) : Prop :=
  ∃ pieces : List Piece, (∀ p ∈ pieces, p.Ok) ∧ pieces.flatMap Piece.bytes = bytes

/-- A wrong order: it keeps rows as they arrived, whatever their statuses. The headline that a
view lists the sessions that want attention first is shown to reject it. -/
@[expose]
def View.arrival {α : Type} (_ : α → Status.Status) (rows : List α) : List α := rows

/-- A wrong order: each status has its own place, a working session's before a quiet one's, so
a row moves whenever its program starts or stops saying it works. The headline that a running session's
row keeps its place is shown to reject it. -/
@[expose]
def View.byActivity {α : Type} (status : α → Status.Status) (rows : List α) : List α :=
  [Status.Status.asks, .unknown, .exitedBad, .errored, .wantsYou, .exitedOk, .working, .paused,
        .idle, .resumable].flatMap
    fun st => rows.filter fun x => status x == st

/-- The first key a view orders rows by, what needs you to act: `⚑` 0, then `✗` 1, `!` 2, `?` 3
and `⣿` 4, and 5 for every status that needs nothing of you. -/
@[expose]
def View.needs : Status.Status → Nat
  | .asks => 0
  | .exitedBad => 1
  | .errored => 2
  | .unknown => 3
  | .wantsYou => 4
  | _ => 5

/-- The second key a view orders rows by, where a session is in its life: running 0, `⣷`, `⣤`
and `⣀` in one place, saved 1, `~`, which a resume runs again, and ended 2, `✓`. A status that
needs you ranks by the first key alone, and takes its session's place: `⚑`, `!` and `⣿` running,
`✗` ended and `?`, of a session linger could not read, with the running ones. -/
@[expose]
def View.lifecycle : Status.Status → Nat
  | .resumable => 1
  | .exitedOk | .exitedBad => 2
  | _ => 0

/-- A wrong order: the one before views ordered by lifecycle, `⚑ ✗ ! ? ⣿`, then the running
sessions, then `✓`, then `~`, so a session that ended sits above one a resume runs again. The
headline that a view is ordered by what needs you, then by lifecycle, is shown to reject it. -/
@[expose]
def View.endedAboveSaved {α : Type} (status : α → Status.Status) (rows : List α) : List α :=
  ([[Status.Status.asks], [.exitedBad], [.errored], [.unknown], [.wantsYou],
          [.working, .paused, .idle], [.exitedOk], [.resumable]] :
        List (List Status.Status)).flatMap
    fun place => rows.filter fun x => place.contains (status x)

/-- A wrong order: the one before views ranked by what needs you to act, `⚑ ? ✗ ! ⣿`, then `✓`,
the running sessions, `⣷`, `⣤` and `⣀` together, then `~`, so a session that ended well sits above
the live ones. The headline that no row that ended well or can only be resumed sits above a live
one is shown to reject it. -/
@[expose]
def View.doneAboveLive {α : Type} (status : α → Status.Status) (rows : List α) : List α :=
  ([[Status.Status.asks], [.unknown], [.exitedBad], [.errored], [.wantsYou], [.exitedOk],
          [.working, .paused, .idle], [.resumable]] :
        List (List Status.Status)).flatMap
    fun place => rows.filter fun x => place.contains (status x)

end Linger.Display

namespace Linger.Display.Alert

open Linger.Display.Status (Status)

/-- A wrong alert: one for every session that asks in each sample, the first included, whether
or not it asked before, and never for the attached session. The headline that an alert fires once
per change into asking is shown to reject it. -/
@[expose]
def everySample (_ : Option (List (String × Status))) (current : List (String × Status))
    (own : String) : List String :=
  (current.filter fun row => row.2 == .asks && row.1 != own).map (·.1)

/-- A wrong alert: one for every session that changed into asking since the previous sample, the
attached session included, whose own bell its terminal already hears. The headline that an
alert never names the attached session is shown to reject it. -/
@[expose]
def withSelf (previous : Option (List (String × Status))) (current : List (String × Status))
    (_ : String) : List String :=
  match previous with
  | none => []
  | some before => (current.filter fun row => row.2 == .asks && !before.contains row).map (·.1)

end Linger.Display.Alert
