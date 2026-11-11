module

public section

/-! # What the status headline theorems mean

A session's status says what linger saw of it, in one glyph: the seven statuses, the observation
a listing row is classified from, and the legend line each status stands for, written as
predicates on that observation independently of the classifier that computes them. -/

namespace Linger.Display.Status

/-- Seven mutually exclusive states, in priority order: a row shows the
first one that applies. -/
inductive Status where
  /-- `?` — no answer: the daemon did not answer, or the saved session could not be read. -/
  | unknown
  /-- `!` — the program ended any other way: a nonzero exit, a signal, or an ending linger did
  not see. -/
  | exitedBad
  /-- `✓` — the program exited 0. It did its job. -/
  | exitedOk
  /-- `~` — no daemon, but a checkpoint is on disk whose program was interrupted before it
  ended: attach resumes it. -/
  | resumable
  /-- `⣿` — new output since the session was last looked at, a bell included, then it stopped. -/
  | wantsYou
  /-- `⣷` — output right now. -/
  | working
  /-- `⣀` — nothing new since you last looked. -/
  | idle
  deriving DecidableEq, Repr, Inhabited

/-- What a row is classified from. Booleans the runtime computes, so the
classifier depends on nothing else — no clock, no filesystem. -/
structure Obs where
  /-- We got a trustworthy answer about this row. -/
  known : Bool := true
  /-- The session's socket is live. -/
  daemonUp : Bool := true
  /-- The status a shell reports for how the program ended, once it has: from the daemon while
  it ends, then from the name's end record, which a socket-less row reads. -/
  exit : Option Nat := none
  /-- Output within the "working" window. -/
  fresh : Bool := false
  /-- Output, or a bell, since the session was last looked at (attach, output while
  attached, or capture). -/
  unseen : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- The legend, as predicates on an observation: the observation each status's line in
`linger help` describes. -/
@[expose]
def Is : Status → Obs → Prop
  | .unknown, o => o.known = false
  | .exitedOk, o => o.known = true ∧ o.exit = some 0
  | .exitedBad, o => o.known = true ∧ ∃ n, o.exit = some n ∧ n ≠ 0
  | .resumable, o => o.known = true ∧ o.exit = none ∧ o.daemonUp = false
  | .working, o => o.known = true ∧ o.exit = none ∧ o.daemonUp = true ∧ o.fresh = true
  | .wantsYou, o =>
    o.known = true ∧ o.exit = none ∧ o.daemonUp = true ∧ o.fresh = false ∧ o.unseen = true
  | .idle, o =>
    o.known = true ∧ o.exit = none ∧ o.daemonUp = true ∧ o.fresh = false ∧ o.unseen = false

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
  a shell reports it: the session's result, until `kill` discards it. -/
  | ended (status : Nat)
  /-- No socket, and the saved session cannot be read: its end record, which says whether its
  program ended, cannot be read. A checkpoint that will not load would be one too, but the
  listing does not load checkpoints. -/
  | broken
  /-- From a peer's porcelain over ssh: whether the peer lists the session live,
  and the peer's own `status` name, read by `Status.ofName`. -/
  | remote (live : Bool) (peerStatus : String)
  /-- A socket whose daemon holds the name, read from the name's end record instead of asking:
  whether the daemon last saw fresh output, and output since the session was last looked at
  (`Session.Record.published`). -/
  | published (fresh unseen : Bool)
  deriving Repr

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

/-- The pieces linger may write. Text and titles are printable. A control sequence selects
graphic rendition (`m`), moves the cursor (`H`), sets the scroll region (`r`), erases the screen
but not its scrollback (`J` with parameters at most 2), resets a mode (`l`), or sets DEC private
mode 7 (autowrap), 25 (cursor shown), 1049 (alternate screen) or 2004 (bracketed paste) (`h`).
An escape ends a string (`\`) or selects the keypad's numeric mode (`>`). No piece asks the
terminal for a reply, resets it or erases its scrollback, and bracketed paste is the one mode a
piece sets that changes what the terminal sends. -/
@[expose]
def Piece.Ok : Piece → Prop
  | .text c => Printable c
  | .csi priv params final =>
    (priv = false ∧
        (final = 0x6D ∨ final = 0x48 ∨ final = 0x72 ∨ (final = 0x4A ∧ ∀ n ∈ params, n ≤ 2))) ∨
      final = 0x6C ∨ (final = 0x68 ∧ priv = true ∧ ∀ n ∈ params, n ∈ [7, 25, 1049, 2004])
  | .title cs => ∀ c ∈ cs, Printable c
  | .esc final => final = 0x5C ∨ final = 0x3E
  | .lf | .cr | .tab | .ascii _ | .shiftIn => True

/-- Bytes made only of pieces linger may write. -/
@[expose]
def Clean (bytes : List UInt8) : Prop :=
  ∃ pieces : List Piece, (∀ p ∈ pieces, p.Ok) ∧ pieces.flatMap Piece.bytes = bytes

end Linger.Display
