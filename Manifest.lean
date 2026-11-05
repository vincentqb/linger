module

public import Linger.Session.Spec
public import Linger.Target.Spec
public import Linger.Terminal.Spec

/-! # Headline theorems

The guarantees linger must keep. Each is stated over definitions in the components' `Spec`
modules and over the program parts declared below as holes: each hole is `sorry` here, the
program supplies it, and the claims say what it must do. `Theorems/Claims.lean` proves the same
statements of the program's parts, and `./lake comparator` checks that it proves exactly these,
that each part has the declared type, and that no axiom beyond `propext`, `Quot.sound` and
`Classical.choice` is used. Changing a statement or a hole here changes what linger claims.

Not claimed: anything about the IO executors, the C shim or the operating system, which suites
test instead. -/

public section

open Linger.Session Linger.Target Linger.Terminal

/-! ## The program's parts

### Session targets -/

/-- The session-name validator every command applies to the names it is given. -/
@[expose]
def Linger.Target.Name.check : String → Option String := sorry

/-- The command line linger runs on a remote host, for a verb and its words. -/
@[expose]
def Linger.Target.Remote.command : String → List String → String := sorry

/-! ### Terminal -/

/-- A terminal: the emulator state a session keeps of its pty's screen. -/
@[expose]
def Linger.Terminal.Vt.Vt : Type := sorry

/-- A fresh terminal with the given columns and rows. -/
@[expose]
def Linger.Terminal.Vt.Vt.init : (cols rows : Nat) → Vt.Vt := sorry

/-- The terminal after it parses the given output bytes. -/
@[expose]
def Linger.Terminal.Vt.Vt.feed : Vt.Vt → List UInt8 → Vt.Vt := sorry

/-- The terminal resized to the given columns and rows. -/
@[expose]
def Linger.Terminal.Vt.Vt.resize : Vt.Vt → (cols rows : Nat) → Vt.Vt := sorry

/-- The terminal with its partial parser state forgotten, as a checkpoint saves it. -/
@[expose]
def Linger.Terminal.Vt.Vt.quiesce : Vt.Vt → Vt.Vt := sorry

/-- The terminals the checkpoint decoder accepts. -/
@[expose]
def Linger.Terminal.Vt.Vt.Decodable : Vt.Vt → Prop := sorry

/-- The screen's width in columns. -/
@[expose]
def Linger.Terminal.Vt.Vt.colCount : Vt.Vt → Nat := sorry

/-- The screen's height in rows. -/
@[expose]
def Linger.Terminal.Vt.Vt.rowCount : Vt.Vt → Nat := sorry

/-- A row of the screen, by its index from the top. -/
@[expose]
def Linger.Terminal.Vt.Vt.getRow : Vt.Vt → Nat → Vt.Row := sorry

/-- The cursor's column and row. -/
@[expose]
def Linger.Terminal.Vt.Vt.cursorPos : Vt.Vt → Nat × Nat := sorry

/-- The terminal's modes. -/
@[expose]
def Linger.Terminal.Vt.Vt.getModes : Vt.Vt → Vt.Modes := sorry

/-- The pen new text is drawn with. -/
@[expose]
def Linger.Terminal.Vt.Vt.getPen : Vt.Vt → Vt.Pen := sorry

/-- The rows scrolled off the main screen, oldest first. -/
@[expose]
def Linger.Terminal.Vt.Vt.scrollback : Vt.Vt → List Vt.Row := sorry

/-- The terminal's scroll region, character sets and screen selection. -/
@[expose]
def Linger.Terminal.Vt.stick : Vt.Vt → Vt.Sticky := sorry

/-- The window title the application last set. -/
@[expose]
def Linger.Terminal.Vt.Vt.windowTitle : Vt.Vt → String := sorry

/-- Whether the parser is between control sequences and between characters. -/
@[expose]
def Linger.Terminal.Vt.Vt.atBoundary : Vt.Vt → Bool := sorry

/-- The repaint linger sends a client that attaches to a session with this terminal. -/
@[expose]
def Linger.Terminal.Render.restore : Vt.Vt → Render.Bytes := sorry

/-- The history rows the repaint carries. -/
@[expose]
def Linger.Terminal.Render.sbRows : Vt.Vt → Array Vt.Row := sorry

/-- The screen as text, as `linger capture` prints it. -/
@[expose]
def Linger.Terminal.Render.screenText : Vt.Vt → Render.Bytes := sorry

/-- The sequence linger sends a terminal it hands back. -/
@[expose]
def Linger.Terminal.Render.leaveAnsi : Render.Bytes := sorry

/-- A repaint streamed to a client in bounded chunks. -/
@[expose]
def Linger.Terminal.Replay.Plan : Type := sorry

/-- The stream of a terminal's repaint, captured when a client attaches. -/
@[expose]
def Linger.Terminal.Replay.start : Vt.Vt → Replay.Plan := sorry

/-- The stream's next chunk within a byte budget, and the rest of the stream, or nothing once
the stream has ended. -/
@[expose]
def Linger.Terminal.Replay.next :
    (budget : Nat) → Replay.Plan → Option (Render.Bytes × Replay.Plan) := sorry

/-! ### Sessions -/

/-- A session daemon's state: its terminal, its clients, its labels and its pty scanner. -/
@[expose]
def Linger.Session.State : Type := sorry

/-- The state a daemon boots with, from its terminal, its restored labels and its own metadata. -/
@[expose]
def Linger.Session.State.boot : Vt.Vt → List (String × String) → List (String × String) → State :=
  sorry

/-- The session after a trace of events, and the effects it asks the runtime for, in order. -/
@[expose]
def Linger.Session.run : State → List Event → State × List (Effect Replay.Plan) := sorry

/-- The record of the connection with the given identifier, if it is connected. -/
@[expose]
def Linger.Session.State.client? : State → Nat → Option Client := sorry

/-- The session's terminal. -/
@[expose]
def Linger.Session.State.terminal : State → Vt.Vt := sorry

/-- The session's clients. -/
@[expose]
def Linger.Session.State.roster : State → List Client := sorry

/-- The session's labels. -/
@[expose]
def Linger.Session.State.labelList : State → List (String × String) := sorry

/-- The state of the scanner the pty's output passes through. -/
@[expose]
def Linger.Session.State.scanner : State → Mediation.Scan := sorry

/-- The terminal a daemon boots with, given the one its checkpoint restored, if any. -/
@[expose]
def Linger.Session.bootVt : Option Vt.Vt → Vt.Vt := sorry

/-- The daemon's event driver: it handles a batch of events in order and executes each event's
effects through the given interpreter, which reports disconnects and checkpoint failures back
as events. -/
@[expose]
def Linger.Session.Driver.run :
    {m : Type → Type} →
      [Monad m] →
      {World : Type} →
      (State → World → (eff : Effect Replay.Plan) → m (World × Driver.Reply eff)) →
        Driver.Result State World → List Event → m (Driver.Result State World) := sorry

/-- The bytes a checkpoint is saved as. -/
@[expose]
def Linger.Session.Checkpoint.saveBytes : Checkpoint.Ckpt Vt.Vt → ByteArray := sorry

/-- The checkpoint some bytes decode to, if they are one. -/
@[expose]
def Linger.Session.Checkpoint.loadBytes : ByteArray → Option (Checkpoint.Ckpt Vt.Vt) := sorry

/-- A byte queue the daemon keeps: its pty's input, or a client's output. -/
@[expose]
def Linger.Session.Buf.Buf : Type := sorry

/-- The empty queue. -/
@[expose]
def Linger.Session.Buf.Buf.empty : Buf.Buf := sorry

/-- The pty input queue offered some bytes under a cap, and whether it dropped them. -/
@[expose]
def Linger.Session.Buf.bufOffer : (cap : Nat) → Buf.Buf → ByteArray → Buf.Buf × Bool := sorry

/-- A client output queue with some bytes appended under a cap, and whether the daemon must cut
the client. -/
@[expose]
def Linger.Session.Buf.bufEnqueue : (cap : Nat) → Buf.Buf → ByteArray → Buf.Buf × Bool := sorry

/-- The queue after the writer got the given number of bytes out. -/
@[expose]
def Linger.Session.Buf.bufAdvance : Buf.Buf → Nat → Buf.Buf := sorry

/-- How many bytes the queue still owes. -/
@[expose]
def Linger.Session.Buf.owedLen : Buf.Buf → Nat := sorry

namespace Linger.Claims

/-! ## Session targets -/

/-- Validation accepts exactly the valid names, and returns each unchanged. -/
theorem check_eq_some_iff (s result : String) :
    Name.check s = some result ↔ result = s ∧ Name.Valid s := by sorry

/-- Distinct accepted session names cannot alias: validation never maps two different names to
the same one. -/
theorem check_no_alias {a b name : String} (ha : Name.check a = some name)
    (hb : Name.check b = some name) : a = b := by sorry

/-- The command linger runs on a remote host parses, in the literal POSIX shell model, as
exactly `linger`, the verb and every supplied word, with no other shell action. -/
theorem command_argv (verb : String) (words : List String) :
    Remote.Shell.Words (Remote.command verb words).toList
      (("linger" :: verb :: words).map String.toList) := by
  sorry

/-! ## Terminal -/

/-- Repainting a terminal a session can hold into any other such terminal of the same size
reproduces its screen: the receiver ends with the same dimensions and every row. -/
theorem restore_grid_reachable (v w : Vt.Vt)
    (hv : Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable v)
    (hw : Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable w)
    (hcols : w.colCount = v.colCount) (hrows : w.rowCount = v.rowCount) :
    (w.feed (Render.restore v)).colCount = v.colCount ∧
      (w.feed (Render.restore v)).rowCount = v.rowCount ∧
      ∀ y < v.rowCount, (w.feed (Render.restore v)).getRow y = v.getRow y := by
  sorry

/-- Repainting a terminal a session can hold, with retained history, into another such terminal
of the same size gives the receiver exactly the session's history as the replay budget fits
it. -/
theorem restore_sb_reachable (v w : Vt.Vt)
    (hv : Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable v)
    (hw : Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable w)
    (hcols : w.colCount = v.colCount) (hrows : w.rowCount = v.rowCount)
    (hne : (Render.sbRows v).isEmpty = false) :
    (w.feed (Render.restore v)).scrollback = (Render.sbRows v).toList := by sorry

/-- Outside origin mode, repainting a terminal a session can hold into another such terminal
of the same size puts the receiver's cursor where the session's is. -/
theorem restore_cursor_reachable (v w : Vt.Vt)
    (hv : Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable v)
    (hw : Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable w)
    (hcols : w.colCount = v.colCount) (hrows : w.rowCount = v.rowCount)
    (ho : v.getModes.origin = false) : (w.feed (Render.restore v)).cursorPos = v.cursorPos := by
  sorry

/-- Streaming a repaint with any positive byte budget per step ends, and its chunks, each within
the budget, concatenate to exactly the complete repaint `Render.restore v`. -/
theorem start_faithful (budget : Nat) (positive : 0 < budget) (v : Vt.Vt) :
    Replay.Emits Replay.next budget (Replay.start v) (Render.restore v) := by sorry

/-- `linger capture` prints UTF-8 text with no C0 control, DEL or C1 control character other
than its line terminators. -/
theorem screenText_text (v : Vt.Vt) :
    ∃ cs : List Char,
      Render.screenText v = cs.flatMap String.utf8EncodeChar ∧
        ∀ c ∈ cs,
          c = '\n' ∨ (0x20 ≤ c.toNat ∧ c.toNat ≠ 0x7F ∧ ¬(0x80 ≤ c.toNat ∧ c.toNat < 0xA0)) := by
  sorry

/-- The sequence linger sends a terminal it hands back leaves any terminal at least two rows
tall between control sequences, with default modes and pen, the whole screen as its scroll
region, ASCII character sets with G0 selected, the main screen current and an empty title. -/
theorem leave_canonical_all (w : Vt.Vt) (h2 : 2 ≤ w.rowCount) :
    (w.feed Render.leaveAnsi).atBoundary = true ∧
      (w.feed Render.leaveAnsi).getModes = ({} : Vt.Modes) ∧
      Vt.stick (w.feed Render.leaveAnsi) =
        { rows := w.rowCount, top := 0, bot := w.rowCount - 1, g0 := false, g1 := false,
          so := false, alt := false } ∧
      (w.feed Render.leaveAnsi).getPen = ({} : Vt.Pen) ∧
      (w.feed Render.leaveAnsi).windowTitle = "" := by
  sorry

/-! ## Sessions -/

/-- Saving a checkpoint of a terminal a session can hold and loading it back returns the same
checkpoint, with the terminal's partial parser state forgotten. -/
theorem loadBytes_saveBytes_live (c : Checkpoint.Ckpt Vt.Vt)
    (h : Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable c.vt) :
    Checkpoint.loadBytes (Checkpoint.saveBytes c) = some { c with vt := c.vt.quiesce } := by sorry

/-- A daemon resumed from any bytes on disk boots a terminal a live session can hold. -/
theorem liveReachableVt_resumeVt (b : ByteArray) :
    Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable
      (bootVt ((Checkpoint.loadBytes b).map (·.vt))) := by
  sorry

/-- When each external operation returns a typed result, every finite batch of events
completes without an uncaught exception, keeping the session within its bounds and its
terminal one a live session can hold. Disconnects and checkpoint failures are permitted
results. -/
theorem run_total_safe {World ε : Type}
    (execute : State → World → (eff : Effect Replay.Plan) → Except ε (World × Driver.Reply eff))
    (hw : Driver.Responds execute) (r : Driver.Result State World) (events : List Event)
    (hb : Bounds State.roster State.labelList State.scanner r.st)
    (hlive :
      Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable r.st.terminal) :
    ∃ out,
      Driver.run execute r events = .ok out ∧
        Bounds State.roster State.labelList State.scanner out.st ∧
        Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable
          out.st.terminal := by
  sorry

/-- One client's input bytes, however chunked, leave every other client's record unchanged. -/
theorem run_bytes_isolates (s : State) (id : Nat) (chunks : List (List UInt8)) {other : Nat}
    (h : other ≠ id) : (run s (chunks.map (Event.bytes id))).1.client? other = s.client? other := by
  sorry

/-- An attached client that gave no size cannot drive the session: whatever bytes it sends,
however chunked, never write to the pty, resize it or change the terminal. -/
theorem run_readonly (s : State) (id : Nat) (chunks : List (List UInt8)) {c : Client}
    (hc : s.client? id = some c) (attached : c.attached = true) (watcher : c.sizer = false) :
    (run s (chunks.map (Event.bytes id))).1.terminal = s.terminal ∧
      ∀ eff ∈ (run s (chunks.map (Event.bytes id))).2,
        (∀ bytes, eff ≠ .writePty bytes) ∧ ∀ cols rows, eff ≠ .resizePty cols rows := by
  sorry

/-- The pty input queue never owes more than its cap, through any offers and flushes. -/
theorem reachableIn_bound {cap : Nat} {b : Buf.Buf}
    (h : Buf.InputReach Buf.Buf.empty Buf.bufOffer Buf.bufAdvance cap b) : Buf.owedLen b ≤ cap := by
  sorry

/-- A client output queue the daemon keeps never owes more than its cap, through any appends
and flushes. -/
theorem reachableOut_bound {cap : Nat} {b : Buf.Buf}
    (h : Buf.OutputReach Buf.Buf.empty Buf.bufEnqueue Buf.bufAdvance cap b) :
    Buf.owedLen b ≤ cap := by sorry

/-- In the lock-protocol model, two daemons or offline readers that share a socket or checkpoint
resource are never active at once, across any interleaving of acquisition, release and reuse. -/
theorem at_most_one_owner {s : Claim.State} (reached : Claim.Reachable s) {a b resource : Nat}
    {left right : Claim.Lease} (ha : s.active a = some left) (hb : s.active b = some right)
    (leftUses : left.Uses resource) (rightUses : right.Uses resource) : a = b := by sorry

/-! ## What the parts show

These pin the operations and observations the claims above are stated over, so that the claims
cannot hold of parts that do nothing: in general where the behavior is simple, and on short
inputs to a fresh terminal where it is not.

### Terminal -/

/-- A fresh terminal has the requested size, clamped to between 1 and 1000, blank rows, the
cursor at the top left, default modes and pen, no history, the whole screen as its scroll
region, ASCII character sets with G0 selected, the main screen current, an empty title, and its
parser between control sequences and characters. -/
theorem init_observed (cols rows : Nat) :
    (Vt.Vt.init cols rows).colCount = Vt.clampDim cols ∧
      (Vt.Vt.init cols rows).rowCount = Vt.clampDim rows ∧
      (∀ y < Vt.clampDim rows,
        (Vt.Vt.init cols rows).getRow y = Array.replicate (Vt.clampDim cols) ({} : Vt.Cell)) ∧
      (Vt.Vt.init cols rows).cursorPos = (0, 0) ∧
      (Vt.Vt.init cols rows).getModes = {} ∧
      (Vt.Vt.init cols rows).getPen = {} ∧
      (Vt.Vt.init cols rows).scrollback = [] ∧
      Vt.stick (Vt.Vt.init cols rows) =
        { rows := Vt.clampDim rows, top := 0, bot := Vt.clampDim rows - 1, g0 := false, g1 := false,
          so := false, alt := false } ∧
      (Vt.Vt.init cols rows).windowTitle = "" ∧ (Vt.Vt.init cols rows).atBoundary = true := by
  sorry

/-- A resize sets the clamped size, keeps the cursor within it, resets the scroll region to the
whole screen, and keeps the history, modes, pen, title, character sets, screen selection and
parser state. -/
theorem resize_observed (v : Vt.Vt) (cols rows : Nat) :
    (v.resize cols rows).colCount = Vt.clampDim cols ∧
      (v.resize cols rows).rowCount = Vt.clampDim rows ∧
      (v.resize cols rows).cursorPos =
        (min v.cursorPos.1 (Vt.clampDim cols - 1), min v.cursorPos.2 (Vt.clampDim rows - 1)) ∧
      Vt.stick (v.resize cols rows) =
        { Vt.stick v with
          rows := Vt.clampDim rows, top := 0, bot := Vt.clampDim rows - 1 } ∧
      (v.resize cols rows).scrollback = v.scrollback ∧
      (v.resize cols rows).getModes = v.getModes ∧
      (v.resize cols rows).getPen = v.getPen ∧
      (v.resize cols rows).windowTitle = v.windowTitle ∧
      (v.resize cols rows).atBoundary = v.atBoundary := by
  sorry

/-- Forgetting partial parser state puts the parser between control sequences and characters,
and keeps everything the terminal shows. -/
theorem quiesce_observed (v : Vt.Vt) :
    v.quiesce.atBoundary = true ∧
      v.quiesce.colCount = v.colCount ∧
      v.quiesce.rowCount = v.rowCount ∧
      (∀ y, v.quiesce.getRow y = v.getRow y) ∧
      v.quiesce.cursorPos = v.cursorPos ∧
      v.quiesce.getModes = v.getModes ∧
      v.quiesce.getPen = v.getPen ∧
      v.quiesce.scrollback = v.scrollback ∧
      Vt.stick v.quiesce = Vt.stick v ∧ v.quiesce.windowTitle = v.windowTitle := by
  sorry

/-- Printing `A` on a fresh two-column, one-row terminal puts it under the cursor, moves the
cursor right and makes it the line `linger capture` prints; a line feed on that bottom row then
moves the row into the history, which the repaint carries. -/
theorem print_observed :
    ((Vt.Vt.init 2 1).feed [0x41]).getRow 0 = #[{ base := 'A' }, {}] ∧
      ((Vt.Vt.init 2 1).feed [0x41]).cursorPos = (1, 0) ∧
      Render.screenText ((Vt.Vt.init 2 1).feed [0x41]) = [0x41, 0x0A] ∧
      ((Vt.Vt.init 2 1).feed [0x41, 0x0A]).scrollback = [#[{ base := 'A' }, {}]] ∧
      Render.sbRows ((Vt.Vt.init 2 1).feed [0x41, 0x0A]) = #[#[{ base := 'A' }, {}]] := by
  sorry

/-- On a fresh terminal, SGR 1 makes the pen bold, DECSET 6 turns on origin mode, OSC 2 sets the
window title, DECSTBM sets the scroll region, `ESC ( 0` and `ESC ) 0` give G0 and G1 the DEC
line-drawing set and SO shifts to G1, DECSET 1049 switches to the alternate screen, and a lone
ESC leaves the parser inside a control sequence. -/
theorem controls_observed :
    ((Vt.Vt.init 2 1).feed [0x1B, 0x5B, 0x31, 0x6D]).getPen = { bold := true } ∧
      ((Vt.Vt.init 2 1).feed [0x1B, 0x5B, 0x3F, 0x36, 0x68]).getModes = { origin := true } ∧
      ((Vt.Vt.init 2 1).feed [0x1B, 0x5D, 0x32, 0x3B, 0x74, 0x07]).windowTitle = "t" ∧
      Vt.stick ((Vt.Vt.init 1 3).feed [0x1B, 0x5B, 0x32, 0x3B, 0x33, 0x72]) =
        { rows := 3, top := 1, bot := 2, g0 := false, g1 := false, so := false, alt := false } ∧
      Vt.stick ((Vt.Vt.init 1 3).feed [0x1B, 0x28, 0x30, 0x1B, 0x29, 0x30, 0x0E]) =
        { rows := 3, top := 0, bot := 2, g0 := true, g1 := true, so := true, alt := false } ∧
      Vt.stick ((Vt.Vt.init 1 3).feed [0x1B, 0x5B, 0x3F, 0x31, 0x30, 0x34, 0x39, 0x68]) =
        { rows := 3, top := 0, bot := 2, g0 := false, g1 := false, so := false, alt := true } ∧
      ((Vt.Vt.init 2 1).feed [0x1B]).atBoundary = false := by
  sorry

/-! ### Sessions -/

/-- A daemon boots with the terminal its checkpoint restored, or a fresh 80×24 one, no clients,
its first `maxLabels` restored labels and an idle pty scanner. -/
theorem boot_observed (vt : Vt.Vt) (labels metaKv : List (String × String)) :
    bootVt none = Vt.Vt.init 80 24 ∧
      bootVt (some vt) = vt ∧
      (State.boot vt labels metaKv).terminal = vt ∧
      (State.boot vt labels metaKv).roster = [] ∧
      (State.boot vt labels metaKv).labelList = labels.take maxLabels ∧
      (State.boot vt labels metaKv).scanner = .ground := by
  sorry

/-- A session handles a trace one event at a time, and a client's record is the first in its
roster with the client's identifier. -/
theorem run_observed (s : State) (ev : Event) (evs : List Event) (id : Nat) :
    run s [] = (s, []) ∧
      run s (ev :: evs) =
        ((run (run s [ev]).1 evs).1, (run s [ev]).2 ++ (run (run s [ev]).1 evs).2) ∧
      s.client? id = s.roster.find? (·.id == id) := by
  sorry

/-- A connection the session has room for joins the end of its roster as a fresh record, and one
past `maxClients` is closed without joining; a closed connection leaves no record; pty output
reaches the terminal byte for byte; and a lone ESC from the child puts an idle scanner inside an
escape sequence. -/
theorem events_observed (s : State) (id : Nat) (chunk : List UInt8) :
    (s.roster.length < maxClients → (run s [.connected id]).1.roster = s.roster ++ [{ id }]) ∧
      (maxClients ≤ s.roster.length →
        (run s [.connected id]).1.roster = s.roster ∧ Effect.close id ∈ (run s [.connected id]).2) ∧
      (run s [.closed id]).1.client? id = none ∧
      (run s [.ptyOut chunk]).1.terminal = s.terminal.feed chunk ∧
      (s.scanner = .ground → (run s [.ptyOut [0x1B]]).1.scanner = .esc) := by
  sorry

/-- When every effect succeeds, the driver ends in the state `run` computes from the same events,
unless one of them asks the daemon to exit. -/
theorem driver_observed {World : Type}
    (execute : State → World → (eff : Effect Replay.Plan) → Id (World × Driver.Reply eff))
    (succeeds : ∀ st w eff, (execute st w eff).run.2 = Driver.success eff)
    (r : Driver.Result State World) (events : List Event) (active : r.exiting = false)
    (stays : Effect.exit ∉ (run r.st events).2) :
    (Driver.run execute r events).run.st = (run r.st events).1 ∧
      (Driver.run execute r events).run.exiting = false := by
  sorry

/-- What the daemon's byte queues owe: nothing at first; an offer to the pty input queue drops a
frame that would pass the cap and otherwise appends it; an append to a client output queue
always appends and reports whether the backlog passed the cap; a flush removes the bytes
written. -/
theorem buf_observed (cap n : Nat) (b : Buf.Buf) (more : ByteArray) :
    Buf.owedLen Buf.Buf.empty = 0 ∧
      (Buf.bufOffer cap b more).2 = decide (Buf.owedLen b + more.size > cap) ∧
      Buf.owedLen (Buf.bufOffer cap b more).1 =
        (if Buf.owedLen b + more.size > cap then Buf.owedLen b else Buf.owedLen b + more.size) ∧
      (Buf.bufEnqueue cap b more).2 = decide (Buf.owedLen b + more.size > cap) ∧
      Buf.owedLen (Buf.bufEnqueue cap b more).1 = Buf.owedLen b + more.size ∧
      Buf.owedLen (Buf.bufAdvance b n) = Buf.owedLen b - n := by
  sorry

end Linger.Claims
