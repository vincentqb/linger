module

public import Linger.Session
public import Linger.Session.Checkpoint
public import Linger.Session.Driver
public import Linger.Session.Spec
public import Linger.Target.Spec
public import Linger.Terminal.Render
public import Linger.Terminal.Replay
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

/-! ## The program's parts -/

/-- The session-name validator every command applies to the names it is given. -/
@[expose]
def Linger.Target.Name.check : String → Option String := sorry

/-- The command line linger runs on a remote host, for a verb and its words. -/
@[expose]
def Linger.Target.Remote.command : String → List String → String := sorry

namespace Linger.Claims

open Linger.Session Linger.Target Linger.Terminal

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
theorem restore_grid_reachable (v w : Vt.Vt) (hv : Vt.LiveReachableVt v) (hw : Vt.LiveReachableVt w)
    (hcols : w.colCount = v.colCount) (hrows : w.rowCount = v.rowCount) :
    (w.feed (Render.restore v)).colCount = v.colCount ∧
      (w.feed (Render.restore v)).rowCount = v.rowCount ∧
      ∀ y < v.rowCount, (w.feed (Render.restore v)).getRow y = v.getRow y := by
  sorry

/-- Repainting a terminal a session can hold, with retained history, into another such terminal
of the same size gives the receiver exactly the session's history as the replay budget fits
it. -/
theorem restore_sb_reachable (v w : Vt.Vt) (hv : Vt.LiveReachableVt v) (hw : Vt.LiveReachableVt w)
    (hcols : w.colCount = v.colCount) (hrows : w.rowCount = v.rowCount)
    (hne : (Render.sbRows v).isEmpty = false) :
    (w.feed (Render.restore v)).scrollback = (Render.sbRows v).toList := by sorry

/-- Outside origin mode, repainting a terminal a session can hold into another such terminal
of the same size puts the receiver's cursor where the session's is. -/
theorem restore_cursor_reachable (v w : Vt.Vt) (hv : Vt.LiveReachableVt v)
    (hw : Vt.LiveReachableVt w) (hcols : w.colCount = v.colCount) (hrows : w.rowCount = v.rowCount)
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
theorem loadBytes_saveBytes_live (c : Checkpoint.Ckpt) (h : Vt.LiveReachableVt c.vt) :
    Checkpoint.loadBytes (Checkpoint.saveBytes c) = some { c with vt := c.vt.quiesce } := by sorry

/-- A daemon resumed from any bytes on disk boots a terminal a live session can hold. -/
theorem liveReachableVt_resumeVt (b : ByteArray) :
    Vt.LiveReachableVt (bootVt ((Checkpoint.loadBytes b).map (·.vt))) := by sorry

/-- When each external operation returns a typed result, every finite batch of events
completes without an uncaught exception, keeping the session within its bounds and its
terminal one a live session can hold. Disconnects and checkpoint failures are permitted
results. -/
theorem run_total_safe {World ε : Type}
    (execute : State → World → (eff : Effect) → Except ε (World × Driver.Reply eff))
    (hw : Driver.Responds execute) (r : Driver.Result World) (events : List Event)
    (hb : Bounded r.st) (hlive : LiveVt r.st) :
    ∃ out, Driver.run execute r events = .ok out ∧ Bounded out.st ∧ LiveVt out.st := by sorry

/-- One client's input bytes, however chunked, leave every other client's record unchanged. -/
theorem run_bytes_isolates (s : State) (id : Nat) (chunks : List (List UInt8)) {other : Nat}
    (h : other ≠ id) : (run s (chunks.map (Event.bytes id))).1.client? other = s.client? other := by
  sorry

/-- The pty input queue never owes more than its cap, through any offers and flushes. -/
theorem reachableIn_bound {cap : Nat} {b : Buf.Buf} (h : Buf.ReachableIn cap b) :
    Buf.owedLen b ≤ cap := by sorry

/-- A client output queue the daemon keeps never owes more than its cap, through any appends
and flushes. -/
theorem reachableOut_bound {cap : Nat} {b : Buf.Buf} (h : Buf.ReachableOut cap b) :
    Buf.owedLen b ≤ cap := by sorry

/-- In the lock-protocol model, two daemons or offline readers that share a socket or checkpoint
resource are never active at once, across any interleaving of acquisition, release and reuse. -/
theorem at_most_one_owner {s : Claim.State} (reached : Claim.Reachable s) {a b resource : Nat}
    {left right : Claim.Lease} (ha : s.active a = some left) (hb : s.active b = some right)
    (leftUses : left.Uses resource) (rightUses : right.Uses resource) : a = b := by sorry

end Linger.Claims
