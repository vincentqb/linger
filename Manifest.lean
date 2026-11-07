module

public import Linger.Session.Spec
public import Linger.Target.Spec
public import Linger.Terminal.Spec

/-! # Headline theorems

The guarantees linger must keep, in eight parts:

1. Transparency: a client that attaches shows the session's terminal, losing only history beyond
   the replay budget, and the program reads exactly what its writers sent.
2. Authority and attribution: a connection changes only what its role allows, a name has one
   owner, and every value linger reports has one source, which alone can change it.
3. Exactness: a request takes effect exactly as given, or is refused with a reason and changes
   nothing.
4. Program identity: a session runs exactly the program its creation named, and linger only
   delivers bytes to it.
5. Accountability: every session ends once, with an outcome recorded and reported truthfully to
   anyone who asks, and every request gets a reply or a refusal.
6. Bounded and clean: input cannot raise any buffer, loop or wait past its cap, and nothing a
   session started outlives it.
7. Recovery: resuming from a checkpoint gives back the saved session, less any half-parsed
   control sequence.
8. Clean terminal: what linger writes to a terminal on its own account is safe text or one of
   its fixed sequences, and handing a terminal back leaves it canonical.

Each theorem below is stated over definitions in the components' `Spec` modules and over the
program parts declared below as holes: each hole is `sorry` here, the program supplies it, and
the claims say what it must do. `Theorems/Claims.lean` proves the same statements of the
program's parts, and `./lake comparator` checks that it proves exactly these, that each part has
the declared type, and that no axiom beyond `propext`, `Quot.sound` and `Classical.choice` is
used. Changing a statement or a hole here changes what linger claims. Each part's section says
what it does not claim yet.

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

/-- The session's transition: the state after one event, and the effects it asks the runtime
for, in order. -/
@[expose]
def Linger.Session.step : State → Event → State × List (Effect Replay.Plan) := sorry

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

/-! ## 1. Transparency

The terminals the claims quantify over are those a session can hold: fresh, fed, resized,
quiesced, or read back by the checkpoint decoder, so every claim here also holds of a resumed
session. A client receives the repaint as a stream, in steps of any positive byte budget; each
claim says that the stream ends and that a receiver of the session's size that parses it shows
what the session shows. Not claimed yet: that the receiver keeps showing it as output continues,
and that the program reads exactly the bytes its writers sent. -/

/-- Streaming the repaint of a terminal a session can hold ends, and a receiver of the same size
that parses it ends with the session's dimensions and every row of its screen. -/
theorem replay_grid (budget : Nat) (positive : 0 < budget) (v w : Vt.Vt)
    (hv :
      Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
        (Checkpoint.Decoded Checkpoint.loadBytes) v)
    (hw :
      Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
        (Checkpoint.Decoded Checkpoint.loadBytes) w)
    (hcols : w.colCount = v.colCount) (hrows : w.rowCount = v.rowCount) :
    ∃ bytes,
      Replay.Emits Replay.next budget (Replay.start v) bytes ∧
        (w.feed bytes).colCount = v.colCount ∧
        (w.feed bytes).rowCount = v.rowCount ∧
        ∀ y < v.rowCount, (w.feed bytes).getRow y = v.getRow y := by
  sorry

/-- `replay_grid` rejects a stream that sends nothing: a blank receiver keeps a row the session
painted. -/
theorem replay_grid_rejects_silence :
    ¬∀ (budget : Nat),
        0 < budget →
          ∀ (v w : Vt.Vt),
            Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
                (Checkpoint.Decoded Checkpoint.loadBytes) v →
              Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
                (Checkpoint.Decoded Checkpoint.loadBytes) w →
              w.colCount = v.colCount →
              w.rowCount = v.rowCount →
              ∃ bytes,
                Replay.Emits (fun _ _ => none) budget (Replay.start v) bytes ∧
                  (w.feed bytes).colCount = v.colCount ∧
                  (w.feed bytes).rowCount = v.rowCount ∧
                  ∀ y < v.rowCount, (w.feed bytes).getRow y = v.getRow y := by
  sorry

/-- Streaming the repaint of a terminal a session can hold, with retained history, ends, and a
receiver of the same size that parses it ends with exactly the session's history as the replay
budget fits it. -/
theorem replay_history (budget : Nat) (positive : 0 < budget) (v w : Vt.Vt)
    (hv :
      Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
        (Checkpoint.Decoded Checkpoint.loadBytes) v)
    (hw :
      Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
        (Checkpoint.Decoded Checkpoint.loadBytes) w)
    (hcols : w.colCount = v.colCount) (hrows : w.rowCount = v.rowCount)
    (retained : (Render.sbRows v).isEmpty = false) :
    ∃ bytes,
      Replay.Emits Replay.next budget (Replay.start v) bytes ∧
        (w.feed bytes).scrollback = (Render.sbRows v).toList := by
  sorry

/-- `replay_history` rejects a stream that sends nothing: a receiver without history gets none
of the session's. -/
theorem replay_history_rejects_silence :
    ¬∀ (budget : Nat),
        0 < budget →
          ∀ (v w : Vt.Vt),
            Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
                (Checkpoint.Decoded Checkpoint.loadBytes) v →
              Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
                (Checkpoint.Decoded Checkpoint.loadBytes) w →
              w.colCount = v.colCount →
              w.rowCount = v.rowCount →
              (Render.sbRows v).isEmpty = false →
              ∃ bytes,
                Replay.Emits (fun _ _ => none) budget (Replay.start v) bytes ∧
                  (w.feed bytes).scrollback = (Render.sbRows v).toList := by
  sorry

/-- Outside origin mode, streaming the repaint of a terminal a session can hold ends, and a
receiver of the same size that parses it puts its cursor where the session's is. -/
theorem replay_cursor (budget : Nat) (positive : 0 < budget) (v w : Vt.Vt)
    (hv :
      Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
        (Checkpoint.Decoded Checkpoint.loadBytes) v)
    (hw :
      Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
        (Checkpoint.Decoded Checkpoint.loadBytes) w)
    (hcols : w.colCount = v.colCount) (hrows : w.rowCount = v.rowCount)
    (ho : v.getModes.origin = false) :
    ∃ bytes,
      Replay.Emits Replay.next budget (Replay.start v) bytes ∧
        (w.feed bytes).cursorPos = v.cursorPos := by
  sorry

/-- `replay_cursor` rejects a stream that sends nothing: a receiver keeps its cursor where it was. -/
theorem replay_cursor_rejects_silence :
    ¬∀ (budget : Nat),
        0 < budget →
          ∀ (v w : Vt.Vt),
            Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
                (Checkpoint.Decoded Checkpoint.loadBytes) v →
              Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
                (Checkpoint.Decoded Checkpoint.loadBytes) w →
              w.colCount = v.colCount →
              w.rowCount = v.rowCount →
              v.getModes.origin = false →
              ∃ bytes,
                Replay.Emits (fun _ _ => none) budget (Replay.start v) bytes ∧
                  (w.feed bytes).cursorPos = v.cursorPos := by
  sorry

/-! ## 2. Authority and attribution

A watcher is a client attached without a size. Not claimed yet: that a name has one owner
(proved of a model of the lock protocol, `Claim.at_most_one_owner`, and tested of the daemon),
and which source each reported value has. -/

/-- One client's bytes, however chunked, leave every other client's record unchanged. -/
theorem run_bytes_isolates (s : State) (id : Nat) (chunks : List (List UInt8)) {other : Nat}
    (h : other ≠ id) :
    (Session.trace Session.step s (chunks.map (Event.bytes id))).1.client? other =
      s.client? other := by
  sorry

/-- `run_bytes_isolates` rejects a session that forgets every client on any event. -/
theorem run_bytes_isolates_rejects_reset :
    ¬∀ (s : State) (id : Nat) (chunks : List (List UInt8)) {other : Nat},
        other ≠ id →
          (Session.trace
                  (fun _ _ => (State.boot (Vt.Vt.init 1 1) [] [], ([] : List (Effect Replay.Plan))))
                  s (chunks.map (Event.bytes id))).1.client?
              other =
            s.client? other := by
  sorry

/-- A watcher can look and leave, and nothing else: whatever bytes it sends, however chunked,
leave the terminal and the labels unchanged, and every effect they cause is a message to the
watcher, its own disconnection or a checkpoint. -/
theorem run_readonly (s : State) (id : Nat) (chunks : List (List UInt8)) {c : Client}
    (hc : s.client? id = some c) (attached : c.attached = true) (watcher : c.sizer = false) :
    (Session.trace Session.step s (chunks.map (Event.bytes id))).1.terminal = s.terminal ∧
      (Session.trace Session.step s (chunks.map (Event.bytes id))).1.labelList = s.labelList ∧
      ∀ eff ∈ (Session.trace Session.step s (chunks.map (Event.bytes id))).2,
        (∃ m, eff = .send id m) ∨ eff = .close id ∨ eff = .checkpoint := by
  sorry

/-- `run_readonly` rejects a session that ends itself on any event, a watcher's included. -/
theorem run_readonly_rejects_kill :
    ¬∀ (s : State) (id : Nat) (chunks : List (List UInt8)) {c : Client},
        (fun (_ : State) (i : Nat) => some ({ id := i, attached := true } : Client)) s id = some c →
          c.attached = true →
          c.sizer = false →
          (Session.trace (fun s _ => (s, ([.killChild] : List (Effect Replay.Plan)))) s
                  (chunks.map (Event.bytes id))).1.terminal =
              s.terminal ∧
            (Session.trace (fun s _ => (s, ([.killChild] : List (Effect Replay.Plan)))) s
                  (chunks.map (Event.bytes id))).1.labelList =
              s.labelList ∧
            ∀
              eff ∈
                (Session.trace (fun s _ => (s, ([.killChild] : List (Effect Replay.Plan)))) s
                    (chunks.map (Event.bytes id))).2,
              (∃ m, eff = .send id m) ∨ eff = .close id ∨ eff = .checkpoint := by
  sorry

/-! ## 3. Exactness

Not claimed yet: that a session starts in the directory it was given (a failed `chdir` falls
back to `$HOME`) and with the environment it was given (the program inherits the caller's). -/

/-- Validation accepts exactly the valid names, and returns each unchanged. -/
theorem check_eq_some_iff (s result : String) :
    Name.check s = some result ↔ result = s ∧ Name.Valid s := by sorry

/-- `check_eq_some_iff` rejects a validator that accepts every name, the empty one included. -/
theorem check_eq_some_iff_rejects_any :
    ¬∀ (s result : String), (fun s => some s) s = some result ↔ result = s ∧ Name.Valid s := by
  sorry

/-- The command linger runs on a remote host parses, in the literal POSIX shell model, as
exactly `linger`, the verb and every supplied word, with no other shell action. -/
theorem command_argv (verb : String) (words : List String) :
    Remote.Shell.Words (Remote.command verb words).toList
      (("linger" :: verb :: words).map String.toList) := by
  sorry

/-- `command_argv` rejects an empty command line, which parses as no words. -/
theorem command_argv_rejects_empty :
    ¬∀ (verb : String) (words : List String),
        Remote.Shell.Words ((fun (_ : String) (_ : List String) => "") verb words).toList
          (("linger" :: verb :: words).map String.toList) := by
  sorry

/-! ## 4. Program identity

Not claimed yet: that `linger run` starts the program it names (it starts `$SHELL` and types the
words into it, joined with spaces), and that a resumed session starts in the directory requested
(it starts in the checkpoint's). -/

/-! ## 5. Accountability

Not claimed yet: that whoever asks after a session ends hears its outcome. The name's end record
keeps it, a record always gives a reader an answer (`Record.answer_isSome`), and suites test the
files and locks around it. The session refuses a message it does not know (`onMsg_unknown`), and
`info` reports each ending with its own fields (`outcomeFields_injective`). -/

/-- When the session's program ends, every client attached to the session or waiting for its end
is told how the program ended and then the status a shell would report for that ending, and the
daemon's last effect is its exit. -/
theorem step_ended_reports (s : State) (o : Outcome) {c : Client} (hc : c ∈ s.roster)
    (listening : c.attached = true ∨ c.waiting = true) :
    [Effect.send c.id (.ended o), Effect.send c.id (.exited o.status)] <:+:
        (Session.step s (.childExited o)).2 ∧
      (Session.step s (.childExited o)).2.getLast? = some .exit := by
  sorry

/-- `step_ended_reports` rejects a session that reports a status alone, which cannot tell a
death by signal from an exit code. -/
theorem step_ended_reports_rejects_status :
    ¬∀ (s : State) (o : Outcome) {c : Client},
        c ∈ (fun (_ : State) => [({ id := 0, attached := true } : Client)]) s →
          c.attached = true ∨ c.waiting = true →
          [Effect.send c.id (.ended o), Effect.send c.id (.exited o.status)] <:+:
              ((fun s _ => (s, ([.send 0 (.exited 1), .exit] : List (Effect Replay.Plan)))) s
                  (Event.childExited o)).2 ∧
            ((fun s _ => (s, ([.send 0 (.exited 1), .exit] : List (Effect Replay.Plan)))) s
                  (Event.childExited o)).2.getLast? =
              some .exit := by
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
      Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
        (Checkpoint.Decoded Checkpoint.loadBytes) r.st.terminal) :
    ∃ out,
      Driver.run execute r events = .ok out ∧
        Bounds State.roster State.labelList State.scanner out.st ∧
        Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
          (Checkpoint.Decoded Checkpoint.loadBytes) out.st.terminal := by
  sorry

/-- `run_total_safe` rejects a driver that ignores its events and lands on a state past the
label cap, read through labels that overflow on any terminal other than the starting one. -/
theorem run_total_safe_rejects_jump :
    ¬∀ {World ε : Type}
        (execute :
          State → World → (eff : Effect Replay.Plan) → Except ε (World × Driver.Reply eff)),
        Driver.Responds execute →
          ∀ (r : Driver.Result State World) (events : List Event),
            Bounds State.roster
                (fun st =>
                  if st.terminal.colCount = 80 then [] else List.replicate (maxLabels + 1) ("", ""))
                State.scanner r.st →
              Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
                (Checkpoint.Decoded Checkpoint.loadBytes) r.st.terminal →
              ∃ out,
                Driver.jump (State.boot (Vt.Vt.init 1 1) [] []) execute r events = .ok out ∧
                  Bounds State.roster
                    (fun st =>
                      if st.terminal.colCount = 80 then []
                      else List.replicate (maxLabels + 1) ("", ""))
                    State.scanner out.st ∧
                  Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
                    (Checkpoint.Decoded Checkpoint.loadBytes) out.st.terminal := by
  sorry

/-! ## 6. Bounded and clean

`run_total_safe` keeps the session's clients, labels, frame decoders and pty scanner within their
caps. Not claimed yet, though suites test it: that when a session ends, no process of its terminal
session remains. The daemon sends SIGHUP to each, then SIGKILL to those still running a second
later, and reaps the program last, so the program's pid, which is the session's id, stays
reserved until then. A process that leaves the session with `setsid`, or runs as another user,
is out of reach, and on macOS, or Linux before 5.3, a pid freed and reused between reading its
session and signalling it could receive the signal. -/

/-- The pty input queue never owes more than its cap, through any offers and flushes. -/
theorem reachableIn_bound {cap : Nat} {b : Buf.Buf}
    (h : Buf.InputReach Buf.Buf.empty Buf.bufOffer Buf.bufAdvance cap b) : Buf.owedLen b ≤ cap := by
  sorry

/-- `reachableIn_bound` rejects an input queue that appends every offer, whatever its cap. -/
theorem reachableIn_bound_rejects_append :
    ¬∀ {cap : Nat} {b : Buf.Buf},
        Buf.InputReach Buf.Buf.empty Buf.bufEnqueue Buf.bufAdvance cap b → Buf.owedLen b ≤ cap := by
  sorry

/-- A client output queue the daemon keeps never owes more than its cap, through any appends
and flushes. -/
theorem reachableOut_bound {cap : Nat} {b : Buf.Buf}
    (h : Buf.OutputReach Buf.Buf.empty Buf.bufEnqueue Buf.bufAdvance cap b) :
    Buf.owedLen b ≤ cap := by sorry

/-- `reachableOut_bound` rejects an output queue that never asks to cut its client. -/
theorem reachableOut_bound_rejects_uncut :
    ¬∀ {cap : Nat} {b : Buf.Buf},
        Buf.OutputReach Buf.Buf.empty (fun cap b more => ((Buf.bufEnqueue cap b more).1, false))
            Buf.bufAdvance cap b →
          Buf.owedLen b ≤ cap := by
  sorry

/-! ## 7. Recovery

Every claim in section 1 covers the terminals the checkpoint decoder returns, so any bytes on
disk resume a session those claims cover, or are refused. -/

/-- Saving a checkpoint of a terminal a session can hold and loading it back returns the same
checkpoint, with the terminal's partial parser state forgotten. -/
theorem loadBytes_saveBytes_live (c : Checkpoint.Ckpt Vt.Vt)
    (h :
      Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
        (Checkpoint.Decoded Checkpoint.loadBytes) c.vt) :
    Checkpoint.loadBytes (Checkpoint.saveBytes c) = some { c with vt := c.vt.quiesce } := by sorry

/-- `loadBytes_saveBytes_live` rejects a decoder that refuses every file. -/
theorem loadBytes_saveBytes_live_rejects_refusal :
    ¬∀ (c : Checkpoint.Ckpt Vt.Vt),
        Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
            (Checkpoint.Decoded (fun _ => none : ByteArray → Option (Checkpoint.Ckpt Vt.Vt))) c.vt →
          (fun _ => none : ByteArray → Option (Checkpoint.Ckpt Vt.Vt)) (Checkpoint.saveBytes c) =
            some { c with vt := c.vt.quiesce } := by
  sorry

/-- A daemon resumed from the saved checkpoint of a terminal a session can hold boots with that
terminal, its partial parser state forgotten, and the checkpoint's first `maxLabels` labels. -/
theorem resume_restores (c : Checkpoint.Ckpt Vt.Vt)
    (h :
      Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
        (Checkpoint.Decoded Checkpoint.loadBytes) c.vt)
    (metaKv : List (String × String)) :
    let saved := Checkpoint.loadBytes (Checkpoint.saveBytes c)
    let booted := State.boot (bootVt (saved.map (·.vt))) ((saved.map (·.labels)).getD []) metaKv
    booted.terminal = c.vt.quiesce ∧ booted.labelList = c.labels.take maxLabels := by
  sorry

/-- `resume_restores` rejects a daemon that boots a fresh terminal whatever its checkpoint holds. -/
theorem resume_restores_rejects_fresh :
    ¬∀ (c : Checkpoint.Ckpt Vt.Vt),
        Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
            (Checkpoint.Decoded Checkpoint.loadBytes) c.vt →
          ∀ (metaKv : List (String × String)),
            let saved := Checkpoint.loadBytes (Checkpoint.saveBytes c)
            let booted :=
              State.boot ((fun (_ : Option Vt.Vt) => Vt.Vt.init 1 1) (saved.map (·.vt)))
                ((saved.map (·.labels)).getD []) metaKv
            booted.terminal = c.vt.quiesce ∧ booted.labelList = c.labels.take maxLabels := by
  sorry

/-! ## 8. Clean terminal

Not claimed yet: one statement covering every sequence linger writes on its own account; each
printer below is claimed on its own. -/

/-- `linger capture` prints UTF-8 text with no C0 control, DEL or C1 control character other
than its line terminators. -/
theorem screenText_text (v : Vt.Vt) :
    ∃ cs : List Char,
      Render.screenText v = cs.flatMap String.utf8EncodeChar ∧
        ∀ c ∈ cs,
          c = '\n' ∨ (0x20 ≤ c.toNat ∧ c.toNat ≠ 0x7F ∧ ¬(0x80 ≤ c.toNat ∧ c.toNat < 0xA0)) := by
  sorry

/-- `screenText_text` rejects a capture that prints an escape byte. -/
theorem screenText_text_rejects_escape :
    ¬∀ (v : Vt.Vt),
        ∃ cs : List Char,
          (fun (_ : Vt.Vt) => ([0x1B] : Render.Bytes)) v = cs.flatMap String.utf8EncodeChar ∧
            ∀ c ∈ cs,
              c = '\n' ∨
                (0x20 ≤ c.toNat ∧ c.toNat ≠ 0x7F ∧ ¬(0x80 ≤ c.toNat ∧ c.toNat < 0xA0)) := by
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

/-- `leave_canonical_all` rejects a handback that is a lone escape byte, which leaves the
parser inside a control sequence. -/
theorem leave_canonical_all_rejects_escape :
    ¬∀ (w : Vt.Vt),
        2 ≤ w.rowCount →
          (w.feed ([0x1B] : Render.Bytes)).atBoundary = true ∧
            (w.feed ([0x1B] : Render.Bytes)).getModes = ({} : Vt.Modes) ∧
            Vt.stick (w.feed ([0x1B] : Render.Bytes)) =
              { rows := w.rowCount, top := 0, bot := w.rowCount - 1, g0 := false, g1 := false,
                so := false, alt := false } ∧
            (w.feed ([0x1B] : Render.Bytes)).getPen = ({} : Vt.Pen) ∧
            (w.feed ([0x1B] : Render.Bytes)).windowTitle = "" := by
  sorry

end Linger.Claims
