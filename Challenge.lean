module

public import Linger.Display.Spec
public import Linger.Session.Spec
public import Linger.Target.Spec
public import Linger.Terminal.Spec

/-! # Headline theorems

The guarantees linger must keep, in ten parts. Each part's section states its headline theorems,
each with a kill, and says what it does not claim yet:

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
9. Work follows events: linger works only in response to an event, a byte, a request, a program
   ending or a deadline an earlier event set, and each event sets at most a fixed number of
   deadlines. An event costs in proportion to its size and its audience, never to how many
   sessions exist, so every linger process goes quiet after the last event. Parts 1 to 8 decide
   what linger does and this one how cheaply: work no event pays for is allowed only where it is
   named, with its bound.
10. Graceful under load: work a request needs never waits on optional work or on another
   session, every wait is bounded and says what it missed, and optional work is skipped or
   coalesced, never queued.

The status rule: a session's status is one glyph for one observation, `⣷` output right now, `⣿`
new output, then it stopped, `⣀` nothing new since you looked, `✓` ended with status 0, `!` ended
any other way, `~` saved with no daemon and `?` no answer, and titles and `ls --summary` count
`⣿`, `!` and `?`. Its section follows the ten parts.

Each theorem below is stated over definitions in the components' `Spec` modules and over the
program parts declared below as holes: each hole is `sorry` here, the program supplies it, and
the claims say what it must do. `Theorems/Solution.lean` proves the same statements of the
program's parts, and `./lake comparator` checks that it proves exactly these, that each part has
the declared type, and that no axiom beyond `propext`, `Quot.sound` and `Classical.choice` is
used. Changing a statement or a hole here changes what linger claims.

Not claimed: anything about the IO executors, the C shim or the operating system, which suites
test instead. -/

public section

open Linger.Display Linger.Session Linger.Target Linger.Terminal

/-! ## The program's parts

### Session targets -/

/-- The session-name validator every command applies to the names it is given. -/
@[expose]
def Linger.Target.Name.check : String → Option String := sorry

/-- The command line linger runs on a remote host, for a verb and its words. -/
@[expose]
def Linger.Target.Remote.command : String → List String → String := sorry

/-- The target and the command's words that `attach` and `capture` read from their arguments. -/
@[expose]
def Linger.Target.Remote.targetArgs : List String → Option (String × List String) := sorry

/-- The operands that place a target in an argv linger builds for itself. -/
@[expose]
def Linger.Target.Remote.targetOperands : String → List String := sorry

/-- One word quoted for a remote POSIX shell. -/
@[expose]
def Linger.Target.Remote.shellQuote : String → String := sorry

/-- The remote host list, checked: the hosts back, or why the list is refused. -/
@[expose]
def Linger.Target.Remote.checkHosts : List String → Except String (List String) := sorry

/-! ### Environment -/

/-- The program a session starts without a command, from `SHELL`. -/
@[expose]
def Linger.Os.Env.shellOf : Option String → String := sorry

/-- The remote hosts file, from `HOME`. -/
@[expose]
def Linger.Os.Env.remotesFile : Option String → Option String := sorry

/-- Whether the detach key detaches, for a read-only attach or a writable one, from
`LINGER_NO_DETACH_KEY`. -/
@[expose]
def Linger.Os.Env.detachEnabled : Bool → Option String → Bool := sorry

/-- Where a resumed session runs, from `HOME`, its saved directory and whether that is still a
directory. -/
@[expose]
def Linger.Os.Env.resumeDir : Option String → String → Bool → Option String := sorry

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

/-- Apply a step as many times as a control sequence's count asks, but at most `cap` times. -/
@[expose]
def Linger.Terminal.Vt.Vt.repeatAtMost : Vt.Vt → (cap count : Nat) → (Vt.Vt → Vt.Vt) → Vt.Vt :=
  sorry

/-- The history rows the repaint carries. -/
@[expose]
def Linger.Terminal.Render.sbRows : Vt.Vt → Array Vt.Row := sorry

/-- The screen as text, as `linger capture` prints it. -/
@[expose]
def Linger.Terminal.Render.screenText : Vt.Vt → Render.Bytes := sorry

/-- The history and then the screen as text, as `linger capture --history` prints them. -/
@[expose]
def Linger.Terminal.Render.history : Vt.Vt → Render.Bytes := sorry

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

/-! ### Statuses -/

/-- The status a listing row shows for what linger observed of its session. -/
@[expose]
def Linger.Display.Status.classify : Status.Obs → Status.Status := sorry

/-- The glyph a status is shown as. -/
@[expose]
def Linger.Display.Status.icon : Status.Status → Char := sorry

/-- The attention summary titles and `ls --summary` show for the statuses of some sessions. -/
@[expose]
def Linger.Display.Status.summary : List Status.Status → String := sorry

/-- A window title from the session's name, the application's title and the attention summary,
within a capacity in characters. -/
@[expose]
def Linger.Display.Title.compose : String → String → String → Nat → String := sorry

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

/-- When the session next needs a tick, if ever: `none` when it waits only for events. -/
@[expose]
def Linger.Session.State.nextTick : State → Option Nat := sorry

/-- The text of the session's `info` reply: one field per line, its key, a tab and its value. -/
@[expose]
def Linger.Session.infoText : State → List UInt8 := sorry

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

/-- What `start` does with a name, given whether a live session and a saved one hold it. -/
@[expose]
def Linger.Session.Start.plan : (live saved : Bool) → Start.Plan := sorry

/-- Whether a daemon started for `start` or `resume` goes on to run the program at its commit
point, given whether it took the request's ticket. -/
@[expose]
def Linger.Session.Start.proceeds : Bool → Bool := sorry

/-- What `start` or `resume` answers about the program once its request is decided, given whether
the command took the request's ticket and whether the program runs. -/
@[expose]
def Linger.Session.Start.answer : Bool → Bool → Start.Answer := sorry

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

namespace Linger

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

/-- DEL bytes, and C0 controls the terminal does not act on, sent between control sequences and
characters change nothing: the terminal neither prints them nor reacts to them. -/
theorem feed_inert (v : Vt.Vt) (bytes : List UInt8) (between : v.atBoundary = true)
    (inert : ∀ b ∈ bytes, b = 0x7F ∨ b < 0x07 ∨ 0x0F < b ∧ b < 0x20 ∧ b ≠ 0x1B) :
    v.feed bytes = v := by sorry

/-- `feed_inert` rejects a terminal that prints DEL as a question mark. -/
theorem feed_inert_rejects_print :
    ¬∀ (v : Vt.Vt) (bytes : List UInt8),
        v.atBoundary = true →
          (∀ b ∈ bytes, b = 0x7F ∨ b < 0x07 ∨ 0x0F < b ∧ b < 0x20 ∧ b ≠ 0x1B) →
          (fun (v : Vt.Vt) (bytes : List UInt8) =>
                v.feed (bytes.map fun b => if b = 0x7F then 0x3F else b))
              v bytes =
            v := by
  sorry

/-! ## 2. Authority and attribution

A watcher is a client attached without a size. Not claimed yet: that a name has one owner
(proved of a model of the lock protocol, `Claim.at_most_one_owner`, and tested of the daemon),
and which source each reported value has. `start` takes no name a session holds
(`start_plan`); the daemon decides that holding the name. -/

/-- `start` takes a name only when no live session holds it and none is saved. Otherwise it
refuses, saying which holds it: a live one first, whose daemon also owns any saved state. -/
theorem start_plan (live saved : Bool) :
    Start.plan live saved = if live then .running else if saved then .saved else .take := by sorry

/-- `start_plan` rejects a `start` that takes every name. -/
theorem start_plan_rejects_take :
    ¬∀ (live saved : Bool),
        (fun (_ _ : Bool) => Start.Plan.take) live saved =
          if live then .running else if saved then .saved else .take := by
  sorry

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

/-- No other account chooses the hosts linger asks: the remote hosts file is under a nonempty
`HOME`, and with `HOME` unset or empty there is none, never a shared fallback. -/
theorem remotesFile_home (home : Option String) :
    Os.Env.remotesFile home = none ↔ home = none ∨ home = some "" := by sorry

/-- `remotesFile_home` rejects a remotes file that falls back to a shared directory. -/
theorem remotesFile_home_rejects_shared :
    ¬∀ (home : Option String),
        (fun (_ : Option String) => some "remotes") home = none ↔ home = none ∨ home = some "" := by
  sorry

/-! ## 3. Exactness

Not claimed yet, though suites test it: that `start` runs its program in the caller's directory
or not at all (125, as `env -C`), with the caller's environment, which only `TERM`,
`TERM_PROGRAM`, `TERM_PROGRAM_VERSION` and `LINGER_SESSION` change, and that a resume says so
when it runs in `$HOME`. -/

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

/-- No two spellings name one session: validation never maps two different strings to the
same name. -/
theorem check_no_alias (a b name : String) (ha : Name.check a = some name)
    (hb : Name.check b = some name) : a = b := by sorry

/-- `check_no_alias` rejects a validator that folds every spelling into one name. -/
theorem check_no_alias_rejects_fold :
    ¬∀ (a b name : String),
        (fun (_ : String) => some "s") a = some name →
          (fun (_ : String) => some "s") b = some name → a = b := by
  sorry

/-- A target linger places in an argv it builds for itself reads back as exactly that name,
with every word after it left to the command, a name that starts with `-` included. -/
theorem targetArgs_targetOperands (name : String) (rest : List String) :
    Remote.targetArgs (Remote.targetOperands name ++ rest) = some (name, rest) := by sorry

/-- `targetArgs_targetOperands` rejects operands that leave the target out. -/
theorem targetArgs_targetOperands_rejects_none :
    ¬∀ (name : String) (rest : List String),
        Remote.targetArgs ((fun (_ : String) => ([] : List String)) name ++ rest) =
          some (name, rest) := by
  sorry

/-- A word linger quotes for the remote shell reads back as exactly that word, and leaves what
follows it, a space or the end, to be read next. -/
theorem shellQuote_roundtrip (s : String) (tail : List Char)
    (boundary : tail = [] ∨ ∃ rest, tail = ' ' :: rest) :
    Remote.Shell.word ((Remote.shellQuote s).toList ++ tail) = some (s.toList, tail) := by sorry

/-- `shellQuote_roundtrip` rejects a word passed to the remote shell unquoted. -/
theorem shellQuote_roundtrip_rejects_bare :
    ¬∀ (s : String) (tail : List Char),
        (tail = [] ∨ ∃ rest, tail = ' ' :: rest) →
          Remote.Shell.word (((fun (s : String) => s) s).toList ++ tail) =
            some (s.toList, tail) := by
  sorry

/-- The remote host list is accepted exactly when no host repeats and none holds a control
character or DEL, and then as given: a bad list is refused, never cleaned up. -/
theorem checkHosts_ok_iff (hosts result : List String) :
    Remote.checkHosts hosts = .ok result ↔
      result = hosts ∧ hosts.Nodup ∧ ∀ x ∈ hosts, Remote.hostClean x = true := by
  sorry

/-- `checkHosts_ok_iff` rejects a check that accepts a host listed twice. -/
theorem checkHosts_ok_iff_rejects_any :
    ¬∀ (hosts result : List String),
        (fun (hosts : List String) => (.ok hosts : Except String (List String))) hosts =
            .ok result ↔
          result = hosts ∧ hosts.Nodup ∧ ∀ x ∈ hosts, Remote.hostClean x = true := by
  sorry

/-- The detach key always detaches a read-only attach, whose only exit it is, and detaches a
writable one exactly when `LINGER_NO_DETACH_KEY` is unset. -/
theorem detach_key (flag : Option String) :
    Os.Env.detachEnabled true flag = true ∧ Os.Env.detachEnabled false flag = flag.isNone := by
  sorry

/-- `detach_key` rejects a detach key that never detaches. -/
theorem detach_key_rejects_never :
    ¬∀ (flag : Option String),
        (fun (_ : Bool) (_ : Option String) => false) true flag = true ∧
          (fun (_ : Bool) (_ : Option String) => false) false flag = flag.isNone := by
  sorry

/-- A resumed session runs in its saved directory while that is a directory; once it is gone,
in a nonempty `HOME`; and with `HOME` unset or empty, nowhere, so the resume refuses. -/
theorem resumeDir_where (home : Option String) (saved dir : String) (set : dir ≠ "") :
    Os.Env.resumeDir home saved true = some saved ∧
      Os.Env.resumeDir (some dir) saved false = some dir ∧
      Os.Env.resumeDir none saved false = none ∧ Os.Env.resumeDir (some "") saved false = none := by
  sorry

/-- `resumeDir_where` rejects a resume that runs in its saved directory once it is gone. -/
theorem resumeDir_where_rejects_gone :
    ¬∀ (home : Option String) (saved dir : String),
        dir ≠ "" →
          (fun (_ : Option String) (saved : String) (_ : Bool) => some saved) home saved true =
              some saved ∧
            (fun (_ : Option String) (saved : String) (_ : Bool) => some saved) (some dir) saved
                false =
              some dir ∧
            (fun (_ : Option String) (saved : String) (_ : Bool) => some saved) none saved false =
              none ∧
            (fun (_ : Option String) (saved : String) (_ : Bool) => some saved) (some "") saved
                false =
              none := by
  sorry

/-! ## 4. Program identity

Not claimed yet, though suites test it: that `start` runs exactly the program and words it is
given, without a shell, and that `resume` runs `$SHELL` again on a saved session's last screen. -/

/-- A session started without a command runs `$SHELL`, or `sh` when `SHELL` is unset or empty,
since an empty word names no program. -/
theorem shellOf_choice (shell : String) (set : shell ≠ "") :
    Os.Env.shellOf (some shell) = shell ∧
      Os.Env.shellOf none = "sh" ∧ Os.Env.shellOf (some "") = "sh" := by
  sorry

/-- `shellOf_choice` rejects a session that ignores `SHELL`. -/
theorem shellOf_choice_rejects_fixed :
    ¬∀ (shell : String),
        shell ≠ "" →
          (fun (_ : Option String) => "sh") (some shell) = shell ∧
            (fun (_ : Option String) => "sh") none = "sh" ∧
            (fun (_ : Option String) => "sh") (some "") = "sh" := by
  sorry

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

/-- A control sequence's count, which can reach 65535, repeats its action at most `cap` times,
and the terminal caps it by its screen: a larger count costs no more. -/
theorem repeatAtMost_eq_repeat (v : Vt.Vt) (cap count : Nat) (f : Vt.Vt → Vt.Vt) :
    v.repeatAtMost cap count f = Nat.repeat f (min count cap) v := by sorry

/-- `repeatAtMost_eq_repeat` rejects a repeat that runs as many times as the count asks. -/
theorem repeatAtMost_eq_repeat_rejects_uncapped :
    ¬∀ (v : Vt.Vt) (cap count : Nat) (f : Vt.Vt → Vt.Vt),
        (fun (v : Vt.Vt) (_ count : Nat) (f : Vt.Vt → Vt.Vt) => Nat.repeat f count v) v cap count
            f =
          Nat.repeat f (min count cap) v := by
  sorry

/-- A replay step never sends more bytes than its budget. -/
theorem next_bounded {budget : Nat} {p q : Replay.Plan} {bytes : Render.Bytes}
    (h : Replay.next budget p = some (bytes, q)) : bytes.length ≤ budget := by sorry

/-- `next_bounded` rejects a replay that sends a byte whatever its budget. -/
theorem next_bounded_rejects_overrun :
    ¬∀ {budget : Nat} {p q : Replay.Plan} {bytes : Render.Bytes},
        (fun (_ : Nat) (p : Replay.Plan) => some (([0] : Render.Bytes), p)) budget p =
            some (bytes, q) →
          bytes.length ≤ budget := by
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

/-- A checkpoint that loads saves again as one that loads back the same: recovery never drifts
across save and load. -/
theorem loadBytes_resave {b : ByteArray} {c : Checkpoint.Ckpt Vt.Vt}
    (h : Checkpoint.loadBytes b = some c) :
    Checkpoint.loadBytes (Checkpoint.saveBytes c) = some c := by sorry

/-- `loadBytes_resave` rejects a save that writes one fixed checkpoint whatever it is given. -/
theorem loadBytes_resave_rejects_fixed :
    ¬∀ {b : ByteArray} {c : Checkpoint.Ckpt Vt.Vt},
        Checkpoint.loadBytes b = some c →
          Checkpoint.loadBytes
              ((fun (_ : Checkpoint.Ckpt Vt.Vt) => Checkpoint.saveBytes ⟨Vt.Vt.init 1 1, "x", []⟩)
                c) =
            some c := by
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

/-- `linger capture --history` prints UTF-8 text with no C0 control, DEL or C1 control character
other than its line terminators. -/
theorem history_text (v : Vt.Vt) :
    ∃ cs : List Char,
      Render.history v = cs.flatMap String.utf8EncodeChar ∧
        ∀ c ∈ cs,
          c = '\n' ∨ (0x20 ≤ c.toNat ∧ c.toNat ≠ 0x7F ∧ ¬(0x80 ≤ c.toNat ∧ c.toNat < 0xA0)) := by
  sorry

/-- `history_text` rejects a history that prints an escape byte. -/
theorem history_text_rejects_escape :
    ¬∀ (v : Vt.Vt),
        ∃ cs : List Char,
          (fun (_ : Vt.Vt) => ([0x1B] : Render.Bytes)) v = cs.flatMap String.utf8EncodeChar ∧
            ∀ c ∈ cs,
              c = '\n' ∨
                (0x20 ≤ c.toNat ∧ c.toNat ≠ 0x7F ∧ ¬(0x80 ≤ c.toNat ∧ c.toNat < 0xA0)) := by
  sorry

/-- An `info` reply is UTF-8 text with no C0 control, DEL or C1 control character other than its
field and line separators, whatever its labels hold. -/
theorem infoText_text (s : State) :
    ∃ cs : List Char,
      Session.infoText s = cs.flatMap String.utf8EncodeChar ∧
        ∀ c ∈ cs,
          c = '\t' ∨
            c = '\n' ∨ (0x20 ≤ c.toNat ∧ c.toNat ≠ 0x7F ∧ ¬(0x80 ≤ c.toNat ∧ c.toNat < 0xA0)) := by
  sorry

/-- `infoText_text` rejects a reply that prints an escape byte. -/
theorem infoText_text_rejects_escape :
    ¬∀ (s : State),
        ∃ cs : List Char,
          (fun (_ : State) => ([0x1B] : List UInt8)) s = cs.flatMap String.utf8EncodeChar ∧
            ∀ c ∈ cs,
              c = '\t' ∨
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

/-! ## 9. Work follows events

Not claimed yet: that an event's work follows its size and its audience, never the number of
sessions, and that a daemon sleeps until its session's next tick or its next event.
`scripts/gates.sh` lists every timer the program sets, with its bound, and the quiet suite counts
the wakeups of idle sessions. -/

/-- After the last event, a session's daemon wakes at most twice on its own: ticking at the
deadlines the session sets, for its save and for the end of its output's freshness, it then needs
no tick until the next event. -/
theorem ticks_settle (s : State) (now t₁ t₂ : Nat)
    (h₁ : (Session.trace Session.step s [.tick now]).1.nextTick = some t₁)
    (h₂ : (Session.trace Session.step s [.tick now, .tick t₁]).1.nextTick = some t₂) :
    (Session.trace Session.step s [.tick now, .tick t₁, .tick t₂]).1.nextTick = none := by sorry

/-- `ticks_settle` rejects a session that always asks for another tick, as a daemon that polls
would. -/
theorem ticks_settle_rejects_poll :
    ¬∀ (s : State) (now t₁ t₂ : Nat),
        (fun (_ : State) => (some 0 : Option Nat)) (Session.trace Session.step s [.tick now]).1 =
            some t₁ →
          (fun (_ : State) => (some 0 : Option Nat))
              (Session.trace Session.step s [.tick now, .tick t₁]).1 =
            some t₂ →
          (fun (_ : State) => (some 0 : Option Nat))
              (Session.trace Session.step s [.tick now, .tick t₁, .tick t₂]).1 =
            none := by
  sorry

/-! ## 10. Graceful under load

A command waits for its daemon's answer a bounded time, and what it answers when that time runs
out is still true. Not claimed yet: that work a request needs never waits on optional work or on
another session, that every other wait is bounded and says what it missed, and that optional work
is skipped or coalesced. The robust and resume suites test it. -/

/-- A request's answer is true, even when its wait runs out: `start` and `resume` race the daemon
they started for the request's ticket, whoever takes it decides, and so the command answers that
the program runs only when it does, and that it does not only when it never will. -/
theorem start_answer_true (r : Start.Request) (h : Start.Reachable Start.proceeds Start.answer r) :
    (r.answer = some .started → r.runs = true) ∧
      (r.answer = some .notStarted → r.runs = false) := by
  sorry

/-- `start_answer_true` rejects a command that answers that the program runs whatever happened. -/
theorem start_answer_true_rejects_started :
    ¬∀ (r : Start.Request),
        Start.Reachable Start.proceeds (fun _ _ => Start.Answer.started) r →
          (r.answer = some .started → r.runs = true) ∧
            (r.answer = some .notStarted → r.runs = false) := by
  sorry

/-- `start_answer_true` rejects a daemon that runs the program even after the command withdrew
the request. -/
theorem start_answer_true_rejects_proceed :
    ¬∀ (r : Start.Request),
        Start.Reachable (fun _ => true) Start.answer r →
          (r.answer = some .started → r.runs = true) ∧
            (r.answer = some .notStarted → r.runs = false) := by
  sorry

/-! ## The status rule -/

/-- Every observation gets exactly the status its legend line describes: `?` no answer, `✓` ended
with status 0, `!` ended any other way, `~` saved with no daemon, `⣷` output right now, `⣿` new
output, then it stopped, and `⣀` nothing new since you looked. -/
theorem classify_iff (o : Status.Obs) (s : Status.Status) :
    Status.classify o = s ↔ Status.Is s o := by sorry

/-- `classify_iff` rejects a classifier that calls every session idle. -/
theorem classify_iff_rejects_idle :
    ¬∀ (o : Status.Obs) (s : Status.Status),
        (fun (_ : Status.Obs) => Status.Status.idle) o = s ↔ Status.Is s o := by
  sorry

/-- Each status is shown as its own glyph. -/
theorem icon_glyphs :
    Status.icon .working = '⣷' ∧
      Status.icon .wantsYou = '⣿' ∧
      Status.icon .idle = '⣀' ∧
      Status.icon .exitedOk = '✓' ∧
      Status.icon .exitedBad = '!' ∧ Status.icon .resumable = '~' ∧ Status.icon .unknown = '?' := by
  sorry

/-- `icon_glyphs` rejects an icon that shows every status as `?`. -/
theorem icon_glyphs_rejects_unknown :
    ¬((fun (_ : Status.Status) => '?') .working = '⣷' ∧
        (fun (_ : Status.Status) => '?') .wantsYou = '⣿' ∧
        (fun (_ : Status.Status) => '?') .idle = '⣀' ∧
        (fun (_ : Status.Status) => '?') .exitedOk = '✓' ∧
        (fun (_ : Status.Status) => '?') .exitedBad = '!' ∧
        (fun (_ : Status.Status) => '?') .resumable = '~' ∧
        (fun (_ : Status.Status) => '?') .unknown = '?') := by
  sorry

/-- Titles and `ls --summary` count only `⣿`, `!` and `?`: in that order, how many sessions show
each, when that is not zero, followed by its glyph, separated by spaces. -/
theorem summary_exact (statuses : List Status.Status) :
    Status.summary statuses =
      String.intercalate " "
        ((if statuses.count .wantsYou = 0 then []
          else [(toString (statuses.count .wantsYou)).push (Status.icon .wantsYou)]) ++
          (if statuses.count .exitedBad = 0 then []
          else [(toString (statuses.count .exitedBad)).push (Status.icon .exitedBad)]) ++
          (if statuses.count .unknown = 0 then []
          else [(toString (statuses.count .unknown)).push (Status.icon .unknown)])) := by
  sorry

/-- `summary_exact` rejects a summary that counts every session. -/
theorem summary_exact_rejects_count :
    ¬∀ (statuses : List Status.Status),
        (fun (all : List Status.Status) => toString all.length) statuses =
          String.intercalate " "
            ((if statuses.count .wantsYou = 0 then []
              else [(toString (statuses.count .wantsYou)).push (Status.icon .wantsYou)]) ++
              (if statuses.count .exitedBad = 0 then []
              else [(toString (statuses.count .exitedBad)).push (Status.icon .exitedBad)]) ++
              (if statuses.count .unknown = 0 then []
              else [(toString (statuses.count .unknown)).push (Status.icon .unknown)])) := by
  sorry

/-- A window title keeps the attention summary last and whole: whatever the capacity, the title
is the session's name and the application's title within what the summary leaves, then the
summary. -/
theorem compose_attention_last (session application summary : String) (capacity : Nat) :
    Title.compose session application summary capacity =
      Title.compose session application ""
          (capacity - (if summary.isEmpty then "" else " · " ++ summary).length) ++
        (if summary.isEmpty then "" else " · " ++ summary) := by
  sorry

/-- `compose_attention_last` rejects a title that puts the summary first. -/
theorem compose_attention_last_rejects_first :
    ¬∀ (session application summary : String) (capacity : Nat),
        (fun (session application summary : String) (_ : Nat) => summary ++ session ++ application)
            session application summary capacity =
          (fun (session application summary : String) (_ : Nat) =>
                summary ++ session ++ application)
              session application ""
              (capacity - (if summary.isEmpty then "" else " · " ++ summary).length) ++
            (if summary.isEmpty then "" else " · " ++ summary) := by
  sorry

end Linger
