module

public import Linger.App.CoreSpec
public import Linger.Display.CoreSpec
public import Linger.Import.CoreSpec
public import Linger.Os.CoreSpec
public import Linger.Selector.CoreSpec
public import Linger.Session.CoreSpec
public import Linger.Target.CoreSpec
public import Linger.Session.WorldSpec
public import Linger.Target.WorldSpec
public import Terminal.CoreCode.Mediation
public import Terminal.CoreCode.Render
public import Terminal.CoreCode.Replay
public import Terminal.CoreSpec
public import Terminal.CoreCode.Title
public import Terminal.CoreCode.Vt
public import Os.WorldSpec
meta import SoftwareChallenge

/-! # Headline theorems

The guarantees linger must keep, in ten parts. Each part's section states its headline theorems,
each with a kill, and says what it does not claim yet:

1. Transparency: a client that attaches shows the session's terminal, losing only history beyond
   the replay budget, and then receives the program's output as linger's mediator releases it;
   a program whose terminal is in raw mode reads exactly what its writers sent and hears focus as
   a terminal reports it.
2. Authority and attribution: a connection changes only what its mode allows, a name has one
   owner, and every value linger reports has one source, which alone can change it.
3. Exactness: a request takes effect exactly as given, or is refused with a reason and changes
   nothing.
4. Program identity: a session runs exactly the program its creation named, from a state its
   start alone decides, and linger only delivers bytes to it.
5. Accountability: every session ends once, through one ending, whether its program ends, a kill
   stops it or a signal stops its daemon, which saves it, with how it ended recorded and reported
   truthfully to anyone who asks; every request gets a reply or a refusal, and every command
   exits with the code of an answer true of what happened.
6. Bounded and clean: input cannot raise any buffer, loop or wait past its cap, and nothing of a
   session's terminal session that linger's signals reach outlives it.
7. Recovery: resuming from a checkpoint gives back the saved session, less any half-parsed
   control sequence, and a crash costs at most the changes of the last interval, never the
   session: a checkpoint that does not decode is kept and refused, not replaced. An upgrade
   carries a running session to a newer binary whole, or leaves it running as it was.
8. Clean terminal: what linger writes to a terminal on its own account is safe text or one of
   its fixed sequences, in color only where the caller's environment allows it, and handing a
   terminal back leaves it canonical.
9. Work follows events: linger works only in response to an event, a byte, a request, a program
   ending or a deadline an earlier event set, and each event sets at most a fixed number of
   deadlines. An event costs in proportion to its size and its audience, never to how many
   sessions exist, so every linger process goes quiet after the last event. Parts 1 to 8 decide
   what linger does and this one how cheaply: work no event pays for is allowed only where it is
   named, with its bound.
10. Graceful under load: work a request needs never waits on optional work or on another
   session, every wait is bounded and says what it missed, and optional work is skipped or
   coalesced, never queued.

The status rule: a session's status is one glyph for one observation, `⚑` a bell or a desktop
notification since you looked, from a program still running, `⣷` output right now, `⣿` new output,
then it stopped, `⣀` nothing new since you looked, `✓` ended with status 0, `✗` ended any other
way, `~` saved with no daemon and `?` no answer; a program waiting for you outranks one printing,
and titles and `ls --summary` count `⚑`, `⣿`, `✗` and `?`. No two statuses share a glyph, and
`linger help`'s legend gives each glyph one line, which begins with it (`icon_glyphs`); a row of a
session with no daemon shows the status the legend gives what its end record says, and a remote
host's saved row only an ending or `~` (`rowStatus_saved`). Its section follows the ten parts, with
the titles, listings and selector views that show statuses: a view ranks rows by what needs you
to act, `⚑`, then `✗` and `?`, then `⣿`, first, then by where the session is in its life, the
running sessions, then the saved ones, `~`, then the ended ones, `✓` (`sort_two_keys`), so no row
that ended well or can only be resumed sits above a live one, a finished session comes last, and a
running session's row keeps its place whether it is printing or quiet. Output is `⣷` for a working
window of three seconds from the poll round that saw it (`Session.workingMs`), so a program that
redraws more often, as `top` does, reads `⣷` at every poll round of every redraw, and once it
stops, it reads quiet from the round a working window after its last redraw, for which its
session sets a tick (`steady_working`). A client attached to one session tells its terminal, with
one OSC 9 desktop notification, of each other local session that changed into asking between two
of the samples its title takes, and of none on the first, whose asks the title counts
(`announce_changes`). Within a place a view keeps the listing's order,
and a listing orders names as people read them: a total order (`before_total`) that puts names
differing only in one number in the order of that number, `w2` before `w10` (`before_number`). A session
asks exactly while its program has rung the bell or posted a notification since the session was
last looked at, and tells how its shell's last command ended until someone sees it, each as part 2
says its program owns it (`step_owned`). An ending is
no status: `✓` and `✗` stay the endings of the session's own program.

Each theorem below is stated over definitions in the components' `CoreSpec` modules and the world
claims in their `WorldSpec` modules, over the terminal package's parts, which its own challenge
claims, and over the program parts declared below as holes: each hole is `sorry` here, the program
supplies it, and the claims say what it must do. `Theorems/Solution.lean` proves the same statements
of the program's parts, and `./lake comparator` checks that it proves exactly these, that each part
has the declared type, and that no axiom beyond `propext`, `Quot.sound` and `Classical.choice` is
used. Changing a statement or a hole here changes what linger claims.

Not claimed: that the IO executors, the C shim and the operating system behave as the world
claims say, which each claim's check tests on the host it runs on and the suites named with
each claim test through linger, except for power loss, which `Disk.Durable` speaks of and no
check or suite causes; scheduling, allocation failure, termination
by SIGKILL or power loss and failures of the compiler, the runtime or the C shim; a bound in bytes
or rows on what a crash loses, which is bounded in time; memory beyond the logical bytes the
buffers retain; ownership among processes that do not cooperate or replace the lock files;
fidelity beyond linger's own terminal model, which stands in for every receiver; the incoming
title content and the saved cursor slot, which fixtures cover; processes or images, since
recovery restores screens; that an exit status tells linger's answers from a program's, since a
program may exit with any status, as with `timeout` and `env`, so that the porcelain output is
the exact channel; for a saved tmux pane, captures other than the latest save's archive;
and that an imported pane's saved command never runs, which a gate checks. -/

public section

open Linger.App Linger.Display Linger.Session Linger.Target Terminal

/-! ## The program's parts

### Command line -/

def Linger.App.Entry.route : List String → App.Entry.Route := sorry

def Linger.App.Commands.table : List App.Commands.Command := sorry

def Linger.App.Commands.lookup : String → Option App.Commands.Command := sorry

def Linger.App.Commands.helpLine : App.Commands.Command → String := sorry

def Linger.App.Commands.helpLines : List String := sorry

def Linger.App.Fields.table : List App.Fields.Field := sorry

def Linger.Os.Answer.code : Os.Answer → UInt32 := sorry

def Linger.App.Wait.heldNameMs : Nat := sorry

def Linger.App.Wait.decide : Option Nat → Option Nat → Nat → App.Wait.Heard → App.Wait.Next := sorry

def Linger.App.Recovery.decide : Bool → Option ByteArray → App.Recovery (Checkpoint.Ckpt Vt.Vt) :=
  sorry

def Linger.App.Recovery.visit : Bool → Option (List UInt8) → List App.Visit.Step := sorry

def Linger.App.Capture.plan : List App.Capture.Step := sorry

def Linger.App.Capture.phases : List App.Capture.Step → List App.Capture.Phase := sorry

/-! ### Session targets -/

def Linger.Target.Name.check : String → Option String := sorry

def Linger.Target.Name.accept : String → Option String := sorry

def Linger.Target.Remote.commandWords : String → List String → List String := sorry

def Linger.Target.Remote.decode : List String → Option (List String) := sorry

def Linger.Target.Remote.targetArgs : List String → Option (String × List String) := sorry

def Linger.Target.Remote.targetOperands : String → List String := sorry

def Linger.Target.Remote.targetArgv :
    Remote.Transport → String → List String → String → List String → List String := sorry

def Linger.Target.Remote.checkHosts : List String → Except String (List String) := sorry

/-! ### Environment -/

def Linger.Os.Env.shellOf : Option String → String := sorry

def Linger.Os.Env.remotesFile : Option String → Option String := sorry

def Linger.Os.Env.detachEnabled : Bool → Option String → Bool := sorry

def Linger.Os.Env.resumeDir : Option String → String → Bool → Option String := sorry

def Linger.Os.Env.withColor : Bool → Option String → Option String → Bool := sorry

/-! ### Statuses -/

def Linger.Display.Status.classify : Status.Obs → Status.Status := sorry

def Linger.Display.Status.icon : Status.Status → Char := sorry

def Linger.Display.Status.legend : List String := sorry

def Linger.Display.Status.summary : List Status.Status → String := sorry

def Linger.Display.Status.name : Status.Status → String := sorry

def Linger.Display.Status.ofName : String → Status.Status := sorry

def Linger.Display.Listing.rowFields : String → List (String × String) → List (String × String) :=
  sorry

def Linger.Display.Listing.rowStatus : Listing.Row → Status.Status := sorry

def Linger.Display.Listing.terminalListing :
    Bool → Option Nat → List (List (String × String)) → List UInt8 := sorry

def Linger.Display.Listing.rowText :
    Option Nat → Listing.Layout → List (String × String) → List Char := sorry

def Linger.Display.Listing.columns : Listing.Layout → List (String × String) → List (List Char) :=
  sorry

def Linger.Display.Listing.cells : List (String × String) → List String := sorry

def Linger.Display.Listing.caption : List (String × String) → String := sorry

def Linger.Display.Listing.program : List (String × String) → String := sorry

def Linger.Display.View.sort {α : Type} : (α → Status.Status) → List α → List α := sorry

def Linger.Display.View.before : String → String → Bool := sorry

def Linger.Display.View.hidden : List String → Nat × List (String × Nat) := sorry

def Linger.Display.Title.compose : String → String → String → Nat → String := sorry

def Linger.Display.Alert.announce :
    Option (List (String × Status.Status)) → List (String × Status.Status) → String → List String :=
  sorry

def Linger.Display.Alert.notification : String → String → List UInt8 := sorry

/-! ### Sessions -/

def Linger.Session.State : Type := sorry

def Linger.Session.State.boot : Vt.Vt → List (String × String) → List (String × String) → State :=
  sorry

def Linger.Session.Claim.enters : Bool → Bool → Bool := sorry

def Linger.Session.Locks.release : Session.Records → String → Session.Records := sorry

def Linger.Session.Names.entryFile : String → String := sorry

def Linger.Session.Names.entryName : String → Option String := sorry

def Linger.Session.ending : List Linger.Session.Stop.Send := sorry

def Linger.Session.drainTimeoutMs : Nat := sorry

def Linger.Session.freshMs : Nat := sorry

def Linger.Session.pollTimeout : Nat → List Nat → Int32 := sorry

def Linger.Session.Offloop.ask {R W : Type} : Offloop R W → W → Offloop R W × Option W := sorry

def Linger.Session.Offloop.done {R W : Type} : Offloop R W → Offloop R W × Option W := sorry

def Linger.Session.step : State → Event → State × List (Effect Replay.Plan) := sorry

def Linger.Session.State.client? : State → Nat → Option Client := sorry

def Linger.Session.State.terminal : State → Vt.Vt := sorry

def Linger.Session.State.roster : State → List Client := sorry

def Linger.Session.State.fieldList : State → List (String × String) := sorry

def Linger.Session.State.scanner : State → Mediation.Scan := sorry

def Linger.Session.State.seen : State → Seen := sorry

def Linger.Session.State.owned : State → Owned := sorry

def Linger.Session.State.nextTick : State → Option Nat := sorry

def Linger.Session.infoText : State → List UInt8 := sorry

def Linger.Session.infoFields : State → List (String × String) := sorry

def Linger.Session.outcomeFields : Outcome → List (String × String) := sorry

def Linger.Session.endingFields : Ending → List (String × String) := sorry

def Linger.Session.Wire.encode : Wire.Msg → List UInt8 := sorry

def Linger.Session.Wire.Decoder.feed : Wire.Decoder → List UInt8 → Wire.Decoder × List Wire.Msg :=
  sorry

def Linger.Session.Wire.inputFrames : List UInt8 → List Wire.Msg := sorry

def Linger.Session.Wire.admits : Option Nat → Bool := sorry

def Linger.Session.Record.encode : Record → List UInt8 := sorry

def Linger.Session.Record.answer : Option (List UInt8) → Option Ending := sorry

def Linger.Session.bootVt : Option Vt.Vt → Vt.Vt := sorry

def Linger.Session.Driver.run :
    {m : Type → Type} →
      [Monad m] →
      {World : Type} →
      (State → World → (eff : Effect Replay.Plan) → m (World × Driver.Reply eff)) →
        Driver.Result State World → List Event → m (Driver.Result State World) := sorry

def Linger.Session.Checkpoint.saveBytes : Checkpoint.Ckpt Vt.Vt → ByteArray := sorry

def Linger.Session.Checkpoint.loadBytes : ByteArray → Option (Checkpoint.Ckpt Vt.Vt) := sorry

def Linger.Session.Handoff.encode : State → Handoff.World → List UInt8 := sorry

def Linger.Session.Handoff.decode : List UInt8 → Option (State × Handoff.World) := sorry

def Linger.Session.Handoff.kept : Handoff.World → List Nat := sorry

def Linger.Session.Upgrade.proceeds : Option (List Nat) → Bool := sorry

def Linger.Session.Start.plan : (live saved : Bool) → Start.Plan := sorry

def Linger.Session.Start.programOf : String → List String → String × Array String := sorry

def Linger.Session.Start.proceeds : Bool → Bool := sorry

def Linger.Session.Start.answer : Bool → Bool → Start.Answer := sorry

def Linger.Session.Start.environment :
    String → String → List String → List (String × Option String) := sorry

def Linger.Session.Start.reset : Spawn.Reset := sorry

def Linger.Session.Start.failureStatus : Spawn.Failure → UInt8 := sorry

def Linger.Session.Start.metadata :
    (name pid created cmd dir : String) → Option String → List (String × String) := sorry

def Linger.Session.Names.resolve : Names.Table → String → Option String := sorry

def Linger.Session.Names.nameOf : Names.Table → String → Option String := sorry

def Linger.Session.Names.claim : Names.Table → String → String → Names.Table := sorry

def Linger.Session.Names.rename : Names.Table → String → String → String → Names.Table := sorry

def Linger.Session.Names.call : Names.Op → Names.Call := sorry

def Linger.Session.Names.Rename.plan : Bool → Bool → Bool → Bool → Names.Rename.Plan := sorry

def Linger.Session.Buf.Buf : Type := sorry

def Linger.Session.Buf.Buf.empty : Buf.Buf := sorry

def Linger.Session.Buf.bufOffer : (cap : Nat) → Buf.Buf → ByteArray → Buf.Buf × Bool := sorry

def Linger.Session.Buf.bufEnqueue : (cap : Nat) → Buf.Buf → ByteArray → Buf.Buf × Bool := sorry

def Linger.Session.Buf.bufAdvance : Buf.Buf → Nat → Buf.Buf := sorry

def Linger.Session.Buf.owedLen : Buf.Buf → Nat := sorry

def Linger.Session.Buf.writeFrom : Buf.Buf → ByteArray := sorry

/-! ### Selector and import -/

def Linger.Selector.Picker.matchCount : Selector.Picker.State → Nat := sorry

def Linger.Selector.Picker.step : Selector.Picker.State → Selector.Key → Selector.Picker.Outcome :=
  sorry

def Linger.Selector.Picker.frame :
    Selector.Picker.State →
      Selector.Picker.Snapshot →
      (String → Status.Status) → Bool → Bool → Bool → Option Nat → Nat → Nat → List UInt8 := sorry

def Linger.Selector.Picker.frameRows :
    Selector.Picker.State →
      Selector.Picker.Snapshot →
      (String → Status.Status) → Bool → Bool → Bool → Option Nat → Nat → Nat → List (List UInt8) :=
  sorry

def Linger.Selector.Picker.enter :
    Selector.Picker.State →
      List String → Option String → List String → List (String × String) → Selector.Picker.State :=
  sorry

def Linger.Selector.Picker.relist :
    Selector.Picker.State → Bool → List String → List (String × String) → Selector.Picker.State :=
  sorry

def Linger.Selector.Picker.update : List (List UInt8) → List (List UInt8) → List UInt8 := sorry

def Linger.Selector.Picker.fetch : Bool → Selector.Picker.Event → Bool := sorry

def Linger.Selector.Picker.enterAnsi : List UInt8 := sorry

def Linger.Selector.Picker.exitAnsi : List UInt8 := sorry

def Linger.Import.Resurrect.listed :
    Session.Records → List Import.Resurrect.Pane → List Import.Resurrect.Pane := sorry

def Linger.Import.Resurrect.adopt :
    Session.Records → Import.Resurrect.Pane → Option String → Option (Checkpoint.Ckpt Vt.Vt) :=
  sorry

def Linger.Import.Resurrect.dismiss : Session.Records → String → Session.Records := sorry

def Linger.Import.Resurrect.dismissal : Session.Record := sorry

def Linger.Import.Resurrect.captureLimit : Nat := sorry

def Linger.Import.Resurrect.captureBytes : String → List UInt8 := sorry

def Linger.Import.Resurrect.checkpoint :
    Import.Resurrect.Pane → Option String → Checkpoint.Ckpt Vt.Vt := sorry

namespace Linger

/-! ## 1. Transparency

What a repaint gives a client is claimed by the terminal package (`packages/terminal`), of the
terminals a session can hold: fresh, fed, resized, quiesced, or admitted by the toolkit's decoder
door, which every terminal linger's checkpoint decoder returns passes
(`Checkpoint.live_of_decoded`). There a client receives the repaint as a stream, in steps of any
positive byte budget, the stream ends, and a receiver of the same size that parses it shows what the
terminal shows and, for a repaint taken between control sequences and characters, keeps showing it
as the same output reaches both; and a terminal's history only gains rows at its end, unless output
may ask to erase it. Here: a read that attaches a connection, writable or read-only, streams it the
repaint of the session's terminal as the attach leaves it, and the read sends it nothing before the
repaint: only the pty's resize and the program's focus report come first. A chunk of program output
feeds the session's terminal exactly that chunk, reaches every attached client, writable or
read-only, in roster order, as the same frames, each nonempty and of at most 64 KiB, whose payloads
are exactly the bytes the terminal package's mediator releases, in order, and writes the program
only the mediator's replies to its queries. The daemon does what the session asks: when every effect
succeeds, its driver hands the session each event and then what the event's effects feed back, ends
in the state of their trace, and executes exactly the trace's effects, in order, each with the state
its event left (`run_refines`, in part 5). Linger writes to a session's terminal exactly the input
it accepted for the program, in order, whatever mode the program set, and a program whose terminal
is in raw mode reads exactly that, when the kernel hands raw input on unchanged (`Pty.Delivers`,
which its check and the agent suite test byte for byte); linger accepts each frame a writable client
sends, whatever its terminal's size, whole, or refuses it whole when the program's queue is full;
and `send` hands the program text of any length in frames the decoder takes, whose payloads are the
text, in order. A program that enabled focus reporting hears that it gained focus when a writable
client attaches to a session nobody could type into, whatever its size, and that it lost it when the
last one leaves. Not claimed: which bytes the mediator releases, which `Terminal.Mediation` decides:
all the program wrote but the queries linger owns, which its terminal answers or nobody does, a
request still incomplete at a chunk's end waiting for the next; an attach a read completes with
other messages; that the runtime streams a repaint ahead of the output that follows it, which the
delivery suite checks; and what a program reads in any other mode than raw, such as the cooked mode
a terminal starts in, whose line discipline edits lines and turns ^C into a signal. -/

theorem step_attach_repaint (s : State) (id : Nat) (chunk : List UInt8) {c : Client}
    {dec : Wire.Decoder} {mode : Mode} {cols rows : UInt32} (hc : s.client? id = some c)
    (fresh : c.attached = false) (read : c.decoder.feed chunk = (dec, [.attach mode cols rows]))
    (healthy : dec.errored = false) :
    ∃ pty after,
      (Session.step s (.bytes id chunk)).2 =
          pty ++
            Effect.replay id (Replay.start (Session.step s (.bytes id chunk)).1.terminal) :: after ∧
        ∀ eff ∈ pty,
          (∃ bytes, eff = .writePty bytes) ∨ ∃ cols rows, eff = .resizePty cols rows := by
  sorry

@[kills step_attach_repaint]
theorem step_attach_repaint_rejects_blank :
    ¬∀ (s : State) (id : Nat) (chunk : List UInt8) {c : Client} {dec : Wire.Decoder} {mode : Mode}
        {cols rows : UInt32},
        s.client? id = some c →
          c.attached = false →
          c.decoder.feed chunk = (dec, [.attach mode cols rows]) →
          dec.errored = false →
          ∃ pty after,
            (Session.without Effect.replays Session.step s (.bytes id chunk)).2 =
                pty ++
                  Effect.replay id
                      (Replay.start
                        (Session.without Effect.replays Session.step s
                            (.bytes id chunk)).1.terminal) ::
                    after ∧
              ∀ eff ∈ pty,
                (∃ bytes, eff = .writePty bytes) ∨ ∃ cols rows, eff = .resizePty cols rows := by
  sorry

theorem step_output_delivered (s : State) (chunk : List UInt8) :
    (Session.step s (.ptyOut chunk)).1.terminal = s.terminal.feed chunk ∧
      ∃ answers frames : List (List UInt8),
        (Session.step s (.ptyOut chunk)).2 =
            answers.map Effect.writePty ++
              (s.roster.filter (·.attached)).flatMap
                (fun c => frames.map fun frame => Effect.send c.id (.output frame)) ∧
          answers.flatten = (Mediation.feed s.terminal s.scanner chunk).replies ∧
          frames.flatten = (Mediation.feed s.terminal s.scanner chunk).visible ∧
          ∀ frame ∈ frames, frame ≠ [] ∧ frame.length ≤ 65536 := by
  sorry

@[kills step_output_delivered]
theorem step_output_delivered_rejects_drop :
    ¬∀ (s : State) (chunk : List UInt8),
        (Session.without Effect.rendered Session.step s (.ptyOut chunk)).1.terminal =
            s.terminal.feed chunk ∧
          ∃ answers frames : List (List UInt8),
            (Session.without Effect.rendered Session.step s (.ptyOut chunk)).2 =
                answers.map Effect.writePty ++
                  (s.roster.filter (·.attached)).flatMap
                    (fun c => frames.map fun frame => Effect.send c.id (.output frame)) ∧
              answers.flatten = (Mediation.feed s.terminal s.scanner chunk).replies ∧
              frames.flatten = (Mediation.feed s.terminal s.scanner chunk).visible ∧
              ∀ frame ∈ frames, frame ≠ [] ∧ frame.length ≤ 65536 := by
  sorry

theorem step_input_exact (s : State) (id : Nat) (chunk : List UInt8) {c : Client}
    {dec : Wire.Decoder} {inputs : List (List UInt8)} (hc : s.client? id = some c)
    (typist : c.mode = .writable) (read : c.decoder.feed chunk = (dec, inputs.map Wire.Msg.input))
    (healthy : dec.errored = false) :
    (Session.step s (.bytes id chunk)).2 = inputs.map Effect.writePty := by sorry

@[kills step_input_exact]
theorem step_input_exact_rejects_drop :
    ¬∀ (s : State) (id : Nat) (chunk : List UInt8) {c : Client} {dec : Wire.Decoder}
        {inputs : List (List UInt8)},
        s.client? id = some c →
          c.mode = .writable →
          c.decoder.feed chunk = (dec, inputs.map Wire.Msg.input) →
          dec.errored = false →
          ((fun (s : State) (_ : Event) => (s, ([] : List (Effect Replay.Plan)))) s
                (.bytes id chunk)).2 =
            inputs.map Effect.writePty := by
  sorry

theorem input_exact (reads : Pty.Mode → ByteArray → ByteArray) (delivers : Pty.Delivers reads)
    {cap : Nat} {accepted written : ByteArray} {b : Buf.Buf}
    (life :
      Buf.InputLife Buf.Buf.empty Buf.bufOffer Buf.bufAdvance Buf.writeFrom cap accepted written
        b) :
    written ++ Buf.writeFrom b = accepted ∧
      reads .raw written ++ Buf.writeFrom b = accepted ∧
      ∀ more, (Buf.bufOffer cap b more).2 = true ↔ cap < Buf.owedLen b + more.size := by
  sorry

@[kills input_exact]
theorem input_exact_rejects_lost :
    ¬∀ (reads : Pty.Mode → ByteArray → ByteArray),
        Pty.Delivers reads →
          ∀ {cap : Nat} {accepted written : ByteArray} {b : Buf.Buf},
            Buf.InputLife Buf.Buf.empty (fun (_ : Nat) (b : Buf.Buf) (_ : ByteArray) => (b, false))
                Buf.bufAdvance Buf.writeFrom cap accepted written b →
              written ++ Buf.writeFrom b = accepted ∧
                reads .raw written ++ Buf.writeFrom b = accepted ∧
                ∀ more,
                  ((fun (_ : Nat) (b : Buf.Buf) (_ : ByteArray) => (b, false)) cap b more).2 =
                      true ↔
                    cap < Buf.owedLen b + more.size := by
  sorry

theorem decode_encode_chunked (ms : List Wire.Msg) (fits : ∀ m ∈ ms, m.Fits)
    (chunks : List (List UInt8)) (cut : chunks.flatten = ms.flatMap Wire.encode) :
    Wire.feedAll Wire.Decoder.feed {} chunks = ({ buf := [], errored := false }, ms) := by sorry

@[kills decode_encode_chunked]
theorem decode_encode_chunked_rejects_silence :
    ¬∀ (ms : List Wire.Msg),
        (∀ m ∈ ms, m.Fits) →
          ∀ (chunks : List (List UInt8)),
            chunks.flatten = ms.flatMap (fun (_ : Wire.Msg) => ([] : List UInt8)) →
              Wire.feedAll Wire.Decoder.feed {} chunks = ({ buf := [], errored := false }, ms) := by
  sorry

theorem inputFrames_exact (bytes : List UInt8) :
    ∃ chunks : List (List UInt8),
      Wire.inputFrames bytes = chunks.map Wire.Msg.input ∧
        chunks.flatten = bytes ∧ ∀ m ∈ Wire.inputFrames bytes, m.Fits := by
  sorry

@[kills inputFrames_exact]
theorem inputFrames_exact_rejects_one :
    ¬∀ (bytes : List UInt8),
        ∃ chunks : List (List UInt8),
          (fun (bytes : List UInt8) => [Wire.Msg.input bytes]) bytes = chunks.map Wire.Msg.input ∧
            chunks.flatten = bytes ∧
            ∀ m ∈ (fun (bytes : List UInt8) => [Wire.Msg.input bytes]) bytes, m.Fits := by
  sorry

theorem step_attach_focus (s : State) (id : Nat) (chunk : List UInt8) {c : Client}
    {dec : Wire.Decoder} {mode : Mode} {cols rows : UInt32} (hc : s.client? id = some c)
    (read : c.decoder.feed chunk = (dec, [.attach mode cols rows])) (healthy : dec.errored = false)
    (bytes : List UInt8) :
    Effect.writePty bytes ∈ (Session.step s (.bytes id chunk)).2 ↔
      bytes = [0x1B, 0x5B, 0x49] ∧
        s.terminal.getModes.focusEvents = true ∧
        c.attached = false ∧
        mode = .writable ∧
        ∀ other ∈ s.roster,
          other.id ≠ id → (other.attached && other.mode == .writable) = false := by
  sorry

@[kills step_attach_focus]
theorem step_attach_focus_rejects_eager :
    ¬∀ (s : State) (id : Nat) (chunk : List UInt8) {c : Client} {dec : Wire.Decoder} {mode : Mode}
        {cols rows : UInt32},
        s.client? id = some c →
          c.decoder.feed chunk = (dec, [.attach mode cols rows]) →
          dec.errored = false →
          ∀ (bytes : List UInt8),
            Effect.writePty bytes ∈
                ((fun (s : State) (_ : Event) =>
                      (s, ([.writePty [0x1B, 0x5B, 0x49]] : List (Effect Replay.Plan))))
                    s (.bytes id chunk)).2 ↔
              bytes = [0x1B, 0x5B, 0x49] ∧
                s.terminal.getModes.focusEvents = true ∧
                c.attached = false ∧
                mode = .writable ∧
                ∀ other ∈ s.roster,
                  other.id ≠ id → (other.attached && other.mode == .writable) = false := by
  sorry

theorem step_closed_focus (s : State) (id : Nat) (bytes : List UInt8) :
    Effect.writePty bytes ∈ (Session.step s (.closed id)).2 ↔
      bytes = [0x1B, 0x5B, 0x4F] ∧
        s.terminal.getModes.focusEvents = true ∧
        (s.client? id).any (·.mode == .writable) = true ∧
        s.roster.any (fun c => c.attached && c.mode == .writable) = true ∧
        (Session.step s (.closed id)).1.roster.any (fun c => c.attached && c.mode == .writable) =
          false := by
  sorry

@[kills step_closed_focus]
theorem step_closed_focus_rejects_eager :
    ¬∀ (s : State) (id : Nat) (bytes : List UInt8),
        Effect.writePty bytes ∈
            ((fun (s : State) (_ : Event) =>
                  (s, ([.writePty [0x1B, 0x5B, 0x4F]] : List (Effect Replay.Plan))))
                s (.closed id)).2 ↔
          bytes = [0x1B, 0x5B, 0x4F] ∧
            s.terminal.getModes.focusEvents = true ∧
            (s.client? id).any (·.mode == .writable) = true ∧
            s.roster.any (fun c => c.attached && c.mode == .writable) = true ∧
            ((fun (s : State) (_ : Event) =>
                      (s, ([.writePty [0x1B, 0x5B, 0x4F]] : List (Effect Replay.Plan))))
                    s (.closed id)).1.roster.any
                (fun c => c.attached && c.mode == .writable) =
              false := by
  sorry

/-! ## 2. Authority and attribution

A connection's rights are the mode it attached with, read-only or writable, and nothing else: a
watcher is a client that attached read-only, whatever its terminal's size, a client keeps the
rights it attached with whatever sizes it then reports, and a connection that never attached is
writable. No pty resize the session asks for has a zero dimension: each is the size, clamped, of
an attach or a resize in the read that asked for it, a size with no zero, so a terminal with no
size yet never reaches the pty. Not claimed: which client sizes the session, the newest writable
one whose terminal has a size, which the session fixtures and the attach suite check.
`start` takes no name a session holds (`start_plan`); the daemon decides that holding the name,
which has one owner (`one_owner`).
A session's ID is fixed when it is created and keys its files and its `LINGER_SESSION`; its name
is a handle that leads to the ID, which `rename` changes (`Session.Names`). A name is clean text,
spaces and Unicode included, accepted exactly as it is, which every command takes as one argument
and the names directory keeps, a name that is no key as `=` and its hexadecimal, and reads back
(`names_round_trip`); a key, a name of the older grammar, stays accepted, one that starts with
`-` after `--`, and only a key can be its session's own ID. A session created
under a name that is no session's ID takes it for its ID, as every session an older linger keyed
by name did, so with no entries every valid name leads to itself and old files keep their
meaning; in a table linger keeps, a name leads to an ID exactly when that ID shows as the name,
so no two names lead to one ID (`names_one_to_one`). A rename moves the name to the same ID,
leaves the old name leading elsewhere and no other name changed (`rename_moves`), so every
command, which reaches a session through the ID its name leads to, reaches it by the new name and
the program, terminal, clients, waiters, description and status it keeps by its ID stay as they
were. A start of a name that leads nowhere, because a renamed session holds the name's own ID,
gives it a fresh ID that no session holds (`claim_fresh`); an ID shows as its entry's name or as
itself only when it is a name, never a fresh ID (`nameOf_shown`). `rename` moves a name exactly when
the new name is valid, a live or saved session has the old one, none has the new one, an ended one
still listed included, and no older linger started the session's daemon, and each refusal names
a reason that holds (`rename_plan`), as `start` refuses a name a live or saved session holds,
saying which (`start_plan`),
and places a name on disk only with calls that never replace one, so of a start and a rename
onto one name, whichever comes first, the second fails and the name keeps the first one's
session (`one_name`, assuming `Os.Place.NoReplace`). Not claimed: that a command resolves its
name once and keys everything after by the ID, that the daemon takes the name only while it still
leads to its ID, holding the ID's locks, that `rename` holds the names lock and the new name's ID's
locks while it places the name, which the rename suite checks, and that a client attached before
a rename titles its terminal with the new name, which it does from its next attach.
What a session's program owns has one source each, and the session machine reads each from it
alone (`step_owned`): the title is what OSC 0 and OSC 2 set on the session's terminal, as the
terminal it fed the output holds it; whether it asks, a bell or a notification since the last
look, and the notification's text are what the terminal package's mediator hears of a BEL, an OSC
9 that is no ConEmu sub-command and an OSC 777 `notify`; its commands are what its shell's OSC 133
marks tell, each as `Commands.hear` says the marks' standard means it, so a `D` after a `C` is
that command's ending, with the command line the `C` gave and the status the `D` gave, a later `C`
replaces it, and a `D` with no `C` since the last `D` or `A` is no ending; its foreground and its
echo are what the operating system last reported of its terminal; and whether it is ready and its
status text are what it sent through `sd_notify`'s socket, which its `NOTIFY_SOCKET` names.
Output changes each exactly as its source in that output tells, output while a client is attached
is seen as it arrives, so it leaves nothing to tell, a look, an attach or a capture, clears the
ask, its text and the ending and nothing else, the daemon's reading of the world changes what it
reported and nothing else, a notification changes the readiness and the status and nothing else,
and no other event, no client input among them, changes any; a session lists `⚑` exactly while
its program asks. A program is ready exactly once it sent `READY=1`, and its status text is the
value of the last `STATUS=` it sent, every other key telling nothing, when datagrams sent to a
socket's path arrive whole and in order (`notify_exact`, over the os package's `Os.Dgram.Whole`,
which its check tests); a daemon reads at most `Notify.cap` bytes of each, `Notify.keys`
assignments of each and `Notify.perRound` of them a poll round, and a listing shows the status as
clean text. The program's fields a listing reports, as `Fields.table` gives the program each,
are readings of these alone: two sessions whose programs own the same report the same program
fields (`fields_owned`). Not claimed: a notification sent while a daemon upgrades, which the
image that replaces it binds its socket afresh for; which bytes the mediator hears as a bell, a
notification or a mark, which `Terminal.Mediation` decides and its fixtures and the status suite check, and which
set the title, which `Terminal.Vt` decides and its fixtures check; a mark inside a full-screen
program, which the session hears as its shell's.
The fields of a session's record, the description an older linger saved and an import's
provenance, come from the checkpoint the session booted from, and no event changes them
(`step_fields_kept`); they, the boot metadata and the terminal a session reports each have
one source, and a listing names each row by its socket. A human row reads only
the fields `Listing.sources` names (`rowText_sources`): the program's title is the caption, its
status text in its place while it sets none, the program's own words first, and a description an
older linger saved in their place while the program gives neither, and the foreground program, which the operating system reports, shows only when that caption does not name
it (`caption_precedence`); its glyph and name are never cut, the rest
fits a width in display columns (`rowText_fits`), and each character is printable
(`rowText_clean`). One field, one column: a row's parts, the glyph, the name and the caption,
program, directory, age and watchers cells, each take the display columns its view's layout gives
them while the name fits its column, so each field starts at one column in every row
(`columns_aligned`), and each cell reads only its own fields (`cells_sources`); the layout may
depend on the view, a cell's content may not. A session's `info` reports the foreground the
operating system reports of its terminal as that process sees itself, its words, its process and
its directory (`info_foreground`, over `Pty.Foreground`, which its check tests), and whether its
terminal echoes what is typed, its `ECHO` flag as the program last set it (`info_echo`, over
`Pty.Echo`, which its check tests), a machine field no human row shows. Not claimed:
that the daemon reports the title, foreground and idle time it read, which the overview suite
checks, and that a row shows the text of a notification right after its caption
while its session asks, and only then, and how the last command that finished unseen ended right
after that, which the listing tests and the status suite check.
In the chooser, a key does only what it does in a line editor: Enter attaches only to a listed
target (`picker_attach_listed`) and creates only a new, valid one (`picker_create_new`), and
Ctrl-D, which deletes the character under the cursor and on an empty line ends the input, ends the
visit only on an empty query, since the cursor sits after the query (`picker_eof_empty`). The
chooser's view moves only when its person moves it: a listing keeps the rows it shows where they
are, a vanished row closing up and a new one last, unless it sorts them again, as when the chooser
opens and on Ctrl-L (`relist_keeps_rows`). Returning is the inverse of leaving: the view a visit
enters after an attach is the one it left, its rows where they were and new ones last, selecting
the session it was in, and a visit opened inside a session selects that session; a session the
listing no longer has, as after a seen ending, leaves the first row selected (`enter_returns`).
Not claimed: which key requests which action, which
the selector's key proofs and the manager suite check, that the chooser sorts exactly when it
opens and on Ctrl-L, which the manager suite checks, and that the highlight follows its row, which
the selector's picker proofs show, that a cursor on a candidate's index selects it, which holds
with an empty query, whose rows are the candidates in order, and that the chooser enters with the
session it returns from or `LINGER_SESSION` names, which the manager suite checks. -/

theorem one_owner (grant : Claim.State → Nat → Nat → Bool) (exclusive : Claim.Exclusive grant)
    {s : Claim.State} (reached : Claim.Reachable grant Claim.enters s) {a b resource : Nat}
    {left right : Claim.Lease} (ha : s.active a = some left) (hb : s.active b = some right)
    (leftUses : left.Uses resource) (rightUses : right.Uses resource) : a = b := by sorry

@[kills one_owner]
theorem one_owner_rejects_socket :
    ¬∀ (grant : Claim.State → Nat → Nat → Bool),
        Claim.Exclusive grant →
          ∀ {s : Claim.State},
            Claim.Reachable grant (fun (socket _ : Bool) => socket) s →
              ∀ {a b resource : Nat} {left right : Claim.Lease},
                s.active a = some left →
                  s.active b = some right → left.Uses resource → right.Uses resource → a = b := by
  sorry

theorem names_one_to_one (t : Names.Table) (wf : Names.Wf t) (a b id : String) :
    (Names.resolve t a = some id → Names.resolve t b = some id → a = b) ∧
      (Names.resolve t a = some id ↔ Names.nameOf t id = some a) ∧
      Names.resolve [] a = Name.check a := by
  sorry

@[kills names_one_to_one]
theorem names_one_to_one_rejects_stale :
    ¬∀ (t : Names.Table),
        Names.Wf t →
          ∀ (a b id : String),
            (Names.resolveStale t a = some id → Names.resolveStale t b = some id → a = b) ∧
              (Names.resolveStale t a = some id ↔ Names.nameOf t id = some a) ∧
              Names.resolveStale [] a = Name.check a := by
  sorry

theorem rename_moves (t : Names.Table) (wf : Names.Wf t) (old new id : String)
    (found : Names.resolve t old = some id) (free : t.lookup new = none) (other : old ≠ new) :
    Names.Wf (Names.rename t old new id) ∧
      Names.resolve (Names.rename t old new id) new = some id ∧
      Names.resolve (Names.rename t old new id) old ≠ some id ∧
      ∀ n, n ≠ old → n ≠ new → Names.resolve (Names.rename t old new id) n = Names.resolve t n := by
  sorry

@[kills rename_moves]
theorem rename_moves_rejects_reid :
    ¬∀ (t : Names.Table),
        Names.Wf t →
          ∀ (old new id : String),
            Names.resolve t old = some id →
              t.lookup new = none →
              old ≠ new →
              Names.Wf (Names.renameReid t old new id) ∧
                Names.resolve (Names.renameReid t old new id) new = some id ∧
                Names.resolve (Names.renameReid t old new id) old ≠ some id ∧
                ∀ n,
                  n ≠ old →
                    n ≠ new →
                    Names.resolve (Names.renameReid t old new id) n = Names.resolve t n := by
  sorry

theorem claim_fresh (t : Names.Table) (wf : Names.Wf t) (name id : String)
    (unnamed : Names.resolve t name = none) (fresh : Names.Fresh id) (unused : id ∉ t.map (·.2)) :
    Names.Wf (Names.claim t name id) ∧
      Names.resolve (Names.claim t name id) name = some id ∧
      ∀ n, n ≠ name → Names.resolve (Names.claim t name id) n = Names.resolve t n := by
  sorry

@[kills claim_fresh]
theorem claim_fresh_rejects_self :
    ¬∀ (t : Names.Table),
        Names.Wf t →
          ∀ (name id : String),
            Names.resolve t name = none →
              Names.Fresh id →
              id ∉ t.map (·.2) →
              Names.Wf (Names.claimSelf t name id) ∧
                Names.resolve (Names.claimSelf t name id) name = some id ∧
                ∀ n,
                  n ≠ name → Names.resolve (Names.claimSelf t name id) n = Names.resolve t n := by
  sorry

theorem nameOf_shown (t : Names.Table) (id name : String) (shown : Names.nameOf t id = some name) :
    (name, id) ∈ t ∨ Name.check id = some name := by sorry

@[kills nameOf_shown]
theorem nameOf_shown_rejects_bare :
    ¬∀ (t : Names.Table) (id name : String),
        Names.nameOfBare t id = some name → (name, id) ∈ t ∨ Name.check id = some name := by
  sorry

theorem rename_plan (valid oldHeld older newHeld : Bool) :
    (Names.Rename.plan valid oldHeld older newHeld = .move ↔
        valid = true ∧ oldHeld = true ∧ newHeld = false ∧ older = false) ∧
      (Names.Rename.plan valid oldHeld older newHeld = .refuse .invalid ↔ valid = false) ∧
      (Names.Rename.plan valid oldHeld older newHeld = .refuse .missing ↔
        valid = true ∧ oldHeld = false) ∧
      (Names.Rename.plan valid oldHeld older newHeld = .refuse .taken ↔
        valid = true ∧ oldHeld = true ∧ newHeld = true) ∧
      (Names.Rename.plan valid oldHeld older newHeld = .refuse .older ↔
        valid = true ∧ oldHeld = true ∧ newHeld = false ∧ older = true) := by
  sorry

@[kills rename_plan]
theorem rename_plan_rejects_move :
    ¬∀ (valid oldHeld older newHeld : Bool),
        ((fun (_ _ _ _ : Bool) => Names.Rename.Plan.move) valid oldHeld older newHeld = .move ↔
            valid = true ∧ oldHeld = true ∧ newHeld = false ∧ older = false) ∧
          ((fun (_ _ _ _ : Bool) => Names.Rename.Plan.move) valid oldHeld older newHeld =
              .refuse .invalid ↔
            valid = false) ∧
          ((fun (_ _ _ _ : Bool) => Names.Rename.Plan.move) valid oldHeld older newHeld =
              .refuse .missing ↔
            valid = true ∧ oldHeld = false) ∧
          ((fun (_ _ _ _ : Bool) => Names.Rename.Plan.move) valid oldHeld older newHeld =
              .refuse .taken ↔
            valid = true ∧ oldHeld = true ∧ newHeld = true) ∧
          ((fun (_ _ _ _ : Bool) => Names.Rename.Plan.move) valid oldHeld older newHeld =
              .refuse .older ↔
            valid = true ∧ oldHeld = true ∧ newHeld = false ∧ older = true) := by
  sorry

theorem one_name
    (placed : Bool → (String → Option Nat) → String → String → Option (String → Option Nat))
    (noReplace : Os.Place.NoReplace placed) (first second : Names.Op) (names : String → Option Nat)
    (src src' dst : String) (file : Nat) (named : names src = some file)
    {after : String → Option Nat}
    (placedFirst : (Names.call first).run placed names src dst = some after) :
    after dst = some file ∧ (Names.call second).run placed after src' dst = none := by sorry

@[kills one_name]
theorem one_name_rejects_replace :
    ¬∀ (placed : Bool → (String → Option Nat) → String → String → Option (String → Option Nat)),
        Os.Place.NoReplace placed →
          ∀ (first second : Names.Op) (names : String → Option Nat) (src src' dst : String)
            (file : Nat),
            names src = some file →
              ∀ {after : String → Option Nat},
                ((fun (_ : Names.Op) => Names.Call.replace) first).run placed names src dst =
                    some after →
                  after dst = some file ∧
                    ((fun (_ : Names.Op) => Names.Call.replace) second).run placed after src' dst =
                      none := by
  sorry

theorem step_fields_kept (s : State) (ev : Event) :
    (Session.step s ev).1.fieldList = s.fieldList := by sorry

@[kills step_fields_kept]
theorem step_fields_kept_rejects_reset :
    ¬∀ (s : State) (ev : Event),
        ((fun (s : State) (_ : Event) =>
                (State.boot s.terminal [] [], ([] : List (Effect Replay.Plan))))
              s ev).1.fieldList =
          s.fieldList := by
  sorry

theorem infoFields_boot (vt : Vt.Vt) (fields metadata : List (String × String)) (evs : List Event) :
    ∃ rest,
      Session.infoFields (Session.trace Session.step (State.boot vt fields metadata) evs).1 =
        metadata ++ rest := by
  sorry

@[kills infoFields_boot]
theorem infoFields_boot_rejects_reboot :
    ¬∀ (vt : Vt.Vt) (fields metadata : List (String × String)) (evs : List Event),
        ∃ rest,
          Session.infoFields
              (Session.trace
                  (fun (_ : State) (_ : Event) =>
                    (State.boot (Vt.Vt.init 1 1) [] [], ([] : List (Effect Replay.Plan))))
                  (State.boot vt fields metadata) evs).1 =
            metadata ++ rest := by
  sorry

theorem step_terminal_sources (s : State) (ev : Event) :
    (∃ chunk, ev = .ptyOut chunk ∧ (Session.step s ev).1.terminal = s.terminal.feed chunk) ∨
      ∃ sizes : List (Nat × Nat),
        (Session.step s ev).1.terminal =
          sizes.foldl (fun v (size : Nat × Nat) => v.resize size.1 size.2) s.terminal := by
  sorry

@[kills step_terminal_sources]
theorem step_terminal_sources_rejects_print :
    ¬∀ (s : State) (ev : Event),
        (∃ chunk,
            ev = .ptyOut chunk ∧
              ((fun (s : State) (_ : Event) =>
                      (State.boot (s.terminal.feed [0x41]) [] [], ([] : List (Effect Replay.Plan))))
                    s ev).1.terminal =
                s.terminal.feed chunk) ∨
          ∃ sizes : List (Nat × Nat),
            ((fun (s : State) (_ : Event) =>
                    (State.boot (s.terminal.feed [0x41]) [] [], ([] : List (Effect Replay.Plan))))
                  s ev).1.terminal =
              sizes.foldl (fun v (size : Nat × Nat) => v.resize size.1 size.2) s.terminal := by
  sorry

theorem step_owned (s : State) (ev : Event) :
    (∀ chunk,
        ev = .ptyOut chunk →
          (Session.step s ev).1.owned =
            s.owned.hear (Mediation.feed s.terminal s.scanner chunk).vt.windowTitle
              (Mediation.feed s.terminal s.scanner chunk).asks
              (Mediation.feed s.terminal s.scanner chunk).notice
              (Mediation.feed s.terminal s.scanner chunk).marks (seenBy s.roster)) ∧
      (∀ o, ev = .observed o → (Session.step s ev).1.owned = s.owned.observe o) ∧
      (∀ d, ev = .notified d → (Session.step s ev).1.owned = s.owned.notify d) ∧
      (∀ id chunk,
        ev = .bytes id chunk →
          (Session.step s ev).1.owned = s.owned ∨
            (Session.step s ev).1.owned = s.owned.look ∧
              ∃ c, s.client? id = some c ∧ ∃ m ∈ (c.decoder.feed chunk).2, m.Looks) ∧
      (∀ (id : Nat) (chunk : List UInt8) (c : Client) (dec : Wire.Decoder) (m : Wire.Msg),
        ev = .bytes id chunk →
          s.client? id = some c →
          c.attached = false →
          c.decoder.feed chunk = (dec, [m]) →
          dec.errored = false → m.Looks → (Session.step s ev).1.owned = s.owned.look) ∧
      ((∀ chunk, ev ≠ .ptyOut chunk) →
        (∀ o, ev ≠ .observed o) →
        (∀ id chunk, ev ≠ .bytes id chunk) →
        (∀ d, ev ≠ .notified d) → (Session.step s ev).1.owned = s.owned) ∧
      (Status.classify { fresh := s.seen.fresh, unseen := s.seen.unseen, asks := s.seen.asks } =
          .asks ↔
        s.owned.asks = true) := by
  sorry

@[kills step_owned]
theorem step_owned_rejects_rung :
    ¬∀ (s : State) (ev : Event),
        (∀ chunk,
            ev = .ptyOut chunk →
              ((fun (s : State) (_ : Event) => Session.step s (.ptyOut [0x07])) s ev).1.owned =
                s.owned.hear (Mediation.feed s.terminal s.scanner chunk).vt.windowTitle
                  (Mediation.feed s.terminal s.scanner chunk).asks
                  (Mediation.feed s.terminal s.scanner chunk).notice
                  (Mediation.feed s.terminal s.scanner chunk).marks (seenBy s.roster)) ∧
          (∀ o,
            ev = .observed o →
              ((fun (s : State) (_ : Event) => Session.step s (.ptyOut [0x07])) s ev).1.owned =
                s.owned.observe o) ∧
          (∀ d,
            ev = .notified d →
              ((fun (s : State) (_ : Event) => Session.step s (.ptyOut [0x07])) s ev).1.owned =
                s.owned.notify d) ∧
          (∀ id chunk,
            ev = .bytes id chunk →
              ((fun (s : State) (_ : Event) => Session.step s (.ptyOut [0x07])) s ev).1.owned =
                  s.owned ∨
                ((fun (s : State) (_ : Event) => Session.step s (.ptyOut [0x07])) s ev).1.owned =
                    s.owned.look ∧
                  ∃ c, s.client? id = some c ∧ ∃ m ∈ (c.decoder.feed chunk).2, m.Looks) ∧
          (∀ (id : Nat) (chunk : List UInt8) (c : Client) (dec : Wire.Decoder) (m : Wire.Msg),
            ev = .bytes id chunk →
              s.client? id = some c →
              c.attached = false →
              c.decoder.feed chunk = (dec, [m]) →
              dec.errored = false →
              m.Looks →
              ((fun (s : State) (_ : Event) => Session.step s (.ptyOut [0x07])) s ev).1.owned =
                s.owned.look) ∧
          ((∀ chunk, ev ≠ .ptyOut chunk) →
            (∀ o, ev ≠ .observed o) →
            (∀ id chunk, ev ≠ .bytes id chunk) →
            (∀ d, ev ≠ .notified d) →
            ((fun (s : State) (_ : Event) => Session.step s (.ptyOut [0x07])) s ev).1.owned =
              s.owned) ∧
          (Status.classify { fresh := s.seen.fresh, unseen := s.seen.unseen, asks := s.seen.asks } =
              .asks ↔
            s.owned.asks = true) := by
  sorry

@[kills step_owned]
theorem step_owned_rejects_lumped :
    ¬∀ (s : State) (ev : Event),
        (∀ chunk,
            ev = .ptyOut chunk →
              (Session.step s ev).1.owned =
                s.owned.hear (Mediation.feed s.terminal s.scanner chunk).vt.windowTitle
                  (Mediation.feed s.terminal s.scanner chunk).asks
                  (Mediation.feed s.terminal s.scanner chunk).notice
                  (Mediation.feed s.terminal s.scanner chunk).marks (seenBy s.roster)) ∧
          (∀ o, ev = .observed o → (Session.step s ev).1.owned = s.owned.observe o) ∧
          (∀ d, ev = .notified d → (Session.step s ev).1.owned = s.owned.notify d) ∧
          (∀ id chunk,
            ev = .bytes id chunk →
              (Session.step s ev).1.owned = s.owned ∨
                (Session.step s ev).1.owned = s.owned.look ∧
                  ∃ c, s.client? id = some c ∧ ∃ m ∈ (c.decoder.feed chunk).2, m.Looks) ∧
          (∀ (id : Nat) (chunk : List UInt8) (c : Client) (dec : Wire.Decoder) (m : Wire.Msg),
            ev = .bytes id chunk →
              s.client? id = some c →
              c.attached = false →
              c.decoder.feed chunk = (dec, [m]) →
              dec.errored = false → m.Looks → (Session.step s ev).1.owned = s.owned.look) ∧
          ((∀ chunk, ev ≠ .ptyOut chunk) →
            (∀ o, ev ≠ .observed o) →
            (∀ id chunk, ev ≠ .bytes id chunk) →
            (∀ d, ev ≠ .notified d) → (Session.step s ev).1.owned = s.owned) ∧
          (Status.lumped Status.classify
                { fresh := s.seen.fresh, unseen := s.seen.unseen, asks := s.seen.asks } =
              .asks ↔
            s.owned.asks = true) := by
  sorry

theorem notify_exact (received : Nat → List (List UInt8) → List (List UInt8))
    (whole : Os.Dgram.Whole received) (vt : Vt.Vt) (fields metadata : List (String × String))
    (evs : List Event) (sent : List (List UInt8)) (fits : ∀ d ∈ sent, d.length ≤ Notify.cap)
    (heard : Notify.heard evs = received Notify.cap sent) :
    (Session.trace Session.step (State.boot vt fields metadata) evs).1.owned.ready =
        Notify.ready sent ∧
      (Session.trace Session.step (State.boot vt fields metadata) evs).1.owned.status =
        Notify.status sent := by
  sorry

@[kills notify_exact]
theorem notify_exact_rejects_output :
    ¬∀ (received : Nat → List (List UInt8) → List (List UInt8)),
        Os.Dgram.Whole received →
          ∀ (vt : Vt.Vt) (fields metadata : List (String × String)) (evs : List Event)
            (sent : List (List UInt8)),
            (∀ d ∈ sent, d.length ≤ Notify.cap) →
              Notify.heard evs = received Notify.cap sent →
              (Session.trace (Session.outputNotifies Session.step) (State.boot vt fields metadata)
                      evs).1.owned.ready =
                  Notify.ready sent ∧
                (Session.trace (Session.outputNotifies Session.step) (State.boot vt fields metadata)
                      evs).1.owned.status =
                  Notify.status sent := by
  sorry

theorem start_plan (live saved : Bool) :
    (Start.plan live saved = .take ↔ live = false ∧ saved = false) ∧
      (Start.plan live saved = .running ↔ live = true) ∧
      (Start.plan live saved = .saved ↔ live = false ∧ saved = true) := by
  sorry

@[kills start_plan]
theorem start_plan_rejects_take :
    ¬∀ (live saved : Bool),
        ((fun (_ _ : Bool) => Start.Plan.take) live saved = .take ↔ live = false ∧ saved = false) ∧
          ((fun (_ _ : Bool) => Start.Plan.take) live saved = .running ↔ live = true) ∧
          ((fun (_ _ : Bool) => Start.Plan.take) live saved = .saved ↔
            live = false ∧ saved = true) := by
  sorry

theorem run_bytes_isolates (s : State) (id : Nat) (chunks : List (List UInt8)) {other : Nat}
    (h : other ≠ id) :
    (Session.trace Session.step s (chunks.map (Event.bytes id))).1.client? other =
      s.client? other := by
  sorry

@[kills run_bytes_isolates]
theorem run_bytes_isolates_rejects_reset :
    ¬∀ (s : State) (id : Nat) (chunks : List (List UInt8)) {other : Nat},
        other ≠ id →
          (Session.trace
                  (fun _ _ => (State.boot (Vt.Vt.init 1 1) [] [], ([] : List (Effect Replay.Plan))))
                  s (chunks.map (Event.bytes id))).1.client?
              other =
            s.client? other := by
  sorry

theorem run_readonly (s : State) (id : Nat) (chunks : List (List UInt8)) {c : Client}
    (hc : s.client? id = some c) (attached : c.attached = true) (watcher : c.mode = .readOnly) :
    (Session.trace Session.step s (chunks.map (Event.bytes id))).1.terminal = s.terminal ∧
      (Session.trace Session.step s (chunks.map (Event.bytes id))).1.fieldList = s.fieldList ∧
      ∀ eff ∈ (Session.trace Session.step s (chunks.map (Event.bytes id))).2,
        (∃ m, eff = .send id m) ∨ eff = .close id ∨ eff = .checkpoint := by
  sorry

@[kills run_readonly]
theorem run_readonly_rejects_kill :
    ¬∀ (s : State) (id : Nat) (chunks : List (List UInt8)) {c : Client},
        (fun (_ : State) (i : Nat) =>
                some ({ id := i, attached := true, mode := .readOnly } : Client))
              s id =
            some c →
          c.attached = true →
          c.mode = .readOnly →
          (Session.trace (fun s _ => (s, ([.stopProgram] : List (Effect Replay.Plan)))) s
                  (chunks.map (Event.bytes id))).1.terminal =
              s.terminal ∧
            (Session.trace (fun s _ => (s, ([.stopProgram] : List (Effect Replay.Plan)))) s
                  (chunks.map (Event.bytes id))).1.fieldList =
              s.fieldList ∧
            ∀
              eff ∈
                (Session.trace (fun s _ => (s, ([.stopProgram] : List (Effect Replay.Plan)))) s
                    (chunks.map (Event.bytes id))).2,
              (∃ m, eff = .send id m) ∨ eff = .close id ∨ eff = .checkpoint := by
  sorry

theorem step_attach_mode (s : State) (id : Nat) (chunk : List UInt8) {c : Client}
    {dec : Wire.Decoder} {mode : Mode} {cols rows : UInt32} (hc : s.client? id = some c)
    (fresh : c.attached = false) (read : c.decoder.feed chunk = (dec, [.attach mode cols rows]))
    (healthy : dec.errored = false) :
    ∃ c',
      (Session.step s (.bytes id chunk)).1.client? id = some c' ∧
        c'.attached = true ∧ c'.mode = mode := by
  sorry

@[kills step_attach_mode]
theorem step_attach_mode_rejects_unsized :
    ¬∀ (s : State) (id : Nat) (chunk : List UInt8) {c : Client} {dec : Wire.Decoder} {mode : Mode}
        {cols rows : UInt32},
        (fun (s : State) (i : Nat) =>
                (s.client? i).map fun c =>
                  { c with mode := if c.cols = 0 ∨ c.rows = 0 then .readOnly else c.mode })
              s id =
            some c →
          c.attached = false →
          c.decoder.feed chunk = (dec, [.attach mode cols rows]) →
          dec.errored = false →
          ∃ c',
            (fun (s : State) (i : Nat) =>
                    (s.client? i).map fun c =>
                      { c with mode := if c.cols = 0 ∨ c.rows = 0 then .readOnly else c.mode })
                  (Session.step s (.bytes id chunk)).1 id =
                some c' ∧
              c'.attached = true ∧ c'.mode = mode := by
  sorry

theorem step_resize_mode (s : State) (id : Nat) (chunk : List UInt8) {c : Client}
    {dec : Wire.Decoder} {sizes : List (UInt32 × UInt32)} (hc : s.client? id = some c)
    (read : c.decoder.feed chunk = (dec, sizes.map fun size => .resize size.1 size.2))
    (healthy : dec.errored = false) :
    ((Session.step s (.bytes id chunk)).1.client? id).map (·.mode) = some c.mode := by sorry

@[kills step_resize_mode]
theorem step_resize_mode_rejects_unsized :
    ¬∀ (s : State) (id : Nat) (chunk : List UInt8) {c : Client} {dec : Wire.Decoder}
        {sizes : List (UInt32 × UInt32)},
        (fun (s : State) (i : Nat) =>
                (s.client? i).map fun c =>
                  { c with mode := if c.cols = 0 ∨ c.rows = 0 then .readOnly else c.mode })
              s id =
            some c →
          c.decoder.feed chunk = (dec, sizes.map fun size => .resize size.1 size.2) →
          dec.errored = false →
          ((fun (s : State) (i : Nat) =>
                    (s.client? i).map fun c =>
                      { c with mode := if c.cols = 0 ∨ c.rows = 0 then .readOnly else c.mode })
                  (Session.step s (.bytes id chunk)).1 id).map
              (·.mode) =
            some c.mode := by
  sorry

theorem step_resizes_sized (s : State) (ev : Event) (cols rows : UInt32)
    (resized : Effect.resizePty cols rows ∈ (Session.step s ev).2) :
    0 < cols ∧
      0 < rows ∧
      ∃ id chunk c,
        ev = .bytes id chunk ∧
          s.client? id = some c ∧
          ∃ m ∈ (c.decoder.feed chunk).2,
            ∃ mode width height,
              (m = .attach mode width height ∨ m = .resize width height) ∧
                width ≠ 0 ∧
                height ≠ 0 ∧
                cols.toNat = Vt.clampDim width.toNat ∧ rows.toNat = Vt.clampDim height.toNat := by
  sorry

@[kills step_resizes_sized]
theorem step_resizes_sized_rejects_zero :
    ¬∀ (s : State) (ev : Event) (cols rows : UInt32),
        Effect.resizePty cols rows ∈
            ((fun (s : State) (_ : Event) => (s, ([.resizePty 0 0] : List (Effect Replay.Plan)))) s
                ev).2 →
          0 < cols ∧
            0 < rows ∧
            ∃ id chunk c,
              ev = .bytes id chunk ∧
                s.client? id = some c ∧
                ∃ m ∈ (c.decoder.feed chunk).2,
                  ∃ mode width height,
                    (m = .attach mode width height ∨ m = .resize width height) ∧
                      width ≠ 0 ∧
                      height ≠ 0 ∧
                      cols.toNat = Vt.clampDim width.toNat ∧
                      rows.toNat = Vt.clampDim height.toNat := by
  sorry

theorem rowFields_name (socketName : String) (info : List (String × String)) :
    (Listing.rowFields socketName info).lookup "name" = some socketName := by sorry

@[kills rowFields_name]
theorem rowFields_name_rejects_reply :
    ¬∀ (socketName : String) (info : List (String × String)),
        ((fun (_ : String) (info : List (String × String)) => info) socketName info).lookup "name" =
          some socketName := by
  sorry

theorem rowText_sources (width : Option Nat) (layout : Listing.Layout)
    (info info' : List (String × String))
    (h : ∀ key ∈ Listing.sources, info.lookup key = info'.lookup key) :
    Listing.rowText width layout info = Listing.rowText width layout info' := by sorry

@[kills rowText_sources]
theorem rowText_sources_rejects_every_field :
    ¬∀ (width : Option Nat) (layout : Listing.Layout) (info info' : List (String × String)),
        (∀ key ∈ Listing.sources, info.lookup key = info'.lookup key) →
          (fun (_ : Option Nat) (_ : Listing.Layout) (info : List (String × String)) =>
                info.flatMap fun kv => kv.2.toList)
              width layout info =
            (fun (_ : Option Nat) (_ : Listing.Layout) (info : List (String × String)) =>
                info.flatMap fun kv => kv.2.toList)
              width layout info' := by
  sorry

theorem caption_precedence (info : List (String × String)) :
    ((info.lookup "title").getD "" ≠ "" → Listing.caption info = (info.lookup "title").getD "") ∧
      ((info.lookup "title").getD "" = "" →
        (info.lookup "status_text").getD "" ≠ "" →
        Listing.caption info = (info.lookup "status_text").getD "") ∧
      ((info.lookup "title").getD "" = "" →
        (info.lookup "status_text").getD "" = "" →
        Listing.caption info = (info.lookup "description").getD "") ∧
      (Listing.program info = "" ∨
        ¬(Listing.command (Listing.program info)).toList <:+: (Listing.caption info).toList) := by
  sorry

@[kills caption_precedence]
theorem caption_precedence_rejects_described :
    ¬∀ (info : List (String × String)),
        ((info.lookup "title").getD "" ≠ "" →
            (fun (info : List (String × String)) => (info.lookup "description").getD "") info =
              (info.lookup "title").getD "") ∧
          ((info.lookup "title").getD "" = "" →
            (info.lookup "status_text").getD "" ≠ "" →
            (fun (info : List (String × String)) => (info.lookup "description").getD "") info =
              (info.lookup "status_text").getD "") ∧
          ((info.lookup "title").getD "" = "" →
            (info.lookup "status_text").getD "" = "" →
            (fun (info : List (String × String)) => (info.lookup "description").getD "") info =
              (info.lookup "description").getD "") ∧
          (Listing.program info = "" ∨
            ¬(Listing.command (Listing.program info)).toList <:+:
                ((fun (info : List (String × String)) => (info.lookup "description").getD "")
                    info).toList) := by
  sorry

theorem info_foreground (reported seen : UInt32 → Option Foreground)
    (foreground : Pty.Foreground reported seen) (s : State) (master : UInt32) (o : Observation)
    (read : o.foreground = reported master) {fg : Foreground} (found : reported master = some fg) :
    ∃ process,
      seen master = some process ∧
        ("fg", String.intercalate " " process.argv) ∈
          Session.infoFields (Session.step s (.observed o)).1 ∧
        ("fgpid", toString process.pid) ∈ Session.infoFields (Session.step s (.observed o)).1 ∧
        ("fgdir", process.dir) ∈ Session.infoFields (Session.step s (.observed o)).1 := by
  sorry

@[kills info_foreground]
theorem info_foreground_rejects_unreported :
    ¬∀ (reported seen : UInt32 → Option Foreground),
        Pty.Foreground reported seen →
          ∀ (s : State) (master : UInt32) (o : Observation),
            o.foreground = reported master →
              ∀ {fg : Foreground},
                reported master = some fg →
                  ∃ process,
                    seen master = some process ∧
                      ("fg", String.intercalate " " process.argv) ∈
                        (fun (_ : State) => ([] : List (String × String)))
                          (Session.step s (.observed o)).1 ∧
                      ("fgpid", toString process.pid) ∈
                        (fun (_ : State) => ([] : List (String × String)))
                          (Session.step s (.observed o)).1 ∧
                      ("fgdir", process.dir) ∈
                        (fun (_ : State) => ([] : List (String × String)))
                          (Session.step s (.observed o)).1 := by
  sorry

theorem info_echo (reported set : UInt32 → Option Bool) (echo : Pty.Echo reported set) (s : State)
    (master : UInt32) (o : Observation) (read : o.echo = reported master) {on : Bool}
    (found : reported master = some on) :
    set master = some on ∧
      ("echo", toString on) ∈ Session.infoFields (Session.step s (.observed o)).1 := by
  sorry

@[kills info_echo]
theorem info_echo_rejects_unreported :
    ¬∀ (reported set : UInt32 → Option Bool),
        Pty.Echo reported set →
          ∀ (s : State) (master : UInt32) (o : Observation),
            o.echo = reported master →
              ∀ {on : Bool},
                reported master = some on →
                  set master = some on ∧
                    ("echo", toString on) ∈
                      (fun (_ : State) => ([] : List (String × String)))
                        (Session.step s (.observed o)).1 := by
  sorry

theorem rowText_fits (width : Option Nat) (layout : Listing.Layout)
    (info : List (String × String)) :
    (Status.icon (Status.ofName ((info.lookup "status").getD "")) ::
          ' ' :: ((info.lookup "name").getD "").toList.map Terminal.Render.textChar <+:
        Listing.rowText width layout info) ∧
      ∀ w,
        width = some w →
          ((Listing.rowText width layout info).map Terminal.Vt.charWidth).sum ≤
            max w (2 + (((info.lookup "name").getD "").toList.map Terminal.Vt.charWidth).sum) := by
  sorry

@[kills rowText_fits]
theorem rowText_fits_rejects_overflow :
    ¬∀ (width : Option Nat) (layout : Listing.Layout) (info : List (String × String)),
        (Status.icon (Status.ofName ((info.lookup "status").getD "")) ::
              ' ' :: ((info.lookup "name").getD "").toList.map Terminal.Render.textChar <+:
            (fun (_ : Option Nat) (_ : Listing.Layout) (info : List (String × String)) =>
                Status.icon (Status.ofName ((info.lookup "status").getD "")) ::
                  ' ' ::
                  (((info.lookup "name").getD "").toList.map Terminal.Render.textChar ++
                    ['…', '…', '…']))
              width layout info) ∧
          ∀ w,
            width = some w →
              (((fun (_ : Option Nat) (_ : Listing.Layout) (info : List (String × String)) =>
                          Status.icon (Status.ofName ((info.lookup "status").getD "")) ::
                            ' ' ::
                            (((info.lookup "name").getD "").toList.map Terminal.Render.textChar ++
                              ['…', '…', '…']))
                        width layout info).map
                    Terminal.Vt.charWidth).sum ≤
                max w
                  (2 + (((info.lookup "name").getD "").toList.map Terminal.Vt.charWidth).sum) := by
  sorry

theorem rowText_clean (width : Option Nat) (layout : Listing.Layout)
    (info : List (String × String)) :
    ∀ c ∈ Listing.rowText width layout info, Display.Printable c := by sorry

@[kills rowText_clean]
theorem rowText_clean_rejects_escape :
    ¬∀ (width : Option Nat) (layout : Listing.Layout) (info : List (String × String)),
        ∀
          c ∈
            (fun (_ : Option Nat) (_ : Listing.Layout) (_ : List (String × String)) => ['\x1b'])
              width layout info,
          Display.Printable c := by
  sorry

theorem columns_aligned (layout : Listing.Layout) (info : List (String × String)) :
    (∃ blanks : List Char,
        (∀ c ∈ blanks, c = ' ') ∧
          (Listing.columns layout info).flatten = Listing.rowText none layout info ++ blanks) ∧
      ((((info.lookup "name").getD "").toList.map Terminal.Vt.charWidth).sum ≤ layout.nameCol →
        (Listing.columns layout info).map (fun part => (part.map Terminal.Vt.charWidth).sum) =
          layout.spans) := by
  sorry

@[kills columns_aligned]
theorem columns_aligned_rejects_join :
    ¬∀ (layout : Listing.Layout) (info : List (String × String)),
        (∃ blanks : List Char,
            (∀ c ∈ blanks, c = ' ') ∧
              ((fun (_ : Listing.Layout) (info : List (String × String)) =>
                      [(String.intercalate " " (info.map (·.2))).toList])
                    layout info).flatten =
                Listing.rowText none layout info ++ blanks) ∧
          ((((info.lookup "name").getD "").toList.map Terminal.Vt.charWidth).sum ≤ layout.nameCol →
            ((fun (_ : Listing.Layout) (info : List (String × String)) =>
                      [(String.intercalate " " (info.map (·.2))).toList])
                    layout info).map
                (fun part => (part.map Terminal.Vt.charWidth).sum) =
              layout.spans) := by
  sorry

theorem cells_sources (i : Nat) (info info' : List (String × String))
    (h : ∀ key ∈ Listing.cellSources.getD i [], info.lookup key = info'.lookup key) :
    (Listing.cells info)[i]? = (Listing.cells info')[i]? := by sorry

@[kills cells_sources]
theorem cells_sources_rejects_all :
    ¬∀ (i : Nat) (info info' : List (String × String)),
        (∀ key ∈ Listing.cellSources.getD i [], info.lookup key = info'.lookup key) →
          ((fun (info : List (String × String)) => [String.join (info.map (·.2))]) info)[i]? =
            ((fun (info : List (String × String)) => [String.join (info.map (·.2))])
                info')[i]? := by
  sorry

theorem picker_attach_listed (s : Selector.Picker.State) (key : Selector.Key) (target : String)
    (h : Selector.Picker.step s key = .attach target) : target ∈ s.candidates := by sorry

@[kills picker_attach_listed]
theorem picker_attach_listed_rejects_fixed :
    ¬∀ (s : Selector.Picker.State) (key : Selector.Key) (target : String),
        (fun (_ : Selector.Picker.State) (_ : Selector.Key) => Selector.Picker.Outcome.attach "s") s
              key =
            .attach target →
          target ∈ s.candidates := by
  sorry

theorem picker_create_new (s : Selector.Picker.State) (key : Selector.Key) (target : String)
    (h : Selector.Picker.step s key = .create target) :
    target ∉ s.candidates ∧ target ≠ "" ∧ Name.Accepted ((target.splitOn "@").headD "") := by sorry

@[kills picker_create_new]
theorem picker_create_new_rejects_empty :
    ¬∀ (s : Selector.Picker.State) (key : Selector.Key) (target : String),
        (fun (_ : Selector.Picker.State) (_ : Selector.Key) => Selector.Picker.Outcome.create "") s
              key =
            .create target →
          target ∉ s.candidates ∧ target ≠ "" ∧ Name.Accepted ((target.splitOn "@").headD "") := by
  sorry

theorem relist_keeps_rows (s : Selector.Picker.State) (resort : Bool) (ordered : List String)
    (descriptions : List (String × String)) :
    (Selector.Picker.relist s resort ordered descriptions).candidates =
        (if resort then ordered
        else
          s.candidates.filter (fun t => ordered.contains t) ++
            ordered.filter fun t => !s.candidates.contains t) ∧
      (Selector.Picker.relist s resort ordered descriptions).query = s.query ∧
      (Selector.Picker.relist s resort ordered descriptions).descriptions = descriptions := by
  sorry

@[kills relist_keeps_rows]
theorem relist_keeps_rows_rejects_resort :
    ¬∀ (s : Selector.Picker.State) (resort : Bool) (ordered : List String)
        (descriptions : List (String × String)),
        ((fun (s : Selector.Picker.State) (_ : Bool) (ordered : List String)
                    (descriptions : List (String × String)) =>
                  { s with
                    candidates := ordered, descriptions := descriptions })
                s resort ordered descriptions).candidates =
            (if resort then ordered
            else
              s.candidates.filter (fun t => ordered.contains t) ++
                ordered.filter fun t => !s.candidates.contains t) ∧
          ((fun (s : Selector.Picker.State) (_ : Bool) (ordered : List String)
                    (descriptions : List (String × String)) =>
                  { s with
                    candidates := ordered, descriptions := descriptions })
                s resort ordered descriptions).query =
            s.query ∧
          ((fun (s : Selector.Picker.State) (_ : Bool) (ordered : List String)
                    (descriptions : List (String × String)) =>
                  { s with
                    candidates := ordered, descriptions := descriptions })
                s resort ordered descriptions).descriptions =
            descriptions := by
  sorry

theorem enter_returns (s : Selector.Picker.State) (shown : List String) (focus : Option String)
    (ordered : List String) (descriptions : List (String × String)) :
    (Selector.Picker.enter s shown focus ordered descriptions).candidates =
        shown.filter (fun t => ordered.contains t) ++ ordered.filter (fun t => !shown.contains t) ∧
      (Selector.Picker.enter s shown focus ordered descriptions).query = s.query ∧
      (∀ t,
        focus = some t →
          s.query = "" →
          t ∈ ordered →
          (Selector.Picker.enter s shown focus ordered
                  descriptions).candidates[(Selector.Picker.enter s shown focus ordered
                  descriptions).cursor]? =
            some t) ∧
      ((∀ t, focus = some t → s.query = "" → t ∉ ordered) →
        (Selector.Picker.enter s shown focus ordered descriptions).cursor = 0) := by
  sorry

@[kills enter_returns]
theorem enter_returns_rejects_top :
    ¬∀ (s : Selector.Picker.State) (shown : List String) (focus : Option String)
        (ordered : List String) (descriptions : List (String × String)),
        ((fun (s : Selector.Picker.State) (_ : List String) (_ : Option String)
                    (ordered : List String) (descriptions : List (String × String)) =>
                  { s with
                    candidates := ordered, descriptions := descriptions, cursor := 0 })
                s shown focus ordered descriptions).candidates =
            shown.filter (fun t => ordered.contains t) ++
              ordered.filter (fun t => !shown.contains t) ∧
          ((fun (s : Selector.Picker.State) (_ : List String) (_ : Option String)
                    (ordered : List String) (descriptions : List (String × String)) =>
                  { s with
                    candidates := ordered, descriptions := descriptions, cursor := 0 })
                s shown focus ordered descriptions).query =
            s.query ∧
          (∀ t,
            focus = some t →
              s.query = "" →
              t ∈ ordered →
              ((fun (s : Selector.Picker.State) (_ : List String) (_ : Option String)
                          (ordered : List String) (descriptions : List (String × String)) =>
                        { s with
                          candidates := ordered, descriptions := descriptions, cursor := 0 })
                      s shown focus ordered
                      descriptions).candidates[((fun (s : Selector.Picker.State) (_ : List String)
                          (_ : Option String) (ordered : List String)
                          (descriptions : List (String × String)) =>
                        { s with
                          candidates := ordered, descriptions := descriptions, cursor := 0 })
                      s shown focus ordered descriptions).cursor]? =
                some t) ∧
          ((∀ t, focus = some t → s.query = "" → t ∉ ordered) →
            ((fun (s : Selector.Picker.State) (_ : List String) (_ : Option String)
                      (ordered : List String) (descriptions : List (String × String)) =>
                    { s with
                      candidates := ordered, descriptions := descriptions, cursor := 0 })
                  s shown focus ordered descriptions).cursor =
              0) := by
  sorry

theorem picker_eof_empty (s : Selector.Picker.State) :
    Selector.Picker.step s .deleteCharEof = if s.query = "" then .cancel else .stay s := by sorry

@[kills picker_eof_empty]
theorem picker_eof_empty_rejects_cancel :
    ¬∀ (s : Selector.Picker.State),
        (fun (_ : Selector.Picker.State) (_ : Selector.Key) => Selector.Picker.Outcome.cancel) s
            .deleteCharEof =
          if s.query = "" then .cancel else .stay s := by
  sorry

/-! ## 3. Exactness

`start` runs its program in the caller's directory and with the caller's environment, which only
`LINGER_SESSION`, `TERM`, `COLORTERM`, `TERM_PROGRAM` and `TERM_PROGRAM_VERSION` change, when the
operating system runs what linger asks (`start_runs`, in part 4); `LINGER_SESSION` holds the
session's ID, which no rename changes. A program that cannot start there
makes `start` return what `env -C` would, and a resume that runs elsewhere than its saved directory
says so. An unset or empty variable reads as its standard default: SHELL as `sh`, HOME as no
remotes file and no directory a resume runs in, and `LINGER_NO_DETACH_KEY`, set to anything, turns
the detach key off for a writable attach only (`env_defaults`).

A command on a `name@host` target runs through the host's transport, a command that runs linger
elsewhere: the one the remotes file names for the host, or else ssh. Linger runs the transport's
attach command for an attach, which gives the far end a terminal, and its query command for every
other verb, followed by `linger` and the verb and words encoded as plain words, with the target
placed as `targetOperands` places it for `attach` and `capture`, which read it with `targetArgs`
(`transport_exact`). A transport that runs a `linger` with exactly the plain words after its own,
or nothing (`Transport.Delivers`), delivers words the remote entry routes as exactly the verb and
words, whatever they hold. SSH joins those words with spaces into one line, which any login shell
that passes plain words on (`Shell.Literal`) hands the remote linger as they are
(`command_exact`); the remote entry decodes them before it routes the command line, and refuses
one that does not decode as a usage error. POSIX quoting would not: fish reads a backslash inside
single quotes, so a quoted word could close its quote there and run what follows. Not claimed:
that a transport reaches its host, which is the transport's, its keys, jumps, latency and
authentication included; that the remote linger decodes, since an older one refuses the encoded
line as a usage error; nor that a command line fits the remote host's argument limit.

The command line is complete and minimal. Every operation of the session model, `Op`, has a
command, a word that names it, and exactly one: one word names each
operation, so no command is another's alias or a second reader or writer of what another reads or
writes, the table has one row for each operation, in `Op.all`'s order, each word names its own
row, and help lists the rows, each line its command's word (`commands_minimal`). A command exists
only for an `Op`, so adding one changes `Op`, and with it what linger claims. Every field a
listing reports is human, shown in rows as clean text, or machine, exact and only in `--porcelain`;
each has one owner, the user, through one command, the program or linger (`fields_owned`): the
name is the one field the user owns, which `rename` writes, and says what the session is, and the
program's fields are readings of what its session keeps of it alone, as part 2 says. Not claimed: that
the session CLI dispatches each command line through `lookup` to its row's operation, which its IO
code does and the manager suite checks, with any other word a usage error; nor that each option is
one parameter of one operation with one spelling, which the suites check.

A tmux-resurrect save is a source linger reads and never writes. A pane takes its name from its
window, as a key, a later pane's name that an earlier one took made unique with a natural-order
suffix, `-2`, `-3`, and keeps the window's own text as its description. Its panes are rows of `ls`
and the chooser exactly while linger keeps no record of their names, no socket, checkpoint, end
record or names entry that names them or leads to them (`listed_unrecorded`), so whether a pane was dealt with is read from the records linger
already keeps. An attach or a resume of such a pane writes its checkpoint only while no record
names it, and otherwise writes nothing, so it never replaces a record (`adopt_exclusive`). A kill
of one writes an end record and nothing else, so the pane stays hidden while the end records are
kept (`dismiss_hides`), which no command removes, and that record says only what happened: a kill
dismissed a pane linger never ran, so nothing ended, and `wait` answers for the name, as before
the kill, that no session has it (`dismissal_happened`). Not claimed: that the IO code
decides each of these holding the name's locks and creates the checkpoint only where no file is,
which the interop suite checks, and that linger writes, moves or deletes nothing in tmux's
directory, which the interop suite checks by hashing it around every command. -/

theorem route_exact (args : List String) :
    App.Entry.route args =
      if args.head? = some Remote.marker then
        (Remote.decode args.tail).elim .malformed App.Entry.Route.of
      else App.Entry.Route.of args := by
  sorry

@[kills route_exact]
theorem route_exact_rejects_selector :
    ¬∀ (args : List String),
        (fun (args : List String) => App.Entry.Route.session args) args =
          if args.head? = some Remote.marker then
            (Remote.decode args.tail).elim .malformed App.Entry.Route.of
          else App.Entry.Route.of args := by
  sorry

theorem commands_minimal :
    (∀ op : App.Commands.Op,
        ∃ word,
          (App.Commands.lookup word).map (·.op) = some op ∧
            ∀ other, (App.Commands.lookup other).map (·.op) = some op → other = word) ∧
      App.Commands.table.map (·.op) = App.Commands.Op.all ∧
      App.Commands.helpLines = App.Commands.table.map App.Commands.helpLine ∧
      ∀ command ∈ App.Commands.table,
        App.Commands.lookup command.word = some command ∧
          ∃ rest, App.Commands.helpLine command = command.word ++ " " ++ rest := by
  sorry

@[kills commands_minimal]
theorem commands_minimal_rejects_aliased :
    ¬((∀ op : App.Commands.Op,
          ∃ word,
            ((fun (word : String) => App.Commands.aliased.find? fun command => command.word == word)
                      word).map
                  (·.op) =
                some op ∧
              ∀ other,
                ((fun (word : String) =>
                            App.Commands.aliased.find? fun command => command.word == word)
                          other).map
                      (·.op) =
                    some op →
                  other = word) ∧
        App.Commands.table.map (·.op) = App.Commands.Op.all ∧
        App.Commands.helpLines = App.Commands.table.map App.Commands.helpLine ∧
        ∀ command ∈ App.Commands.table,
          (fun (word : String) => App.Commands.aliased.find? fun command => command.word == word)
                command.word =
              some command ∧
            ∃ rest, App.Commands.helpLine command = command.word ++ " " ++ rest) := by
  sorry

theorem fields_owned :
    (App.Fields.table.map (·.key)).Nodup ∧
      (∀ key ∈ Listing.sources, key ∈ App.Fields.table.map (·.key)) ∧
      (∀ f ∈ App.Fields.table, (f.kind = .human ↔ f.key ∈ Listing.shown)) ∧
      (∀ f ∈ App.Fields.table,
        ∀ op,
          f.owner = .user op →
            op ∈ App.Commands.Op.all ∧ ∀ g ∈ App.Fields.table, g.owner = .user op → g = f) ∧
      ∀ (vt vt' : Vt.Vt) (fields fields' metadata : List (String × String)) (evs evs' : List Event),
        (∀ kv ∈ metadata, App.Fields.owns App.Fields.table .program kv.1 = false) →
          (Session.trace Session.step (State.boot vt fields metadata) evs).1.owned =
            (Session.trace Session.step (State.boot vt' fields' metadata) evs').1.owned →
          (Session.infoFields
                  (Session.trace Session.step (State.boot vt fields metadata) evs).1).filter
              (fun kv => App.Fields.owns App.Fields.table .program kv.1) =
            (Session.infoFields
                  (Session.trace Session.step (State.boot vt' fields' metadata) evs').1).filter
              fun kv => App.Fields.owns App.Fields.table .program kv.1 := by
  sorry

@[kills fields_owned]
theorem fields_owned_rejects_named_twice :
    ¬((App.Fields.namedTwice.map (·.key)).Nodup ∧
        (∀ key ∈ Listing.sources, key ∈ App.Fields.namedTwice.map (·.key)) ∧
        (∀ f ∈ App.Fields.namedTwice, (f.kind = .human ↔ f.key ∈ Listing.shown)) ∧
        (∀ f ∈ App.Fields.namedTwice,
          ∀ op,
            f.owner = .user op →
              op ∈ App.Commands.Op.all ∧ ∀ g ∈ App.Fields.namedTwice, g.owner = .user op → g = f) ∧
        ∀ (vt vt' : Vt.Vt) (fields fields' metadata : List (String × String))
          (evs evs' : List Event),
          (∀ kv ∈ metadata, App.Fields.owns App.Fields.namedTwice .program kv.1 = false) →
            (Session.trace Session.step (State.boot vt fields metadata) evs).1.owned =
              (Session.trace Session.step (State.boot vt' fields' metadata) evs').1.owned →
            (Session.infoFields
                    (Session.trace Session.step (State.boot vt fields metadata) evs).1).filter
                (fun kv => App.Fields.owns App.Fields.namedTwice .program kv.1) =
              (Session.infoFields
                    (Session.trace Session.step (State.boot vt' fields' metadata) evs').1).filter
                fun kv => App.Fields.owns App.Fields.namedTwice .program kv.1) := by
  sorry

@[kills fields_owned]
theorem fields_owned_rejects_counted :
    ¬((App.Fields.table.map (·.key)).Nodup ∧
        (∀ key ∈ Listing.sources, key ∈ App.Fields.table.map (·.key)) ∧
        (∀ f ∈ App.Fields.table, (f.kind = .human ↔ f.key ∈ Listing.shown)) ∧
        (∀ f ∈ App.Fields.table,
          ∀ op,
            f.owner = .user op →
              op ∈ App.Commands.Op.all ∧ ∀ g ∈ App.Fields.table, g.owner = .user op → g = f) ∧
        ∀ (vt vt' : Vt.Vt) (fields fields' metadata : List (String × String))
          (evs evs' : List Event),
          (∀ kv ∈ metadata, App.Fields.owns App.Fields.table .program kv.1 = false) →
            (Session.trace Session.step (State.boot vt fields metadata) evs).1.owned =
              (Session.trace Session.step (State.boot vt' fields' metadata) evs').1.owned →
            ((fun (s : State) => [("title", toString s.roster.length)])
                    (Session.trace Session.step (State.boot vt fields metadata) evs).1).filter
                (fun kv => App.Fields.owns App.Fields.table .program kv.1) =
              ((fun (s : State) => [("title", toString s.roster.length)])
                    (Session.trace Session.step (State.boot vt' fields' metadata) evs').1).filter
                fun kv => App.Fields.owns App.Fields.table .program kv.1) := by
  sorry

theorem listed_unrecorded (records : Session.Records) (panes : List Import.Resurrect.Pane)
    (pane : Import.Resurrect.Pane) :
    pane ∈ Import.Resurrect.listed records panes ↔
      pane ∈ panes ∧ records.holds pane.name = false := by
  sorry

@[kills listed_unrecorded]
theorem listed_unrecorded_rejects_never :
    ¬∀ (records : Session.Records) (panes : List Import.Resurrect.Pane)
        (pane : Import.Resurrect.Pane),
        pane ∈
            (fun (_ : Session.Records) (_ : List Import.Resurrect.Pane) =>
                ([] : List Import.Resurrect.Pane))
              records panes ↔
          pane ∈ panes ∧ records.holds pane.name = false := by
  sorry

theorem adopt_exclusive (records : Session.Records) (pane : Import.Resurrect.Pane)
    (contents : Option String) :
    Import.Resurrect.adopt records pane contents =
      if records.holds pane.name then none
      else some (Import.Resurrect.checkpoint pane contents) := by
  sorry

@[kills adopt_exclusive]
theorem adopt_exclusive_rejects_overwrite :
    ¬∀ (records : Session.Records) (pane : Import.Resurrect.Pane) (contents : Option String),
        (fun (_ : Session.Records) (pane : Import.Resurrect.Pane) (contents : Option String) =>
              some (Import.Resurrect.checkpoint pane contents))
            records pane contents =
          if records.holds pane.name then none
          else some (Import.Resurrect.checkpoint pane contents) := by
  sorry

theorem dismiss_hides (records later : Session.Records) (pane : Import.Resurrect.Pane)
    (panes : List Import.Resurrect.Pane)
    (kept : ∀ name ∈ (Import.Resurrect.dismiss records pane.name).endings, name ∈ later.endings) :
    (Import.Resurrect.dismiss records pane.name).sockets = records.sockets ∧
      (Import.Resurrect.dismiss records pane.name).checkpoints = records.checkpoints ∧
      (∀ name,
        name ∈ (Import.Resurrect.dismiss records pane.name).endings ↔
          name = pane.name ∨ name ∈ records.endings) ∧
      pane ∉ Import.Resurrect.listed later panes := by
  sorry

@[kills dismiss_hides]
theorem dismiss_hides_rejects_memory :
    ¬∀ (records later : Session.Records) (pane : Import.Resurrect.Pane)
        (panes : List Import.Resurrect.Pane),
        (∀
            name ∈
              ((fun (records : Session.Records) (_ : String) => records) records pane.name).endings,
            name ∈ later.endings) →
          ((fun (records : Session.Records) (_ : String) => records) records pane.name).sockets =
              records.sockets ∧
            ((fun (records : Session.Records) (_ : String) => records) records
                  pane.name).checkpoints =
              records.checkpoints ∧
            (∀ name,
              name ∈
                  ((fun (records : Session.Records) (_ : String) => records) records
                      pane.name).endings ↔
                name = pane.name ∨ name ∈ records.endings) ∧
            pane ∉ Import.Resurrect.listed later panes := by
  sorry

theorem dismissal_happened (afterSave : List UInt8 → Option (List UInt8))
    (kept : Record.Kept afterSave) (deadline heldSince : Option Nat) (now : Nat) :
    Record.answer (afterSave (Record.encode Import.Resurrect.dismissal)) = some .dismissed ∧
      Wait.decide deadline heldSince now
          (.recorded (Record.answer (afterSave (Record.encode Import.Resurrect.dismissal)))) =
        .answer .notFound := by
  sorry

@[kills dismissal_happened]
theorem dismissal_happened_rejects_hangup :
    ¬∀ (afterSave : List UInt8 → Option (List UInt8)),
        Record.Kept afterSave →
          ∀ (deadline heldSince : Option Nat) (now : Nat),
            Record.answer (afterSave (Record.encode (Record.ended (.signaled 1)))) =
                some .dismissed ∧
              Wait.decide deadline heldSince now
                  (.recorded
                    (Record.answer (afterSave (Record.encode (Record.ended (.signaled 1)))))) =
                .answer .notFound := by
  sorry

theorem names_round_trip (s name : String) :
    (Name.accept s = some name ↔ name = s ∧ Name.Accepted s) ∧
      (Name.Usable name →
        Remote.targetArgs (Remote.targetOperands name) = some (name, []) ∧
          Names.entryName (Names.entryFile name) = some name) ∧
      Name.accept "build · ✓ tests" = some "build · ✓ tests" := by
  sorry

@[kills names_round_trip]
theorem names_round_trip_rejects_keyed :
    ¬∀ (s name : String),
        (Name.keyed s = some name ↔ name = s ∧ Name.Accepted s) ∧
          (Name.Usable name →
            Remote.targetArgs (Remote.targetOperands name) = some (name, []) ∧
              Names.entryName (Names.entryFile name) = some name) ∧
          Name.keyed "build · ✓ tests" = some "build · ✓ tests" := by
  sorry

theorem check_eq_some_iff (s result : String) :
    Name.check s = some result ↔ result = s ∧ Name.Valid s := by sorry

@[kills check_eq_some_iff]
theorem check_eq_some_iff_rejects_any :
    ¬∀ (s result : String), (fun s => some s) s = some result ↔ result = s ∧ Name.Valid s := by
  sorry

theorem command_exact (split : String → List String) (literal : Remote.Shell.Literal split)
    (verb : String) (words : List String) :
    ∃ args,
      split (String.intercalate " " (Remote.commandWords verb words)) = "linger" :: args ∧
        App.Entry.route args = App.Entry.Route.of (verb :: words) := by
  sorry

@[kills command_exact]
theorem command_exact_rejects_quoted :
    ¬∀ (split : String → List String),
        Remote.Shell.Literal split →
          ∀ (verb : String) (words : List String),
            ∃ args,
              split
                    (String.intercalate " "
                      ((fun (verb : String) (words : List String) =>
                          ("linger" :: verb :: words).map fun word =>
                            String.ofList
                              ('\'' ::
                                  word.toList.flatMap
                                    (fun c => if c = '\'' then ['\'', '\\', '\'', '\''] else [c]) ++
                                ['\'']))
                        verb words)) =
                  "linger" :: args ∧
                App.Entry.route args = App.Entry.Route.of (verb :: words) := by
  sorry

theorem transport_exact (t : Remote.Transport) (verb name : String) (options args : List String)
    (deliver : List String → List String → Option (List String))
    (delivers : Remote.Transport.Delivers deliver t) :
    (∃ line,
        Remote.targetArgv t verb options name args =
            (if verb = "attach" then t.attach else t.query) ++ "linger" :: line ∧
          (∀ received,
            deliver (if verb = "attach" then t.attach else t.query) ("linger" :: line) =
                some received →
              received = "linger" :: line) ∧
          App.Entry.route line =
            App.Entry.Route.of
              (verb :: options ++
                (if verb = "attach" ∨ verb = "capture" ∨ verb = "ls" then Remote.targetOperands name
                else [name]) ++
                args)) ∧
      Remote.targetArgs (Remote.targetOperands name ++ args) = some (name, args) := by
  sorry

@[kills transport_exact]
theorem transport_exact_rejects_ssh :
    ¬∀ (t : Remote.Transport) (verb name : String) (options args : List String)
        (deliver : List String → List String → Option (List String)),
        Remote.Transport.Delivers deliver t →
          (∃ line,
              (fun (_ : Remote.Transport) (_ : String) (_ : List String) (_ : String)
                        (_ : List String) =>
                      ["ssh", "-T", "--"])
                    t verb options name args =
                  (if verb = "attach" then t.attach else t.query) ++ "linger" :: line ∧
                (∀ received,
                  deliver (if verb = "attach" then t.attach else t.query) ("linger" :: line) =
                      some received →
                    received = "linger" :: line) ∧
                App.Entry.route line =
                  App.Entry.Route.of
                    (verb :: options ++
                      (if verb = "attach" ∨ verb = "capture" ∨ verb = "ls" then
                        Remote.targetOperands name
                      else [name]) ++
                      args)) ∧
            Remote.targetArgs (Remote.targetOperands name ++ args) = some (name, args) := by
  sorry

@[kills transport_exact]
theorem transport_exact_rejects_unread :
    ¬∀ (t : Remote.Transport) (verb name : String) (options args : List String)
        (deliver : List String → List String → Option (List String)),
        Remote.Transport.Delivers deliver t →
          (∃ line,
              Remote.targetArgv t verb options name args =
                  (if verb = "attach" then t.attach else t.query) ++ "linger" :: line ∧
                (∀ received,
                  deliver (if verb = "attach" then t.attach else t.query) ("linger" :: line) =
                      some received →
                    received = "linger" :: line) ∧
                App.Entry.route line =
                  App.Entry.Route.of
                    (verb :: options ++
                      (if verb = "attach" ∨ verb = "capture" ∨ verb = "ls" then
                        (fun (_ : String) => ([] : List String)) name
                      else [name]) ++
                      args)) ∧
            Remote.targetArgs ((fun (_ : String) => ([] : List String)) name ++ args) =
              some (name, args) := by
  sorry

theorem env_defaults (home flag : Option String) (shell dir saved : String) (named : shell ≠ "")
    (set : dir ≠ "") :
    (Os.Env.shellOf (some shell) = shell ∧
        Os.Env.shellOf none = "sh" ∧ Os.Env.shellOf (some "") = "sh") ∧
      (Os.Env.remotesFile home = none ↔ home = none ∨ home = some "") ∧
      (Os.Env.detachEnabled true flag = true ∧ Os.Env.detachEnabled false flag = flag.isNone) ∧
      Os.Env.resumeDir home saved true = some saved ∧
      Os.Env.resumeDir (some dir) saved false = some dir ∧
      Os.Env.resumeDir none saved false = none ∧ Os.Env.resumeDir (some "") saved false = none := by
  sorry

@[kills env_defaults]
theorem env_defaults_rejects_fixed :
    ¬∀ (home flag : Option String) (shell dir saved : String),
        shell ≠ "" →
          dir ≠ "" →
          ((fun (_ : Option String) => "sh") (some shell) = shell ∧
              (fun (_ : Option String) => "sh") none = "sh" ∧
              (fun (_ : Option String) => "sh") (some "") = "sh") ∧
            (Os.Env.remotesFile home = none ↔ home = none ∨ home = some "") ∧
            (Os.Env.detachEnabled true flag = true ∧
              Os.Env.detachEnabled false flag = flag.isNone) ∧
            Os.Env.resumeDir home saved true = some saved ∧
            Os.Env.resumeDir (some dir) saved false = some dir ∧
            Os.Env.resumeDir none saved false = none ∧
            Os.Env.resumeDir (some "") saved false = none := by
  sorry

@[kills env_defaults]
theorem env_defaults_rejects_shared :
    ¬∀ (home flag : Option String) (shell dir saved : String),
        shell ≠ "" →
          dir ≠ "" →
          (Os.Env.shellOf (some shell) = shell ∧
              Os.Env.shellOf none = "sh" ∧ Os.Env.shellOf (some "") = "sh") ∧
            ((fun (_ : Option String) => some "remotes") home = none ↔
              home = none ∨ home = some "") ∧
            (Os.Env.detachEnabled true flag = true ∧
              Os.Env.detachEnabled false flag = flag.isNone) ∧
            Os.Env.resumeDir home saved true = some saved ∧
            Os.Env.resumeDir (some dir) saved false = some dir ∧
            Os.Env.resumeDir none saved false = none ∧
            Os.Env.resumeDir (some "") saved false = none := by
  sorry

@[kills env_defaults]
theorem env_defaults_rejects_never :
    ¬∀ (home flag : Option String) (shell dir saved : String),
        shell ≠ "" →
          dir ≠ "" →
          (Os.Env.shellOf (some shell) = shell ∧
              Os.Env.shellOf none = "sh" ∧ Os.Env.shellOf (some "") = "sh") ∧
            (Os.Env.remotesFile home = none ↔ home = none ∨ home = some "") ∧
            ((fun (_ : Bool) (_ : Option String) => false) true flag = true ∧
              (fun (_ : Bool) (_ : Option String) => false) false flag = flag.isNone) ∧
            Os.Env.resumeDir home saved true = some saved ∧
            Os.Env.resumeDir (some dir) saved false = some dir ∧
            Os.Env.resumeDir none saved false = none ∧
            Os.Env.resumeDir (some "") saved false = none := by
  sorry

@[kills env_defaults]
theorem env_defaults_rejects_gone :
    ¬∀ (home flag : Option String) (shell dir saved : String),
        shell ≠ "" →
          dir ≠ "" →
          (Os.Env.shellOf (some shell) = shell ∧
              Os.Env.shellOf none = "sh" ∧ Os.Env.shellOf (some "") = "sh") ∧
            (Os.Env.remotesFile home = none ↔ home = none ∨ home = some "") ∧
            (Os.Env.detachEnabled true flag = true ∧
              Os.Env.detachEnabled false flag = flag.isNone) ∧
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

theorem checkHosts_ok_iff (hosts result : List String) :
    Remote.checkHosts hosts = .ok result ↔
      result = hosts ∧ hosts.Nodup ∧ ∀ x ∈ hosts, Remote.hostClean x = true := by
  sorry

@[kills checkHosts_ok_iff]
theorem checkHosts_ok_iff_rejects_any :
    ¬∀ (hosts result : List String),
        (fun (hosts : List String) => (.ok hosts : Except String (List String))) hosts =
            .ok result ↔
          result = hosts ∧ hosts.Nodup ∧ ∀ x ∈ hosts, Remote.hostClean x = true := by
  sorry

theorem failureStatus_exact (why : String) :
    Start.failureStatus (.directory why) = 125 ∧
      Start.failureStatus (.notFound why) = 127 ∧ Start.failureStatus (.notRunnable why) = 126 := by
  sorry

@[kills failureStatus_exact]
theorem failureStatus_exact_rejects_alike :
    ¬∀ (why : String),
        (fun (_ : Spawn.Failure) => (1 : UInt8)) (.directory why) = 125 ∧
          (fun (_ : Spawn.Failure) => (1 : UInt8)) (.notFound why) = 127 ∧
          (fun (_ : Spawn.Failure) => (1 : UInt8)) (.notRunnable why) = 126 := by
  sorry

theorem metadata_dirs (name pid created cmd dir : String) (saved : Option String) :
    ("start_dir", dir) ∈ Start.metadata name pid created cmd dir saved ∧
      ∀ d,
        ("saved_dir", d) ∈ Start.metadata name pid created cmd dir saved ↔
          saved = some d ∧ d ≠ dir := by
  sorry

@[kills metadata_dirs]
theorem metadata_dirs_rejects_silent :
    ¬∀ (name pid created cmd dir : String) (saved : Option String),
        ("start_dir", dir) ∈
            (fun (_ _ _ _ dir : String) (_ : Option String) => [("start_dir", dir)]) name pid
              created cmd dir saved ∧
          ∀ d,
            ("saved_dir", d) ∈
                (fun (_ _ _ _ dir : String) (_ : Option String) => [("start_dir", dir)]) name pid
                  created cmd dir saved ↔
              saved = some d ∧ d ≠ dir := by
  sorry

/-! ## 4. Program identity

A session runs the program its creation named, with its words, or without a command the
session's shell alone, which is what a resume runs again on the saved session's last screen
(`resume_restores`, in part 7). The operating system runs it as asked: the world claim
`Spawn.Runs`, which its check and the agent and resume suites test. Its terminal says what it is:
`TERM=xterm-256color`, `COLORTERM=truecolor`, since the session's terminal keeps and repaints
24-bit colour, and linger's name and version; its `NOTIFY_SOCKET` names the socket its daemon
reads its `sd_notify` notifications from, as systemd's does for a service, whatever the command
that asked for the session had; it reads every other variable as the command that asked for the
session has it, but linger's own, whose names begin `LINGER_` (`Start.lingers`), which it never
sees but for its session's `LINGER_SESSION`, so `env -i K=V … linger start` gives it exactly `K=V`
and the session's variables (`start_runs`).

The program starts from what its start asks, never from how linger was started: every signal at its
default action, none blocked, and its terminal on descriptors 0, 1 and 2 with no other open,
whatever the command that asked for the session ignored, blocked or left open, as a shell's `&` job
ignores SIGINT and SIGQUIT and `exec 3>&1` leaves a pipe open (`start_clean`, over the world claim
`Spawn.Clean`, which its check and the agent suite test). Not claimed: the rest of what a program
inherits as any child does, such as resource limits, the file mode mask, scheduling priority and the
user and groups it runs as.

Linger only delivers what a person types: input reaches the program and nothing else of the
session. Two runs from one boot whose events differ only in the bytes of the input messages
clients send, each read whole frames, end in the same session, with the same effects but for the
bytes they write to the program (`input_unrecorded`), so every record a session asks for, a
checkpoint of its terminal, its fields and its metadata, its name's end record and the handoff of
its state, is the same whatever was typed, and none holds what was typed. Not claimed: a read that
cuts a frame, whose start the session holds until the rest arrives; that the daemon hands a session
over only once it holds no such start and has written its program every byte it owed it, which the
upgrade code decides; and that a person's input reaches no file, which the attach suite checks of a
line typed with echo off. -/

theorem input_unrecorded (vt : Vt.Vt) (fields metadata : List (String × String))
    (evs evs' : List Event) (framed : ∀ ev ∈ evs, Framed Wire.encode ev)
    (typed : Typed Wire.encode evs evs') :
    (Session.trace Session.step (State.boot vt fields metadata) evs).1 =
        (Session.trace Session.step (State.boot vt fields metadata) evs').1 ∧
      (Session.trace Session.step (State.boot vt fields metadata) evs).2.map Effect.blind =
        (Session.trace Session.step (State.boot vt fields metadata) evs').2.map Effect.blind := by
  sorry

@[kills input_unrecorded]
theorem input_unrecorded_rejects_kept :
    ¬∀ (vt : Vt.Vt) (fields metadata : List (String × String)) (evs evs' : List Event),
        (∀ ev ∈ evs, Framed Wire.encode ev) →
          Typed Wire.encode evs evs' →
          (Session.trace
                  (Session.keepsInput Session.step fun (s : State) (chunk : List UInt8) =>
                    (Session.step s (.ptyOut chunk)).1)
                  (State.boot vt fields metadata) evs).1 =
              (Session.trace
                  (Session.keepsInput Session.step fun (s : State) (chunk : List UInt8) =>
                    (Session.step s (.ptyOut chunk)).1)
                  (State.boot vt fields metadata) evs').1 ∧
            (Session.trace
                    (Session.keepsInput Session.step fun (s : State) (chunk : List UInt8) =>
                      (Session.step s (.ptyOut chunk)).1)
                    (State.boot vt fields metadata) evs).2.map
                Effect.blind =
              (Session.trace
                    (Session.keepsInput Session.step fun (s : State) (chunk : List UInt8) =>
                      (Session.step s (.ptyOut chunk)).1)
                    (State.boot vt fields metadata) evs').2.map
                Effect.blind := by
  sorry

theorem start_runs (inherited : String → Option String)
    (start :
      String →
        String → Array String → List (String × Option String) → Spawn.Reset → Option Spawn.Started)
    (runs : Spawn.Runs inherited start) (names : List String)
    (named : ∀ key, (inherited key).isSome → key ∈ names) (id notify dir shell : String)
    (argv : List String) {started : Spawn.Started}
    (ok :
      start dir (Start.programOf shell argv).1 (Start.programOf shell argv).2
          (Start.environment id notify names) Start.reset =
        some started) :
    started.argv = argv.headD shell :: argv.drop 1 ∧
      started.dir = dir ∧
      started.env "LINGER_SESSION" = some id ∧
      started.env "TERM" = some "xterm-256color" ∧
      started.env "COLORTERM" = some "truecolor" ∧
      started.env "TERM_PROGRAM" = some "linger" ∧
      started.env "TERM_PROGRAM_VERSION" = some Mediation.versionNumber ∧
      started.env "NOTIFY_SOCKET" = some notify ∧
      ∀ key,
        key ∉
            ["LINGER_SESSION", "TERM", "COLORTERM", "TERM_PROGRAM", "TERM_PROGRAM_VERSION",
              "NOTIFY_SOCKET"] →
          started.env key = if Start.lingers key then none else inherited key := by
  sorry

@[kills start_runs]
theorem start_runs_rejects_passing :
    ¬∀ (inherited : String → Option String)
        (start :
          String →
            String →
            Array String → List (String × Option String) → Spawn.Reset → Option Spawn.Started),
        Spawn.Runs inherited start →
          ∀ (names : List String),
            (∀ key, (inherited key).isSome → key ∈ names) →
              ∀ (id notify dir shell : String) (argv : List String) {started : Spawn.Started},
                start dir (Start.programOf shell argv).1 (Start.programOf shell argv).2
                      ((fun (id notify : String) (_ : List String) =>
                          Start.environment id notify [])
                        id notify names)
                      Start.reset =
                    some started →
                  started.argv = argv.headD shell :: argv.drop 1 ∧
                    started.dir = dir ∧
                    started.env "LINGER_SESSION" = some id ∧
                    started.env "TERM" = some "xterm-256color" ∧
                    started.env "COLORTERM" = some "truecolor" ∧
                    started.env "TERM_PROGRAM" = some "linger" ∧
                    started.env "TERM_PROGRAM_VERSION" = some Mediation.versionNumber ∧
                    started.env "NOTIFY_SOCKET" = some notify ∧
                    ∀ key,
                      key ∉
                          ["LINGER_SESSION", "TERM", "COLORTERM", "TERM_PROGRAM",
                            "TERM_PROGRAM_VERSION", "NOTIFY_SOCKET"] →
                        started.env key = if Start.lingers key then none else inherited key := by
  sorry

theorem start_clean
    (start :
      String →
        String → Array String → List (String × Option String) → Spawn.Reset → Option Spawn.Started)
    (clean : Spawn.Clean start) (name notify dir shell : String) (names argv : List String)
    {started : Spawn.Started}
    (ok :
      start dir (Start.programOf shell argv).1 (Start.programOf shell argv).2
          (Start.environment name notify names) Start.reset =
        some started) :
    (∀ sig, started.ignored sig = false) ∧
      (∀ sig, started.blocked sig = false) ∧
      ∀ fd, started.descriptor fd = if fd < 3 then some .terminal else none := by
  sorry

@[kills start_clean]
theorem start_clean_rejects_inherited :
    ¬∀
        (start :
          String →
            String →
            Array String → List (String × Option String) → Spawn.Reset → Option Spawn.Started),
        Spawn.Clean start →
          ∀ (name notify dir shell : String) (names argv : List String) {started : Spawn.Started},
            start dir (Start.programOf shell argv).1 (Start.programOf shell argv).2
                  (Start.environment name notify names)
                  ({ dispositions := false, mask := true, descriptors := true } : Spawn.Reset) =
                some started →
              (∀ sig, started.ignored sig = false) ∧
                (∀ sig, started.blocked sig = false) ∧
                ∀ fd, started.descriptor fd = if fd < 3 then some .terminal else none := by
  sorry

/-! ## 5. Accountability

A session ends through one ending, whatever ends it (`step_ended_reports`): its program, by itself;
a kill, once the daemon has stopped the program; or SIGHUP, SIGINT, SIGQUIT or SIGTERM to the
daemon, the system stopping linger at logout or shutdown, after which the daemon stops the program
the same way (`step_signal_saves`). Every client attached or waiting hears how the session ended
before the daemon exits, and the daemon leaves its name an end record that says so. A kill discards
the session, and a program's own ending stays exactly until someone has
seen it: one that ends while a client is attached, typist or watcher, is seen as it ends, and the
session then ends as a kill ends it, its checkpoint deleted once every client is told
(`step_ended_reports`, with `seenBy`); one that ends with nobody attached saves its last screen,
as the ending found it, and keeps it, and the first attach to it, in either mode,
shows that screen, then how its program ended, and discards it once it leaves (`visit_result`). A
watcher counts as seeing, since it is shown the same screen and told the same ending as a typist
(`seenBy`); `wait` and `ls` tell the status, not the screen, and `capture` exports it, so
none of them sees it. A session a signal stopped is saved, not ended: everyone hears which signal stopped the daemon and
nothing of an outcome of its program, which `resume` runs again from that screen. When the file
system keeps what linger saves (`Record.Kept`, which its check and the agent suite test), a name's
end record keeps how its last session ended, for whoever asks later: how its program ended, or which
signal stopped its daemon, which never reads as an outcome or an unknown ending; a record its
session left while the program still ran answers that the ending is unknown, and only a name with no
record answers nothing (`record_answer`). `ls` reports each ending in fields no other ending has, a
program's ending in the same fields whether a daemon or an end record tells it
(`endingFields_injective`). `wait` answers with how the session ended when its daemon or the end
record says, for a saved session `saved` with the signal that stopped its daemon, never a status of
its program, and that it could not find out only when that is so: the program's ending is unknown,
or the name stays held, with no daemon answering, from the look that first found it so for longer
than a daemon's ending lasts, and never while a daemon may still be ending, its drain and the
waits of its signals (`wait_held`). Every command answers with one of the answers `Os.Answer`
names, the operating system's vocabulary, the selector as the session commands do, and exits with
its code: a signal's status says which signal, whatever it stopped: a program it killed, a
command it stopped and a session whose daemon it stopped each answer 128 plus its number, as a
shell reports a program that signal ended (`code_documented`), and a chooser cancelled by a key
answers 130, as fzf's does. An attach goes only to a daemon whose `info`
answer reports this version's protocol level, as every daemon of this version does
(`infoFields_protocol`), so a daemon an older linger started, of any earlier level, is refused with
a reason, never sent an attach it would refuse as unknown or drop unanswered. Not claimed: that the
answer comes within the client's wait and that the refusal names the session and the level, which
the attach suite checks against a level-2 daemon, one that reports no level and one that never
answers; that a daemon hears a stop signal, which the operating system delivers through the daemon's
signal pipe and the resume suite checks, and when it cannot make the pipe takes its default action;
that an attached client, the chooser and `ls -r`, given SIGTERM, SIGHUP or SIGINT,
hand their terminal back or retire their transports and answer `stopped` with the first that came,
however late in their cleanup it came, and that `main` then ends the process by that signal, as a
program that does not catch it ends, which the attach, manager and remote suites check, and the
resume suite that a client attached when a signal saves its session answers `saved`; that a client
the model counts as attached when the program ends still reads what it is told, and that an attach
executes the steps `visit_result` names, discarding only the checkpoint it showed and keeping the
session when a signal interrupts the view, which the attach and watch suites check; and that the
process exits with the code of its command's answer, or for `stopped` ends by its signal, which the
type of every executor's result, `main`'s one exit and a gate on the shells keep.

The daemon's driver runs the session's trace. When every effect succeeds, a stop replying how the
program ended, the driver hands the session each event and then what that event's effects feed
back, a stop's reply as the event `stopped`, before the next event; it ends in the state of the
trace of `Session.step` over those events, executes exactly that trace's effects, in order, each
with the state its event left, and exits exactly when one of them asks it to (`run_refines`).
Whatever its effects reply, an executor that answers every effect lets it return and keeps the
session within its bounds (`run_total_safe`), disconnects and failed saves never stop it
(`run_feedback_alive`), and an event whose
effects stop the program ends the session (`run_stop_exits`). Not claimed: which events the
driver hands the session and which effects it executes when an effect fails. -/

theorem step_kill_stops (s : State) (id : Nat) (chunk : List UInt8) {c : Client}
    {dec : Wire.Decoder} {rest : List Wire.Msg} (hc : s.client? id = some c)
    (writable : c.mode = .writable) (read : c.decoder.feed chunk = (dec, .kill :: rest))
    (healthy : dec.errored = false) :
    (Session.step s (.bytes id chunk)).2 = [.stopProgram, .close id] ∧
      (Session.step s (.bytes id chunk)).1.terminal = s.terminal ∧
      (Session.step s (.bytes id chunk)).1.fieldList = s.fieldList := by
  sorry

@[kills step_kill_stops]
theorem step_kill_stops_rejects_exit :
    ¬∀ (s : State) (id : Nat) (chunk : List UInt8) {c : Client} {dec : Wire.Decoder}
        {rest : List Wire.Msg},
        s.client? id = some c →
          c.mode = .writable →
          c.decoder.feed chunk = (dec, .kill :: rest) →
          dec.errored = false →
          ((fun (s : State) (_ : Event) => (s, ([.exit] : List (Effect Replay.Plan)))) s
                  (.bytes id chunk)).2 =
              [.stopProgram, .close id] ∧
            ((fun (s : State) (_ : Event) => (s, ([.exit] : List (Effect Replay.Plan)))) s
                  (.bytes id chunk)).1.terminal =
              s.terminal ∧
            ((fun (s : State) (_ : Event) => (s, ([.exit] : List (Effect Replay.Plan)))) s
                  (.bytes id chunk)).1.fieldList =
              s.fieldList := by
  sorry

theorem step_ended_reports (s : State) (ev : Event) :
    (Effect.exit ∈ (Session.step s ev).2 ↔ (ev.ends (seenBy s.roster)).isSome) ∧
      ∀ e keep,
        ev.ends (seenBy s.roster) = some (e, keep) →
          ∃ front,
            (Session.step s ev).2 =
                front ++
                  [.record e.record, if keep then Effect.checkpoint else Effect.dropCheckpoint,
                    .exit] ∧
              Effect.checkpoint ∉ front ∧
              Effect.dropCheckpoint ∉ front ∧
              (∀ c ∈ s.roster,
                c.attached = true ∨ c.waiting = true → e.told.map (Effect.send c.id) <:+: front) ∧
              (Session.step s ev).1.terminal = s.terminal := by
  sorry

@[kills step_ended_reports]
theorem step_ended_reports_rejects_status :
    ¬∀ (s : State) (ev : Event),
        (Effect.exit ∈
              ((fun s _ =>
                    (s,
                      ([.send 0 (.exited 1), .record (.ended .unknown), .dropCheckpoint, .exit] :
                        List (Effect Replay.Plan))))
                  s ev).2 ↔
            (ev.ends
                (seenBy
                  ((fun (_ : State) => [({ id := 0, attached := true } : Client)]) s))).isSome) ∧
          ∀ e keep,
            ev.ends (seenBy ((fun (_ : State) => [({ id := 0, attached := true } : Client)]) s)) =
                some (e, keep) →
              ∃ front,
                ((fun s _ =>
                          (s,
                            ([.send 0 (.exited 1), .record (.ended .unknown), .dropCheckpoint,
                                .exit] :
                              List (Effect Replay.Plan))))
                        s ev).2 =
                    front ++
                      [.record e.record, if keep then Effect.checkpoint else Effect.dropCheckpoint,
                        .exit] ∧
                  Effect.checkpoint ∉ front ∧
                  Effect.dropCheckpoint ∉ front ∧
                  (∀ c ∈ (fun (_ : State) => [({ id := 0, attached := true } : Client)]) s,
                    c.attached = true ∨ c.waiting = true →
                      e.told.map (Effect.send c.id) <:+: front) ∧
                  ((fun s _ =>
                          (s,
                            ([.send 0 (.exited 1), .record (.ended .unknown), .dropCheckpoint,
                                .exit] :
                              List (Effect Replay.Plan))))
                        s ev).1.terminal =
                    s.terminal := by
  sorry

theorem step_signal_saves (s : State) (n : UInt8) :
    ∃ front,
      (Session.step s (.signal n)).2 =
          .stopProgram :: front ++ [.record (.saved n), .checkpoint, .exit] ∧
        Effect.dropCheckpoint ∉ front ∧
        (∀ c ∈ s.roster,
          c.attached = true ∨ c.waiting = true → Effect.send c.id (.saved n) ∈ front) ∧
        (Session.step s (.signal n)).1.terminal = s.terminal := by
  sorry

@[kills step_signal_saves]
theorem step_signal_saves_rejects_drop :
    ¬∀ (s : State) (n : UInt8),
        ∃ front,
          ((fun (s : State) (_ : Event) =>
                    (s,
                      ([.stopProgram, .record (.saved 15), .dropCheckpoint, .exit] :
                        List (Effect Replay.Plan))))
                  s (.signal n)).2 =
              .stopProgram :: front ++ [.record (.saved n), .checkpoint, .exit] ∧
            Effect.dropCheckpoint ∉ front ∧
            (∀ c ∈ s.roster,
              c.attached = true ∨ c.waiting = true → Effect.send c.id (.saved n) ∈ front) ∧
            ((fun (s : State) (_ : Event) =>
                    (s,
                      ([.stopProgram, .record (.saved 15), .dropCheckpoint, .exit] :
                        List (Effect Replay.Plan))))
                  s (.signal n)).1.terminal =
              s.terminal := by
  sorry

@[kills step_signal_saves]
theorem step_signal_saves_rejects_silent :
    ¬∀ (s : State) (n : UInt8),
        ∃ front,
          ((fun (s : State) (_ : Event) =>
                    (s,
                      ([.stopProgram, .record (.saved 15), .checkpoint, .exit] :
                        List (Effect Replay.Plan))))
                  s (.signal n)).2 =
              .stopProgram :: front ++ [.record (.saved n), .checkpoint, .exit] ∧
            Effect.dropCheckpoint ∉ front ∧
            (∀ c ∈ (fun (_ : State) => [({ id := 0, attached := true } : Client)]) s,
              c.attached = true ∨ c.waiting = true → Effect.send c.id (.saved n) ∈ front) ∧
            ((fun (s : State) (_ : Event) =>
                    (s,
                      ([.stopProgram, .record (.saved 15), .checkpoint, .exit] :
                        List (Effect Replay.Plan))))
                  s (.signal n)).1.terminal =
              s.terminal := by
  sorry

theorem visit_result (afterSave : List UInt8 → Option (List UInt8)) (kept : Record.Kept afterSave)
    (readOnly : Bool) (o : Outcome) (n : UInt8) (seen : Option Seen) :
    App.Recovery.visit readOnly (afterSave (Record.encode (.ended o))) =
        [.show, .tell o, .discard] ∧
      App.Recovery.visit readOnly (afterSave (Record.encode (.saved n))) =
        (if readOnly then [.show] else [.resume]) ∧
      App.Recovery.visit readOnly (afterSave (Record.encode (.running seen))) =
        (if readOnly then [.show] else [.resume]) ∧
      App.Recovery.visit readOnly none = (if readOnly then [.show] else [.resume]) := by
  sorry

@[kills visit_result]
theorem visit_result_rejects_resume :
    ¬∀ (afterSave : List UInt8 → Option (List UInt8)),
        Record.Kept afterSave →
          ∀ (readOnly : Bool) (o : Outcome) (n : UInt8) (seen : Option Seen),
            (fun (readOnly : Bool) (_ : Option (List UInt8)) =>
                    if readOnly then [App.Visit.Step.show] else [App.Visit.Step.resume])
                  readOnly (afterSave (Record.encode (.ended o))) =
                [.show, .tell o, .discard] ∧
              (fun (readOnly : Bool) (_ : Option (List UInt8)) =>
                    if readOnly then [App.Visit.Step.show] else [App.Visit.Step.resume])
                  readOnly (afterSave (Record.encode (.saved n))) =
                (if readOnly then [.show] else [.resume]) ∧
              (fun (readOnly : Bool) (_ : Option (List UInt8)) =>
                    if readOnly then [App.Visit.Step.show] else [App.Visit.Step.resume])
                  readOnly (afterSave (Record.encode (.running seen))) =
                (if readOnly then [.show] else [.resume]) ∧
              (fun (readOnly : Bool) (_ : Option (List UInt8)) =>
                    if readOnly then [App.Visit.Step.show] else [App.Visit.Step.resume])
                  readOnly none =
                (if readOnly then [.show] else [.resume]) := by
  sorry

theorem record_answer (afterSave : List UInt8 → Option (List UInt8)) (kept : Record.Kept afterSave)
    (o : Outcome) (n : UInt8) (seen : Option Seen) (file : Option (List UInt8)) :
    Record.answer (afterSave (Record.encode (.ended o))) = some (.program o) ∧
      Record.answer (afterSave (Record.encode (.saved n))) = some (.saved n) ∧
      Record.answer (afterSave (Record.encode (.running seen))) = some (.program .unknown) ∧
      (Record.answer file).isSome = file.isSome := by
  sorry

@[kills record_answer]
theorem record_answer_rejects_unknown :
    ¬∀ (afterSave : List UInt8 → Option (List UInt8)),
        Record.Kept afterSave →
          ∀ (o : Outcome) (n : UInt8) (seen : Option Seen) (file : Option (List UInt8)),
            (fun (_ : Option (List UInt8)) => some (Ending.program .unknown))
                  (afterSave (Record.encode (.ended o))) =
                some (.program o) ∧
              (fun (_ : Option (List UInt8)) => some (Ending.program .unknown))
                  (afterSave (Record.encode (.saved n))) =
                some (.saved n) ∧
              (fun (_ : Option (List UInt8)) => some (Ending.program .unknown))
                  (afterSave (Record.encode (.running seen))) =
                some (.program .unknown) ∧
              ((fun (_ : Option (List UInt8)) => some (Ending.program .unknown)) file).isSome =
                file.isSome := by
  sorry

@[kills record_answer]
theorem record_answer_rejects_running :
    ¬∀ (afterSave : List UInt8 → Option (List UInt8)),
        Record.Kept afterSave →
          ∀ (o : Outcome) (n : UInt8) (seen : Option Seen) (file : Option (List UInt8)),
            Record.answer
                  (afterSave ((fun (_ : Record) => Record.encode (.running none)) (.ended o))) =
                some (.program o) ∧
              Record.answer
                  (afterSave ((fun (_ : Record) => Record.encode (.running none)) (.saved n))) =
                some (.saved n) ∧
              Record.answer
                  (afterSave
                    ((fun (_ : Record) => Record.encode (.running none)) (.running seen))) =
                some (.program .unknown) ∧
              (Record.answer file).isSome = file.isSome := by
  sorry

theorem wait_ending (deadline heldSince : Option Nat) (now : Nat) (e : Ending) :
    Wait.decide deadline heldSince now (.ended e) = .answer e.answer ∧
      Wait.decide deadline heldSince now (.recorded (some e)) = .answer e.answer := by
  sorry

@[kills wait_ending]
theorem wait_ending_rejects_failed :
    ¬∀ (deadline heldSince : Option Nat) (now : Nat) (e : Ending),
        (fun (_ _ : Option Nat) (_ : Nat) (_ : Wait.Heard) => Wait.Next.answer .failed) deadline
              heldSince now (.ended e) =
            .answer e.answer ∧
          (fun (_ _ : Option Nat) (_ : Nat) (_ : Wait.Heard) => Wait.Next.answer .failed) deadline
              heldSince now (.recorded (some e)) =
            .answer e.answer := by
  sorry

theorem wait_held (deadline heldSince : Option Nat) (now : Nat) (heard : Wait.Heard) :
    (Wait.decide deadline heldSince now heard = .answer .failed ↔
        heard = .ended (.program .unknown) ∨
          heard = .recorded (some (.program .unknown)) ∨
          heard = .held ∧ ∃ since, heldSince = some since ∧ since + Wait.heldNameMs ≤ now) ∧
      (heard = .held →
        (∀ due, deadline = some due → now < due) →
        (∀ since, heldSince = some since → now < since + Wait.heldNameMs) →
        Wait.decide deadline heldSince now heard = .again (some (heldSince.getD now))) ∧
      (heard = .held →
        ∀ since,
          heldSince = some since →
            now < since + (Session.drainTimeoutMs + (Session.ending.map (·.wait)).sum) →
            Wait.decide deadline heldSince now heard ≠ .answer .failed) := by
  sorry

@[kills wait_held]
theorem wait_held_rejects_eager :
    ¬∀ (deadline heldSince : Option Nat) (now : Nat) (heard : Wait.Heard),
        ((fun (_ _ : Option Nat) (_ : Nat) (_ : Wait.Heard) => Wait.Next.answer .failed) deadline
                heldSince now heard =
              .answer .failed ↔
            heard = .ended (.program .unknown) ∨
              heard = .recorded (some (.program .unknown)) ∨
              heard = .held ∧ ∃ since, heldSince = some since ∧ since + Wait.heldNameMs ≤ now) ∧
          (heard = .held →
            (∀ due, deadline = some due → now < due) →
            (∀ since, heldSince = some since → now < since + Wait.heldNameMs) →
            (fun (_ _ : Option Nat) (_ : Nat) (_ : Wait.Heard) => Wait.Next.answer .failed) deadline
                heldSince now heard =
              .again (some (heldSince.getD now))) ∧
          (heard = .held →
            ∀ since,
              heldSince = some since →
                now < since + (Session.drainTimeoutMs + (Session.ending.map (·.wait)).sum) →
                (fun (_ _ : Option Nat) (_ : Nat) (_ : Wait.Heard) => Wait.Next.answer .failed)
                    deadline heldSince now heard ≠
                  .answer .failed) := by
  sorry

@[kills wait_held]
theorem wait_held_rejects_drain :
    ¬∀ (deadline heldSince : Option Nat) (now : Nat) (heard : Wait.Heard),
        (Wait.decide deadline heldSince now heard = .answer .failed ↔
            heard = .ended (.program .unknown) ∨
              heard = .recorded (some (.program .unknown)) ∨
              heard = .held ∧
                ∃ since, heldSince = some since ∧ since + Session.drainTimeoutMs ≤ now) ∧
          (heard = .held →
            (∀ due, deadline = some due → now < due) →
            (∀ since, heldSince = some since → now < since + Session.drainTimeoutMs) →
            Wait.decide deadline heldSince now heard = .again (some (heldSince.getD now))) ∧
          (heard = .held →
            ∀ since,
              heldSince = some since →
                now < since + (Session.drainTimeoutMs + (Session.ending.map (·.wait)).sum) →
                Wait.decide deadline heldSince now heard ≠ .answer .failed) := by
  sorry

theorem code_documented (status : UInt32) (signal : UInt8) :
    Os.Answer.code .done = 0 ∧
      Os.Answer.code .notDone = 1 ∧
      Os.Answer.code .usage = 2 ∧
      Os.Answer.code .timedOut = 124 ∧
      Os.Answer.code .failed = 125 ∧
      Os.Answer.code .cannotRun = 126 ∧
      Os.Answer.code .notFound = 127 ∧
      Os.Answer.code .cancelled = 130 ∧
      Os.Answer.code (.stopped signal) = 128 + signal.toUInt32 ∧
      Os.Answer.code (.saved signal) = 128 + signal.toUInt32 ∧
      Os.Answer.code (.program status) = status := by
  sorry

@[kills code_documented]
theorem code_documented_rejects_zero :
    ¬∀ (status : UInt32) (signal : UInt8),
        (fun (_ : Os.Answer) => (0 : UInt32)) .done = 0 ∧
          (fun (_ : Os.Answer) => (0 : UInt32)) .notDone = 1 ∧
          (fun (_ : Os.Answer) => (0 : UInt32)) .usage = 2 ∧
          (fun (_ : Os.Answer) => (0 : UInt32)) .timedOut = 124 ∧
          (fun (_ : Os.Answer) => (0 : UInt32)) .failed = 125 ∧
          (fun (_ : Os.Answer) => (0 : UInt32)) .cannotRun = 126 ∧
          (fun (_ : Os.Answer) => (0 : UInt32)) .notFound = 127 ∧
          (fun (_ : Os.Answer) => (0 : UInt32)) .cancelled = 130 ∧
          (fun (_ : Os.Answer) => (0 : UInt32)) (.stopped signal) = 128 + signal.toUInt32 ∧
          (fun (_ : Os.Answer) => (0 : UInt32)) (.saved signal) = 128 + signal.toUInt32 ∧
          (fun (_ : Os.Answer) => (0 : UInt32)) (.program status) = status := by
  sorry

@[kills code_documented]
theorem code_documented_rejects_lumped :
    ¬∀ (status : UInt32) (signal : UInt8),
        Os.Answer.lumped .done = 0 ∧
          Os.Answer.lumped .notDone = 1 ∧
          Os.Answer.lumped .usage = 2 ∧
          Os.Answer.lumped .timedOut = 124 ∧
          Os.Answer.lumped .failed = 125 ∧
          Os.Answer.lumped .cannotRun = 126 ∧
          Os.Answer.lumped .notFound = 127 ∧
          Os.Answer.lumped .cancelled = 130 ∧
          Os.Answer.lumped (.stopped signal) = 128 + signal.toUInt32 ∧
          Os.Answer.lumped (.saved signal) = 128 + signal.toUInt32 ∧
          Os.Answer.lumped (.program status) = status := by
  sorry

theorem endingFields_injective :
    (∀ o, Session.endingFields (.program o) = Session.outcomeFields o) ∧
      ∀ e₁ e₂, Session.endingFields e₁ = Session.endingFields e₂ → e₁ = e₂ := by
  sorry

@[kills endingFields_injective]
theorem endingFields_injective_rejects_unknown :
    ¬((∀ o,
          (fun (e : Ending) =>
                Session.endingFields (if e = .saved 15 then .program .unknown else e))
              (.program o) =
            Session.outcomeFields o) ∧
        ∀ e₁ e₂,
          (fun (e : Ending) =>
                  Session.endingFields (if e = .saved 15 then .program .unknown else e))
                e₁ =
              (fun (e : Ending) =>
                  Session.endingFields (if e = .saved 15 then .program .unknown else e))
                e₂ →
            e₁ = e₂) := by
  sorry

@[kills endingFields_injective]
theorem endingFields_injective_rejects_silence :
    ¬((∀ o,
          Session.endingFields (.program o) =
            (fun (_ : Outcome) => ([] : List (String × String))) o) ∧
        ∀ e₁ e₂, Session.endingFields e₁ = Session.endingFields e₂ → e₁ = e₂) := by
  sorry

theorem infoFields_protocol (s : State) :
    ("protocol", toString Wire.protocol) ∈ Session.infoFields s := by sorry

@[kills infoFields_protocol]
theorem infoFields_protocol_rejects_empty :
    ¬∀ (s : State),
        ("protocol", toString Wire.protocol) ∈
          (fun (_ : State) => ([] : List (String × String))) s := by
  sorry

theorem admits_level (level : Option Nat) :
    Wire.admits level = true ↔ level = some Wire.protocol := by sorry

@[kills admits_level]
theorem admits_level_rejects_any :
    ¬∀ (level : Option Nat),
        (fun (_ : Option Nat) => true) level = true ↔ level = some Wire.protocol := by
  sorry

theorem step_unknown_refused (s : State) (id : Nat) (chunk : List UInt8) {c : Client}
    {dec : Wire.Decoder} {tag : UInt8} {payload : List UInt8} (hc : s.client? id = some c)
    (read : c.decoder.feed chunk = (dec, [.unknown tag payload])) (healthy : dec.errored = false) :
    (Session.step s (.bytes id chunk)).2 = [.send id (.err "unknown message".toUTF8.toList)] ∧
      (Session.step s (.bytes id chunk)).1.terminal = s.terminal ∧
      (Session.step s (.bytes id chunk)).1.fieldList = s.fieldList := by
  sorry

@[kills step_unknown_refused]
theorem step_unknown_refused_rejects_silence :
    ¬∀ (s : State) (id : Nat) (chunk : List UInt8) {c : Client} {dec : Wire.Decoder} {tag : UInt8}
        {payload : List UInt8},
        s.client? id = some c →
          c.decoder.feed chunk = (dec, [.unknown tag payload]) →
          dec.errored = false →
          ((fun (s : State) (_ : Event) => (s, ([] : List (Effect Replay.Plan)))) s
                  (.bytes id chunk)).2 =
              [.send id (.err "unknown message".toUTF8.toList)] ∧
            ((fun (s : State) (_ : Event) => (s, ([] : List (Effect Replay.Plan)))) s
                  (.bytes id chunk)).1.terminal =
              s.terminal ∧
            ((fun (s : State) (_ : Event) => (s, ([] : List (Effect Replay.Plan)))) s
                  (.bytes id chunk)).1.fieldList =
              s.fieldList := by
  sorry

theorem run_refines {World : Type}
    (execute : State → World → (eff : Effect Replay.Plan) → Id (World × Driver.Reply eff))
    (ending : Outcome)
    (succeeds : ∀ st world eff, (execute st world eff).2 = Driver.success ending eff)
    (r : Driver.Result State World) (events : List Event) (running : r.exiting = false) :
    ∃ handled exits,
      Driver.Handles Session.step ending r.st events handled exits ∧
        (Driver.run execute r events).st = (Session.trace Session.step r.st handled).1 ∧
        (Driver.run execute r events).world =
          (Session.trace (Driver.withState Session.step) r.st handled).2.foldl
            (fun world (asked : State × Effect Replay.Plan) => (execute asked.1 world asked.2).1)
            r.world ∧
        (Driver.run execute r events).exiting = exits := by
  sorry

@[kills run_refines]
theorem run_refines_rejects_inert :
    ¬∀ {World : Type}
        (execute : State → World → (eff : Effect Replay.Plan) → Id (World × Driver.Reply eff))
        (ending : Outcome),
        (∀ st world eff, (execute st world eff).2 = Driver.success ending eff) →
          ∀ (r : Driver.Result State World) (events : List Event),
            r.exiting = false →
              ∃ handled exits,
                Driver.Handles Session.step ending r.st events handled exits ∧
                  (Driver.inert execute r events).st = (Session.trace Session.step r.st handled).1 ∧
                  (Driver.inert execute r events).world =
                    (Session.trace (Driver.withState Session.step) r.st handled).2.foldl
                      (fun world (asked : State × Effect Replay.Plan) =>
                        (execute asked.1 world asked.2).1)
                      r.world ∧
                  (Driver.inert execute r events).exiting = exits := by
  sorry

theorem run_total_safe {World ε : Type}
    (execute : State → World → (eff : Effect Replay.Plan) → Except ε (World × Driver.Reply eff))
    (hw : Driver.Responds execute) (r : Driver.Result State World) (events : List Event)
    (hb : Bounds State.roster State.fieldList State.scanner r.st)
    (hlive :
      Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
        (Checkpoint.Decoded Checkpoint.loadBytes) r.st.terminal) :
    ∃ out,
      Driver.run execute r events = .ok out ∧
        Bounds State.roster State.fieldList State.scanner out.st ∧
        Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
          (Checkpoint.Decoded Checkpoint.loadBytes) out.st.terminal := by
  sorry

@[kills run_total_safe]
theorem run_total_safe_rejects_jump :
    ¬∀ {World ε : Type}
        (execute :
          State → World → (eff : Effect Replay.Plan) → Except ε (World × Driver.Reply eff)),
        Driver.Responds execute →
          ∀ (r : Driver.Result State World) (events : List Event),
            Bounds State.roster
                (fun st =>
                  if st.terminal.colCount = 80 then [] else List.replicate (maxFields + 1) ("", ""))
                State.scanner r.st →
              Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
                (Checkpoint.Decoded Checkpoint.loadBytes) r.st.terminal →
              ∃ out,
                Driver.jump (State.boot (Vt.Vt.init 1 1) [] []) execute r events = .ok out ∧
                  Bounds State.roster
                    (fun st =>
                      if st.terminal.colCount = 80 then []
                      else List.replicate (maxFields + 1) ("", ""))
                    State.scanner out.st ∧
                  Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
                    (Checkpoint.Decoded Checkpoint.loadBytes) out.st.terminal := by
  sorry

theorem run_feedback_alive {World : Type}
    (execute : State → World → (eff : Effect Replay.Plan) → Id (World × Driver.Reply eff))
    (r : Driver.Result State World) (events : List Event) (running : r.exiting = false)
    (failures : ∀ ev ∈ events, ev = .checkpointFailed ∨ ∃ id, ev = .closed id) :
    (Driver.run execute r events).exiting = false := by sorry

@[kills run_feedback_alive]
theorem run_feedback_alive_rejects_halt :
    ¬∀ {World : Type}
        (execute : State → World → (eff : Effect Replay.Plan) → Id (World × Driver.Reply eff))
        (r : Driver.Result State World) (events : List Event),
        r.exiting = false →
          (∀ ev ∈ events, ev = .checkpointFailed ∨ ∃ id, ev = .closed id) →
          (Driver.halt execute r events).exiting = false := by
  sorry

theorem run_stop_exits {World : Type}
    (execute : State → World → (eff : Effect Replay.Plan) → Id (World × Driver.Reply eff))
    (r : Driver.Result State World) (ev : Event) (running : r.exiting = false)
    (stops : Effect.stopProgram ∈ (Session.step r.st ev).2) :
    (Driver.run execute r [ev]).exiting = true := by sorry

@[kills run_stop_exits]
theorem run_stop_exits_rejects_jump :
    ¬∀ {World : Type}
        (execute : State → World → (eff : Effect Replay.Plan) → Id (World × Driver.Reply eff))
        (r : Driver.Result State World) (ev : Event),
        r.exiting = false →
          Effect.stopProgram ∈ (Session.step r.st ev).2 →
          (Driver.jump (State.boot (Vt.Vt.init 1 1) [] []) execute r [ev]).exiting = true := by
  sorry

/-! ## 6. Bounded and clean

After every batch of events, the driver leaves the session's clients, record fields, frame decoders and pty
scanner within their caps, whatever its effects reply, when its executor answers every effect
(`run_total_safe`, in part 5); when every effect succeeds, the states it leaves are those of the
session's trace (`run_refines`, in part 5). The pty's input queue never owes more than its cap, nor
does a client's output queue the daemon keeps (`reachableIn_bound`, `reachableOut_bound`); a read
gets at most one rendered reply, its frames followed by `done`, and when it leaves its sender
unattached at most one pty resize (`step_bytes_one_reply`); every frame of program output carries at
most 64 KiB (`step_output_delivered`, in part 1); and a tmux capture's bytes are at most twice its
limit (`captureBytes_bounded`). When a session ends, by a kill or by its program's own end, the
daemon signals the program's whole process group, which the program leads, at once, and the rest
of its terminal session, with each signal of `Session.ending`: SIGHUP, then SIGKILL to what still
runs at the grace, `Stop.grace`; it then writes the end record, so `kill` and `wait` return once
that is done, and reaps the program last, so the program's pid, which is the group's and the
session's id, stays reserved until then. Of the processes of the program's group, none still runs
once the ending is over (`ending_clean`), when a signal to a group reaches every member
(`Os.Signal.Group`, which its check tests) and SIGKILL ends within a second each process it
reaches (`Signal.Ends`, which its check and the attach suite test and a process stuck in the
kernel falsifies). Not claimed: how many pty resizes a read asks for while its sender stays
attached; the rest of the terminal session, which the attach suite tests; and the processes
linger's signals miss: one that left the group and the terminal session with `setsid`, which only
a PID namespace would hold, and one of another user.

State is bounded by what it means: every file in linger's state is one fact, a session's socket,
its notification socket, which its daemon removes as the session ends and a listing removes with
a stale socket, or checkpoint or an ID's end record, or a names entry, and a lock file means
nothing of its own.
A process that held an ID's locks deletes their files, still holding them, as it lets them go,
when no socket, notification socket, checkpoint or end record has the ID and no names entry leads to it, and keeps
every other lock file, so after any command every lock file names a session or an ending, when
only the command's ID named nothing before (`locks_named`); the names lock, `names/.lock`, names
no session, and its holder deletes it as it lets it go. A deleted lock file excludes as one kept: only a holder deletes one, and a
process that locks a file checks that the path still names it, locking the path's file again when
not (`Os.Shell.flock`), which `fstat` and `stat` tell apart, so it keeps a lock only of the file
the path names (the os package's `lock_named`, over `Os.Lock.Tells`), and `Claim.Exclusive`
holds of the lock of the file a path names and a name keeps one owner (`one_owner`). End records
are not bounded: one is kept for each name a session ended under or a kill hid a saved tmux pane
under, so `wait` answers and the pane stays hidden, and the lock files are bounded by them. Not
claimed: that each command lets its locks go as `Locks.release` says, which the identity suite
checks, nor that a crash or a SIGKILL leaves no lock file, which the next command on the name or
the next listing deletes. -/

theorem locks_named (records : Session.Records) (name : String)
    (before : ∀ held ∈ records.locks, held = name ∨ records.holds held = true) :
    (Session.Locks.release records name).sockets = records.sockets ∧
      (Session.Locks.release records name).notifies = records.notifies ∧
      (Session.Locks.release records name).checkpoints = records.checkpoints ∧
      (Session.Locks.release records name).endings = records.endings ∧
      (∀ held ∈ records.locks,
        records.holds held = true → held ∈ (Session.Locks.release records name).locks) ∧
      ∀ held ∈ (Session.Locks.release records name).locks,
        (Session.Locks.release records name).holds held = true := by
  sorry

@[kills locks_named]
theorem locks_named_rejects_kept :
    ¬∀ (records : Session.Records) (name : String),
        (∀ held ∈ records.locks, held = name ∨ records.holds held = true) →
          ((fun (records : Session.Records) (_ : String) => records) records name).sockets =
              records.sockets ∧
            ((fun (records : Session.Records) (_ : String) => records) records name).notifies =
              records.notifies ∧
            ((fun (records : Session.Records) (_ : String) => records) records name).checkpoints =
              records.checkpoints ∧
            ((fun (records : Session.Records) (_ : String) => records) records name).endings =
              records.endings ∧
            (∀ held ∈ records.locks,
              records.holds held = true →
                held ∈
                  ((fun (records : Session.Records) (_ : String) => records) records name).locks) ∧
            ∀ held ∈ ((fun (records : Session.Records) (_ : String) => records) records name).locks,
              ((fun (records : Session.Records) (_ : String) => records) records name).holds held =
                true := by
  sorry

theorem reachableIn_bound {cap : Nat} {b : Buf.Buf}
    (h : Buf.InputReach Buf.Buf.empty Buf.bufOffer Buf.bufAdvance cap b) : Buf.owedLen b ≤ cap := by
  sorry

@[kills reachableIn_bound]
theorem reachableIn_bound_rejects_append :
    ¬∀ {cap : Nat} {b : Buf.Buf},
        Buf.InputReach Buf.Buf.empty Buf.bufEnqueue Buf.bufAdvance cap b → Buf.owedLen b ≤ cap := by
  sorry

theorem reachableOut_bound {cap : Nat} {b : Buf.Buf}
    (h : Buf.OutputReach Buf.Buf.empty Buf.bufEnqueue Buf.bufAdvance cap b) :
    Buf.owedLen b ≤ cap := by sorry

@[kills reachableOut_bound]
theorem reachableOut_bound_rejects_uncut :
    ¬∀ {cap : Nat} {b : Buf.Buf},
        Buf.OutputReach Buf.Buf.empty (fun cap b more => ((Buf.bufEnqueue cap b more).1, false))
            Buf.bufAdvance cap b →
          Buf.owedLen b ≤ cap := by
  sorry

theorem step_bytes_one_reply (s : State) (id : Nat) (chunk : List UInt8) :
    ((Session.step s (.bytes id chunk)).2.all (!·.rendered) ∨
        ∃ pre frames post,
          (Session.step s (.bytes id chunk)).2 = pre ++ frames ++ Effect.send id .done :: post ∧
            frames.all (·.rendered) ∧ (pre ++ post).all (!·.rendered)) ∧
      (((Session.step s (.bytes id chunk)).1.client? id).all (!·.attached) →
        ((Session.step s (.bytes id chunk)).2.filter (·.resizes)).length ≤ 1) := by
  sorry

@[kills step_bytes_one_reply]
theorem step_bytes_one_reply_rejects_twice :
    ¬∀ (s : State) (id : Nat) (chunk : List UInt8),
        (((fun (s : State) (_ : Event) =>
                    (s, ([.resizePty 1 1, .resizePty 1 1] : List (Effect Replay.Plan))))
                  s (.bytes id chunk)).2.all
              (!·.rendered) ∨
            ∃ pre frames post,
              ((fun (s : State) (_ : Event) =>
                        (s, ([.resizePty 1 1, .resizePty 1 1] : List (Effect Replay.Plan))))
                      s (.bytes id chunk)).2 =
                  pre ++ frames ++ Effect.send id .done :: post ∧
                frames.all (·.rendered) ∧ (pre ++ post).all (!·.rendered)) ∧
          ((((fun (s : State) (_ : Event) =>
                        (s, ([.resizePty 1 1, .resizePty 1 1] : List (Effect Replay.Plan))))
                      s (.bytes id chunk)).1.client?
                  id).all
              (!·.attached) →
            (((fun (s : State) (_ : Event) =>
                        (s, ([.resizePty 1 1, .resizePty 1 1] : List (Effect Replay.Plan))))
                      s (.bytes id chunk)).2.filter
                  (·.resizes)).length ≤
              1) := by
  sorry

theorem captureBytes_bounded (contents : String) :
    (Import.Resurrect.captureBytes contents).length ≤ 2 * Import.Resurrect.captureLimit := by sorry

@[kills captureBytes_bounded]
theorem captureBytes_bounded_rejects_unbounded :
    ¬∀ (contents : String),
        ((fun (_ : String) => List.replicate (2 * Import.Resurrect.captureLimit + 1) (0 : UInt8))
              contents).length ≤
          2 * Import.Resurrect.captureLimit := by
  sorry

theorem ending_clean (gone : UInt32 → Nat → Nat → Bool) (ends : Signal.Ends gone)
    (member reaches : Nat → Nat → Bool) (group : Os.Signal.Group member reaches) (program : Nat)
    (alive : List Nat) (members : ∀ pid ∈ alive, member program pid = true) :
    (Session.ending.head?.map (·.signal)) = some 1 ∧
      Session.ending.foldl (Stop.survivors (Stop.reach program reaches) gone) alive = [] := by
  sorry

@[kills ending_clean]
theorem ending_clean_rejects_pid :
    ¬∀ (gone : UInt32 → Nat → Nat → Bool),
        Signal.Ends gone →
          ∀ (member reaches : Nat → Nat → Bool),
            Os.Signal.Group member reaches →
              ∀ (program : Nat) (alive : List Nat),
                (∀ pid ∈ alive, member program pid = true) →
                  (Stop.pidOnly.head?.map (·.signal)) = some 1 ∧
                    Stop.pidOnly.foldl (Stop.survivors (Stop.reach program reaches) gone) alive =
                      [] := by
  sorry

/-! ## 7. Recovery

The terminal package's claims cover every terminal the checkpoint decoder returns
(`Checkpoint.live_of_decoded`), so any bytes on disk resume a session those claims cover, or are
refused, and a command never takes bytes that do not decode for no checkpoint: it starts nothing
over them and leaves them as they are, for `kill` to discard (`recovery_exact`). A resume gives
back the saved terminal and the saved record's own fields, its description and an import's
provenance, but no label an older linger saved (`resume_restores`). A crash costs at most the
changes of the last interval. A session asks for a save within `ckptIntervalMs` of every
change no save holds, by the clock its ticks give it (`unsaved_due`); its daemon saves off its loop
and replaces the checkpoint whole and durably, so that after a crash
the file at the path is the last save whose flushes returned, or the one then running, whole
(`Disk.Durable`, which the resume suite tests by killing a daemon while it saves, and its check once
both flushes returned); and resuming then gives back that save, never a fresh session
(`crash_resumes`). A record an older linger wrote reads as it meant then: a record of format 3,
its tag then today's layout, that holds no description reads with the description a tmux import
gives its labels, the window's name, as an import from before a row had a description recorded
the pane's provenance and none (`older_record_described`); a record of today's
format reads as written (`loadBytes_saveBytes_live`), so a description its user cleared stays
cleared. Not claimed: that records of formats 1 and 2 read the same way, which the checkpoint
proofs state (`load_saveV2_live`, `load_saveV1_live`); that a description a user cleared in a
record of an earlier format stays cleared, since those formats do not tell it from one never
given; a bound in bytes or rows on what a crash loses, since the bound is
in time, the interval and the saves then running, whatever the program wrote in it, and a bound in
rows waits for an append-only store of the history; and that power loss keeps what the flushes
returned for, which rests on `Disk.Durable` and which no check or suite causes.

An upgrade replaces a daemon's image with a newer binary's, by an exec, which keeps the daemon's
process, its program, which stays its child on the same terminal, and the descriptors it keeps
(`Os.Exec.Keeps`): every descriptor the handoff names, the listening socket, the pty, the signal
pipe, the locks and every connection (`upgrade_keeps`). The new image
resumes from the handoff, which carries the session's whole state and what the daemon still owed
its program and its connections, so the session is carried, not rebuilt: the handoff of a session
whose terminal's parser is quiet decodes as exactly that session (`handoff_carries`, whose kill
rebuilds it as a resume does). A handoff names its format, and a binary decodes the formats it
lists and no other (`handoff_versioned`); a daemon hands its session only to a binary whose probe
lists the format it writes (`upgrade_probes`), and keeps serving otherwise, as it does when the
exec fails. Not claimed: that the binary the exec starts is the one the probe ran, since the file
may be replaced between them, nor that it has the resources to decode the handoff; such an image
ends, and the session's program loses its daemon, with the checkpoint the old image saved just
before the exec left to resume. -/

theorem handoff_carries (s : State) (w : Handoff.World)
    (h :
      Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
        (Checkpoint.Decoded Checkpoint.loadBytes) s.terminal)
    (quiet : s.terminal.quiesce = s.terminal) :
    Handoff.decode (Handoff.encode s w) = some (s, w) := by sorry

@[kills handoff_carries]
theorem handoff_carries_rejects_rebuilt :
    ¬∀ (s : State) (w : Handoff.World),
        Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
            (Checkpoint.Decoded Checkpoint.loadBytes) s.terminal →
          s.terminal.quiesce = s.terminal →
          Handoff.decode
              ((fun (s : State) (w : Handoff.World) =>
                  Handoff.encode (State.boot s.terminal s.fieldList []) w)
                s w) =
            some (s, w) := by
  sorry

theorem upgrade_keeps (exec : Nat → List Nat → List Nat → Nat × List Nat × List Nat)
    (keeps : Os.Exec.Keeps exec) (pid : Nat) (w : Handoff.World) :
    (exec pid [w.childPid] (Handoff.kept w)).1 = pid ∧
      (exec pid [w.childPid] (Handoff.kept w)).2.1 = [w.childPid] ∧
      ∀ fd ∈ w.fds, fd ∈ (exec pid [w.childPid] (Handoff.kept w)).2.2 := by
  sorry

@[kills upgrade_keeps]
theorem upgrade_keeps_rejects_unconnected :
    ¬∀ (exec : Nat → List Nat → List Nat → Nat × List Nat × List Nat),
        Os.Exec.Keeps exec →
          ∀ (pid : Nat) (w : Handoff.World),
            (exec pid [w.childPid] ((fun (w : Handoff.World) => [w.listenFd, w.ptyFd]) w)).1 = pid ∧
              (exec pid [w.childPid] ((fun (w : Handoff.World) => [w.listenFd, w.ptyFd]) w)).2.1 =
                [w.childPid] ∧
              ∀ fd ∈ w.fds,
                fd ∈
                  (exec pid [w.childPid]
                      ((fun (w : Handoff.World) => [w.listenFd, w.ptyFd]) w)).2.2 := by
  sorry

theorem handoff_versioned (s : State) (w : Handoff.World) (v : Nat) (rest : List UInt8) :
    Handoff.version ∈ Handoff.formats ∧
      (Handoff.encode s w).take (Handoff.header Handoff.version).length =
        Handoff.header Handoff.version ∧
      (v ∉ Handoff.formats → v < 256 → Handoff.decode (Handoff.header v ++ rest) = none) := by
  sorry

@[kills handoff_versioned]
theorem handoff_versioned_rejects_unread :
    ¬∀ (s : State) (w : Handoff.World) (v : Nat) (rest : List UInt8),
        Handoff.version ∈ Handoff.formats ∧
          (Handoff.encode s w).take (Handoff.header Handoff.version).length =
            Handoff.header Handoff.version ∧
          (v ∉ Handoff.formats →
            v < 256 →
            (fun (bytes : List UInt8) =>
                  Handoff.decode
                    (Handoff.header Handoff.version ++
                      bytes.drop (Handoff.header Handoff.version).length))
                (Handoff.header v ++ rest) =
              none) := by
  sorry

theorem upgrade_probes (reported : Option (List Nat)) :
    Upgrade.proceeds reported = true ↔
      ∃ formats, reported = some formats ∧ Handoff.version ∈ formats := by
  sorry

@[kills upgrade_probes]
theorem upgrade_probes_rejects_unprobed :
    ¬∀ (reported : Option (List Nat)),
        (fun (_ : Option (List Nat)) => true) reported = true ↔
          ∃ formats, reported = some formats ∧ Handoff.version ∈ formats := by
  sorry

theorem loadBytes_saveBytes_live (c : Checkpoint.Ckpt Vt.Vt)
    (h :
      Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
        (Checkpoint.Decoded Checkpoint.loadBytes) c.vt) :
    Checkpoint.loadBytes (Checkpoint.saveBytes c) = some { c with vt := c.vt.quiesce } := by sorry

@[kills loadBytes_saveBytes_live]
theorem loadBytes_saveBytes_live_rejects_refusal :
    ¬∀ (c : Checkpoint.Ckpt Vt.Vt),
        Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
            (Checkpoint.Decoded (fun _ => none : ByteArray → Option (Checkpoint.Ckpt Vt.Vt))) c.vt →
          (fun _ => none : ByteArray → Option (Checkpoint.Ckpt Vt.Vt)) (Checkpoint.saveBytes c) =
            some { c with vt := c.vt.quiesce } := by
  sorry

theorem resume_restores (c : Checkpoint.Ckpt Vt.Vt)
    (h :
      Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
        (Checkpoint.Decoded Checkpoint.loadBytes) c.vt)
    (metaKv : List (String × String)) :
    (State.boot (bootVt ((Checkpoint.loadBytes (Checkpoint.saveBytes c)).map (·.vt)))
            (((Checkpoint.loadBytes (Checkpoint.saveBytes c)).map (·.fields)).getD [])
            metaKv).terminal =
        c.vt.quiesce ∧
      (State.boot (bootVt ((Checkpoint.loadBytes (Checkpoint.saveBytes c)).map (·.vt)))
            (((Checkpoint.loadBytes (Checkpoint.saveBytes c)).map (·.fields)).getD [])
            metaKv).fieldList =
        (c.fields.filter (recordField ·.1)).take maxFields := by
  sorry

@[kills resume_restores]
theorem resume_restores_rejects_fresh :
    ¬∀ (c : Checkpoint.Ckpt Vt.Vt),
        Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
            (Checkpoint.Decoded Checkpoint.loadBytes) c.vt →
          ∀ (metaKv : List (String × String)),
            (State.boot
                    ((fun (_ : Option Vt.Vt) => Vt.Vt.init 1 1)
                      ((Checkpoint.loadBytes (Checkpoint.saveBytes c)).map (·.vt)))
                    (((Checkpoint.loadBytes (Checkpoint.saveBytes c)).map (·.fields)).getD [])
                    metaKv).terminal =
                c.vt.quiesce ∧
              (State.boot
                    ((fun (_ : Option Vt.Vt) => Vt.Vt.init 1 1)
                      ((Checkpoint.loadBytes (Checkpoint.saveBytes c)).map (·.vt)))
                    (((Checkpoint.loadBytes (Checkpoint.saveBytes c)).map (·.fields)).getD [])
                    metaKv).fieldList =
                (c.fields.filter (recordField ·.1)).take maxFields := by
  sorry

theorem loadBytes_resave {b : ByteArray} {c : Checkpoint.Ckpt Vt.Vt}
    (h : Checkpoint.loadBytes b = some c) :
    Checkpoint.loadBytes (Checkpoint.saveBytes c) = some c := by sorry

@[kills loadBytes_resave]
theorem loadBytes_resave_rejects_fixed :
    ¬∀ {b : ByteArray} {c : Checkpoint.Ckpt Vt.Vt},
        Checkpoint.loadBytes b = some c →
          Checkpoint.loadBytes
              ((fun (_ : Checkpoint.Ckpt Vt.Vt) => Checkpoint.saveBytes ⟨Vt.Vt.init 1 1, "x", []⟩)
                c) =
            some c := by
  sorry

theorem recovery_exact (create : Bool) (file : Option ByteArray) :
    App.Recovery.decide create file =
      (file.map fun bytes =>
            ((Checkpoint.loadBytes bytes).map App.Recovery.resume).getD (.refuse .notDone)).getD
        (if create then .fresh else .refuse .notFound) := by
  sorry

@[kills recovery_exact]
theorem recovery_exact_rejects_missing :
    ¬∀ (create : Bool) (file : Option ByteArray),
        (fun (create : Bool) (file : Option ByteArray) =>
              ((file.bind Checkpoint.loadBytes).map App.Recovery.resume).getD
                (if create then App.Recovery.fresh else .refuse .notFound))
            create file =
          (file.map fun bytes =>
                ((Checkpoint.loadBytes bytes).map App.Recovery.resume).getD (.refuse .notDone)).getD
            (if create then .fresh else .refuse .notFound) := by
  sorry

theorem crash_resumes (afterCrash : Option ByteArray → ByteArray → Bool → Option ByteArray)
    (durable : Disk.Durable afterCrash) (create synced : Bool) (old new : Checkpoint.Ckpt Vt.Vt)
    (hold :
      Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
        (Checkpoint.Decoded Checkpoint.loadBytes) old.vt)
    (hnew :
      Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
        (Checkpoint.Decoded Checkpoint.loadBytes) new.vt) :
    ∃ c,
      App.Recovery.decide create
            (afterCrash (some (Checkpoint.saveBytes old)) (Checkpoint.saveBytes new) synced) =
          .resume c ∧
        (c = { new with vt := new.vt.quiesce } ∨
          synced = false ∧ c = { old with vt := old.vt.quiesce }) := by
  sorry

@[kills crash_resumes]
theorem crash_resumes_rejects_fresh :
    ¬∀ (afterCrash : Option ByteArray → ByteArray → Bool → Option ByteArray),
        Disk.Durable afterCrash →
          ∀ (create synced : Bool) (old new : Checkpoint.Ckpt Vt.Vt),
            Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
                (Checkpoint.Decoded Checkpoint.loadBytes) old.vt →
              Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
                (Checkpoint.Decoded Checkpoint.loadBytes) new.vt →
              ∃ c,
                (fun (_ : Bool) (_ : Option ByteArray) =>
                        (App.Recovery.fresh : App.Recovery (Checkpoint.Ckpt Vt.Vt)))
                      create
                      (afterCrash (some (Checkpoint.saveBytes old)) (Checkpoint.saveBytes new)
                        synced) =
                    .resume c ∧
                  (c = { new with vt := new.vt.quiesce } ∨
                    synced = false ∧ c = { old with vt := old.vt.quiesce }) := by
  sorry

theorem unsaved_due (vt : Vt.Vt) (fields metaKv : List (String × String)) (pre post : List Event)
    (ev : Event) :
    (Session.step (Session.trace Session.step (State.boot vt fields metaKv) pre).1 ev).1.terminal ≠
          (Session.trace Session.step (State.boot vt fields metaKv) pre).1.terminal ∨
        (Session.step (Session.trace Session.step (State.boot vt fields metaKv) pre).1
              ev).1.fieldList ≠
          (Session.trace Session.step (State.boot vt fields metaKv) pre).1.fieldList →
      Effect.checkpoint ∉
        (Session.trace Session.step (Session.trace Session.step (State.boot vt fields metaKv) pre).1
            (ev :: post)).2 →
      ∃ due,
        due ≤ Session.clock pre + ckptIntervalMs ∧
          (∃ wake,
            (Session.trace Session.step
                    (Session.trace Session.step (State.boot vt fields metaKv) pre).1
                    (ev :: post)).1.nextTick =
                some wake ∧
              wake ≤ due) ∧
          ∀ now,
            due ≤ now →
              Effect.checkpoint ∈
                (Session.step
                    (Session.trace Session.step
                        (Session.trace Session.step (State.boot vt fields metaKv) pre).1
                        (ev :: post)).1
                    (.tick now)).2 := by
  sorry

@[kills unsaved_due]
theorem unsaved_due_rejects_never :
    ¬∀ (vt : Vt.Vt) (fields metaKv : List (String × String)) (pre post : List Event) (ev : Event),
        (Session.step (Session.trace Session.step (State.boot vt fields metaKv) pre).1
                  ev).1.terminal ≠
              (Session.trace Session.step (State.boot vt fields metaKv) pre).1.terminal ∨
            (Session.step (Session.trace Session.step (State.boot vt fields metaKv) pre).1
                  ev).1.fieldList ≠
              (Session.trace Session.step (State.boot vt fields metaKv) pre).1.fieldList →
          Effect.checkpoint ∉
            (Session.trace Session.step
                (Session.trace Session.step (State.boot vt fields metaKv) pre).1 (ev :: post)).2 →
          ∃ due,
            due ≤ Session.clock pre + ckptIntervalMs ∧
              (∃ wake,
                (fun (_ : State) => (none : Option Nat))
                      (Session.trace Session.step
                          (Session.trace Session.step (State.boot vt fields metaKv) pre).1
                          (ev :: post)).1 =
                    some wake ∧
                  wake ≤ due) ∧
              ∀ now,
                due ≤ now →
                  Effect.checkpoint ∈
                    (Session.step
                        (Session.trace Session.step
                            (Session.trace Session.step (State.boot vt fields metaKv) pre).1
                            (ev :: post)).1
                        (.tick now)).2 := by
  sorry

theorem checkpoint_metadata (pane : Import.Resurrect.Pane) (contents : Option String) :
    (Import.Resurrect.checkpoint pane contents).cwd = pane.dir ∧
      (Import.Resurrect.checkpoint pane contents).fields.lookup "tmux.command" =
        some pane.details.command ∧
      (Import.Resurrect.checkpoint pane contents).fields.lookup "tmux.saved-command" =
        some pane.details.savedCommand ∧
      (Import.Resurrect.checkpoint pane contents).fields.lookup "tmux.capture" =
        some (if contents.isSome then "saved" else "none") := by
  sorry

@[kills checkpoint_metadata]
theorem checkpoint_metadata_rejects_blank :
    ¬∀ (pane : Import.Resurrect.Pane) (contents : Option String),
        ((fun (_ : Import.Resurrect.Pane) (_ : Option String) =>
                  (⟨Vt.Vt.init 1 1, "", []⟩ : Checkpoint.Ckpt Vt.Vt))
                pane contents).cwd =
            pane.dir ∧
          ((fun (_ : Import.Resurrect.Pane) (_ : Option String) =>
                    (⟨Vt.Vt.init 1 1, "", []⟩ : Checkpoint.Ckpt Vt.Vt))
                  pane contents).fields.lookup
              "tmux.command" =
            some pane.details.command ∧
          ((fun (_ : Import.Resurrect.Pane) (_ : Option String) =>
                    (⟨Vt.Vt.init 1 1, "", []⟩ : Checkpoint.Ckpt Vt.Vt))
                  pane contents).fields.lookup
              "tmux.saved-command" =
            some pane.details.savedCommand ∧
          ((fun (_ : Import.Resurrect.Pane) (_ : Option String) =>
                    (⟨Vt.Vt.init 1 1, "", []⟩ : Checkpoint.Ckpt Vt.Vt))
                  pane contents).fields.lookup
              "tmux.capture" =
            some (if contents.isSome then "saved" else "none") := by
  sorry

theorem older_record_described (c : Checkpoint.Ckpt Vt.Vt)
    (h :
      Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
        (Checkpoint.Decoded Checkpoint.loadBytes) c.vt)
    (undescribed : c.fields.lookup "description" = none) (old : ByteArray)
    (format3 :
      old.data.toList =
        [0x4C, 0x4E, 0x47, 0x52, 3] ++ (Checkpoint.saveBytes c).data.toList.drop 5) :
    Checkpoint.loadBytes old =
      some
        { c with
          vt := c.vt.quiesce, fields := c.fields ++ Checkpoint.importDescription c.fields } := by
  sorry

@[kills older_record_described]
theorem older_record_described_rejects_stored :
    ¬∀ (c : Checkpoint.Ckpt Vt.Vt),
        Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
            (Checkpoint.Decoded
              (fun (b : ByteArray) =>
                (Checkpoint.loadBytes b).map fun (c : Checkpoint.Ckpt Vt.Vt) =>
                  (⟨c.vt, c.cwd, c.fields.filter (·.1 != "description")⟩ : Checkpoint.Ckpt Vt.Vt)))
            c.vt →
          c.fields.lookup "description" = none →
          ∀ (old : ByteArray),
            old.data.toList =
                [0x4C, 0x4E, 0x47, 0x52, 3] ++ (Checkpoint.saveBytes c).data.toList.drop 5 →
              (fun (b : ByteArray) =>
                    (Checkpoint.loadBytes b).map fun (c : Checkpoint.Ckpt Vt.Vt) =>
                      (⟨c.vt, c.cwd, c.fields.filter (·.1 != "description")⟩ :
                        Checkpoint.Ckpt Vt.Vt))
                  old =
                some
                  { c with
                    vt := c.vt.quiesce,
                    fields := c.fields ++ Checkpoint.importDescription c.fields } := by
  sorry

/-! ## 8. Clean terminal

What linger writes to a terminal on its own account is clean (`Display.Clean`): printable text,
line breaks, tabs and a short list of control sequences, none of which asks the terminal for a
reply, resets it or erases its scrollback. A gate lists every write to standard output in the
program with whose bytes it writes: a printer `writes_clean` names, or the session's own bytes,
its output and the repaint of its screen, which the terminal package's headlines describe.
Linger's listings, those of `ls` and the chooser, are in color exactly when they go to
a terminal, NO_COLOR is unset or empty, as no-color.org reads it, and TERM names a terminal other
than `dumb`, which takes no escape sequences (`withColor_iff`); a gate ties each to
`Os.Env.withColor` of whether standard output is a terminal, NO_COLOR and TERM, each read once.
Not claimed: what linger prints as lines of text (help, version, `ls --summary`, porcelain
records) and its messages on standard error. -/

theorem infoText_text (s : State) :
    ∃ cs : List Char,
      Session.infoText s = cs.flatMap String.utf8EncodeChar ∧
        ∀ c ∈ cs,
          c = '\t' ∨
            c = '\n' ∨ (0x20 ≤ c.toNat ∧ c.toNat ≠ 0x7F ∧ ¬(0x80 ≤ c.toNat ∧ c.toNat < 0xA0)) := by
  sorry

@[kills infoText_text]
theorem infoText_text_rejects_escape :
    ¬∀ (s : State),
        ∃ cs : List Char,
          (fun (_ : State) => ([0x1B] : List UInt8)) s = cs.flatMap String.utf8EncodeChar ∧
            ∀ c ∈ cs,
              c = '\t' ∨
                c = '\n' ∨
                (0x20 ≤ c.toNat ∧ c.toNat ≠ 0x7F ∧ ¬(0x80 ≤ c.toNat ∧ c.toNat < 0xA0)) := by
  sorry

theorem writes_clean :
    (∀ withColor width rows, Display.Clean (Display.Listing.terminalListing withColor width rows)) ∧
      (∀ state snapshot statusOf loaded withColor savedTmux remoteAge cols rows,
        Display.Clean
          (Selector.Picker.frame state snapshot statusOf loaded withColor savedTmux remoteAge cols
            rows)) ∧
      (∀ state snapshot statusOf loaded withColor savedTmux remoteAge cols rows,
        ∀
          row ∈
            Selector.Picker.frameRows state snapshot statusOf loaded withColor savedTmux remoteAge
              cols rows,
          Display.Clean row) ∧
      (∀ before after : List (List UInt8),
        (∀ row ∈ after, Display.Clean row) → Display.Clean (Selector.Picker.update before after)) ∧
      Display.Clean Selector.Picker.enterAnsi ∧
      Display.Clean Selector.Picker.exitAnsi ∧
      (∀ title, Display.Clean (Terminal.Title.ansi title)) ∧
      (∀ v title, Display.Clean (Terminal.Title.update v title)) ∧
      (∀ v, Display.Clean (Terminal.Render.screenText v)) ∧
      (∀ v, Display.Clean (Terminal.Render.history v)) ∧
      (∀ s, Display.Clean (Session.infoText s)) ∧
      (∀ name notice, Display.Clean (Display.Alert.notification name notice)) ∧
      Display.Clean Terminal.Render.leaveAnsi := by
  sorry

@[kills writes_clean]
theorem writes_clean_rejects_reset :
    ¬((∀ withColor width rows,
          Display.Clean
            ((fun (_ : Bool) (_ : Option Nat) (_ : List (List (String × String))) =>
                ([0x1B, 0x63] : List UInt8))
              withColor width rows)) ∧
        (∀ state snapshot statusOf loaded withColor savedTmux remoteAge cols rows,
          Display.Clean
            (Selector.Picker.frame state snapshot statusOf loaded withColor savedTmux remoteAge cols
              rows)) ∧
        (∀ state snapshot statusOf loaded withColor savedTmux remoteAge cols rows,
          ∀
            row ∈
              Selector.Picker.frameRows state snapshot statusOf loaded withColor savedTmux remoteAge
                cols rows,
            Display.Clean row) ∧
        (∀ before after : List (List UInt8),
          (∀ row ∈ after, Display.Clean row) →
            Display.Clean (Selector.Picker.update before after)) ∧
        Display.Clean Selector.Picker.enterAnsi ∧
        Display.Clean Selector.Picker.exitAnsi ∧
        (∀ title, Display.Clean (Terminal.Title.ansi title)) ∧
        (∀ v title, Display.Clean (Terminal.Title.update v title)) ∧
        (∀ v, Display.Clean (Terminal.Render.screenText v)) ∧
        (∀ v, Display.Clean (Terminal.Render.history v)) ∧
        (∀ s, Display.Clean (Session.infoText s)) ∧
        (∀ name notice, Display.Clean (Display.Alert.notification name notice)) ∧
        Display.Clean Terminal.Render.leaveAnsi) := by
  sorry

theorem withColor_iff (terminal : Bool) (noColor term : Option String) :
    Os.Env.withColor terminal noColor term = true ↔
      terminal = true ∧
        (noColor = none ∨ noColor = some "") ∧
        ∃ name, term = some name ∧ name ≠ "" ∧ name ≠ "dumb" := by
  sorry

@[kills withColor_iff]
theorem withColor_iff_rejects_presence :
    ¬∀ (terminal : Bool) (noColor term : Option String),
        (fun (terminal : Bool) (noColor : Option String) (_ : Option String) =>
                terminal && noColor.isNone)
              terminal noColor term =
            true ↔
          terminal = true ∧
            (noColor = none ∨ noColor = some "") ∧
            ∃ name, term = some name ∧ name ≠ "" ∧ name ≠ "dumb" := by
  sorry

/-! ## 9. Work follows events

A daemon's state holds its own session alone, so no event's work depends on how many sessions exist.
Program output costs work only for the clients attached to its session (`step_output_delivered`, in
part 1), and a daemon's poll that no event or signal ends returns no sooner than the earliest
deadline the daemon holds, and never when it holds none (`poll_wakes`), when poll(2) waits out its
timeout (`Poll.Sleeps`, which its check tests by timing quiet polls, as the quiet suite does, which
also counts the wakeups of idle sessions). `scripts/gates.sh` lists every timer the program sets,
with its bound. On the screen, the selector repaints only what an event changed
(`picker_repaints_changes`): from a frame on screen to the next one, its update writes, for each row
that differs, the cursor's move to that row and the row's paint, so it costs the rows that differ
and moving the highlight costs two; it writes nothing to a row the two frames share, whatever that
row shows; and over a terminal showing the first frame it shows exactly what the second frame shows
there. Only the first frame, the first after a resize and the first after the refresh key paint
every row: Ctrl-L, which clears and redraws the screen in a line editor, redraws the chooser's.
The chooser queries remote hosts, through a transport command each, only when an event asks it to
(`fetch_follows_events`): a listing it starts queries them exactly when no listing came before it
since it opened, or the refresh key, Ctrl-L, came after the one before; its other listings, one
each second while it is open, a timer `scripts/gates.sh` names, read its local sessions alone and
keep the remote rows the last query reported, and the header says how long before the latest
listing that query started (`remote 12s`), so a remote row's status reads as of then; each change
of that age repaints the header's row alone. Not claimed: that the header's age is that time,
which the manager suite checks, how much later than its deadline a loaded host lets a daemon wake,
and an update over a terminal in insert or origin mode, without autowrap, with a narrower scroll
region or a DEC line-drawing character set, none of which the picker sets. Not claimed yet: that
an event's work follows its size. -/

theorem steady_working (s : State) (chunk : List UInt8) (start period : Nat)
    (between : Nat → List Nat) (rounds : Nat) (gaps : period < Session.workingMs)
    (within : ∀ i d, d ∈ between i → d ≤ period) :
    (∀ i ≤ rounds,
        ∀ k ≤ (between i).length,
          (Session.trace Session.step s
                (Session.steady chunk start period between i ++
                  Session.redraw chunk (start + i * period)
                    ((0 :: between i).take (k + 1)))).1.seen.fresh =
            true) ∧
      (∃ due,
        (Session.trace Session.step s
                (Session.steady chunk start period between (rounds + 1))).1.nextTick =
            some due ∧
          due ≤ start + rounds * period + Session.freshMs) ∧
      ∀ (quiet : List Nat) (t : Nat),
        start + rounds * period + Session.freshMs ≤ t →
          (Session.trace Session.step s
                (Session.steady chunk start period between (rounds + 1) ++ quiet.map Event.tick ++
                  [Event.tick t])).1.seen.fresh =
            false := by
  sorry

@[kills steady_working]
theorem steady_working_rejects_second :
    ¬∀ (s : State) (chunk : List UInt8) (start period : Nat) (between : Nat → List Nat)
        (rounds : Nat),
        period < Session.workingMs →
          (∀ i d, d ∈ between i → d ≤ period) →
          (∀ i ≤ rounds,
              ∀ k ≤ (between i).length,
                (Session.trace Session.step s
                      (Session.steady chunk start period between i ++
                        Session.redraw chunk (start + i * period)
                          ((0 :: between i).take (k + 1)))).1.seen.fresh =
                  true) ∧
            (∃ due,
              (Session.trace Session.step s
                      (Session.steady chunk start period between (rounds + 1))).1.nextTick =
                  some due ∧
                due ≤ start + rounds * period + (1000 : Nat)) ∧
            ∀ (quiet : List Nat) (t : Nat),
              start + rounds * period + (1000 : Nat) ≤ t →
                (Session.trace Session.step s
                      (Session.steady chunk start period between (rounds + 1) ++
                        quiet.map Event.tick ++
                        [Event.tick t])).1.seen.fresh =
                  false := by
  sorry

theorem ticks_settle (s : State) (now t₁ t₂ : Nat)
    (h₁ : (Session.trace Session.step s [.tick now]).1.nextTick = some t₁)
    (h₂ : (Session.trace Session.step s [.tick now, .tick t₁]).1.nextTick = some t₂) :
    (Session.trace Session.step s [.tick now, .tick t₁, .tick t₂]).1.nextTick = none := by sorry

@[kills ticks_settle]
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

theorem poll_wakes (quiet : Int32 → Nat → Prop) (sleeps : Poll.Sleeps quiet) (now : Nat)
    (deadlines : List Nat) (fit : ∀ d ∈ deadlines, d - now ≤ 2147483647) (ms : Nat)
    (woke : quiet (Session.pollTimeout now deadlines) ms) :
    ∃ due, deadlines.min? = some due ∧ due - now ≤ ms := by sorry

@[kills poll_wakes]
theorem poll_wakes_rejects_polling :
    ¬∀ (quiet : Int32 → Nat → Prop),
        Poll.Sleeps quiet →
          ∀ (now : Nat) (deadlines : List Nat),
            (∀ d ∈ deadlines, d - now ≤ 2147483647) →
              ∀ (ms : Nat),
                quiet ((fun (_ : Nat) (_ : List Nat) => (100 : Int32)) now deadlines) ms →
                  ∃ due, deadlines.min? = some due ∧ due - now ≤ ms := by
  sorry

theorem picker_repaints_changes (sa sb : Selector.Picker.State) (na nb : Selector.Picker.Snapshot)
    (fa fb : String → Status.Status) (la ca ta lb cb tb : Bool) (aa ab : Option Nat) (v : Vt.Vt)
    (hv : Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable v)
    (between : v.atBoundary = true) (replacing : v.getModes.insert = false)
    (wraps : v.getModes.wrap = true) (absolute : v.getModes.origin = false)
    (top : (Vt.stick v).top = 0) (bottom : (Vt.stick v).bot = v.rowCount - 1)
    (ascii0 : (Vt.stick v).g0 = false) (ascii1 : (Vt.stick v).g1 = false) :
    (∀ y < v.rowCount,
        ((v.feed (Selector.Picker.frame sa na fa la ca ta aa v.colCount v.rowCount)).feed
                (Selector.Picker.update
                  (Selector.Picker.frameRows sa na fa la ca ta aa v.colCount v.rowCount)
                  (Selector.Picker.frameRows sb nb fb lb cb tb ab v.colCount v.rowCount))).getRow
            y =
          (v.feed (Selector.Picker.frame sb nb fb lb cb tb ab v.colCount v.rowCount)).getRow y) ∧
      (∀ y < v.rowCount,
        (Selector.Picker.frameRows sa na fa la ca ta aa v.colCount v.rowCount)[y]? =
            (Selector.Picker.frameRows sb nb fb lb cb tb ab v.colCount v.rowCount)[y]? →
          (v.feed
                  (Selector.Picker.update
                    (Selector.Picker.frameRows sa na fa la ca ta aa v.colCount v.rowCount)
                    (Selector.Picker.frameRows sb nb fb lb cb tb ab v.colCount v.rowCount))).getRow
              y =
            v.getRow y) ∧
      (Selector.Picker.update (Selector.Picker.frameRows sa na fa la ca ta aa v.colCount v.rowCount)
            (Selector.Picker.frameRows sb nb fb lb cb tb ab v.colCount v.rowCount)).length ≤
        ((List.range
                (Selector.Picker.frameRows sb nb fb lb cb tb ab v.colCount v.rowCount).length).map
            fun y =>
            if
                (Selector.Picker.frameRows sa na fa la ca ta aa v.colCount v.rowCount)[y]? =
                  (Selector.Picker.frameRows sb nb fb lb cb tb ab v.colCount v.rowCount)[y]? then
              0
            else
              (Display.digits (y + 1)).length + 5 +
                ((Selector.Picker.frameRows sb nb fb lb cb tb ab v.colCount v.rowCount)[y]?.getD
                    []).length).sum := by
  sorry

@[kills picker_repaints_changes]
theorem picker_repaints_changes_rejects_full :
    ¬∀ (sa sb : Selector.Picker.State) (na nb : Selector.Picker.Snapshot)
        (fa fb : String → Status.Status) (la ca ta lb cb tb : Bool) (aa ab : Option Nat)
        (v : Vt.Vt),
        Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable v →
          v.atBoundary = true →
          v.getModes.insert = false →
          v.getModes.wrap = true →
          v.getModes.origin = false →
          (Vt.stick v).top = 0 →
          (Vt.stick v).bot = v.rowCount - 1 →
          (Vt.stick v).g0 = false →
          (Vt.stick v).g1 = false →
          (∀ y < v.rowCount,
              ((v.feed (Selector.Picker.frame sa na fa la ca ta aa v.colCount v.rowCount)).feed
                      ((fun (_ after : List (List UInt8)) =>
                          ([0x1B, 0x5B, 0x48, 0x1B, 0x5B, 0x32, 0x4A] : List UInt8) ++
                            (after.intersperse [0x0D, 0x0A]).flatten)
                        (Selector.Picker.frameRows sa na fa la ca ta aa v.colCount v.rowCount)
                        (Selector.Picker.frameRows sb nb fb lb cb tb ab v.colCount
                          v.rowCount))).getRow
                  y =
                (v.feed (Selector.Picker.frame sb nb fb lb cb tb ab v.colCount v.rowCount)).getRow
                  y) ∧
            (∀ y < v.rowCount,
              (Selector.Picker.frameRows sa na fa la ca ta aa v.colCount v.rowCount)[y]? =
                  (Selector.Picker.frameRows sb nb fb lb cb tb ab v.colCount v.rowCount)[y]? →
                (v.feed
                        ((fun (_ after : List (List UInt8)) =>
                            ([0x1B, 0x5B, 0x48, 0x1B, 0x5B, 0x32, 0x4A] : List UInt8) ++
                              (after.intersperse [0x0D, 0x0A]).flatten)
                          (Selector.Picker.frameRows sa na fa la ca ta aa v.colCount v.rowCount)
                          (Selector.Picker.frameRows sb nb fb lb cb tb ab v.colCount
                            v.rowCount))).getRow
                    y =
                  v.getRow y) ∧
            ((fun (_ after : List (List UInt8)) =>
                    ([0x1B, 0x5B, 0x48, 0x1B, 0x5B, 0x32, 0x4A] : List UInt8) ++
                      (after.intersperse [0x0D, 0x0A]).flatten)
                  (Selector.Picker.frameRows sa na fa la ca ta aa v.colCount v.rowCount)
                  (Selector.Picker.frameRows sb nb fb lb cb tb ab v.colCount v.rowCount)).length ≤
              ((List.range
                      (Selector.Picker.frameRows sb nb fb lb cb tb ab v.colCount
                          v.rowCount).length).map
                  fun y =>
                  if
                      (Selector.Picker.frameRows sa na fa la ca ta aa v.colCount v.rowCount)[y]? =
                        (Selector.Picker.frameRows sb nb fb lb cb tb ab v.colCount
                            v.rowCount)[y]? then
                    0
                  else
                    (Display.digits (y + 1)).length + 5 +
                      ((Selector.Picker.frameRows sb nb fb lb cb tb ab v.colCount
                                v.rowCount)[y]?.getD
                          []).length).sum := by
  sorry

theorem fetch_follows_events (events : List Selector.Picker.Event) :
    Selector.Picker.due Selector.Picker.fetch events = true ↔
      (∀ e ∈ events, e.isKey = true) ∨
        Selector.Picker.Event.key .refresh ∈
          events.reverse.takeWhile Selector.Picker.Event.isKey := by
  sorry

@[kills fetch_follows_events]
theorem fetch_follows_events_rejects_polling :
    ¬∀ (events : List Selector.Picker.Event),
        Selector.Picker.due (fun (_ : Bool) (_ : Selector.Picker.Event) => true) events = true ↔
          (∀ e ∈ events, e.isKey = true) ∨
            Selector.Picker.Event.key .refresh ∈
              events.reverse.takeWhile Selector.Picker.Event.isKey := by
  sorry

/-! ## 10. Graceful under load

A command waits for its daemon's answer a bounded time, and what it answers when that time runs
out is still true. A daemon saves its checkpoint and writes its end record, their flushes
included, off its loop, on a thread of its own (`scripts/gates.sh`), so a slow disk holds up no
answer and no output: a write starts only when none of its kind runs, one asked for meanwhile
waits in place of any that waited, and the last one asked for is the last to start, at once or as
soon as the running one ends (`offloop_coalesces`). Every wait sleeps as `Os.Wait.next`
decides (`scripts/gates.sh`), so it gives up once its deadline has passed, which the os package
claims (`packages/os`), and then reports what
it missed: `start` that its daemon did not answer and `ls` a remote host as `?`. A `capture` of
a saved session loads and renders it holding the name's locks and lets them go before it writes, so no step it takes holding them waits on a party outside linger, and an
attach or a resume that starts the session while a pager or a pipe nobody reads holds up the
capture's write waits for the locks only as long as the load and the render take
(`capture_waits_unlocked`): the shell runs these steps in the phases `Capture.phases` cuts them
into, which hold the locks exactly where `Capture.work` says, whatever the plan, and runs them
for every capture of a saved session (`scripts/gates.sh`). A write that
finds its descriptor full, as one another program left nonblocking is, waits for the reader and
goes on, never taken for a reader that is gone, which the os package claims. Not claimed: the
waits with no deadline, each on something that ends without waiting itself, or on purpose:
`wait`, which takes no time limit of its own, since `timeout(1)` composes with it, an idle
daemon's poll, `start` or `resume` once their daemon took the
request's ticket, a daemon's last disk write, which it reports after a second, and a command's
write to a reader that does not read, as a blocking write waits too. How long a wait takes under
load the robust, resume and status suites measure. -/

theorem start_answer_true (r : Start.Request) (h : Start.Reachable Start.proceeds Start.answer r) :
    (r.answer = some .started → r.runs = true) ∧
      (r.answer = some .notStarted → r.runs = false) := by
  sorry

@[kills start_answer_true]
theorem start_answer_true_rejects_started :
    ¬∀ (r : Start.Request),
        Start.Reachable Start.proceeds (fun _ _ => Start.Answer.started) r →
          (r.answer = some .started → r.runs = true) ∧
            (r.answer = some .notStarted → r.runs = false) := by
  sorry

@[kills start_answer_true]
theorem start_answer_true_rejects_proceed :
    ¬∀ (r : Start.Request),
        Start.Reachable (fun _ => true) Start.answer r →
          (r.answer = some .started → r.runs = true) ∧
            (r.answer = some .notStarted → r.runs = false) := by
  sorry

theorem offloop_coalesces {W : Type} (earlier : List (Offloop.Op W)) (w : W) (ends : Nat) :
    (((earlier ++ (.ask w : Offloop.Op W) :: List.replicate ends .done).foldl
              (Offloop.cycle Offloop.ask Offloop.done) ({}, [])).2.getLast? =
          some w ∨
        ends = 0 ∧
          ((earlier ++ (.ask w : Offloop.Op W) :: List.replicate ends .done).foldl
                (Offloop.cycle Offloop.ask Offloop.done) ({}, [])).1.waiting =
            some w) ∧
      ∀ ops : List (Offloop.Op W),
        (ops.foldl (Offloop.cycle Offloop.ask Offloop.done) ({}, [])).2.length ≤
          (ops.filter Offloop.Op.isDone).length + 1 := by
  sorry

@[kills offloop_coalesces]
theorem offloop_coalesces_rejects_eager :
    ¬∀ {W : Type} (earlier : List (Offloop.Op W)) (w : W) (ends : Nat),
        (((earlier ++ (.ask w : Offloop.Op W) :: List.replicate ends .done).foldl
                  (Offloop.cycle Offloop.eager Offloop.done) ({}, [])).2.getLast? =
              some w ∨
            ends = 0 ∧
              ((earlier ++ (.ask w : Offloop.Op W) :: List.replicate ends .done).foldl
                    (Offloop.cycle Offloop.eager Offloop.done) ({}, [])).1.waiting =
                some w) ∧
          ∀ ops : List (Offloop.Op W),
            (ops.foldl (Offloop.cycle Offloop.eager Offloop.done) ({}, [])).2.length ≤
              (ops.filter Offloop.Op.isDone).length + 1 := by
  sorry

theorem capture_waits_unlocked :
    (∀ steps,
        (App.Capture.phases steps).flatMap App.Capture.Phase.work = App.Capture.work steps false) ∧
      (App.Capture.work App.Capture.plan false).map Prod.fst = [.load, .render, .write] ∧
      (.load, true) ∈ App.Capture.work App.Capture.plan false ∧
      ∀ step,
        (step, true) ∈ App.Capture.work App.Capture.plan false → step.waitsOutside = false := by
  sorry

@[kills capture_waits_unlocked]
theorem capture_waits_unlocked_rejects_inside :
    ¬((∀ steps,
          (App.Capture.phases steps).flatMap App.Capture.Phase.work =
            App.Capture.work steps false) ∧
        (App.Capture.work [.acquire, .load, .render, .write, .release] false).map Prod.fst =
          [.load, .render, .write] ∧
        (.load, true) ∈ App.Capture.work [.acquire, .load, .render, .write, .release] false ∧
        ∀ step,
          (step, true) ∈ App.Capture.work [.acquire, .load, .render, .write, .release] false →
            step.waitsOutside = false) := by
  sorry

@[kills capture_waits_unlocked]
theorem capture_waits_unlocked_rejects_held :
    ¬((∀ steps,
          ((fun (steps : List App.Capture.Step) => [App.Capture.Phase.locked steps]) steps).flatMap
              App.Capture.Phase.work =
            App.Capture.work steps false) ∧
        (App.Capture.work App.Capture.plan false).map Prod.fst = [.load, .render, .write] ∧
        (.load, true) ∈ App.Capture.work App.Capture.plan false ∧
        ∀ step,
          (step, true) ∈ App.Capture.work App.Capture.plan false → step.waitsOutside = false) := by
  sorry

/-! ## The status rule

And the titles, listings and selector views that show statuses; what makes a session ask and what
it tells of its shell's commands is part 2's (`step_owned`). Not claimed: that the porcelain and
a row report the text of the last notification since the last look and an ending's command line
and status, which the status suite checks; repainting the marks after a reattach, which a repaint
does not carry; and that the daemon publishes what it sees to its name's end record, which the
quiet and status suites check. -/

theorem classify_iff (o : Status.Obs) (s : Status.Status) :
    Status.classify o = s ↔ Status.Is s o := by sorry

@[kills classify_iff]
theorem classify_iff_rejects_idle :
    ¬∀ (o : Status.Obs) (s : Status.Status),
        (fun (_ : Status.Obs) => Status.Status.idle) o = s ↔ Status.Is s o := by
  sorry

theorem icon_glyphs :
    (∀ a b, Status.icon a = Status.icon b → a = b) ∧
      (∀ st, (Status.legend.map fun line => line.toList.head?).count (some (Status.icon st)) = 1) ∧
      ∀ line ∈ Status.legend, ∃ st, line.toList.head? = some (Status.icon st) := by
  sorry

@[kills icon_glyphs]
theorem icon_glyphs_rejects_unknown :
    ¬((∀ a b, (fun (_ : Status.Status) => '?') a = (fun (_ : Status.Status) => '?') b → a = b) ∧
        (∀ st,
          (Status.legend.map fun line => line.toList.head?).count
              (some ((fun (_ : Status.Status) => '?') st)) =
            1) ∧
        ∀ line ∈ Status.legend,
          ∃ st, line.toList.head? = some ((fun (_ : Status.Status) => '?') st)) := by
  sorry

theorem summary_exact (statuses : List Status.Status) :
    Status.summary statuses =
      String.intercalate " "
        ((if statuses.count .asks = 0 then []
          else [(toString (statuses.count .asks)).push (Status.icon .asks)]) ++
          (if statuses.count .wantsYou = 0 then []
          else [(toString (statuses.count .wantsYou)).push (Status.icon .wantsYou)]) ++
          (if statuses.count .exitedBad = 0 then []
          else [(toString (statuses.count .exitedBad)).push (Status.icon .exitedBad)]) ++
          (if statuses.count .unknown = 0 then []
          else [(toString (statuses.count .unknown)).push (Status.icon .unknown)])) := by
  sorry

@[kills summary_exact]
theorem summary_exact_rejects_count :
    ¬∀ (statuses : List Status.Status),
        (fun (all : List Status.Status) => toString all.length) statuses =
          String.intercalate " "
            ((if statuses.count .asks = 0 then []
              else [(toString (statuses.count .asks)).push (Status.icon .asks)]) ++
              (if statuses.count .wantsYou = 0 then []
              else [(toString (statuses.count .wantsYou)).push (Status.icon .wantsYou)]) ++
              (if statuses.count .exitedBad = 0 then []
              else [(toString (statuses.count .exitedBad)).push (Status.icon .exitedBad)]) ++
              (if statuses.count .unknown = 0 then []
              else [(toString (statuses.count .unknown)).push (Status.icon .unknown)])) := by
  sorry

theorem rowStatus_saved (status : Nat) (st : Status.Status) :
    Status.Is (Listing.rowStatus (.ended status)) { daemonUp := false, exit := some status } ∧
      (∃ o : Status.Obs,
        o.known = true ∧
          o.daemonUp = false ∧ Status.Is (Listing.rowStatus (.remote false (Status.name st))) o) ∧
      (st = .exitedOk ∨ st = .exitedBad →
        Listing.rowStatus (.remote false (Status.name st)) = st) := by
  sorry

@[kills rowStatus_saved]
theorem rowStatus_saved_rejects_unknown :
    ¬∀ (status : Nat) (st : Status.Status),
        Status.Is ((fun (_ : Listing.Row) => Status.Status.unknown) (.ended status))
            { daemonUp := false, exit := some status } ∧
          (∃ o : Status.Obs,
            o.known = true ∧
              o.daemonUp = false ∧
              Status.Is
                ((fun (_ : Listing.Row) => Status.Status.unknown) (.remote false (Status.name st)))
                o) ∧
          (st = .exitedOk ∨ st = .exitedBad →
            (fun (_ : Listing.Row) => Status.Status.unknown) (.remote false (Status.name st)) =
              st) := by
  sorry

theorem compose_attention_last (session application summary : String) (capacity : Nat) :
    Title.compose session application summary capacity =
      Title.compose session application ""
          (capacity - (if summary.isEmpty then "" else " · " ++ summary).length) ++
        (if summary.isEmpty then "" else " · " ++ summary) := by
  sorry

@[kills compose_attention_last]
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

theorem announce_changes (before current : List (String × Status.Status)) (own name : String) :
    Alert.announce none current own = [] ∧
      (name ∈ Alert.announce (some before) current own ↔
        name ≠ own ∧ (name, Status.Status.asks) ∈ current ∧ (name, Status.Status.asks) ∉ before) ∧
      ((current.map (·.1)).Nodup → (Alert.announce (some before) current own).Nodup) := by
  sorry

@[kills announce_changes]
theorem announce_changes_rejects_every_sample :
    ¬∀ (before current : List (String × Status.Status)) (own name : String),
        Alert.everySample none current own = [] ∧
          (name ∈ Alert.everySample (some before) current own ↔
            name ≠ own ∧
              (name, Status.Status.asks) ∈ current ∧ (name, Status.Status.asks) ∉ before) ∧
          ((current.map (·.1)).Nodup → (Alert.everySample (some before) current own).Nodup) := by
  sorry

@[kills announce_changes]
theorem announce_changes_rejects_self :
    ¬∀ (before current : List (String × Status.Status)) (own name : String),
        Alert.withSelf none current own = [] ∧
          (name ∈ Alert.withSelf (some before) current own ↔
            name ≠ own ∧
              (name, Status.Status.asks) ∈ current ∧ (name, Status.Status.asks) ∉ before) ∧
          ((current.map (·.1)).Nodup → (Alert.withSelf (some before) current own).Nodup) := by
  sorry

theorem sort_attention_first {α : Type} (status : α → Status.Status) (rows : List α) :
    (View.sort status rows).Perm rows ∧
      ∃ first rest,
        View.sort status rows = first ++ rest ∧
          (∀ x ∈ first,
            status x = .asks ∨ status x = .wantsYou ∨ status x = .exitedBad ∨ status x = .unknown) ∧
          ∀ x ∈ rest,
            ¬(status x = .asks ∨
                status x = .wantsYou ∨ status x = .exitedBad ∨ status x = .unknown) := by
  sorry

@[kills sort_attention_first]
theorem sort_attention_first_rejects_arrival :
    ¬∀ {α : Type} (status : α → Status.Status) (rows : List α),
        (View.arrival status rows).Perm rows ∧
          ∃ first rest,
            View.arrival status rows = first ++ rest ∧
              (∀ x ∈ first,
                status x = .asks ∨
                  status x = .wantsYou ∨ status x = .exitedBad ∨ status x = .unknown) ∧
              ∀ x ∈ rest,
                ¬(status x = .asks ∨
                    status x = .wantsYou ∨ status x = .exitedBad ∨ status x = .unknown) := by
  sorry

theorem sort_keeps_place {α : Type} (status status' : α → Status.Status) (rows : List α)
    (h :
      ∀ x ∈ rows,
        status x = status' x ∨
          ((status x = .working ∨ status x = .idle) ∧ (status' x = .working ∨ status' x = .idle))) :
    View.sort status rows = View.sort status' rows := by sorry

@[kills sort_keeps_place]
theorem sort_keeps_place_rejects_activity :
    ¬∀ {α : Type} (status status' : α → Status.Status) (rows : List α),
        (∀ x ∈ rows,
            status x = status' x ∨
              ((status x = .working ∨ status x = .idle) ∧
                (status' x = .working ∨ status' x = .idle))) →
          View.byActivity status rows = View.byActivity status' rows := by
  sorry

theorem sort_live_above_done {α : Type} (status : α → Status.Status) (rows first rest : List α)
    (split : View.sort status rows = first ++ rest) (x : α) (above : x ∈ first)
    (ended : status x = .exitedOk ∨ status x = .resumable) (y : α) (below : y ∈ rest) :
    ¬(status y = .asks ∨ status y = .wantsYou ∨ status y = .working ∨ status y = .idle) := by sorry

@[kills sort_live_above_done]
theorem sort_live_above_done_rejects_done_above :
    ¬∀ {α : Type} (status : α → Status.Status) (rows first rest : List α),
        View.doneAboveLive status rows = first ++ rest →
          ∀ (x : α),
            x ∈ first →
              (status x = .exitedOk ∨ status x = .resumable) →
              ∀ (y : α),
                y ∈ rest →
                  ¬(status y = .asks ∨
                      status y = .wantsYou ∨ status y = .working ∨ status y = .idle) := by
  sorry

theorem sort_two_keys {α : Type} (status : α → Status.Status) (earlier : α → α → Prop)
    (rows : List α) (listed : rows.Pairwise earlier) :
    (View.sort status rows).Perm rows ∧
      (View.sort status rows).Pairwise fun a b =>
        View.needs (status a) < View.needs (status b) ∨
          View.needs (status a) = View.needs (status b) ∧
            (View.lifecycle (status a) < View.lifecycle (status b) ∨
              View.lifecycle (status a) = View.lifecycle (status b) ∧ earlier a b) := by
  sorry

@[kills sort_two_keys]
theorem sort_two_keys_rejects_ended_above_saved :
    ¬∀ {α : Type} (status : α → Status.Status) (earlier : α → α → Prop) (rows : List α),
        rows.Pairwise earlier →
          (View.endedAboveSaved status rows).Perm rows ∧
            (View.endedAboveSaved status rows).Pairwise fun a b =>
              View.needs (status a) < View.needs (status b) ∨
                View.needs (status a) = View.needs (status b) ∧
                  (View.lifecycle (status a) < View.lifecycle (status b) ∨
                    View.lifecycle (status a) = View.lifecycle (status b) ∧ earlier a b) := by
  sorry

theorem before_total (a b c : String) :
    View.before a a = false ∧
      (View.before a b = true → View.before b c = true → View.before a c = true) ∧
      (a ≠ b → View.before a b = true ∨ View.before b a = true) := by
  sorry

@[kills before_total]
theorem before_total_rejects_none :
    ¬∀ (a b c : String),
        (fun (_ _ : String) => false) a a = false ∧
          ((fun (_ _ : String) => false) a b = true →
            (fun (_ _ : String) => false) b c = true → (fun (_ _ : String) => false) a c = true) ∧
          (a ≠ b →
            (fun (_ _ : String) => false) a b = true ∨
              (fun (_ _ : String) => false) b a = true) := by
  sorry

theorem before_number (p q : String) (n m : Nat) (h : n < m)
    (hp : ∀ c, p.toList.getLast? = some c → c.isDigit = false)
    (hq : ∀ c, q.toList.head? = some c → c.isDigit = false) :
    View.before (p ++ toString n ++ q) (p ++ toString m ++ q) = true := by sorry

@[kills before_number]
theorem before_number_rejects_lexicographic :
    ¬∀ (p q : String) (n m : Nat),
        n < m →
          (∀ c, p.toList.getLast? = some c → c.isDigit = false) →
          (∀ c, q.toList.head? = some c → c.isDigit = false) →
          (fun (a b : String) => decide (a < b)) (p ++ toString n ++ q) (p ++ toString m ++ q) =
            true := by
  sorry

theorem hidden_adds_up (targets : List String) :
    (View.hidden targets).2 = [] ∨
      ((View.hidden targets).2.map (·.2)).sum = (View.hidden targets).1 := by
  sorry

@[kills hidden_adds_up]
theorem hidden_adds_up_rejects_short :
    ¬∀ (targets : List String),
        ((fun (_ : List String) => (1, [("a", 0)])) targets).2 = [] ∨
          (((fun (_ : List String) => (1, [("a", 0)])) targets).2.map (·.2)).sum =
            ((fun (_ : List String) => (1, [("a", 0)])) targets).1 := by
  sorry

theorem matchCount_push (s typed : Selector.Picker.State) (c : Char)
    (push : typed = { s with query := s.query.push c }) :
    Selector.Picker.matchCount typed ≤ Selector.Picker.matchCount s := by sorry

@[kills matchCount_push]
theorem matchCount_push_rejects_length :
    ¬∀ (s typed : Selector.Picker.State) (c : Char),
        typed = { s with query := s.query.push c } →
          (fun (s : Selector.Picker.State) => s.query.length) typed ≤
            (fun (s : Selector.Picker.State) => s.query.length) s := by
  sorry

end Linger
