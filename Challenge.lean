module

public import Linger.App.Spec
public import Linger.Display.Spec
public import Linger.Import.Spec
public import Linger.Selector.Spec
public import Linger.Session.Spec
public import Linger.Target.Spec
public import Terminal.Mediation
public import Terminal.Render
public import Terminal.Replay
public import Terminal.Spec
public import Terminal.Title
public import Terminal.Vt

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
5. Accountability: every session ends once and one way, whether its program ends or a kill stops
   it, with an outcome recorded and reported truthfully to anyone who asks; every request gets a
   reply or a refusal, and every command exits with the code of an answer true of what happened.
6. Bounded and clean: input cannot raise any buffer, loop or wait past its cap, and nothing of a
   session's terminal session that linger's signals reach outlives it.
7. Recovery: resuming from a checkpoint gives back the saved session, less any half-parsed
   control sequence, and a crash costs at most the changes of the last interval, never the
   session: a checkpoint that does not decode is kept and refused, not replaced.
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
`⣿`, `!` and `?`. Its section follows the ten parts, with the titles, listings and selector
views that show statuses.

Each theorem below is stated over definitions in the components' `Spec` modules, over the
terminal package's parts, which its own challenge claims, and over the program parts declared
below as holes: each hole is `sorry` here, the program supplies it, and
the claims say what it must do. `Theorems/Solution.lean` proves the same statements of the
program's parts, and `./lake comparator` checks that it proves exactly these, that each part has
the declared type, and that no axiom beyond `propext`, `Quot.sound` and `Classical.choice` is
used. Changing a statement or a hole here changes what linger claims.

Not claimed: that the IO executors, the C shim and the operating system behave as the world
claims say, which the suites named with each claim exercise instead, except for power loss,
which `Disk.Durable` speaks of and no suite causes; scheduling, allocation failure, termination
by the operating system and failures of the compiler, the runtime or the C shim; a bound in bytes
or rows on what a crash loses, which is bounded in time; memory beyond the logical bytes the
buffers retain; ownership among processes that do not cooperate or replace the lock files;
fidelity beyond linger's own terminal model, which stands in for every receiver; the incoming
title content and the saved cursor slot, which fixtures cover; processes or images, since
recovery restores screens; that an exit status tells linger's answers from a program's, since a
program may exit with any status, as with `timeout` and `env`, so that `info` and the porcelain
output are the exact channel; for tmux imports, captures other than the latest save's archive;
and that an imported pane's saved command never runs, which a gate checks. -/

public section

open Linger.App Linger.Display Linger.Session Linger.Target Terminal

/-! ## The program's parts

### Command line -/

def Linger.App.Entry.route : List String → App.Entry.Route := sorry

def Linger.App.Commands.table : List App.Commands.Command := sorry

def Linger.App.Commands.lookup : String → Option App.Commands.Command := sorry

def Linger.App.Commands.retired : List (String × String) := sorry

def Linger.App.Commands.usageLine : App.Commands.Command → String := sorry

def Linger.App.Answer.code : App.Answer → UInt32 := sorry

def Linger.App.Answer.listed : List App.Answer := sorry

def Linger.App.Wait.heldNameMs : Nat := sorry

def Linger.App.Wait.decide : Option Nat → Option Nat → Nat → App.Wait.Heard → App.Wait.Next := sorry

def Linger.App.Recovery.decide : Bool → Option ByteArray → App.Recovery (Checkpoint.Ckpt Vt.Vt) :=
  sorry

/-! ### Session targets -/

def Linger.Target.Name.check : String → Option String := sorry

def Linger.Target.Remote.command : String → List String → String := sorry

def Linger.Target.Remote.decode : List String → Option (List String) := sorry

def Linger.Target.Remote.targetArgs : List String → Option (String × List String) := sorry

def Linger.Target.Remote.targetOperands : String → List String := sorry

def Linger.Target.Remote.checkHosts : List String → Except String (List String) := sorry

/-! ### Environment -/

def Linger.Os.Env.shellOf : Option String → String := sorry

def Linger.Os.Env.remotesFile : Option String → Option String := sorry

def Linger.Os.Env.detachEnabled : Bool → Option String → Bool := sorry

def Linger.Os.Env.resumeDir : Option String → String → Bool → Option String := sorry

/-! ### Statuses -/

def Linger.Display.Status.classify : Status.Obs → Status.Status := sorry

def Linger.Display.Status.icon : Status.Status → Char := sorry

def Linger.Display.Status.summary : List Status.Status → String := sorry

def Linger.Display.Status.name : Status.Status → String := sorry

def Linger.Display.Listing.rowFields : String → List (String × String) → List (String × String) :=
  sorry

def Linger.Display.Listing.rowStatus : Listing.Row → Status.Status := sorry

def Linger.Display.Listing.terminalListing : Bool → List (List (String × String)) → List UInt8 :=
  sorry

def Linger.Display.View.sort {α : Type} : (α → Status.Status) → List α → List α := sorry

def Linger.Display.View.groups : List String → List (String × Nat) := sorry

def Linger.Display.View.hidden : List String → Nat × List (String × Nat) := sorry

def Linger.Display.Title.compose : String → String → String → Nat → String := sorry

/-! ### Sessions -/

def Linger.Session.State : Type := sorry

def Linger.Session.State.boot : Vt.Vt → List (String × String) → List (String × String) → State :=
  sorry

def Linger.Session.Claim.enters : Bool → Bool → Bool := sorry

def Linger.Session.ending : List (UInt32 × Nat) := sorry

def Linger.Session.drainTimeoutMs : Nat := sorry

def Linger.Session.pollTimeout : Nat → List Nat → Int32 := sorry

def Linger.Session.Offloop.ask {R W : Type} : Offloop R W → W → Offloop R W × Option W := sorry

def Linger.Session.step : State → Event → State × List (Effect Replay.Plan) := sorry

def Linger.Session.State.client? : State → Nat → Option Client := sorry

def Linger.Session.State.terminal : State → Vt.Vt := sorry

def Linger.Session.State.roster : State → List Client := sorry

def Linger.Session.State.labelList : State → List (String × String) := sorry

def Linger.Session.State.scanner : State → Mediation.Scan := sorry

def Linger.Session.State.nextTick : State → Option Nat := sorry

def Linger.Session.infoText : State → List UInt8 := sorry

def Linger.Session.infoFields : State → List (String × String) := sorry

def Linger.Session.outcomeFields : Outcome → List (String × String) := sorry

def Linger.Session.Wire.encode : Wire.Msg → List UInt8 := sorry

def Linger.Session.Wire.Decoder.feed : Wire.Decoder → List UInt8 → Wire.Decoder × List Wire.Msg :=
  sorry

def Linger.Session.Wire.inputFrames : List UInt8 → List Wire.Msg := sorry

def Linger.Session.Wire.admits : Option Nat → Bool := sorry

def Linger.Session.Record.encode : Record → List UInt8 := sorry

def Linger.Session.Record.answer : Option (List UInt8) → Option Outcome := sorry

def Linger.Session.bootVt : Option Vt.Vt → Vt.Vt := sorry

def Linger.Session.Driver.run :
    {m : Type → Type} →
      [Monad m] →
      {World : Type} →
      (State → World → (eff : Effect Replay.Plan) → m (World × Driver.Reply eff)) →
        Driver.Result State World → List Event → m (Driver.Result State World) := sorry

def Linger.Session.Checkpoint.saveBytes : Checkpoint.Ckpt Vt.Vt → ByteArray := sorry

def Linger.Session.Checkpoint.loadBytes : ByteArray → Option (Checkpoint.Ckpt Vt.Vt) := sorry

def Linger.Session.Start.plan : (live saved : Bool) → Start.Plan := sorry

def Linger.Session.Start.programOf : String → List String → String × Array String := sorry

def Linger.Session.Start.proceeds : Bool → Bool := sorry

def Linger.Session.Start.answer : Bool → Bool → Start.Answer := sorry

def Linger.Session.Start.environment : String → List (String × String) := sorry

def Linger.Session.Start.reset : Spawn.Reset := sorry

def Linger.Session.Start.failureStatus : Spawn.Failure → UInt8 := sorry

def Linger.Session.Start.metadata :
    (name pid created cmd dir : String) → Option String → List (String × String) := sorry

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
      (String → Status.Status) → Bool → Bool → Bool → Nat → Nat → List UInt8 := sorry

def Linger.Selector.Picker.enterAnsi : List UInt8 := sorry

def Linger.Selector.Picker.exitAnsi : List UInt8 := sorry

def Linger.Import.Resurrect.plan :
    List String → List Import.Resurrect.Pane → List Import.Resurrect.Pane := sorry

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
terminal shows; that it keeps showing it as output continues is conjectured, for a repaint taken
between control sequences and characters; and a terminal's history only gains rows at its end,
unless output may ask to erase it. Here: a read that attaches a connection, writable or read-only,
streams it the repaint of the session's terminal as the attach leaves it, and the read sends it
nothing before the repaint: only the pty's resize and the program's focus report come first. A chunk
of program output feeds the session's terminal exactly that chunk, reaches every attached client,
writable or read-only, in roster order, as the same frames, each nonempty and of at most 64 KiB,
whose payloads are exactly the bytes the terminal package's mediator releases, in order, and writes
the program only the mediator's replies to its queries. The daemon does what the session asks: when
every effect succeeds, its driver hands the session each event and then what the event's effects
feed back, ends in the state of their trace, and executes exactly the trace's effects, in order,
each with the state its event left (`run_refines`, in part 5). Linger writes to a session's terminal
exactly the input it accepted for the program, in order, whatever mode the program set, and a
program whose terminal is in raw mode reads exactly that, when the kernel hands raw input on
unchanged (`Pty.Delivers`, which the agent suite exercises byte for byte); linger accepts each frame
a writable client sends, whatever its terminal's size, whole, or refuses it whole when the program's
queue is full; and `send` hands the program text of any length in frames the decoder takes, whose
payloads are the text, in order. A program that enabled focus reporting hears that it gained focus
when a writable client attaches to a session nobody could type into, whatever its size, and that it
lost it when the last one leaves. Not claimed: which bytes the mediator releases, which
`Terminal.Mediation` decides: all the program wrote but the queries linger answers itself, a request
still incomplete at a chunk's end waiting for the next; an attach a read completes with other
messages; that the runtime streams a repaint ahead of the output that follows it, which the delivery
suite checks; and what a program reads in any other mode than raw, such as the cooked mode a
terminal starts in, whose line discipline edits lines and turns ^C into a signal. -/

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
which has one owner (`one_owner`). The labels, the boot metadata and the terminal a session
reports each have one source, and a listing names each row by its socket. -/

theorem one_owner (grant : Claim.State → Nat → Nat → Bool) (exclusive : Claim.Exclusive grant)
    {s : Claim.State} (reached : Claim.Reachable grant Claim.enters s) {a b resource : Nat}
    {left right : Claim.Lease} (ha : s.active a = some left) (hb : s.active b = some right)
    (leftUses : left.Uses resource) (rightUses : right.Uses resource) : a = b := by sorry

theorem one_owner_rejects_socket :
    ¬∀ (grant : Claim.State → Nat → Nat → Bool),
        Claim.Exclusive grant →
          ∀ {s : Claim.State},
            Claim.Reachable grant (fun (socket _ : Bool) => socket) s →
              ∀ {a b resource : Nat} {left right : Claim.Lease},
                s.active a = some left →
                  s.active b = some right → left.Uses resource → right.Uses resource → a = b := by
  sorry

theorem step_labels_requested (s : State) (ev : Event)
    (changed : (Session.step s ev).1.labelList ≠ s.labelList) :
    ∃ id chunk c,
      ev = .bytes id chunk ∧
        s.client? id = some c ∧
        (c.attached = false ∨ c.mode = .writable) ∧
        ∃ m ∈ (c.decoder.feed chunk).2, m.ChangesLabels := by
  sorry

theorem step_labels_requested_rejects_reset :
    ¬∀ (s : State) (ev : Event),
        ((fun (s : State) (_ : Event) =>
                  (State.boot s.terminal [] [], ([] : List (Effect Replay.Plan))))
                s ev).1.labelList ≠
            s.labelList →
          ∃ id chunk c,
            ev = .bytes id chunk ∧
              s.client? id = some c ∧
              (c.attached = false ∨ c.mode = .writable) ∧
              ∃ m ∈ (c.decoder.feed chunk).2, m.ChangesLabels := by
  sorry

theorem infoFields_boot (vt : Vt.Vt) (labels metadata : List (String × String)) (evs : List Event) :
    ∃ rest,
      Session.infoFields (Session.trace Session.step (State.boot vt labels metadata) evs).1 =
        metadata ++ rest := by
  sorry

theorem infoFields_boot_rejects_reboot :
    ¬∀ (vt : Vt.Vt) (labels metadata : List (String × String)) (evs : List Event),
        ∃ rest,
          Session.infoFields
              (Session.trace
                  (fun (_ : State) (_ : Event) =>
                    (State.boot (Vt.Vt.init 1 1) [] [], ([] : List (Effect Replay.Plan))))
                  (State.boot vt labels metadata) evs).1 =
            metadata ++ rest := by
  sorry

theorem step_terminal_sources (s : State) (ev : Event) :
    (∃ chunk, ev = .ptyOut chunk ∧ (Session.step s ev).1.terminal = s.terminal.feed chunk) ∨
      ∃ sizes : List (Nat × Nat),
        (Session.step s ev).1.terminal =
          sizes.foldl (fun v (size : Nat × Nat) => v.resize size.1 size.2) s.terminal := by
  sorry

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

theorem start_plan (live saved : Bool) :
    Start.plan live saved = if live then .running else if saved then .saved else .take := by sorry

theorem start_plan_rejects_take :
    ¬∀ (live saved : Bool),
        (fun (_ _ : Bool) => Start.Plan.take) live saved =
          if live then .running else if saved then .saved else .take := by
  sorry

theorem run_bytes_isolates (s : State) (id : Nat) (chunks : List (List UInt8)) {other : Nat}
    (h : other ≠ id) :
    (Session.trace Session.step s (chunks.map (Event.bytes id))).1.client? other =
      s.client? other := by
  sorry

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
      (Session.trace Session.step s (chunks.map (Event.bytes id))).1.labelList = s.labelList ∧
      ∀ eff ∈ (Session.trace Session.step s (chunks.map (Event.bytes id))).2,
        (∃ m, eff = .send id m) ∨ eff = .close id ∨ eff = .checkpoint := by
  sorry

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
                  (chunks.map (Event.bytes id))).1.labelList =
              s.labelList ∧
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

theorem remotesFile_home (home : Option String) :
    Os.Env.remotesFile home = none ↔ home = none ∨ home = some "" := by sorry

theorem remotesFile_home_rejects_shared :
    ¬∀ (home : Option String),
        (fun (_ : Option String) => some "remotes") home = none ↔ home = none ∨ home = some "" := by
  sorry

theorem rowFields_name (socketName : String) (info : List (String × String)) :
    (Listing.rowFields socketName info).lookup "name" = some socketName := by sorry

theorem rowFields_name_rejects_reply :
    ¬∀ (socketName : String) (info : List (String × String)),
        ((fun (_ : String) (info : List (String × String)) => info) socketName info).lookup "name" =
          some socketName := by
  sorry

theorem picker_attach_listed (s : Selector.Picker.State) (key : Selector.Key) (target : String)
    (h : Selector.Picker.step s key = .attach target) : target ∈ s.candidates := by sorry

theorem picker_attach_listed_rejects_fixed :
    ¬∀ (s : Selector.Picker.State) (key : Selector.Key) (target : String),
        (fun (_ : Selector.Picker.State) (_ : Selector.Key) => Selector.Picker.Outcome.attach "s") s
              key =
            .attach target →
          target ∈ s.candidates := by
  sorry

theorem picker_create_new (s : Selector.Picker.State) (key : Selector.Key) (target : String)
    (h : Selector.Picker.step s key = .create target) :
    target ∉ s.candidates ∧ target ≠ "" ∧ Name.Valid ((target.splitOn "@").headD "") := by sorry

theorem picker_create_new_rejects_empty :
    ¬∀ (s : Selector.Picker.State) (key : Selector.Key) (target : String),
        (fun (_ : Selector.Picker.State) (_ : Selector.Key) => Selector.Picker.Outcome.create "") s
              key =
            .create target →
          target ∉ s.candidates ∧ target ≠ "" ∧ Name.Valid ((target.splitOn "@").headD "") := by
  sorry

/-! ## 3. Exactness

`start` runs its program in the caller's directory and with the caller's environment, which only
`LINGER_SESSION`, `TERM`, `TERM_PROGRAM` and `TERM_PROGRAM_VERSION` change, when the operating
system runs what linger asks (`start_runs`, in part 4). A program that cannot start there makes
`start` return what `env -C` would, and a resume that runs elsewhere than its saved directory
says so.

A command on a `name@host` target reaches the linger on that host as exactly its verb and words,
whatever they hold, through any login shell that passes plain words on (`Shell.Literal`):
`Remote.command` encodes them as plain words, and the remote entry decodes them before it routes
the command line and refuses one that does not decode as a usage error. POSIX quoting would not:
fish reads a backslash inside single quotes, so a quoted word could close its quote there and
run what follows. Not claimed: that the remote linger decodes, since an older one refuses the
encoded line as a usage error, nor that a command line fits the remote host's argument limit. -/

theorem route_exact (args : List String) :
    App.Entry.route args =
      if args.head? = some Remote.marker then
        match Remote.decode args.tail with
        | some argv => App.Entry.Route.of argv
        | none => .malformed
      else App.Entry.Route.of args := by
  sorry

theorem route_exact_rejects_selector :
    ¬∀ (args : List String),
        (fun (args : List String) => App.Entry.Route.session args) args =
          if args.head? = some Remote.marker then
            match Remote.decode args.tail with
            | some argv => App.Entry.Route.of argv
            | none => .malformed
          else App.Entry.Route.of args := by
  sorry

theorem lookup_table :
    (App.Commands.table.flatMap fun command => command.word :: command.aliases).Nodup ∧
      ∀ command ∈ App.Commands.table,
        App.Commands.lookup command.word = some command ∧
          ∀ word ∈ command.aliases, App.Commands.lookup word = some command := by
  sorry

theorem lookup_table_rejects_none :
    ¬((App.Commands.table.flatMap fun command => command.word :: command.aliases).Nodup ∧
        ∀ command ∈ App.Commands.table,
          (fun (_ : String) => (none : Option App.Commands.Command)) command.word = some command ∧
            ∀ word ∈ command.aliases,
              (fun (_ : String) => (none : Option App.Commands.Command)) word = some command) := by
  sorry

theorem retired_free : ∀ entry ∈ App.Commands.retired, App.Commands.lookup entry.1 = none := by
  sorry

theorem retired_free_rejects_any :
    ¬∀ entry ∈ App.Commands.retired,
        (fun (_ : String) =>
              some ({ word := "run", args := "", summary := "" } : App.Commands.Command))
            entry.1 =
          none := by
  sorry

theorem usageLine_exact (command : App.Commands.Command) :
    App.Commands.usageLine command =
      if command.args.isEmpty then s!"usage: linger {command.word}"
      else s!"usage: linger {command.word} {command.args}" := by
  sorry

theorem usageLine_exact_rejects_bare :
    ¬∀ (command : App.Commands.Command),
        (fun (_ : App.Commands.Command) => "usage: linger") command =
          if command.args.isEmpty then s!"usage: linger {command.word}"
          else s!"usage: linger {command.word} {command.args}" := by
  sorry

theorem plan_exact (existing : List String) (panes : List Import.Resurrect.Pane)
    (pane : Import.Resurrect.Pane) :
    pane ∈ Import.Resurrect.plan existing panes ↔ pane ∈ panes ∧ pane.name ∉ existing := by sorry

theorem plan_exact_rejects_all :
    ¬∀ (existing : List String) (panes : List Import.Resurrect.Pane) (pane : Import.Resurrect.Pane),
        pane ∈
            (fun (_ : List String) (panes : List Import.Resurrect.Pane) => panes) existing panes ↔
          pane ∈ panes ∧ pane.name ∉ existing := by
  sorry

theorem plan_again_empty (existing : List String) (panes made : List Import.Resurrect.Pane)
    (first : made = Import.Resurrect.plan existing panes) :
    Import.Resurrect.plan (existing ++ made.map (·.name)) panes = [] := by sorry

theorem plan_again_empty_rejects_all :
    ¬∀ (existing : List String) (panes made : List Import.Resurrect.Pane),
        made =
            (fun (_ : List String) (panes : List Import.Resurrect.Pane) => panes) existing panes →
          (fun (_ : List String) (panes : List Import.Resurrect.Pane) => panes)
              (existing ++ made.map (·.name)) panes =
            [] := by
  sorry

theorem check_eq_some_iff (s result : String) :
    Name.check s = some result ↔ result = s ∧ Name.Valid s := by sorry

theorem check_eq_some_iff_rejects_any :
    ¬∀ (s result : String), (fun s => some s) s = some result ↔ result = s ∧ Name.Valid s := by
  sorry

theorem command_exact (split : String → List String) (literal : Remote.Shell.Literal split)
    (verb : String) (words : List String) :
    ∃ args,
      split (Remote.command verb words) = "linger" :: args ∧
        App.Entry.route args = App.Entry.Route.of (verb :: words) := by
  sorry

theorem command_exact_rejects_quoted :
    ¬∀ (split : String → List String),
        Remote.Shell.Literal split →
          ∀ (verb : String) (words : List String),
            ∃ args,
              split
                    ((fun (verb : String) (words : List String) =>
                        String.intercalate " "
                          (("linger" :: verb :: words).map fun word =>
                            String.ofList
                              ('\'' ::
                                  word.toList.flatMap
                                    (fun c => if c = '\'' then ['\'', '\\', '\'', '\''] else [c]) ++
                                ['\''])))
                      verb words) =
                  "linger" :: args ∧
                App.Entry.route args = App.Entry.Route.of (verb :: words) := by
  sorry

theorem check_no_alias (a b name : String) (ha : Name.check a = some name)
    (hb : Name.check b = some name) : a = b := by sorry

theorem check_no_alias_rejects_fold :
    ¬∀ (a b name : String),
        (fun (_ : String) => some "s") a = some name →
          (fun (_ : String) => some "s") b = some name → a = b := by
  sorry

theorem targetArgs_targetOperands (name : String) (rest : List String) :
    Remote.targetArgs (Remote.targetOperands name ++ rest) = some (name, rest) := by sorry

theorem targetArgs_targetOperands_rejects_none :
    ¬∀ (name : String) (rest : List String),
        Remote.targetArgs ((fun (_ : String) => ([] : List String)) name ++ rest) =
          some (name, rest) := by
  sorry

theorem checkHosts_ok_iff (hosts result : List String) :
    Remote.checkHosts hosts = .ok result ↔
      result = hosts ∧ hosts.Nodup ∧ ∀ x ∈ hosts, Remote.hostClean x = true := by
  sorry

theorem checkHosts_ok_iff_rejects_any :
    ¬∀ (hosts result : List String),
        (fun (hosts : List String) => (.ok hosts : Except String (List String))) hosts =
            .ok result ↔
          result = hosts ∧ hosts.Nodup ∧ ∀ x ∈ hosts, Remote.hostClean x = true := by
  sorry

theorem detach_key (flag : Option String) :
    Os.Env.detachEnabled true flag = true ∧ Os.Env.detachEnabled false flag = flag.isNone := by
  sorry

theorem detach_key_rejects_never :
    ¬∀ (flag : Option String),
        (fun (_ : Bool) (_ : Option String) => false) true flag = true ∧
          (fun (_ : Bool) (_ : Option String) => false) false flag = flag.isNone := by
  sorry

theorem resumeDir_where (home : Option String) (saved dir : String) (set : dir ≠ "") :
    Os.Env.resumeDir home saved true = some saved ∧
      Os.Env.resumeDir (some dir) saved false = some dir ∧
      Os.Env.resumeDir none saved false = none ∧ Os.Env.resumeDir (some "") saved false = none := by
  sorry

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

theorem failureStatus_exact (why : String) :
    Start.failureStatus (.directory why) = 125 ∧
      Start.failureStatus (.notFound why) = 127 ∧ Start.failureStatus (.notRunnable why) = 126 := by
  sorry

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
`Spawn.Runs`, which the agent and resume suites exercise.

The program starts from what its start asks, never from how linger was started: every signal at
its default action, none blocked, and its terminal on descriptors 0, 1 and 2 with no other open,
whatever the command that asked for the session ignored, blocked or left open, as a shell's `&`
job ignores SIGINT and SIGQUIT and `exec 3>&1` leaves a pipe open (`start_clean`, over the world
claim `Spawn.Clean`, which the agent suite exercises). Not claimed: the rest of what a program
inherits as any child does, such as resource limits, the file mode mask, scheduling priority and
the user and groups it runs as. -/

theorem programOf_exact (shell : String) (argv : List String) :
    Start.programOf shell argv = (argv.headD shell, (argv.drop 1).toArray) := by sorry

theorem programOf_exact_rejects_shell :
    ¬∀ (shell : String) (argv : List String),
        (fun (shell : String) (argv : List String) => (shell, #["-c", String.intercalate " " argv]))
            shell argv =
          (argv.headD shell, (argv.drop 1).toArray) := by
  sorry

theorem shellOf_choice (shell : String) (set : shell ≠ "") :
    Os.Env.shellOf (some shell) = shell ∧
      Os.Env.shellOf none = "sh" ∧ Os.Env.shellOf (some "") = "sh" := by
  sorry

theorem shellOf_choice_rejects_fixed :
    ¬∀ (shell : String),
        shell ≠ "" →
          (fun (_ : Option String) => "sh") (some shell) = shell ∧
            (fun (_ : Option String) => "sh") none = "sh" ∧
            (fun (_ : Option String) => "sh") (some "") = "sh" := by
  sorry

theorem start_runs (inherited : String → Option String)
    (start :
      String → String → Array String → List (String × String) → Spawn.Reset → Option Spawn.Started)
    (runs : Spawn.Runs inherited start) (name dir shell : String) (argv : List String)
    {started : Spawn.Started}
    (ok :
      start dir (Start.programOf shell argv).1 (Start.programOf shell argv).2
          (Start.environment name) Start.reset =
        some started) :
    started.argv = argv.headD shell :: argv.drop 1 ∧
      started.dir = dir ∧
      started.env "LINGER_SESSION" = some name ∧
      started.env "TERM" = some "xterm-256color" ∧
      started.env "TERM_PROGRAM" = some "linger" ∧
      started.env "TERM_PROGRAM_VERSION" = some Mediation.versionNumber ∧
      ∀ key,
        key ∉ ["LINGER_SESSION", "TERM", "TERM_PROGRAM", "TERM_PROGRAM_VERSION"] →
          started.env key = inherited key := by
  sorry

theorem start_runs_rejects_unnamed :
    ¬∀ (inherited : String → Option String)
        (start :
          String →
            String → Array String → List (String × String) → Spawn.Reset → Option Spawn.Started),
        Spawn.Runs inherited start →
          ∀ (name dir shell : String) (argv : List String) {started : Spawn.Started},
            start dir (Start.programOf shell argv).1 (Start.programOf shell argv).2
                  ((fun (_ : String) => ([] : List (String × String))) name) Start.reset =
                some started →
              started.argv = argv.headD shell :: argv.drop 1 ∧
                started.dir = dir ∧
                started.env "LINGER_SESSION" = some name ∧
                started.env "TERM" = some "xterm-256color" ∧
                started.env "TERM_PROGRAM" = some "linger" ∧
                started.env "TERM_PROGRAM_VERSION" = some Mediation.versionNumber ∧
                ∀ key,
                  key ∉ ["LINGER_SESSION", "TERM", "TERM_PROGRAM", "TERM_PROGRAM_VERSION"] →
                    started.env key = inherited key := by
  sorry

theorem start_clean
    (start :
      String → String → Array String → List (String × String) → Spawn.Reset → Option Spawn.Started)
    (clean : Spawn.Clean start) (name dir shell : String) (argv : List String)
    {started : Spawn.Started}
    (ok :
      start dir (Start.programOf shell argv).1 (Start.programOf shell argv).2
          (Start.environment name) Start.reset =
        some started) :
    (∀ sig, started.ignored sig = false) ∧
      (∀ sig, started.blocked sig = false) ∧
      ∀ fd, started.descriptor fd = if fd < 3 then some .terminal else none := by
  sorry

theorem start_clean_rejects_inherited :
    ¬∀
        (start :
          String →
            String → Array String → List (String × String) → Spawn.Reset → Option Spawn.Started),
        Spawn.Clean start →
          ∀ (name dir shell : String) (argv : List String) {started : Spawn.Started},
            start dir (Start.programOf shell argv).1 (Start.programOf shell argv).2
                  (Start.environment name)
                  ({ dispositions := false, mask := true, descriptors := true } : Spawn.Reset) =
                some started →
              (∀ sig, started.ignored sig = false) ∧
                (∀ sig, started.blocked sig = false) ∧
                ∀ fd, started.descriptor fd = if fd < 3 then some .terminal else none := by
  sorry

/-! ## 5. Accountability

A session ends one way, whether its program ends by itself or a kill stops it: the daemon hands
a stopped program's end back to the session, everyone attached or waiting hears how the program
ended before the daemon exits, and only a kill discards the session. When the file system keeps
what linger saves (`Record.Kept`, which the agent suite exercises), a name's end record keeps how
its last session's program ended, for whoever asks later, a record its session left while the
program still ran answers that the ending is unknown, and only a name with no record answers
nothing (`record_answer`).
`wait` answers with how the program ended when its daemon or the end record says, and that it
could not find out only when that is so: the ending is unknown, or the name stays held, with no
daemon answering, from the look that first found it so for longer than a daemon's ending lasts.
Every command answers with one of the answers `Answer` names, and exits with its code.
An attach goes only to a daemon whose `info` answer reports this version's protocol level, as
every daemon of this version does (`infoFields_protocol`), so a daemon an older linger started
is refused with a reason, never sent an attach it would refuse as unknown or drop unanswered.
Not claimed: that the answer comes within the client's wait and that the refusal names the
session and the level, which the attach suite checks against a level-2 daemon, one that reports
no level and one that never answers.

The daemon's driver runs the session's trace. When every effect succeeds, a stop replying how the
program ended, the driver hands the session each event and then what that event's effects feed
back, a stop's reply as the event `stopped`, before the next event; it ends in the state of the
trace of `Session.step` over those events, executes exactly that trace's effects, in order, each
with the state its event left, and exits exactly when one of them asks it to (`run_refines`).
Whatever its effects reply, an executor that answers every effect lets it return and keeps the
session within its bounds (`run_total_safe`), disconnects and failed saves never stop it
(`run_feedback_alive`), once it exits it handles no event (`run_exited`), and an event whose
effects stop the program ends the session (`run_stop_exits`). Not claimed: which events the
driver hands the session and which effects it executes when an effect fails. -/

theorem step_kill_stops (s : State) (id : Nat) (chunk : List UInt8) {c : Client}
    {dec : Wire.Decoder} {rest : List Wire.Msg} (hc : s.client? id = some c)
    (writable : c.mode = .writable) (read : c.decoder.feed chunk = (dec, .kill :: rest))
    (healthy : dec.errored = false) :
    (Session.step s (.bytes id chunk)).2 = [.stopProgram, .close id] ∧
      (Session.step s (.bytes id chunk)).1.terminal = s.terminal ∧
      (Session.step s (.bytes id chunk)).1.labelList = s.labelList := by
  sorry

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
                  (.bytes id chunk)).1.labelList =
              s.labelList := by
  sorry

theorem step_ended_reports (s : State) (ev : Event) :
    (Effect.exit ∈ (Session.step s ev).2 ↔ ∃ o, ev = .childExited o ∨ ev = .stopped o) ∧
      ∀ o,
        ev = .childExited o ∨ ev = .stopped o →
          (Session.step s ev).2.getLast? = some .exit ∧
            ∀ c ∈ s.roster,
              c.attached = true ∨ c.waiting = true →
                [Effect.send c.id (.ended o), Effect.send c.id (.exited o.status)] <:+:
                  (Session.step s ev).2 := by
  sorry

theorem step_ended_reports_rejects_status :
    ¬∀ (s : State) (ev : Event),
        (Effect.exit ∈
              ((fun s _ => (s, ([.send 0 (.exited 1), .exit] : List (Effect Replay.Plan)))) s
                  ev).2 ↔
            ∃ o, ev = .childExited o ∨ ev = .stopped o) ∧
          ∀ o,
            ev = .childExited o ∨ ev = .stopped o →
              ((fun s _ => (s, ([.send 0 (.exited 1), .exit] : List (Effect Replay.Plan)))) s
                      ev).2.getLast? =
                  some .exit ∧
                ∀ c ∈ (fun (_ : State) => [({ id := 0, attached := true } : Client)]) s,
                  c.attached = true ∨ c.waiting = true →
                    [Effect.send c.id (.ended o), Effect.send c.id (.exited o.status)] <:+:
                      ((fun s _ => (s, ([.send 0 (.exited 1), .exit] : List (Effect Replay.Plan))))
                          s ev).2 := by
  sorry

theorem step_stopped_discards (s : State) (o : Outcome) :
    (∃ front,
        (Session.step s (.stopped o)).2 = front ++ [.dropCheckpoint, .exit] ∧
          Effect.checkpoint ∉ front) ∧
      (Session.step s (.stopped o)).1.terminal = s.terminal := by
  sorry

theorem step_stopped_discards_rejects_save :
    ¬∀ (s : State) (o : Outcome),
        (∃ front,
            ((fun (s : State) (_ : Event) =>
                      (s, ([.checkpoint, .dropCheckpoint, .exit] : List (Effect Replay.Plan))))
                    s (.stopped o)).2 =
                front ++ [.dropCheckpoint, .exit] ∧
              Effect.checkpoint ∉ front) ∧
          ((fun (s : State) (_ : Event) =>
                  (s, ([.checkpoint, .dropCheckpoint, .exit] : List (Effect Replay.Plan))))
                s (.stopped o)).1.terminal =
            s.terminal := by
  sorry

theorem step_childExited_keeps (s : State) (o : Outcome) :
    (∃ front,
        (Session.step s (.childExited o)).2 = front ++ [.checkpoint, .exit] ∧
          Effect.dropCheckpoint ∉ front) ∧
      (Session.step s (.childExited o)).1.terminal = s.terminal := by
  sorry

theorem step_childExited_keeps_rejects_drop :
    ¬∀ (s : State) (o : Outcome),
        (∃ front,
            ((fun (s : State) (_ : Event) =>
                      (s, ([.dropCheckpoint, .checkpoint, .exit] : List (Effect Replay.Plan))))
                    s (.childExited o)).2 =
                front ++ [.checkpoint, .exit] ∧
              Effect.dropCheckpoint ∉ front) ∧
          ((fun (s : State) (_ : Event) =>
                  (s, ([.dropCheckpoint, .checkpoint, .exit] : List (Effect Replay.Plan))))
                s (.childExited o)).1.terminal =
            s.terminal := by
  sorry

theorem record_answer (afterSave : List UInt8 → Option (List UInt8)) (kept : Record.Kept afterSave)
    (o : Outcome) (seen : Option Seen) (file : Option (List UInt8)) :
    Record.answer (afterSave (Record.encode (.ended o))) = some o ∧
      Record.answer (afterSave (Record.encode (.running seen))) = some .unknown ∧
      (Record.answer file).isSome = file.isSome := by
  sorry

theorem record_answer_rejects_unknown :
    ¬∀ (afterSave : List UInt8 → Option (List UInt8)),
        Record.Kept afterSave →
          ∀ (o : Outcome) (seen : Option Seen) (file : Option (List UInt8)),
            (fun (_ : Option (List UInt8)) => some Outcome.unknown)
                  (afterSave (Record.encode (.ended o))) =
                some o ∧
              (fun (_ : Option (List UInt8)) => some Outcome.unknown)
                  (afterSave (Record.encode (.running seen))) =
                some .unknown ∧
              ((fun (_ : Option (List UInt8)) => some Outcome.unknown) file).isSome =
                file.isSome := by
  sorry

theorem wait_ending (deadline heldSince : Option Nat) (now : Nat) (o : Outcome) :
    Wait.decide deadline heldSince now (.ended o) = .answer (Answer.ofOutcome o) ∧
      Wait.decide deadline heldSince now (.recorded (some o)) = .answer (Answer.ofOutcome o) := by
  sorry

theorem wait_ending_rejects_failed :
    ¬∀ (deadline heldSince : Option Nat) (now : Nat) (o : Outcome),
        (fun (_ _ : Option Nat) (_ : Nat) (_ : Wait.Heard) => Wait.Next.answer .failed) deadline
              heldSince now (.ended o) =
            .answer (Answer.ofOutcome o) ∧
          (fun (_ _ : Option Nat) (_ : Nat) (_ : Wait.Heard) => Wait.Next.answer .failed) deadline
              heldSince now (.recorded (some o)) =
            .answer (Answer.ofOutcome o) := by
  sorry

theorem wait_held (deadline heldSince : Option Nat) (now : Nat) (heard : Wait.Heard) :
    (Wait.decide deadline heldSince now heard = .answer .failed ↔
        heard = .ended .unknown ∨
          heard = .recorded (some .unknown) ∨
          heard = .held ∧ ∃ since, heldSince = some since ∧ since + Wait.heldNameMs ≤ now) ∧
      (heard = .held →
        (∀ due, deadline = some due → now < due) →
        (∀ since, heldSince = some since → now < since + Wait.heldNameMs) →
        Wait.decide deadline heldSince now heard = .again (some (heldSince.getD now))) := by
  sorry

theorem wait_held_rejects_eager :
    ¬∀ (deadline heldSince : Option Nat) (now : Nat) (heard : Wait.Heard),
        ((fun (_ _ : Option Nat) (_ : Nat) (_ : Wait.Heard) => Wait.Next.answer .failed) deadline
                heldSince now heard =
              .answer .failed ↔
            heard = .ended .unknown ∨
              heard = .recorded (some .unknown) ∨
              heard = .held ∧ ∃ since, heldSince = some since ∧ since + Wait.heldNameMs ≤ now) ∧
          (heard = .held →
            (∀ due, deadline = some due → now < due) →
            (∀ since, heldSince = some since → now < since + Wait.heldNameMs) →
            (fun (_ _ : Option Nat) (_ : Nat) (_ : Wait.Heard) => Wait.Next.answer .failed) deadline
                heldSince now heard =
              .again (some (heldSince.getD now))) := by
  sorry

theorem held_covers_ending :
    Session.drainTimeoutMs + (Session.ending.map (·.2)).sum ≤ Wait.heldNameMs := by sorry

theorem held_covers_ending_rejects_drain :
    ¬Session.drainTimeoutMs + (Session.ending.map (·.2)).sum ≤ Session.drainTimeoutMs := by sorry

theorem code_documented (status : UInt32) :
    Answer.code .done = 0 ∧
      Answer.code .notDone = 1 ∧
      Answer.code .usage = 2 ∧
      Answer.code .timedOut = 124 ∧
      Answer.code .failed = 125 ∧
      Answer.code .cannotRun = 126 ∧
      Answer.code .notFound = 127 ∧
      Answer.code .interrupted = 130 ∧ Answer.code (.program status) = status := by
  sorry

theorem code_documented_rejects_zero :
    ¬∀ (status : UInt32),
        (fun (_ : Answer) => (0 : UInt32)) .done = 0 ∧
          (fun (_ : Answer) => (0 : UInt32)) .notDone = 1 ∧
          (fun (_ : Answer) => (0 : UInt32)) .usage = 2 ∧
          (fun (_ : Answer) => (0 : UInt32)) .timedOut = 124 ∧
          (fun (_ : Answer) => (0 : UInt32)) .failed = 125 ∧
          (fun (_ : Answer) => (0 : UInt32)) .cannotRun = 126 ∧
          (fun (_ : Answer) => (0 : UInt32)) .notFound = 127 ∧
          (fun (_ : Answer) => (0 : UInt32)) .interrupted = 130 ∧
          (fun (_ : Answer) => (0 : UInt32)) (.program status) = status := by
  sorry

theorem listed_once : Answer.listed.Nodup ∧ ∀ a, a ∈ Answer.listed ↔ a.Own := by sorry

theorem listed_once_rejects_empty :
    ¬(([] : List Answer).Nodup ∧ ∀ a, a ∈ ([] : List Answer) ↔ a.Own) := by sorry

theorem outcomeFields_injective (o₁ o₂ : Outcome)
    (h : Session.outcomeFields o₁ = Session.outcomeFields o₂) : o₁ = o₂ := by sorry

theorem outcomeFields_injective_rejects_silence :
    ¬∀ (o₁ o₂ : Outcome),
        (fun (_ : Outcome) => ([] : List (String × String))) o₁ =
            (fun (_ : Outcome) => ([] : List (String × String))) o₂ →
          o₁ = o₂ := by
  sorry

theorem infoFields_protocol (s : State) :
    ("protocol", toString Wire.protocol) ∈ Session.infoFields s := by sorry

theorem infoFields_protocol_rejects_empty :
    ¬∀ (s : State),
        ("protocol", toString Wire.protocol) ∈
          (fun (_ : State) => ([] : List (String × String))) s := by
  sorry

theorem admits_level (level : Option Nat) :
    Wire.admits level = true ↔ level = some Wire.protocol := by sorry

theorem admits_level_rejects_any :
    ¬∀ (level : Option Nat),
        (fun (_ : Option Nat) => true) level = true ↔ level = some Wire.protocol := by
  sorry

theorem step_unknown_refused (s : State) (id : Nat) (chunk : List UInt8) {c : Client}
    {dec : Wire.Decoder} {tag : UInt8} {payload : List UInt8} (hc : s.client? id = some c)
    (read : c.decoder.feed chunk = (dec, [.unknown tag payload])) (healthy : dec.errored = false) :
    (Session.step s (.bytes id chunk)).2 = [.send id (.err "unknown message".toUTF8.toList)] ∧
      (Session.step s (.bytes id chunk)).1.terminal = s.terminal ∧
      (Session.step s (.bytes id chunk)).1.labelList = s.labelList := by
  sorry

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
                  (.bytes id chunk)).1.labelList =
              s.labelList := by
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

theorem run_feedback_alive {World : Type}
    (execute : State → World → (eff : Effect Replay.Plan) → Id (World × Driver.Reply eff))
    (r : Driver.Result State World) (events : List Event) (running : r.exiting = false)
    (failures : ∀ ev ∈ events, ev = .checkpointFailed ∨ ∃ id, ev = .closed id) :
    (Driver.run execute r events).exiting = false := by sorry

theorem run_feedback_alive_rejects_halt :
    ¬∀ {World : Type}
        (execute : State → World → (eff : Effect Replay.Plan) → Id (World × Driver.Reply eff))
        (r : Driver.Result State World) (events : List Event),
        r.exiting = false →
          (∀ ev ∈ events, ev = .checkpointFailed ∨ ∃ id, ev = .closed id) →
          (Driver.halt execute r events).exiting = false := by
  sorry

theorem run_exited {m : Type → Type} [Monad m] {World : Type}
    (execute : State → World → (eff : Effect Replay.Plan) → m (World × Driver.Reply eff))
    (r : Driver.Result State World) (events : List Event) (exited : r.exiting = true) :
    Driver.run execute r events = pure r := by sorry

theorem run_exited_rejects_jump :
    ¬∀ {m : Type → Type} [Monad m] {World : Type}
        (execute : State → World → (eff : Effect Replay.Plan) → m (World × Driver.Reply eff))
        (r : Driver.Result State World) (events : List Event),
        r.exiting = true →
          Driver.jump (State.boot (Vt.Vt.init 1 1) [] []) execute r events = pure r := by
  sorry

theorem run_stop_exits {World : Type}
    (execute : State → World → (eff : Effect Replay.Plan) → Id (World × Driver.Reply eff))
    (r : Driver.Result State World) (ev : Event) (running : r.exiting = false)
    (stops : Effect.stopProgram ∈ (Session.step r.st ev).2) :
    (Driver.run execute r [ev]).exiting = true := by sorry

theorem run_stop_exits_rejects_jump :
    ¬∀ {World : Type}
        (execute : State → World → (eff : Effect Replay.Plan) → Id (World × Driver.Reply eff))
        (r : Driver.Result State World) (ev : Event),
        r.exiting = false →
          Effect.stopProgram ∈ (Session.step r.st ev).2 →
          (Driver.jump (State.boot (Vt.Vt.init 1 1) [] []) execute r [ev]).exiting = true := by
  sorry

/-! ## 6. Bounded and clean

After every batch of events, the driver leaves the session's clients, labels, frame decoders and
pty scanner within their caps, whatever its effects reply, when its executor answers every effect
(`run_total_safe`, in part 5); when every effect succeeds, the states it leaves are those of the
session's trace (`run_refines`, in part 5). The pty's input queue never owes more than its cap,
nor does a client's output queue the daemon keeps (`reachableIn_bound`, `reachableOut_bound`); a
read gets at most one rendered reply, its frames followed by `done`, and when it leaves its sender
unattached at most one pty resize (`step_bytes_one_reply`); every frame of program output carries
at most 64 KiB (`step_output_delivered`, in part 1); and a tmux capture's bytes are at most twice
its limit (`captureBytes_bounded`). When a session ends, the daemon sends SIGHUP to its program
and the rest of the program's terminal session, then SIGKILL to those still running a second
later, and reaps the program last, so the program's pid, which is the session's id, stays
reserved until then: of the processes of the terminal session its signals reach, none still runs
once the ending is over (`ending_clean`), when SIGKILL ends within a second each process it
reaches (`Signal.Ends`, which the attach suite exercises and a process stuck in the kernel
falsifies). Not claimed: how many pty resizes a read asks for while its sender stays attached;
and the processes linger's signals miss, as the claim's comment names them: one that left the
terminal session with `setsid`, one of another user and one forked after the daemon looked. -/

theorem reachableIn_bound {cap : Nat} {b : Buf.Buf}
    (h : Buf.InputReach Buf.Buf.empty Buf.bufOffer Buf.bufAdvance cap b) : Buf.owedLen b ≤ cap := by
  sorry

theorem reachableIn_bound_rejects_append :
    ¬∀ {cap : Nat} {b : Buf.Buf},
        Buf.InputReach Buf.Buf.empty Buf.bufEnqueue Buf.bufAdvance cap b → Buf.owedLen b ≤ cap := by
  sorry

theorem reachableOut_bound {cap : Nat} {b : Buf.Buf}
    (h : Buf.OutputReach Buf.Buf.empty Buf.bufEnqueue Buf.bufAdvance cap b) :
    Buf.owedLen b ≤ cap := by sorry

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

theorem captureBytes_bounded_rejects_unbounded :
    ¬∀ (contents : String),
        ((fun (_ : String) => List.replicate (2 * Import.Resurrect.captureLimit + 1) (0 : UInt8))
              contents).length ≤
          2 * Import.Resurrect.captureLimit := by
  sorry

theorem ending_clean (gone : UInt32 → Nat → Nat → Bool) (ends : Signal.Ends gone)
    (alive : List Nat) :
    (Session.ending.head?.map (·.1)) = some 1 ∧
      Session.ending.foldl
          (fun still (signal : UInt32 × Nat) => still.filter (!gone signal.1 signal.2 ·)) alive =
        [] := by
  sorry

theorem ending_clean_rejects_hangup :
    ¬∀ (gone : UInt32 → Nat → Nat → Bool),
        Signal.Ends gone →
          ∀ (alive : List Nat),
            (([(1, 1000)] : List (UInt32 × Nat)).head?.map (·.1)) = some 1 ∧
              ([(1, 1000)] : List (UInt32 × Nat)).foldl
                  (fun still (signal : UInt32 × Nat) => still.filter (!gone signal.1 signal.2 ·))
                  alive =
                [] := by
  sorry

/-! ## 7. Recovery

The terminal package's claims cover every terminal the checkpoint decoder returns
(`Checkpoint.live_of_decoded`), so any bytes on disk resume a session those claims cover, or are
refused, and a command never takes bytes that do not decode for no checkpoint: it starts
nothing over them and leaves them as they are, for `kill` to discard (`recovery_exact`). A crash
costs at most the changes of the last interval. A session asks for a save within
`ckptIntervalMs` of every change no save holds, by the clock its ticks give it (`unsaved_due`);
its daemon saves off its loop and replaces the checkpoint whole and durably, so that after a
crash the file at the path is the last save whose flushes returned, or the one then running,
whole (`Disk.Durable`, which the resume suite exercises by killing a daemon while it saves); and
resuming then gives back that save, never a fresh session (`crash_resumes`). Not claimed: a
bound in bytes or rows on what a crash loses, since the bound is in time, the interval and the
saves then running, whatever the program wrote in it, and a bound in rows waits for an
append-only store of the history; and that power loss keeps what the flushes returned for, which
rests on `Disk.Durable` and which no suite exercises. -/

theorem loadBytes_saveBytes_live (c : Checkpoint.Ckpt Vt.Vt)
    (h :
      Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
        (Checkpoint.Decoded Checkpoint.loadBytes) c.vt) :
    Checkpoint.loadBytes (Checkpoint.saveBytes c) = some { c with vt := c.vt.quiesce } := by sorry

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
    let saved := Checkpoint.loadBytes (Checkpoint.saveBytes c)
    let booted := State.boot (bootVt (saved.map (·.vt))) ((saved.map (·.labels)).getD []) metaKv
    booted.terminal = c.vt.quiesce ∧ booted.labelList = c.labels.take maxLabels := by
  sorry

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

theorem loadBytes_resave {b : ByteArray} {c : Checkpoint.Ckpt Vt.Vt}
    (h : Checkpoint.loadBytes b = some c) :
    Checkpoint.loadBytes (Checkpoint.saveBytes c) = some c := by sorry

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

theorem unsaved_due (vt : Vt.Vt) (labels metaKv : List (String × String)) (pre post : List Event)
    (ev : Event) :
    let s := (Session.trace Session.step (State.boot vt labels metaKv) pre).1
    let after := Session.trace Session.step s (ev :: post)
    (Session.step s ev).1.terminal ≠ s.terminal ∨ (Session.step s ev).1.labelList ≠ s.labelList →
      Effect.checkpoint ∉ after.2 →
      ∃ due,
        due ≤ Session.clock pre + ckptIntervalMs ∧
          (∃ wake, after.1.nextTick = some wake ∧ wake ≤ due) ∧
          ∀ now, due ≤ now → Effect.checkpoint ∈ (Session.step after.1 (.tick now)).2 := by
  sorry

theorem unsaved_due_rejects_never :
    ¬∀ (vt : Vt.Vt) (labels metaKv : List (String × String)) (pre post : List Event) (ev : Event),
        let s := (Session.trace Session.step (State.boot vt labels metaKv) pre).1
        let after := Session.trace Session.step s (ev :: post)
        (Session.step s ev).1.terminal ≠ s.terminal ∨
            (Session.step s ev).1.labelList ≠ s.labelList →
          Effect.checkpoint ∉ after.2 →
          ∃ due,
            due ≤ Session.clock pre + ckptIntervalMs ∧
              (∃ wake, (fun (_ : State) => (none : Option Nat)) after.1 = some wake ∧ wake ≤ due) ∧
              ∀ now, due ≤ now → Effect.checkpoint ∈ (Session.step after.1 (.tick now)).2 := by
  sorry

theorem checkpoint_metadata (pane : Import.Resurrect.Pane) (contents : Option String) :
    (Import.Resurrect.checkpoint pane contents).cwd = pane.dir ∧
      (Import.Resurrect.checkpoint pane contents).labels.lookup "tmux.command" =
        some pane.details.command ∧
      (Import.Resurrect.checkpoint pane contents).labels.lookup "tmux.saved-command" =
        some pane.details.savedCommand ∧
      (Import.Resurrect.checkpoint pane contents).labels.lookup "tmux.capture" =
        some (if contents.isSome then "saved" else "none") := by
  sorry

theorem checkpoint_metadata_rejects_blank :
    ¬∀ (pane : Import.Resurrect.Pane) (contents : Option String),
        ((fun (_ : Import.Resurrect.Pane) (_ : Option String) =>
                  (⟨Vt.Vt.init 1 1, "", []⟩ : Checkpoint.Ckpt Vt.Vt))
                pane contents).cwd =
            pane.dir ∧
          ((fun (_ : Import.Resurrect.Pane) (_ : Option String) =>
                    (⟨Vt.Vt.init 1 1, "", []⟩ : Checkpoint.Ckpt Vt.Vt))
                  pane contents).labels.lookup
              "tmux.command" =
            some pane.details.command ∧
          ((fun (_ : Import.Resurrect.Pane) (_ : Option String) =>
                    (⟨Vt.Vt.init 1 1, "", []⟩ : Checkpoint.Ckpt Vt.Vt))
                  pane contents).labels.lookup
              "tmux.saved-command" =
            some pane.details.savedCommand ∧
          ((fun (_ : Import.Resurrect.Pane) (_ : Option String) =>
                    (⟨Vt.Vt.init 1 1, "", []⟩ : Checkpoint.Ckpt Vt.Vt))
                  pane contents).labels.lookup
              "tmux.capture" =
            some (if contents.isSome then "saved" else "none") := by
  sorry

/-! ## 8. Clean terminal

What linger writes to a terminal on its own account is clean (`Display.Clean`): printable text,
line breaks, tabs and a short list of control sequences, none of which asks the terminal for a
reply, resets it or erases its scrollback. A gate lists every write to standard output in the
program with whose bytes it writes: a printer `writes_clean` names, or the session's own bytes,
its output and the repaint of its screen, which the terminal package's headlines describe. Not
claimed: what linger prints as lines of text (help, version, `ls --summary`, porcelain records)
and its messages on standard error. -/

theorem infoText_text (s : State) :
    ∃ cs : List Char,
      Session.infoText s = cs.flatMap String.utf8EncodeChar ∧
        ∀ c ∈ cs,
          c = '\t' ∨
            c = '\n' ∨ (0x20 ≤ c.toNat ∧ c.toNat ≠ 0x7F ∧ ¬(0x80 ≤ c.toNat ∧ c.toNat < 0xA0)) := by
  sorry

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
    (∀ withColor rows, Display.Clean (Display.Listing.terminalListing withColor rows)) ∧
      (∀ state snapshot statusOf loaded withColor savedTmux cols rows,
        Display.Clean
          (Selector.Picker.frame state snapshot statusOf loaded withColor savedTmux cols rows)) ∧
      Display.Clean Selector.Picker.enterAnsi ∧
      Display.Clean Selector.Picker.exitAnsi ∧
      (∀ title, Display.Clean (Terminal.Title.ansi title)) ∧
      (∀ v title, Display.Clean (Terminal.Title.update v title)) ∧
      (∀ v, Display.Clean (Terminal.Render.screenText v)) ∧
      (∀ v, Display.Clean (Terminal.Render.history v)) ∧
      (∀ s, Display.Clean (Session.infoText s)) ∧ Display.Clean Terminal.Render.leaveAnsi := by
  sorry

theorem writes_clean_rejects_reset :
    ¬((∀ withColor rows,
          Display.Clean
            ((fun (_ : Bool) (_ : List (List (String × String))) => ([0x1B, 0x63] : List UInt8))
              withColor rows)) ∧
        (∀ state snapshot statusOf loaded withColor savedTmux cols rows,
          Display.Clean
            (Selector.Picker.frame state snapshot statusOf loaded withColor savedTmux cols rows)) ∧
        Display.Clean Selector.Picker.enterAnsi ∧
        Display.Clean Selector.Picker.exitAnsi ∧
        (∀ title, Display.Clean (Terminal.Title.ansi title)) ∧
        (∀ v title, Display.Clean (Terminal.Title.update v title)) ∧
        (∀ v, Display.Clean (Terminal.Render.screenText v)) ∧
        (∀ v, Display.Clean (Terminal.Render.history v)) ∧
        (∀ s, Display.Clean (Session.infoText s)) ∧ Display.Clean Terminal.Render.leaveAnsi) := by
  sorry

/-! ## 9. Work follows events

A daemon's state holds its own session alone, so no event's work depends on how many sessions
exist. Program output costs work only for the clients attached to its session
(`step_output_delivered`, in part 1), and a daemon's
poll that no event or signal ends returns no sooner than the earliest deadline the daemon holds,
and never when it holds none (`poll_wakes`), when poll(2) waits out its timeout (`Poll.Sleeps`,
which the quiet suite exercises by timing quiet polls; it also counts the wakeups of idle
sessions). `scripts/gates.sh` lists every timer the program sets, with its bound. Not claimed:
how much later than its deadline a loaded host lets a daemon wake. Not claimed yet: that an
event's work follows its size. -/

theorem ticks_settle (s : State) (now t₁ t₂ : Nat)
    (h₁ : (Session.trace Session.step s [.tick now]).1.nextTick = some t₁)
    (h₂ : (Session.trace Session.step s [.tick now, .tick t₁]).1.nextTick = some t₂) :
    (Session.trace Session.step s [.tick now, .tick t₁, .tick t₂]).1.nextTick = none := by sorry

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

theorem poll_wakes_rejects_polling :
    ¬∀ (quiet : Int32 → Nat → Prop),
        Poll.Sleeps quiet →
          ∀ (now : Nat) (deadlines : List Nat),
            (∀ d ∈ deadlines, d - now ≤ 2147483647) →
              ∀ (ms : Nat),
                quiet ((fun (_ : Nat) (_ : List Nat) => (100 : Int32)) now deadlines) ms →
                  ∃ due, deadlines.min? = some due ∧ due - now ≤ ms := by
  sorry

/-! ## 10. Graceful under load

A command waits for its daemon's answer a bounded time, and what it answers when that time runs
out is still true. A daemon saves its checkpoint and writes its end record, their flushes
included, off its loop, on a thread of its own (`scripts/gates.sh`), so a slow disk holds up no
answer and no output, and the writes it asks for while one runs coalesce into the last. Every wait sleeps as `Os.Wait.next`
decides (`scripts/gates.sh`), so it gives up once its deadline has passed, which the os package
claims (`packages/os`), and then reports what
it missed: `start` that its daemon did not answer, `ls` a remote host as `?`, `wait --timeout`
124. Not claimed: the waits with no deadline, each on something that ends without waiting
itself, or on purpose: `wait` without `--timeout`, an idle daemon's poll, `start` or `resume`
once their daemon took the request's ticket, and a daemon's last disk write, which it reports
after a second. How long a wait takes under load the robust, resume and status suites measure. -/

theorem start_answer_true (r : Start.Request) (h : Start.Reachable Start.proceeds Start.answer r) :
    (r.answer = some .started → r.runs = true) ∧
      (r.answer = some .notStarted → r.runs = false) := by
  sorry

theorem start_answer_true_rejects_started :
    ¬∀ (r : Start.Request),
        Start.Reachable Start.proceeds (fun _ _ => Start.Answer.started) r →
          (r.answer = some .started → r.runs = true) ∧
            (r.answer = some .notStarted → r.runs = false) := by
  sorry

theorem start_answer_true_rejects_proceed :
    ¬∀ (r : Start.Request),
        Start.Reachable (fun _ => true) Start.answer r →
          (r.answer = some .started → r.runs = true) ∧
            (r.answer = some .notStarted → r.runs = false) := by
  sorry

theorem offloop_coalesces {R W : Type} (start : W → R) (ws : List W) :
    (ws.foldl (Offloop.run Offloop.ask start) {}).running = ws.head?.map start ∧
      (ws.foldl (Offloop.run Offloop.ask start) {}).waiting =
        if ws.length ≤ 1 then none else ws.getLast? := by
  sorry

theorem offloop_coalesces_rejects_eager :
    ¬∀ {R W : Type} (start : W → R) (ws : List W),
        (ws.foldl (Offloop.run (fun (o : Offloop R W) (w : W) => (o, some w)) start) {}).running =
            ws.head?.map start ∧
          (ws.foldl (Offloop.run (fun (o : Offloop R W) (w : W) => (o, some w)) start) {}).waiting =
            if ws.length ≤ 1 then none else ws.getLast? := by
  sorry

/-! ## The status rule

And the titles, listings and selector views that show statuses. -/

theorem classify_iff (o : Status.Obs) (s : Status.Status) :
    Status.classify o = s ↔ Status.Is s o := by sorry

theorem classify_iff_rejects_idle :
    ¬∀ (o : Status.Obs) (s : Status.Status),
        (fun (_ : Status.Obs) => Status.Status.idle) o = s ↔ Status.Is s o := by
  sorry

theorem icon_glyphs :
    Status.icon .working = '⣷' ∧
      Status.icon .wantsYou = '⣿' ∧
      Status.icon .idle = '⣀' ∧
      Status.icon .exitedOk = '✓' ∧
      Status.icon .exitedBad = '!' ∧ Status.icon .resumable = '~' ∧ Status.icon .unknown = '?' := by
  sorry

theorem icon_glyphs_rejects_unknown :
    ¬((fun (_ : Status.Status) => '?') .working = '⣷' ∧
        (fun (_ : Status.Status) => '?') .wantsYou = '⣿' ∧
        (fun (_ : Status.Status) => '?') .idle = '⣀' ∧
        (fun (_ : Status.Status) => '?') .exitedOk = '✓' ∧
        (fun (_ : Status.Status) => '?') .exitedBad = '!' ∧
        (fun (_ : Status.Status) => '?') .resumable = '~' ∧
        (fun (_ : Status.Status) => '?') .unknown = '?') := by
  sorry

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

theorem rowStatus_saved (status : Nat) (st : Status.Status) :
    Listing.rowStatus (.ended status) = (if status = 0 then .exitedOk else .exitedBad) ∧
      Listing.rowStatus (.remote false (Status.name st)) =
        if st = .exitedOk ∨ st = .exitedBad then st else .resumable := by
  sorry

theorem rowStatus_saved_rejects_unknown :
    ¬∀ (status : Nat) (st : Status.Status),
        (fun (_ : Listing.Row) => Status.Status.unknown) (.ended status) =
            (if status = 0 then .exitedOk else .exitedBad) ∧
          (fun (_ : Listing.Row) => Status.Status.unknown) (.remote false (Status.name st)) =
            if st = .exitedOk ∨ st = .exitedBad then st else .resumable := by
  sorry

theorem compose_attention_last (session application summary : String) (capacity : Nat) :
    Title.compose session application summary capacity =
      Title.compose session application ""
          (capacity - (if summary.isEmpty then "" else " · " ++ summary).length) ++
        (if summary.isEmpty then "" else " · " ++ summary) := by
  sorry

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

theorem sort_attention_first {α : Type} (status : α → Status.Status) (rows : List α) :
    (View.sort status rows).Perm rows ∧
      ∃ first rest,
        View.sort status rows = first ++ rest ∧
          (∀ x ∈ first, status x = .wantsYou ∨ status x = .exitedBad ∨ status x = .unknown) ∧
          ∀ x ∈ rest, ¬(status x = .wantsYou ∨ status x = .exitedBad ∨ status x = .unknown) := by
  sorry

theorem sort_attention_first_rejects_arrival :
    ¬∀ {α : Type} (status : α → Status.Status) (rows : List α),
        ((fun (_ : α → Status.Status) (rows : List α) => rows) status rows).Perm rows ∧
          ∃ first rest,
            (fun (_ : α → Status.Status) (rows : List α) => rows) status rows = first ++ rest ∧
              (∀ x ∈ first, status x = .wantsYou ∨ status x = .exitedBad ∨ status x = .unknown) ∧
              ∀ x ∈ rest,
                ¬(status x = .wantsYou ∨ status x = .exitedBad ∨ status x = .unknown) := by
  sorry

theorem groups_exact (keys : List String) :
    ((View.groups keys).map (·.2)).sum = keys.length ∧
      ∀ (k : String) (n : Nat), (k, n) ∈ View.groups keys → n = keys.count k := by
  sorry

theorem groups_exact_rejects_fixed :
    ¬∀ (keys : List String),
        (((fun (_ : List String) => [("", 1)]) keys).map (·.2)).sum = keys.length ∧
          ∀ (k : String) (n : Nat),
            (k, n) ∈ (fun (_ : List String) => [("", 1)]) keys → n = keys.count k := by
  sorry

theorem hidden_adds_up (targets : List String) :
    (View.hidden targets).2 = [] ∨
      ((View.hidden targets).2.map (·.2)).sum = (View.hidden targets).1 := by
  sorry

theorem hidden_adds_up_rejects_short :
    ¬∀ (targets : List String),
        ((fun (_ : List String) => (1, [("a", 0)])) targets).2 = [] ∨
          (((fun (_ : List String) => (1, [("a", 0)])) targets).2.map (·.2)).sum =
            ((fun (_ : List String) => (1, [("a", 0)])) targets).1 := by
  sorry

theorem matchCount_push (s typed : Selector.Picker.State) (c : Char)
    (push : typed = { s with query := s.query.push c }) :
    Selector.Picker.matchCount typed ≤ Selector.Picker.matchCount s := by sorry

theorem matchCount_push_rejects_length :
    ¬∀ (s typed : Selector.Picker.State) (c : Char),
        typed = { s with query := s.query.push c } →
          (fun (s : Selector.Picker.State) => s.query.length) typed ≤
            (fun (s : Selector.Picker.State) => s.query.length) s := by
  sorry

end Linger
