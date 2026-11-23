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

public section

open Linger.App Linger.Display Linger.Session Linger.Target Terminal

def Linger.App.Entry.route : List String → App.Entry.Route := sorry

def Linger.App.Commands.table : List App.Commands.Command := sorry

def Linger.App.Commands.lookup : String → Option App.Commands.Command := sorry

def Linger.App.Commands.helpLine : App.Commands.Command → String := sorry

def Linger.App.Commands.helpLines : List String := sorry

def Linger.App.Api.parse : List String → Option App.Api.Request := sorry

def Linger.App.Api.plan : App.Api.Request → App.Api.Act := sorry

def Linger.App.Api.answer : App.Api.Found → Os.Answer := sorry

def Linger.App.Api.Said.render : App.Api.Said → String := sorry

def Linger.App.Fields.table : List App.Fields.Field := sorry

def Linger.Os.Answer.code : Os.Answer → UInt32 := sorry

def Linger.App.Wait.heldNameMs : Nat := sorry

def Linger.App.Wait.decide : Option Nat → Option Nat → Nat → App.Wait.Heard → App.Wait.Next := sorry

def Linger.App.Kill.decide : Nat → Nat → App.Kill.Heard → App.Kill.Next := sorry

def Linger.App.Recovery.decide : Bool → Option ByteArray → App.Recovery (Checkpoint.Ckpt Vt.Vt) :=
  sorry

def Linger.App.Recovery.visit : Bool → Option (List UInt8) → List App.Visit.Step := sorry

def Linger.App.Capture.plan : List App.Capture.Step := sorry

def Linger.App.Capture.phases : List App.Capture.Step → List App.Capture.Phase := sorry

def Linger.App.Handover.plan : Session.Mode → Nat → List (String × String) → App.Handover.Plan :=
  sorry

def Linger.App.Serve.parse : String → Serve.Json → Option (App.Api.Request × List UInt8) := sorry

def Linger.App.Serve.result : App.Api.Found → List (String × Serve.Json) → Serve.Json := sorry

def Linger.App.Serve.records : List (List (String × String)) → List (List (String × String)) :=
  sorry

def Linger.App.Serve.State : Type := sorry

def Linger.App.Serve.State.init : App.Serve.State := sorry

def Linger.App.Serve.State.phase : App.Serve.State → Serve.Phase := sorry

def Linger.App.Serve.step :
    App.Serve.State → Serve.Event → App.Serve.State × List Serve.Effect := sorry

def Linger.App.Serve.State.subscription : App.Serve.State → Option Serve.Id := sorry

def Linger.App.Serve.State.told : App.Serve.State → Option (List Serve.Record) := sorry

def Linger.App.Serve.State.latest : App.Serve.State → Option (List Serve.Record) := sorry

def Linger.App.Serve.Log.push {α : Type} : Nat → Serve.Log α → α → Serve.Log α := sorry

def Linger.App.Serve.State.watching : App.Serve.State → Serve.Id → Option Serve.Watch := sorry

def Linger.App.Serve.Line.of : Vt.Row → Serve.Line := sorry

def Linger.App.Serve.Screen.render : Vt.Vt → Serve.Screen := sorry

def Linger.App.Serve.Screen.changes : Serve.Screen → Serve.Screen → Serve.Screen.Update := sorry

def Linger.App.Serve.Remote.heard : List Serve.Json → UInt32 → Serve.Remote.Heard := sorry

def Linger.App.Serve.Remote.rows : String → List Serve.Record → List Serve.Record := sorry

def Linger.App.Serve.Remote.call :
    App.Api.Request → String → List UInt8 → Option (String × Serve.Json) := sorry

def Linger.App.Serve.Remote.relay : Serve.Id → Serve.Json → List Wire.Msg := sorry

def Linger.App.Serve.Remote.keys : Serve.Id → List UInt8 → Serve.Json := sorry

def Linger.App.Serve.Remote.found : Os.Answer → List (String × Serve.Json) → App.Api.Found := sorry

def Linger.App.Serve.Remote.said : String → List (String × Serve.Json) → List String := sorry

def Linger.Target.Name.check : String → Option String := sorry

def Linger.Target.Name.accept : String → Option String := sorry

def Linger.Target.Remote.targetArgs : List String → Option (String × List String) := sorry

def Linger.Target.Remote.argv : Remote.Transport → List String := sorry

def Linger.Target.Remote.scrub : String → String := sorry

def Linger.Target.Remote.checkHosts : List String → Except String (List String) := sorry

def Linger.Target.Remote.targetValid : String → Bool := sorry

def Linger.Os.Env.shellOf : Option String → String := sorry

def Linger.Os.Env.remotesFile : Option String → Option String := sorry

def Linger.Os.Env.detachEnabled : Bool → Option String → Bool := sorry

def Linger.Os.Env.resumeDir : Option String → String → Bool → Option String := sorry

def Linger.Os.Env.withColor : Bool → Option String → Option String → Bool := sorry

def Linger.Display.Status.classify : Status.Obs → Status.Status := sorry

def Linger.Display.Status.mark : Status.Attention → Char := sorry

def Linger.Display.Status.icon : Status.State → Char := sorry

def Linger.Display.Status.legend : List String := sorry

def Linger.Display.Status.summary : List Status.Attention → String := sorry

def Linger.Display.Status.attentionName : Status.Attention → String := sorry

def Linger.Display.Status.ofAttentionName : String → Status.Attention := sorry

def Linger.Display.Status.name : Status.State → String := sorry

def Linger.Display.Status.ofName : String → Status.State := sorry

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

def Linger.Display.Listing.porcelain : List (List (String × String)) → String := sorry

def Linger.Display.View.sort {α : Type} : (α → Status.Status) → List α → List α := sorry

def Linger.Display.View.before : String → String → Bool := sorry

def Linger.Display.View.hidden : List String → Nat × List (String × Nat) := sorry

def Linger.Display.Title.compose : String → String → String → Nat → String := sorry

def Linger.Display.Alert.announce :
    Option (List (String × Status.Attention)) →
      List (String × Status.Attention) → String → List String := sorry

def Linger.Display.Alert.notification : String → String → List UInt8 := sorry

def Linger.Session.State : Type := sorry

def Linger.Session.State.boot : Vt.Vt → List (String × String) → List (String × String) → State :=
  sorry

def Linger.Session.Claim.enters : Bool → Bool → Bool := sorry

def Linger.Session.Locks.release : Session.Records → String → Session.Records := sorry

def Linger.Session.Names.entryFile : String → String := sorry

def Linger.Session.Names.entryName : String → Option String := sorry

def Linger.Session.ending : List Linger.Session.Stop.Send := sorry

def Linger.Session.drainTimeoutMs : Nat := sorry

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

def Linger.Selector.Picker.parseSnapshot : String → Except String Selector.Picker.Snapshot := sorry

def Linger.Selector.Picker.Snapshot.row :
    Selector.Picker.Snapshot → String → List (String × String) := sorry

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
              (Mediation.feed s.terminal s.scanner chunk).progress
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
      ((Status.classify
              { progress := s.seen.progress, running := s.seen.running, unseen := s.seen.unseen,
                asks := s.seen.asks }).attention =
          .asked ↔
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
                  (Mediation.feed s.terminal s.scanner chunk).progress
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
          ((Status.classify
                  { progress := s.seen.progress, running := s.seen.running, unseen := s.seen.unseen,
                    asks := s.seen.asks }).attention =
              .asked ↔
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
                  (Mediation.feed s.terminal s.scanner chunk).progress
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
          ((Status.lumped Status.classify
                  { progress := s.seen.progress, running := s.seen.running, unseen := s.seen.unseen,
                    asks := s.seen.asks }).attention =
              .asked ↔
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
    (Status.mark (Status.ofAttentionName ((info.lookup "attention").getD "")) ::
          ' ' ::
          Status.icon (Status.ofName ((info.lookup "status").getD "")) ::
          ' ' :: ((info.lookup "name").getD "").toList.map Terminal.Render.textChar <+:
        Listing.rowText width layout info) ∧
      ∀ w,
        width = some w →
          ((Listing.rowText width layout info).map Terminal.Vt.charWidth).sum ≤
            max w (4 + (((info.lookup "name").getD "").toList.map Terminal.Vt.charWidth).sum) := by
  sorry

@[kills rowText_fits]
theorem rowText_fits_rejects_overflow :
    ¬∀ (width : Option Nat) (layout : Listing.Layout) (info : List (String × String)),
        (Status.mark (Status.ofAttentionName ((info.lookup "attention").getD "")) ::
              ' ' ::
              Status.icon (Status.ofName ((info.lookup "status").getD "")) ::
              ' ' :: ((info.lookup "name").getD "").toList.map Terminal.Render.textChar <+:
            (fun (_ : Option Nat) (_ : Listing.Layout) (info : List (String × String)) =>
                Status.mark (Status.ofAttentionName ((info.lookup "attention").getD "")) ::
                  ' ' ::
                  Status.icon (Status.ofName ((info.lookup "status").getD "")) ::
                  ' ' ::
                  (((info.lookup "name").getD "").toList.map Terminal.Render.textChar ++
                    ['…', '…', '…']))
              width layout info) ∧
          ∀ w,
            width = some w →
              (((fun (_ : Option Nat) (_ : Listing.Layout) (info : List (String × String)) =>
                          Status.mark
                              (Status.ofAttentionName ((info.lookup "attention").getD "")) ::
                            ' ' ::
                            Status.icon (Status.ofName ((info.lookup "status").getD "")) ::
                            ' ' ::
                            (((info.lookup "name").getD "").toList.map Terminal.Render.textChar ++
                              ['…', '…', '…']))
                        width layout info).map
                    Terminal.Vt.charWidth).sum ≤
                max w
                  (4 + (((info.lookup "name").getD "").toList.map Terminal.Vt.charWidth).sum) := by
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

theorem picker_moves_cycle (s : Selector.Picker.State) (n k : Nat)
    (rows : ∀ i, (∃ next, Selector.Picker.step { s with cursor := i } .accept = .stay next) ↔ n ≤ i)
    (row : s.cursor < n ∨ n = 0) :
    Selector.Picker.press Selector.Picker.step s (List.replicate k .down) =
        .stay (if n = 0 then s else { s with cursor := (s.cursor + k) % n }) ∧
      Selector.Picker.press Selector.Picker.step s (List.replicate k .up) =
        .stay (if n = 0 then s else { s with cursor := ((s.cursor - k : Int) % n).toNat }) := by
  sorry

@[kills picker_moves_cycle]
theorem picker_moves_cycle_rejects_clamped :
    ¬∀ (s : Selector.Picker.State) (n k : Nat),
        (∀ i,
            (∃ next,
                Selector.Picker.clamped Selector.Picker.step { s with cursor := i } .accept =
                  .stay next) ↔
              n ≤ i) →
          s.cursor < n ∨ n = 0 →
          Selector.Picker.press (Selector.Picker.clamped Selector.Picker.step) s
                (List.replicate k .down) =
              .stay (if n = 0 then s else { s with cursor := (s.cursor + k) % n }) ∧
            Selector.Picker.press (Selector.Picker.clamped Selector.Picker.step) s
                (List.replicate k .up) =
              .stay
                (if n = 0 then s else { s with cursor := ((s.cursor - k : Int) % n).toNat }) := by
  sorry

theorem route_exact (args : List String) : App.Entry.route args = App.Entry.Route.of args := by
  sorry

@[kills route_exact]
theorem route_exact_rejects_selector :
    ¬∀ (args : List String),
        (fun (args : List String) => App.Entry.Route.session args) args =
          App.Entry.Route.of args := by
  sorry

theorem op_meaning (args argv : List String) (request : Api.Request) (found : Api.Found) :
    App.Entry.route args = .session argv →
      App.Api.parse argv = some request →
      (App.Commands.lookup (argv.headD "")).map (·.op) = some request.op ∧
        App.Api.plan request = request.act ∧
        (request.op.finds found = true → App.Api.answer found = found.answer) := by
  sorry

@[kills op_meaning]
theorem op_meaning_rejects_crossed :
    ¬∀ (args argv : List String) (request : Api.Request) (found : Api.Found),
        App.Entry.route args = .session argv →
          App.Api.parse argv = some request →
          (App.Commands.lookup (argv.headD "")).map (·.op) = some request.op ∧
            Api.Request.crossed request = request.act ∧
            (request.op.finds found = true → App.Api.answer found = found.answer) := by
  sorry

@[kills op_meaning]
theorem op_meaning_rejects_outside :
    ¬∀ (args argv : List String) (request : Api.Request) (found : Api.Found),
        App.Entry.route args = .session argv →
          App.Api.parse argv = some request →
          (App.Commands.lookup (argv.headD "")).map (·.op) = some request.op ∧
            App.Api.plan request = request.act ∧
            (request.op.finds found = true →
              (fun (_ : Api.Found) => Os.Answer.timedOut) found = found.answer) := by
  sorry

theorem said_rendered (said : Api.Said) :
    App.Api.Said.render said =
      (if said.fresh then "\r\n" else "") ++ "linger: " ++ said.text ++ "\n" := by
  sorry

@[kills said_rendered]
theorem said_rendered_rejects_bare :
    ¬∀ (said : Api.Said),
        (fun (said : Api.Said) => said.text ++ "\n") said =
          (if said.fresh then "\r\n" else "") ++ "linger: " ++ said.text ++ "\n" := by
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

theorem serve_renders_api (method : String) (params : Serve.Json) (found : Api.Found)
    (members : List (String × Serve.Json)) :
    App.Serve.parse method params =
        (Serve.words method params).bind
          (fun argv =>
            (App.Api.parse argv).bind fun request =>
              (Serve.input method params).map fun bytes => (request, bytes)) ∧
      (∀ request bytes,
        App.Serve.parse method params = some (request, bytes) →
          (Serve.methods.lookup method).map (·.1) = some request.op) ∧
      App.Serve.result found members =
        .obj
          (("answer", .str (Serve.answerName (App.Api.answer found))) ::
            ("code", .number (toString (App.Api.answer found).code)) :: members) := by
  sorry

@[kills serve_renders_api]
theorem serve_renders_api_rejects_crossed :
    ¬∀ (method : String) (params : Serve.Json) (found : Api.Found)
        (members : List (String × Serve.Json)),
        (fun (method : String) (params : Serve.Json) =>
                App.Serve.parse (if method = "session/detach" then "session/kill" else method)
                  params)
              method params =
            (Serve.words method params).bind
              (fun argv =>
                (App.Api.parse argv).bind fun request =>
                  (Serve.input method params).map fun bytes => (request, bytes)) ∧
          (∀ request bytes,
            (fun (method : String) (params : Serve.Json) =>
                    App.Serve.parse (if method = "session/detach" then "session/kill" else method)
                      params)
                  method params =
                some (request, bytes) →
              (Serve.methods.lookup method).map (·.1) = some request.op) ∧
          App.Serve.result found members =
            .obj
              (("answer", .str (Serve.answerName (App.Api.answer found))) ::
                ("code", .number (toString (App.Api.answer found).code)) :: members) := by
  sorry

@[kills serve_renders_api]
theorem serve_renders_api_rejects_outside :
    ¬∀ (method : String) (params : Serve.Json) (found : Api.Found)
        (members : List (String × Serve.Json)),
        App.Serve.parse method params =
            (Serve.words method params).bind
              (fun argv =>
                (App.Api.parse argv).bind fun request =>
                  (Serve.input method params).map fun bytes => (request, bytes)) ∧
          (∀ request bytes,
            App.Serve.parse method params = some (request, bytes) →
              (Serve.methods.lookup method).map (·.1) = some request.op) ∧
          (fun (_ : Api.Found) (members : List (String × Serve.Json)) =>
                Serve.Json.obj (("answer", .str "done") :: ("code", .number "0") :: members))
              found members =
            .obj
              (("answer", .str (Serve.answerName (App.Api.answer found))) ::
                ("code", .number (toString (App.Api.answer found).code)) :: members) := by
  sorry

theorem chooser_same_list (rows : List (List (String × String)))
    (named :
      ∀ record ∈ App.Serve.records rows,
        ∃ rest,
          record = ("name", Serve.Record.key record) :: rest ∧
            Remote.targetValid (Serve.Record.key record) = true ∧ ∀ field ∈ rest, field.1 ≠ "name")
    (distinct : ((App.Serve.records rows).map Serve.Record.key).Nodup) :
    ∃ snapshot,
      Selector.Picker.parseSnapshot (Listing.porcelain rows) = .ok snapshot ∧
        snapshot.candidates = (App.Serve.records rows).map Serve.Record.key ∧
        ∀ record ∈ App.Serve.records rows,
          Selector.Picker.Snapshot.row snapshot (Serve.Record.key record) = record := by
  sorry

@[kills chooser_same_list]
theorem chooser_same_list_rejects_own :
    ¬∀ (rows : List (List (String × String))),
        (∀ record ∈ App.Serve.records rows,
            ∃ rest,
              record = ("name", Serve.Record.key record) :: rest ∧
                Remote.targetValid (Serve.Record.key record) = true ∧
                ∀ field ∈ rest, field.1 ≠ "name") →
          ((App.Serve.records rows).map Serve.Record.key).Nodup →
          ∃ snapshot,
            Selector.Picker.ownList (Listing.porcelain rows) = .ok snapshot ∧
              snapshot.candidates = (App.Serve.records rows).map Serve.Record.key ∧
              ∀ record ∈ App.Serve.records rows,
                Selector.Picker.Snapshot.row snapshot (Serve.Record.key record) = record := by
  sorry

theorem serve_negotiated (s : App.Serve.State) (ev : Serve.Event) :
    Serve.Negotiated App.Serve.State.init App.Serve.State.phase App.Serve.State.subscription
      App.Serve.State.watching App.Serve.step s ev := by
  sorry

@[kills serve_negotiated]
theorem serve_negotiated_rejects_eager :
    ¬∀ (s : App.Serve.State) (ev : Serve.Event),
        Serve.Negotiated App.Serve.State.init App.Serve.State.phase App.Serve.State.subscription
          App.Serve.State.watching (Serve.eager App.Serve.step) s ev := by
  sorry

@[kills serve_negotiated]
theorem serve_negotiated_rejects_chatty :
    ¬∀ (s : App.Serve.State) (ev : Serve.Event),
        Serve.Negotiated App.Serve.State.init App.Serve.State.phase App.Serve.State.subscription
          App.Serve.State.watching (Serve.chatty App.Serve.step) s ev := by
  sorry

theorem one_renderer (v : Vt.Vt) (row : Vt.Row)
    (hv : Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable v) :
    ((App.Serve.Screen.render v).lines.map fun line => line.text ++ [0x0A]).flatten =
        Render.screenText v ∧
      (App.Serve.Screen.render v).lines =
        (List.range v.rowCount).map (fun y => App.Serve.Line.of (v.getRow y)) ∧
      (App.Serve.Line.of row).text = Render.rowText row ∧
      Serve.Span.expand (App.Serve.Line.of row).spans = Serve.Line.pens row ∧
      Serve.Span.Compact (App.Serve.Line.of row).spans ∧
      (App.Serve.Screen.render v).cursor =
        { x := v.cursorPos.1, y := v.cursorPos.2, visible := v.getModes.cursorVisible } ∧
      (App.Serve.Screen.render v).title = v.windowTitle.map Render.textChar := by
  sorry

@[kills one_renderer]
theorem one_renderer_rejects_untrimmed :
    ¬∀ (v : Vt.Vt) (row : Vt.Row),
        Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable v →
          ((Serve.Screen.untrimmed (fun (v : Vt.Vt) => (List.range v.rowCount).map v.getRow)
                      v).lines.map
                  fun line => line.text ++ [0x0A]).flatten =
              Render.screenText v ∧
            (Serve.Screen.untrimmed (fun (v : Vt.Vt) => (List.range v.rowCount).map v.getRow)
                  v).lines =
              (List.range v.rowCount).map (fun y => App.Serve.Line.of (v.getRow y)) ∧
            (App.Serve.Line.of row).text = Render.rowText row ∧
            Serve.Span.expand (App.Serve.Line.of row).spans = Serve.Line.pens row ∧
            Serve.Span.Compact (App.Serve.Line.of row).spans ∧
            (Serve.Screen.untrimmed (fun (v : Vt.Vt) => (List.range v.rowCount).map v.getRow)
                  v).cursor =
              { x := v.cursorPos.1, y := v.cursorPos.2, visible := v.getModes.cursorVisible } ∧
            (Serve.Screen.untrimmed (fun (v : Vt.Vt) => (List.range v.rowCount).map v.getRow)
                  v).title =
              v.windowTitle.map Render.textChar := by
  sorry

theorem history_log_exact (s : App.Serve.State) (version : String) (id : Serve.Id)
    (pending left : Serve.Log Serve.Line) (screen : Serve.Screen)
    (ready : s.phase = .ready version) :
    Serve.HistoryLog App.Serve.State.watching App.Serve.step App.Serve.result s id pending screen
      left := by
  sorry

@[kills history_log_exact]
theorem history_log_exact_rejects_uncounted :
    ¬∀ (s : App.Serve.State) (version : String) (id : Serve.Id)
        (pending left : Serve.Log Serve.Line) (screen : Serve.Screen),
        s.phase = .ready version →
          Serve.HistoryLog App.Serve.State.watching (Serve.uncounted App.Serve.step)
            App.Serve.result s id pending screen left := by
  sorry

theorem serve_attach_exact (s : App.Serve.State) (version : String) (id : Serve.Id)
    (dec : Wire.Decoder) (pending bytes : List UInt8) (ready : s.phase = .ready version) :
    Serve.AttachStream App.Serve.State.watching App.Serve.step App.Serve.result Wire.Decoder.feed s
      id dec pending bytes := by
  sorry

@[kills serve_attach_exact]
theorem serve_attach_exact_rejects_unpainted :
    ¬∀ (s : App.Serve.State) (version : String) (id : Serve.Id) (dec : Wire.Decoder)
        (pending bytes : List UInt8),
        s.phase = .ready version →
          Serve.AttachStream App.Serve.State.watching
            (Serve.unpainted App.Serve.State.watching App.Serve.step) App.Serve.result
            Wire.Decoder.feed s id dec pending bytes := by
  sorry

theorem remote_rows_exact (host : String) (messages : List Serve.Json) (status : UInt32)
    (records : List Serve.Record) :
    Serve.Remote.Rows App.Serve.Remote.heard App.Serve.Remote.rows Name.accept Os.Answer.code host
      messages status records := by
  sorry

@[kills remote_rows_exact]
theorem remote_rows_exact_rejects_unshaken :
    ¬∀ (host : String) (messages : List Serve.Json) (status : UInt32) (records : List Serve.Record),
        Serve.Remote.Rows Serve.Remote.unshaken App.Serve.Remote.rows Name.accept Os.Answer.code
          host messages status records := by
  sorry

theorem remote_exact (request : Api.Request) (name : String) (input : List UInt8)
    (messages : List Serve.Json) (status : UInt32) (answer : Os.Answer)
    (members : List (String × Serve.Json)) (host : String) (t : Remote.Transport)
    (carry : List String → List UInt8 → Option (List UInt8))
    (delivers : Remote.Transport.Delivers carry t) (bytes : List UInt8) :
    Serve.Remote.Exact App.Serve.Remote.call App.Serve.parse App.Serve.Remote.heard Os.Answer.code
        App.Serve.Remote.found App.Api.answer App.Serve.Remote.said Remote.scrub request name input
        messages status answer members host ∧
      Remote.argv t = t.command ++ ["linger", "serve"] ∧
      (carry (Remote.argv t) bytes = none ∨ carry (Remote.argv t) bytes = some bytes) := by
  sorry

@[kills remote_exact]
theorem remote_exact_rejects_crossed :
    ¬∀ (request : Api.Request) (name : String) (input : List UInt8) (messages : List Serve.Json)
        (status : UInt32) (answer : Os.Answer) (members : List (String × Serve.Json))
        (host : String) (t : Remote.Transport)
        (carry : List String → List UInt8 → Option (List UInt8)),
        Remote.Transport.Delivers carry t →
          ∀ (bytes : List UInt8),
            Serve.Remote.Exact
                (fun (request : Api.Request) (name : String) (input : List UInt8) =>
                  App.Serve.Remote.call (if request.op = .detach then .kill name else request) name
                    input)
                App.Serve.parse App.Serve.Remote.heard Os.Answer.code App.Serve.Remote.found
                App.Api.answer App.Serve.Remote.said Remote.scrub request name input messages status
                answer members host ∧
              Remote.argv t = t.command ++ ["linger", "serve"] ∧
              (carry (Remote.argv t) bytes = none ∨ carry (Remote.argv t) bytes = some bytes) := by
  sorry

theorem remote_attach_exact (id : Serve.Id) (stream : List (Serve.Json × List UInt8))
    (typed : List UInt8) :
    Serve.Remote.Shows App.Serve.Remote.relay App.Serve.Remote.keys id stream typed := by sorry

@[kills remote_attach_exact]
theorem remote_attach_exact_rejects_undecoded :
    ¬∀ (id : Serve.Id) (stream : List (Serve.Json × List UInt8)) (typed : List UInt8),
        Serve.Remote.Shows Serve.Remote.undecoded App.Serve.Remote.keys id stream typed := by
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
      Wait.Next.told
          (Wait.decide deadline heldSince now
            (.recorded (Record.answer (afterSave (Record.encode Import.Resurrect.dismissal))))) =
        some .notFound := by
  sorry

@[kills dismissal_happened]
theorem dismissal_happened_rejects_hangup :
    ¬∀ (afterSave : List UInt8 → Option (List UInt8)),
        Record.Kept afterSave →
          ∀ (deadline heldSince : Option Nat) (now : Nat),
            Record.answer (afterSave (Record.encode (Record.ended (.signaled 1)))) =
                some .dismissed ∧
              Wait.Next.told
                  (Wait.decide deadline heldSince now
                    (.recorded
                      (Record.answer (afterSave (Record.encode (Record.ended (.signaled 1))))))) =
                some .notFound := by
  sorry

theorem names_round_trip (s name : String) :
    (Name.accept s = some name ↔ name = s ∧ Name.Accepted s) ∧
      (Name.Usable name →
        Remote.targetArgs ["--", name] = some (name, []) ∧
          Names.entryName (Names.entryFile name) = some name) ∧
      Name.accept "build · ✓ tests" = some "build · ✓ tests" := by
  sorry

@[kills names_round_trip]
theorem names_round_trip_rejects_keyed :
    ¬∀ (s name : String),
        (Name.keyed s = some name ↔ name = s ∧ Name.Accepted s) ∧
          (Name.Usable name →
            Remote.targetArgs ["--", name] = some (name, []) ∧
              Names.entryName (Names.entryFile name) = some name) ∧
          Name.keyed "build · ✓ tests" = some "build · ✓ tests" := by
  sorry

theorem check_eq_some_iff (s result : String) :
    Name.check s = some result ↔ result = s ∧ Name.Valid s := by sorry

@[kills check_eq_some_iff]
theorem check_eq_some_iff_rejects_any :
    ¬∀ (s result : String), (fun s => some s) s = some result ↔ result = s ∧ Name.Valid s := by
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
    Wait.decide deadline heldSince now (.ended e) = .answer (.ended e) ∧
      Wait.decide deadline heldSince now (.recorded (some e)) = .answer (.ended e) := by
  sorry

@[kills wait_ending]
theorem wait_ending_rejects_failed :
    ¬∀ (deadline heldSince : Option Nat) (now : Nat) (e : Ending),
        (fun (_ _ : Option Nat) (_ : Nat) (_ : Wait.Heard) => Wait.Next.answer .unknown) deadline
              heldSince now (.ended e) =
            .answer (.ended e) ∧
          (fun (_ _ : Option Nat) (_ : Nat) (_ : Wait.Heard) => Wait.Next.answer .unknown) deadline
              heldSince now (.recorded (some e)) =
            .answer (.ended e) := by
  sorry

theorem wait_held (deadline heldSince : Option Nat) (now : Nat) (heard : Wait.Heard) :
    (Wait.Next.told (Wait.decide deadline heldSince now heard) = some .failed ↔
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
            Wait.Next.told (Wait.decide deadline heldSince now heard) ≠ some .failed) := by
  sorry

@[kills wait_held]
theorem wait_held_rejects_eager :
    ¬∀ (deadline heldSince : Option Nat) (now : Nat) (heard : Wait.Heard),
        (Wait.Next.told
                ((fun (_ _ : Option Nat) (_ : Nat) (_ : Wait.Heard) => Wait.Next.answer .unknown)
                  deadline heldSince now heard) =
              some .failed ↔
            heard = .ended (.program .unknown) ∨
              heard = .recorded (some (.program .unknown)) ∨
              heard = .held ∧ ∃ since, heldSince = some since ∧ since + Wait.heldNameMs ≤ now) ∧
          (heard = .held →
            (∀ due, deadline = some due → now < due) →
            (∀ since, heldSince = some since → now < since + Wait.heldNameMs) →
            (fun (_ _ : Option Nat) (_ : Nat) (_ : Wait.Heard) => Wait.Next.answer .unknown)
                deadline heldSince now heard =
              .again (some (heldSince.getD now))) ∧
          (heard = .held →
            ∀ since,
              heldSince = some since →
                now < since + (Session.drainTimeoutMs + (Session.ending.map (·.wait)).sum) →
                Wait.Next.told
                    ((fun (_ _ : Option Nat) (_ : Nat) (_ : Wait.Heard) =>
                        Wait.Next.answer .unknown)
                      deadline heldSince now heard) ≠
                  some .failed) := by
  sorry

@[kills wait_held]
theorem wait_held_rejects_drain :
    ¬∀ (deadline heldSince : Option Nat) (now : Nat) (heard : Wait.Heard),
        (Wait.Next.told (Wait.decide deadline heldSince now heard) = some .failed ↔
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
                Wait.Next.told (Wait.decide deadline heldSince now heard) ≠ some .failed) := by
  sorry

theorem kill_answers (taken now : Nat) (heard : Kill.Heard) :
    (Kill.Next.told (Kill.decide taken now heard) = some .done ↔ heard = .free ∨ heard = .newer) ∧
      (Kill.Next.told (Kill.decide taken now heard) = some .notDone ↔
        heard = .asked ∧ taken + Wait.heldNameMs ≤ now) ∧
      (Kill.Next.told (Kill.decide taken now heard) = some .failed ↔
        heard = .held ∧ taken + Wait.heldNameMs ≤ now) ∧
      (Kill.Next.told (Kill.decide taken now heard) = none ↔
        (heard = .asked ∨ heard = .held) ∧ now < taken + Wait.heldNameMs) ∧
      (now < taken + (Session.drainTimeoutMs + (Session.ending.map (·.wait)).sum) →
        Kill.Next.told (Kill.decide taken now heard) = some .done ∨
          Kill.Next.told (Kill.decide taken now heard) = none) := by
  sorry

@[kills kill_answers]
theorem kill_answers_rejects_lock :
    ¬∀ (taken now : Nat) (heard : Kill.Heard),
        (Kill.Next.told (Kill.byLock Wait.heldNameMs taken now heard) = some .done ↔
            heard = .free ∨ heard = .newer) ∧
          (Kill.Next.told (Kill.byLock Wait.heldNameMs taken now heard) = some .notDone ↔
            heard = .asked ∧ taken + Wait.heldNameMs ≤ now) ∧
          (Kill.Next.told (Kill.byLock Wait.heldNameMs taken now heard) = some .failed ↔
            heard = .held ∧ taken + Wait.heldNameMs ≤ now) ∧
          (Kill.Next.told (Kill.byLock Wait.heldNameMs taken now heard) = none ↔
            (heard = .asked ∨ heard = .held) ∧ now < taken + Wait.heldNameMs) ∧
          (now < taken + (Session.drainTimeoutMs + (Session.ending.map (·.wait)).sum) →
            Kill.Next.told (Kill.byLock Wait.heldNameMs taken now heard) = some .done ∨
              Kill.Next.told (Kill.byLock Wait.heldNameMs taken now heard) = none) := by
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

theorem attach_upgrades (mode : Mode) (b : Nat) (info : List (String × String)) (took : Bool) :
    (Handover.plan mode b info = .handOver ↔
        mode = .writable ∧
          (Handover.Daemon.ofInfo info).hands = true ∧
          (Handover.Daemon.ofInfo info).older b = true) ∧
      (mode = .writable →
        (Handover.Daemon.ofInfo info).hands = true →
        (∃ n,
            Handover.after (Handover.plan mode b info) took (Handover.Daemon.ofInfo info) b =
                some n ∧
              b ≤ n) ∨
          Handover.plan mode b info = .handOver ∧
            took = false ∧
            Handover.after (Handover.plan mode b info) took (Handover.Daemon.ofInfo info) b =
              (Handover.Daemon.ofInfo info).build) := by
  sorry

@[kills attach_upgrades]
theorem attach_upgrades_rejects_kept :
    ¬∀ (mode : Mode) (b : Nat) (info : List (String × String)) (took : Bool),
        ((fun (_ : Mode) (_ : Nat) (_ : List (String × String)) => Handover.Plan.keep) mode b info =
              .handOver ↔
            mode = .writable ∧
              (Handover.Daemon.ofInfo info).hands = true ∧
              (Handover.Daemon.ofInfo info).older b = true) ∧
          (mode = .writable →
            (Handover.Daemon.ofInfo info).hands = true →
            (∃ n,
                Handover.after
                      ((fun (_ : Mode) (_ : Nat) (_ : List (String × String)) => Handover.Plan.keep)
                        mode b info)
                      took (Handover.Daemon.ofInfo info) b =
                    some n ∧
                  b ≤ n) ∨
              (fun (_ : Mode) (_ : Nat) (_ : List (String × String)) => Handover.Plan.keep) mode b
                    info =
                  .handOver ∧
                took = false ∧
                Handover.after
                    ((fun (_ : Mode) (_ : Nat) (_ : List (String × String)) => Handover.Plan.keep)
                      mode b info)
                    took (Handover.Daemon.ofInfo info) b =
                  (Handover.Daemon.ofInfo info).build) := by
  sorry

@[kills attach_upgrades]
theorem attach_upgrades_rejects_equal :
    ¬∀ (mode : Mode) (b : Nat) (info : List (String × String)) (took : Bool),
        (Handover.anyBuild mode b info = .handOver ↔
            mode = .writable ∧
              (Handover.Daemon.ofInfo info).hands = true ∧
              (Handover.Daemon.ofInfo info).older b = true) ∧
          (mode = .writable →
            (Handover.Daemon.ofInfo info).hands = true →
            (∃ n,
                Handover.after (Handover.anyBuild mode b info) took (Handover.Daemon.ofInfo info)
                      b =
                    some n ∧
                  b ≤ n) ∨
              Handover.anyBuild mode b info = .handOver ∧
                took = false ∧
                Handover.after (Handover.anyBuild mode b info) took (Handover.Daemon.ofInfo info)
                    b =
                  (Handover.Daemon.ofInfo info).build) := by
  sorry

@[kills attach_upgrades]
theorem attach_upgrades_rejects_watcher :
    ¬∀ (mode : Mode) (b : Nat) (info : List (String × String)) (took : Bool),
        (Handover.anyMode mode b info = .handOver ↔
            mode = .writable ∧
              (Handover.Daemon.ofInfo info).hands = true ∧
              (Handover.Daemon.ofInfo info).older b = true) ∧
          (mode = .writable →
            (Handover.Daemon.ofInfo info).hands = true →
            (∃ n,
                Handover.after (Handover.anyMode mode b info) took (Handover.Daemon.ofInfo info) b =
                    some n ∧
                  b ≤ n) ∨
              Handover.anyMode mode b info = .handOver ∧
                took = false ∧
                Handover.after (Handover.anyMode mode b info) took (Handover.Daemon.ofInfo info) b =
                  (Handover.Daemon.ofInfo info).build) := by
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

theorem changed_exactly (s : App.Serve.State) (version : String) (id : Serve.Id)
    (told latest : List Serve.Record) (ready : s.phase = .ready version)
    (subscribed : s.subscription = some id) (was : s.told = some told)
    (now : s.latest = some latest) :
    (App.Serve.step s .writable).2 =
        (if Serve.changes told latest = [] ∧ Serve.removed told latest = [] then []
        else
          [.send
              (.notify "sessions/changed"
                (Serve.update id (Serve.changes told latest) (Serve.removed told latest)))]) ∧
      (App.Serve.step s .writable).1.subscription = some id ∧
      (App.Serve.step s .writable).1.told = some latest ∧
      (App.Serve.step s .writable).1.latest = some latest := by
  sorry

@[kills changed_exactly]
theorem changed_exactly_rejects_chatty :
    ¬∀ (s : App.Serve.State) (version : String) (id : Serve.Id) (told latest : List Serve.Record),
        s.phase = .ready version →
          s.subscription = some id →
          s.told = some told →
          s.latest = some latest →
          (Serve.chatty App.Serve.step s .writable).2 =
              (if Serve.changes told latest = [] ∧ Serve.removed told latest = [] then []
              else
                [.send
                    (.notify "sessions/changed"
                      (Serve.update id (Serve.changes told latest) (Serve.removed told latest)))]) ∧
            (Serve.chatty App.Serve.step s .writable).1.subscription = some id ∧
            (Serve.chatty App.Serve.step s .writable).1.told = some latest ∧
            (Serve.chatty App.Serve.step s .writable).1.latest = some latest := by
  sorry

theorem screen_table_exact (s : App.Serve.State) (version : String) (id : Serve.Id)
    (told latest screen : Serve.Screen) (left : Serve.Log Serve.Line)
    (ready : s.phase = .ready version) :
    Serve.ScreenTable App.Serve.State.watching App.Serve.step App.Serve.result
      App.Serve.Screen.changes s id told latest screen left := by
  sorry

@[kills screen_table_exact]
theorem screen_table_exact_rejects_every_line :
    ¬∀ (s : App.Serve.State) (version : String) (id : Serve.Id) (told latest screen : Serve.Screen)
        (left : Serve.Log Serve.Line),
        s.phase = .ready version →
          Serve.ScreenTable App.Serve.State.watching App.Serve.step App.Serve.result
            Serve.Screen.everyLine s id told latest screen left := by
  sorry

@[kills screen_table_exact]
theorem screen_table_exact_rejects_first_change :
    ¬∀ (s : App.Serve.State) (version : String) (id : Serve.Id) (told latest screen : Serve.Screen)
        (left : Serve.Log Serve.Line),
        s.phase = .ready version →
          Serve.ScreenTable App.Serve.State.watching App.Serve.step App.Serve.result
            Serve.Screen.firstChange s id told latest screen left := by
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

theorem fault_contained (f : Fault)
    (afterCrash : Option ByteArray → ByteArray → Bool → Option ByteArray)
    (durable : Disk.Durable afterCrash) :
    Fault.Contained Recovery.decide Checkpoint.saveBytes Checkpoint.loadBytes Vt.Vt.init Vt.Vt.feed
      Vt.Vt.resize Vt.Vt.quiesce Session.step State.boot State.terminal State.fieldList
      State.nextTick State.roster Buf.Buf.empty Buf.bufOffer Buf.bufEnqueue Buf.bufAdvance
      Buf.owedLen Serve.step Serve.State.phase Serve.State.subscription Serve.State.told
      Serve.State.latest Serve.Log.push Listing.rowStatus Status.classify Capture.phases
      Capture.plan Offloop.ask Offloop.done afterCrash f f.cost := by
  sorry

@[kills fault_contained]
theorem fault_contained_rejects_uncut :
    ¬∀ f afterCrash,
        Disk.Durable afterCrash →
          Fault.Contained Recovery.decide Checkpoint.saveBytes Checkpoint.loadBytes Vt.Vt.init
            Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Session.step State.boot State.terminal
            State.fieldList State.nextTick State.roster Buf.Buf.empty Buf.bufOffer
            (fun cap b more => ((Buf.bufEnqueue cap b more).1, false)) Buf.bufAdvance Buf.owedLen
            Serve.step Serve.State.phase Serve.State.subscription Serve.State.told
            Serve.State.latest Serve.Log.push Listing.rowStatus Status.classify Capture.phases
            Capture.plan Offloop.ask Offloop.done afterCrash f f.cost := by
  sorry

@[kills fault_contained]
theorem fault_contained_rejects_fresh :
    ¬∀ f afterCrash,
        Disk.Durable afterCrash →
          Fault.Contained (fun _ _ => .fresh) Checkpoint.saveBytes Checkpoint.loadBytes Vt.Vt.init
            Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Session.step State.boot State.terminal
            State.fieldList State.nextTick State.roster Buf.Buf.empty Buf.bufOffer Buf.bufEnqueue
            Buf.bufAdvance Buf.owedLen Serve.step Serve.State.phase Serve.State.subscription
            Serve.State.told Serve.State.latest Serve.Log.push Listing.rowStatus Status.classify
            Capture.phases Capture.plan Offloop.ask Offloop.done afterCrash f f.cost := by
  sorry

@[kills fault_contained]
theorem fault_contained_rejects_never :
    ¬∀ f afterCrash,
        Disk.Durable afterCrash →
          Fault.Contained Recovery.decide Checkpoint.saveBytes Checkpoint.loadBytes Vt.Vt.init
            Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Session.step State.boot State.terminal
            State.fieldList (fun _ => none) State.roster Buf.Buf.empty Buf.bufOffer Buf.bufEnqueue
            Buf.bufAdvance Buf.owedLen Serve.step Serve.State.phase Serve.State.subscription
            Serve.State.told Serve.State.latest Serve.Log.push Listing.rowStatus Status.classify
            Capture.phases Capture.plan Offloop.ask Offloop.done afterCrash f f.cost := by
  sorry

@[kills fault_contained]
theorem fault_contained_rejects_exits :
    ¬∀ f afterCrash,
        Disk.Durable afterCrash →
          Fault.Contained Recovery.decide Checkpoint.saveBytes Checkpoint.loadBytes Vt.Vt.init
            Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce (Fault.exitsOnClose Session.step) State.boot
            State.terminal State.fieldList State.nextTick State.roster Buf.Buf.empty Buf.bufOffer
            Buf.bufEnqueue Buf.bufAdvance Buf.owedLen Serve.step Serve.State.phase
            Serve.State.subscription Serve.State.told Serve.State.latest Serve.Log.push
            Listing.rowStatus Status.classify Capture.phases Capture.plan Offloop.ask Offloop.done
            afterCrash f f.cost := by
  sorry

@[kills fault_contained]
theorem fault_contained_rejects_queued :
    ¬∀ f afterCrash,
        Disk.Durable afterCrash →
          Fault.Contained Recovery.decide Checkpoint.saveBytes Checkpoint.loadBytes Vt.Vt.init
            Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Session.step State.boot State.terminal
            State.fieldList State.nextTick State.roster Buf.Buf.empty Buf.bufOffer Buf.bufEnqueue
            Buf.bufAdvance Buf.owedLen (Serve.queued Serve.step) Serve.State.phase
            Serve.State.subscription Serve.State.told Serve.State.latest Serve.Log.push
            Listing.rowStatus Status.classify Capture.phases Capture.plan Offloop.ask Offloop.done
            afterCrash f f.cost := by
  sorry

@[kills fault_contained]
theorem fault_contained_rejects_keep_all :
    ¬∀ f afterCrash,
        Disk.Durable afterCrash →
          Fault.Contained Recovery.decide Checkpoint.saveBytes Checkpoint.loadBytes Vt.Vt.init
            Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Session.step State.boot State.terminal
            State.fieldList State.nextTick State.roster Buf.Buf.empty Buf.bufOffer Buf.bufEnqueue
            Buf.bufAdvance Buf.owedLen Serve.step Serve.State.phase Serve.State.subscription
            Serve.State.told Serve.State.latest Serve.Log.keepAll Listing.rowStatus Status.classify
            Capture.phases Capture.plan Offloop.ask Offloop.done afterCrash f f.cost := by
  sorry

@[kills fault_contained]
theorem fault_contained_rejects_idle :
    ¬∀ f afterCrash,
        Disk.Durable afterCrash →
          Fault.Contained Recovery.decide Checkpoint.saveBytes Checkpoint.loadBytes Vt.Vt.init
            Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Session.step State.boot State.terminal
            State.fieldList State.nextTick State.roster Buf.Buf.empty Buf.bufOffer Buf.bufEnqueue
            Buf.bufAdvance Buf.owedLen Serve.step Serve.State.phase Serve.State.subscription
            Serve.State.told Serve.State.latest Serve.Log.push (fun _ => ⟨.none, .idle⟩)
            Status.classify Capture.phases Capture.plan Offloop.ask Offloop.done afterCrash f
            f.cost := by
  sorry

@[kills fault_contained]
theorem fault_contained_rejects_inside :
    ¬∀ f afterCrash,
        Disk.Durable afterCrash →
          Fault.Contained Recovery.decide Checkpoint.saveBytes Checkpoint.loadBytes Vt.Vt.init
            Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Session.step State.boot State.terminal
            State.fieldList State.nextTick State.roster Buf.Buf.empty Buf.bufOffer Buf.bufEnqueue
            Buf.bufAdvance Buf.owedLen Serve.step Serve.State.phase Serve.State.subscription
            Serve.State.told Serve.State.latest Serve.Log.push Listing.rowStatus Status.classify
            Capture.phases [.acquire, .load, .render, .write, .release] Offloop.ask Offloop.done
            afterCrash f f.cost := by
  sorry

@[kills fault_contained]
theorem fault_contained_rejects_held :
    ¬∀ f afterCrash,
        Disk.Durable afterCrash →
          Fault.Contained Recovery.decide Checkpoint.saveBytes Checkpoint.loadBytes Vt.Vt.init
            Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Session.step State.boot State.terminal
            State.fieldList State.nextTick State.roster Buf.Buf.empty Buf.bufOffer Buf.bufEnqueue
            Buf.bufAdvance Buf.owedLen Serve.step Serve.State.phase Serve.State.subscription
            Serve.State.told Serve.State.latest Serve.Log.push Listing.rowStatus Status.classify
            (fun steps => [.locked steps]) Capture.plan Offloop.ask Offloop.done afterCrash f
            f.cost := by
  sorry

@[kills fault_contained]
theorem fault_contained_rejects_eager :
    ¬∀ f afterCrash,
        Disk.Durable afterCrash →
          Fault.Contained Recovery.decide Checkpoint.saveBytes Checkpoint.loadBytes Vt.Vt.init
            Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Session.step State.boot State.terminal
            State.fieldList State.nextTick State.roster Buf.Buf.empty Buf.bufOffer Buf.bufEnqueue
            Buf.bufAdvance Buf.owedLen Serve.step Serve.State.phase Serve.State.subscription
            Serve.State.told Serve.State.latest Serve.Log.push Listing.rowStatus Status.classify
            Capture.phases Capture.plan Offloop.eager Offloop.done afterCrash f f.cost := by
  sorry

theorem classify_iff (o : Status.Obs) (s : Status.Status) :
    Status.classify o = s ↔ Status.Is s o := by sorry

@[kills classify_iff]
theorem classify_iff_rejects_idle :
    ¬∀ (o : Status.Obs) (s : Status.Status),
        (fun (_ : Status.Obs) => ({ attention := .none, state := .idle } : Status.Status)) o = s ↔
          Status.Is s o := by
  sorry

theorem working_declared (s : State) :
    s.seen.progress = s.owned.progress ∧
      s.seen.running = s.owned.commands.running.isSome ∧
      ((Status.classify
              { progress := s.seen.progress, running := s.seen.running, unseen := s.seen.unseen,
                asks := s.seen.asks }).state =
          .working ↔
        s.owned.progress = some .normal ∨
          s.owned.progress = some .indeterminate ∨
          s.owned.progress = none ∧ s.owned.commands.running.isSome = true) := by
  sorry

@[kills working_declared]
theorem working_declared_rejects_window :
    ¬∀ (s : State),
        (Seen.windowed Session.infoFields State.seen s).progress = s.owned.progress ∧
          (Seen.windowed Session.infoFields State.seen s).running =
            s.owned.commands.running.isSome ∧
          ((Status.classify
                  { progress := (Seen.windowed Session.infoFields State.seen s).progress,
                    running := (Seen.windowed Session.infoFields State.seen s).running,
                    unseen := (Seen.windowed Session.infoFields State.seen s).unseen,
                    asks := (Seen.windowed Session.infoFields State.seen s).asks }).state =
              .working ↔
            s.owned.progress = some .normal ∨
              s.owned.progress = some .indeterminate ∨
              s.owned.progress = none ∧ s.owned.commands.running.isSome = true) := by
  sorry

theorem progress_status (s : State) (ev : Event) :
    (∀ chunk,
        ev = .ptyOut chunk →
          (Session.step s ev).1.seen.progress =
            ((Mediation.feed s.terminal s.scanner chunk).progress).getD s.seen.progress) ∧
      ((∀ chunk, ev ≠ .ptyOut chunk) → (Session.step s ev).1.seen.progress = s.seen.progress) ∧
      ((s.seen.progress = some .error →
          (Status.classify
                { progress := s.seen.progress, running := s.seen.running, unseen := s.seen.unseen,
                  asks := s.seen.asks }).state =
            .errored) ∧
        (s.seen.progress = some .paused →
          (Status.classify
                { progress := s.seen.progress, running := s.seen.running, unseen := s.seen.unseen,
                  asks := s.seen.asks }).state =
            .paused) ∧
        (s.seen.progress = some .normal ∨ s.seen.progress = some .indeterminate →
          (Status.classify
                { progress := s.seen.progress, running := s.seen.running, unseen := s.seen.unseen,
                  asks := s.seen.asks }).state =
            .working)) := by
  sorry

@[kills progress_status]
theorem progress_status_rejects_error_working :
    ¬∀ (s : State) (ev : Event),
        (∀ chunk,
            ev = .ptyOut chunk →
              (Seen.errorWorks State.seen (Session.step s ev).1).progress =
                ((Mediation.feed s.terminal s.scanner chunk).progress).getD
                  (Seen.errorWorks State.seen s).progress) ∧
          ((∀ chunk, ev ≠ .ptyOut chunk) →
            (Seen.errorWorks State.seen (Session.step s ev).1).progress =
              (Seen.errorWorks State.seen s).progress) ∧
          (((Seen.errorWorks State.seen s).progress = some .error →
              (Status.classify
                    { progress := (Seen.errorWorks State.seen s).progress,
                      running := (Seen.errorWorks State.seen s).running,
                      unseen := (Seen.errorWorks State.seen s).unseen,
                      asks := (Seen.errorWorks State.seen s).asks }).state =
                .errored) ∧
            ((Seen.errorWorks State.seen s).progress = some .paused →
              (Status.classify
                    { progress := (Seen.errorWorks State.seen s).progress,
                      running := (Seen.errorWorks State.seen s).running,
                      unseen := (Seen.errorWorks State.seen s).unseen,
                      asks := (Seen.errorWorks State.seen s).asks }).state =
                .paused) ∧
            ((Seen.errorWorks State.seen s).progress = some .normal ∨
                (Seen.errorWorks State.seen s).progress = some .indeterminate →
              (Status.classify
                    { progress := (Seen.errorWorks State.seen s).progress,
                      running := (Seen.errorWorks State.seen s).running,
                      unseen := (Seen.errorWorks State.seen s).unseen,
                      asks := (Seen.errorWorks State.seen s).asks }).state =
                .working)) := by
  sorry

@[kills progress_status]
theorem progress_status_rejects_pause_working :
    ¬∀ (s : State) (ev : Event),
        (∀ chunk,
            ev = .ptyOut chunk →
              (Seen.pauseWorks State.seen (Session.step s ev).1).progress =
                ((Mediation.feed s.terminal s.scanner chunk).progress).getD
                  (Seen.pauseWorks State.seen s).progress) ∧
          ((∀ chunk, ev ≠ .ptyOut chunk) →
            (Seen.pauseWorks State.seen (Session.step s ev).1).progress =
              (Seen.pauseWorks State.seen s).progress) ∧
          (((Seen.pauseWorks State.seen s).progress = some .error →
              (Status.classify
                    { progress := (Seen.pauseWorks State.seen s).progress,
                      running := (Seen.pauseWorks State.seen s).running,
                      unseen := (Seen.pauseWorks State.seen s).unseen,
                      asks := (Seen.pauseWorks State.seen s).asks }).state =
                .errored) ∧
            ((Seen.pauseWorks State.seen s).progress = some .paused →
              (Status.classify
                    { progress := (Seen.pauseWorks State.seen s).progress,
                      running := (Seen.pauseWorks State.seen s).running,
                      unseen := (Seen.pauseWorks State.seen s).unseen,
                      asks := (Seen.pauseWorks State.seen s).asks }).state =
                .paused) ∧
            ((Seen.pauseWorks State.seen s).progress = some .normal ∨
                (Seen.pauseWorks State.seen s).progress = some .indeterminate →
              (Status.classify
                    { progress := (Seen.pauseWorks State.seen s).progress,
                      running := (Seen.pauseWorks State.seen s).running,
                      unseen := (Seen.pauseWorks State.seen s).unseen,
                      asks := (Seen.pauseWorks State.seen s).asks }).state =
                .working)) := by
  sorry

@[kills progress_status]
theorem progress_status_rejects_forgotten :
    ¬∀ (s : State) (ev : Event),
        (∀ chunk,
            ev = .ptyOut chunk →
              (Session.forgetsProgress Session.step s ev).1.seen.progress =
                ((Mediation.feed s.terminal s.scanner chunk).progress).getD s.seen.progress) ∧
          ((∀ chunk, ev ≠ .ptyOut chunk) →
            (Session.forgetsProgress Session.step s ev).1.seen.progress = s.seen.progress) ∧
          ((s.seen.progress = some .error →
              (Status.classify
                    { progress := s.seen.progress, running := s.seen.running,
                      unseen := s.seen.unseen, asks := s.seen.asks }).state =
                .errored) ∧
            (s.seen.progress = some .paused →
              (Status.classify
                    { progress := s.seen.progress, running := s.seen.running,
                      unseen := s.seen.unseen, asks := s.seen.asks }).state =
                .paused) ∧
            (s.seen.progress = some .normal ∨ s.seen.progress = some .indeterminate →
              (Status.classify
                    { progress := s.seen.progress, running := s.seen.running,
                      unseen := s.seen.unseen, asks := s.seen.asks }).state =
                .working)) := by
  sorry

theorem unseen_lines (s : State) (ev : Event) :
    (∀ chunk,
        ev = .ptyOut chunk →
          (Session.step s ev).1.seen.unseen =
            (!seenBy s.roster &&
              (s.seen.unseen || (Mediation.feed s.terminal s.scanner chunk).lines))) ∧
      (∀ (id : Nat) (chunk : List UInt8) (c : Client) (dec : Wire.Decoder) (m : Wire.Msg),
        ev = .bytes id chunk →
          s.client? id = some c →
          c.attached = false →
          c.decoder.feed chunk = (dec, [m]) →
          dec.errored = false → m.Looks → (Session.step s ev).1.seen.unseen = false) ∧
      ((∀ chunk, ev ≠ .ptyOut chunk) →
        (Session.step s ev).1.seen.unseen = true → s.seen.unseen = true) := by
  sorry

@[kills unseen_lines]
theorem unseen_lines_rejects_output :
    ¬∀ (s : State) (ev : Event),
        (∀ chunk,
            ev = .ptyOut chunk →
              (Seen.anyOutput Session.infoFields State.seen (Session.step s ev).1).unseen =
                (!seenBy s.roster &&
                  ((Seen.anyOutput Session.infoFields State.seen s).unseen ||
                    (Mediation.feed s.terminal s.scanner chunk).lines))) ∧
          (∀ (id : Nat) (chunk : List UInt8) (c : Client) (dec : Wire.Decoder) (m : Wire.Msg),
            ev = .bytes id chunk →
              s.client? id = some c →
              c.attached = false →
              c.decoder.feed chunk = (dec, [m]) →
              dec.errored = false →
              m.Looks →
              (Seen.anyOutput Session.infoFields State.seen (Session.step s ev).1).unseen = false) ∧
          ((∀ chunk, ev ≠ .ptyOut chunk) →
            (Seen.anyOutput Session.infoFields State.seen (Session.step s ev).1).unseen = true →
            (Seen.anyOutput Session.infoFields State.seen s).unseen = true) := by
  sorry

theorem status_clockless (s : State) (times : List Nat) :
    (Session.trace Session.step s (times.map Event.tick)).1.seen = s.seen := by sorry

@[kills status_clockless]
theorem status_clockless_rejects_window :
    ¬∀ (s : State) (times : List Nat),
        Seen.windowed Session.infoFields State.seen
            (Session.trace Session.step s (times.map Event.tick)).1 =
          Seen.windowed Session.infoFields State.seen s := by
  sorry

theorem icon_glyphs :
    (∀ a b, Status.mark a = Status.mark b → a = b) ∧
      (∀ a b, Status.icon a = Status.icon b → a = b) ∧
      (∀ a s, Status.mark a ≠ Status.icon s) ∧
      Status.mark .none = ' ' ∧
      ∃ marks states,
        Status.legend = "Attention" :: marks ++ "State" :: states ∧
          (∀ a : Status.Attention,
            a ≠ .none →
              (marks.map fun line => line.toList.head?).count (some (Status.mark a)) = 1) ∧
          (∀ line ∈ marks,
            ∃ a : Status.Attention, a ≠ .none ∧ line.toList.head? = some (Status.mark a)) ∧
          (∀ s, (states.map fun line => line.toList.head?).count (some (Status.icon s)) = 1) ∧
          ∀ line ∈ states, ∃ s, line.toList.head? = some (Status.icon s) := by
  sorry

@[kills icon_glyphs]
theorem icon_glyphs_rejects_unknown :
    ¬((∀ a b, Status.mark a = Status.mark b → a = b) ∧
        (∀ a b, (fun (_ : Status.State) => '?') a = (fun (_ : Status.State) => '?') b → a = b) ∧
        (∀ a s, Status.mark a ≠ (fun (_ : Status.State) => '?') s) ∧
        Status.mark .none = ' ' ∧
        ∃ marks states,
          Status.legend = "Attention" :: marks ++ "State" :: states ∧
            (∀ a : Status.Attention,
              a ≠ .none →
                (marks.map fun line => line.toList.head?).count (some (Status.mark a)) = 1) ∧
            (∀ line ∈ marks,
              ∃ a : Status.Attention, a ≠ .none ∧ line.toList.head? = some (Status.mark a)) ∧
            (∀ s,
              (states.map fun line => line.toList.head?).count
                  (some ((fun (_ : Status.State) => '?') s)) =
                1) ∧
            ∀ line ∈ states,
              ∃ s, line.toList.head? = some ((fun (_ : Status.State) => '?') s)) := by
  sorry

theorem summary_exact (attentions : List Status.Attention) :
    Status.summary attentions =
      String.intercalate " "
        ((if attentions.count .asked = 0 then []
          else [(toString (attentions.count .asked)).push (Status.mark .asked)]) ++
          (if attentions.count .unread = 0 then []
          else [(toString (attentions.count .unread)).push (Status.mark .unread)])) := by
  sorry

@[kills summary_exact]
theorem summary_exact_rejects_count :
    ¬∀ (attentions : List Status.Attention),
        (fun (all : List Status.Attention) => toString all.length) attentions =
          String.intercalate " "
            ((if attentions.count .asked = 0 then []
              else [(toString (attentions.count .asked)).push (Status.mark .asked)]) ++
              (if attentions.count .unread = 0 then []
              else [(toString (attentions.count .unread)).push (Status.mark .unread)])) := by
  sorry

theorem rowStatus_saved (status : Nat) (st : Status.Status) :
    Status.Is (Listing.rowStatus (.ended status))
        { daemonUp := false, exit := some status, unseen := true } ∧
      (∃ o : Status.Obs,
        o.known = true ∧
          o.daemonUp = false ∧
          Status.Is
            (Listing.rowStatus
              (.remote false (Status.attentionName st.attention) (Status.name st.state)))
            o) ∧
      (st.state = .exitedOk ∨ st.state = .exitedBad →
        Listing.rowStatus
            (.remote false (Status.attentionName st.attention) (Status.name st.state)) =
          st) := by
  sorry

@[kills rowStatus_saved]
theorem rowStatus_saved_rejects_unknown :
    ¬∀ (status : Nat) (st : Status.Status),
        Status.Is
            ((fun (_ : Listing.Row) => ({ attention := .none, state := .unknown } : Status.Status))
              (.ended status))
            { daemonUp := false, exit := some status, unseen := true } ∧
          (∃ o : Status.Obs,
            o.known = true ∧
              o.daemonUp = false ∧
              Status.Is
                ((fun (_ : Listing.Row) =>
                    ({ attention := .none, state := .unknown } : Status.Status))
                  (.remote false (Status.attentionName st.attention) (Status.name st.state)))
                o) ∧
          (st.state = .exitedOk ∨ st.state = .exitedBad →
            (fun (_ : Listing.Row) => ({ attention := .none, state := .unknown } : Status.Status))
                (.remote false (Status.attentionName st.attention) (Status.name st.state)) =
              st) := by
  sorry

theorem row_pair (layout : Listing.Layout) (info : List (String × String)) :
    (∀ a s, ∃ o, Status.classify o = { attention := a, state := s }) ∧
      (Listing.columns layout info).take 2 =
        [[Status.mark (Status.ofAttentionName ((info.lookup "attention").getD "")), ' '],
          [Status.icon (Status.ofName ((info.lookup "status").getD "")), ' ']] := by
  sorry

@[kills row_pair]
theorem row_pair_rejects_single :
    ¬∀ (layout : Listing.Layout) (info : List (String × String)),
        (∀ a s, ∃ o, Status.single Status.classify o = { attention := a, state := s }) ∧
          (Listing.columns layout info).take 2 =
            [[Status.mark (Status.ofAttentionName ((info.lookup "attention").getD "")), ' '],
              [Status.icon (Status.ofName ((info.lookup "status").getD "")), ' ']] := by
  sorry

theorem attention_independent (o o' : Status.Obs) (asks : o.asks = o'.asks)
    (unseen : o.unseen = o'.unseen) :
    (Status.classify o).attention = (Status.classify o').attention := by sorry

@[kills attention_independent]
theorem attention_independent_rejects_single :
    ¬∀ (o o' : Status.Obs),
        o.asks = o'.asks →
          o.unseen = o'.unseen →
          (Status.single Status.classify o).attention =
            (Status.single Status.classify o').attention := by
  sorry

theorem state_independent (o o' : Status.Obs) (known : o.known = o'.known)
    (daemonUp : o.daemonUp = o'.daemonUp) (exit : o.exit = o'.exit)
    (progress : o.progress = o'.progress) (running : o.running = o'.running) :
    (Status.classify o).state = (Status.classify o').state := by sorry

@[kills state_independent]
theorem state_independent_rejects_single :
    ¬∀ (o o' : Status.Obs),
        o.known = o'.known →
          o.daemonUp = o'.daemonUp →
          o.exit = o'.exit →
          o.progress = o'.progress →
          o.running = o'.running →
          (Status.single Status.classify o).state = (Status.single Status.classify o').state := by
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

theorem announce_changes (before current : List (String × Status.Attention)) (own name : String) :
    Alert.announce none current own = [] ∧
      (name ∈ Alert.announce (some before) current own ↔
        name ≠ own ∧
          (name, Status.Attention.asked) ∈ current ∧ (name, Status.Attention.asked) ∉ before) ∧
      ((current.map (·.1)).Nodup → (Alert.announce (some before) current own).Nodup) := by
  sorry

@[kills announce_changes]
theorem announce_changes_rejects_every_sample :
    ¬∀ (before current : List (String × Status.Attention)) (own name : String),
        Alert.everySample none current own = [] ∧
          (name ∈ Alert.everySample (some before) current own ↔
            name ≠ own ∧
              (name, Status.Attention.asked) ∈ current ∧ (name, Status.Attention.asked) ∉ before) ∧
          ((current.map (·.1)).Nodup → (Alert.everySample (some before) current own).Nodup) := by
  sorry

@[kills announce_changes]
theorem announce_changes_rejects_self :
    ¬∀ (before current : List (String × Status.Attention)) (own name : String),
        Alert.withSelf none current own = [] ∧
          (name ∈ Alert.withSelf (some before) current own ↔
            name ≠ own ∧
              (name, Status.Attention.asked) ∈ current ∧ (name, Status.Attention.asked) ∉ before) ∧
          ((current.map (·.1)).Nodup → (Alert.withSelf (some before) current own).Nodup) := by
  sorry

theorem sort_attention_first {α : Type} (status : α → Status.Status) (rows : List α) :
    (View.sort status rows).Perm rows ∧
      ∃ first rest,
        View.sort status rows = first ++ rest ∧
          (∀ x ∈ first, (status x).attention ≠ .none) ∧
          ∀ x ∈ rest, (status x).attention = .none := by
  sorry

@[kills sort_attention_first]
theorem sort_attention_first_rejects_arrival :
    ¬∀ {α : Type} (status : α → Status.Status) (rows : List α),
        (View.arrival status rows).Perm rows ∧
          ∃ first rest,
            View.arrival status rows = first ++ rest ∧
              (∀ x ∈ first, (status x).attention ≠ .none) ∧
              ∀ x ∈ rest, (status x).attention = .none := by
  sorry

theorem sort_keeps_place {α : Type} (status status' : α → Status.Status) (rows : List α)
    (h :
      ∀ x ∈ rows,
        status x = status' x ∨
          (status x).attention = (status' x).attention ∧
            ((status x).state = .working ∨
              (status x).state = .paused ∨ (status x).state = .errored ∨ (status x).state = .idle) ∧
            ((status' x).state = .working ∨
              (status' x).state = .paused ∨
              (status' x).state = .errored ∨ (status' x).state = .idle)) :
    View.sort status rows = View.sort status' rows := by sorry

@[kills sort_keeps_place]
theorem sort_keeps_place_rejects_activity :
    ¬∀ {α : Type} (status status' : α → Status.Status) (rows : List α),
        (∀ x ∈ rows,
            status x = status' x ∨
              (status x).attention = (status' x).attention ∧
                ((status x).state = .working ∨
                  (status x).state = .paused ∨
                  (status x).state = .errored ∨ (status x).state = .idle) ∧
                ((status' x).state = .working ∨
                  (status' x).state = .paused ∨
                  (status' x).state = .errored ∨ (status' x).state = .idle)) →
          View.byActivity status rows = View.byActivity status' rows := by
  sorry

theorem sort_live_above_done {α : Type} (status : α → Status.Status) (rows first rest : List α)
    (split : View.sort status rows = first ++ rest) (x : α) (above : x ∈ first)
    (ended :
      (status x).state = .exitedOk ∨ (status x).state = .exitedBad ∨ (status x).state = .resumable)
    (y : α) (below : y ∈ rest) (same : (status y).attention = (status x).attention) :
    ¬((status y).state = .errored ∨
        (status y).state = .working ∨ (status y).state = .paused ∨ (status y).state = .idle) := by
  sorry

@[kills sort_live_above_done]
theorem sort_live_above_done_rejects_done_above :
    ¬∀ {α : Type} (status : α → Status.Status) (rows first rest : List α),
        View.doneAboveLive status rows = first ++ rest →
          ∀ (x : α),
            x ∈ first →
              ((status x).state = .exitedOk ∨
                (status x).state = .exitedBad ∨ (status x).state = .resumable) →
              ∀ (y : α),
                y ∈ rest →
                  (status y).attention = (status x).attention →
                  ¬((status y).state = .errored ∨
                      (status y).state = .working ∨
                      (status y).state = .paused ∨ (status y).state = .idle) := by
  sorry

theorem sort_two_keys {α : Type} (status : α → Status.Status) (earlier : α → α → Prop)
    (rows : List α) (listed : rows.Pairwise earlier) :
    (View.sort status rows).Perm rows ∧
      (View.sort status rows).Pairwise fun a b =>
        View.needs (status a).attention < View.needs (status b).attention ∨
          View.needs (status a).attention = View.needs (status b).attention ∧
            (View.lifecycle (status a).state < View.lifecycle (status b).state ∨
              View.lifecycle (status a).state = View.lifecycle (status b).state ∧ earlier a b) := by
  sorry

@[kills sort_two_keys]
theorem sort_two_keys_rejects_ended_above_saved :
    ¬∀ {α : Type} (status : α → Status.Status) (earlier : α → α → Prop) (rows : List α),
        rows.Pairwise earlier →
          (View.endedAboveSaved status rows).Perm rows ∧
            (View.endedAboveSaved status rows).Pairwise fun a b =>
              View.needs (status a).attention < View.needs (status b).attention ∨
                View.needs (status a).attention = View.needs (status b).attention ∧
                  (View.lifecycle (status a).state < View.lifecycle (status b).state ∨
                    View.lifecycle (status a).state = View.lifecycle (status b).state ∧
                      earlier a b) := by
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
