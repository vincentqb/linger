module

public import Linger.Session.CoreCode
public import Linger.Session.CoreCode.Buf
public import Linger.Session.CoreSpec
public import Linger.Session.WorldSpec
public import Terminal.CoreCode.Mediation
public import Terminal.CoreCode.Replay
public import Terminal.CoreSpec
import all Linger.App.Proofs.Api
import all Linger.App.Proofs.Capture
import all Linger.App.Proofs.Commands
import all Linger.App.Proofs.Entry
import all Linger.App.Proofs.Kill
import all Linger.App.Proofs.Recovery
import all Linger.App.Proofs.Serve
import all Linger.App.Proofs.Screen
import all Linger.App.Proofs.Wait
import Linger.Display.Proofs.Clean
import all Linger.App.Proofs.Fields
import all Linger.App.Proofs.Owned
import all Linger.Display.Proofs.Alert
import all Linger.Display.Proofs.Listing
import all Linger.Display.Proofs.Status
import all Linger.Display.Proofs.View
import all Linger.Import.Proofs.Resurrect
import all Linger.Selector.Proofs.Picker
import all Linger.Selector.Proofs.Fetch
import all Linger.Display.Proofs.Title
import all Linger.Os.Proofs.Answer
import all Linger.Os.Proofs.Env
import all Os.Proofs.Wait
import Linger.Target.Proofs.Name
import Linger.Target.Proofs.Remote
import all Linger.Session.Proofs.Buf
import all Linger.Session.Proofs.Offloop
import all Linger.Session.Proofs.Present
import all Linger.Session.Proofs.Checkpoint
import all Linger.Session.Proofs.Handoff
import all Linger.Session.Proofs.Claim
import all Linger.Session.Proofs.Names
import all Linger.Session.Proofs.Driver
import all Linger.Session.Proofs.Record
import all Linger.Session.Proofs.Session
import all Linger.Session.Proofs.Start
import all Linger.Session.Proofs.Wire
public import Linger.Session.CoreCode.Record
public import Linger.Session.CoreCode.Wire
import all Terminal.CoreCode.Vt
import all Terminal.Proofs.Vt
import all Terminal.Proofs.Vt.History
import all Terminal.Proofs.Vt.Renderable
import all Terminal.Proofs.Render.Grid
import all Terminal.Proofs.Render.History
import all Terminal.Proofs.Render.PendingWrap
import all Terminal.Proofs.Render.Scrollback
import all Terminal.Proofs.Render.Sticky
import all Terminal.Proofs.Replay
import all Terminal.Proofs.Vt.State

/-! # Part 1 of `Challenge.lean`, transparency: the proofs of its headline theorems and their kills

`Challenge.lean` states them; each proof cites the component theorems it restates, and
`Theorems.Solution` gathers every part for `./lake comparator`. -/

public section

namespace Linger

open Linger.Display Linger.Session Linger.Target Terminal

theorem step_attach_repaint (s : State) (id : Nat) (chunk : List UInt8) {c : Client}
    {dec : Wire.Decoder} {mode : Mode} {cols rows : UInt32} (hc : s.client? id = some c)
    (fresh : c.attached = false) (read : c.decoder.feed chunk = (dec, [.attach mode cols rows]))
    (healthy : dec.errored = false) :
    ∃ pty after,
      (Session.step s (.bytes id chunk)).2 =
          pty ++
            Effect.replay id (Replay.start (Session.step s (.bytes id chunk)).1.terminal) :: after ∧
        ∀ eff ∈ pty, (∃ bytes, eff = .writePty bytes) ∨ ∃ cols rows, eff = .resizePty cols rows :=
  Session.step_attach_repaint s id chunk hc fresh read healthy

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
  intro h
  obtain ⟨joined, -⟩ := Session.connected_client_witness
  obtain ⟨pty, after, effects, -⟩ :=
    @h (Session.trace Session.step (State.boot (Vt.Vt.init 1 1) [] []) [.connected 1]).1 1
      (Wire.encode (.attach .writable 80 24)) { id := 1 } {} .writable 80 24 joined rfl
      (Session.feed_encode_fresh _ trivial) rfl
  have repainted := List.mem_iff_append.mpr ⟨pty, after, effects⟩
  simp [Session.without, Effect.replays] at repainted

theorem step_output_delivered (s : State) (chunk : List UInt8) :
    (Session.step s (.ptyOut chunk)).1.terminal = s.terminal.feed chunk ∧
      ∃ answers frames : List (List UInt8),
        (Session.step s (.ptyOut chunk)).2 =
            answers.map Effect.writePty ++
              (s.roster.filter (·.attached)).flatMap
                (fun c => frames.map fun frame => Effect.send c.id (.output frame)) ∧
          answers.flatten = (Mediation.feed s.terminal s.scanner chunk).replies ∧
          frames.flatten = (Mediation.feed s.terminal s.scanner chunk).visible ∧
          ∀ frame ∈ frames,
            frame ≠ [] ∧ frame.length ≤ 65536 := Session.step_ptyOut_delivered s chunk

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
  intro h
  obtain ⟨⟨c, joined, attached⟩, plain⟩ := Session.attached_output_witness
  obtain ⟨-, answers, frames, effects, -, released, -⟩ :=
    h
      (Session.trace Session.step (State.boot (Vt.Vt.init 1 1) [] [])
          [.connected 1, .bytes 1 (Wire.encode (.attach .writable 80 24))]).1
      [0x41]
  rw [plain] at released
  obtain ⟨frame, framed⟩ : ∃ frame, frame ∈ frames := by
    cases frames with
    | nil => simp at released
    | cons first _ => exact ⟨first, List.mem_cons_self⟩
  have member :
    (Effect.send c.id (.output frame) : Effect Replay.Plan) ∈
      frames.map fun frame => Effect.send c.id (.output frame) :=
    List.mem_map_of_mem framed
  have sent :=
    List.mem_append_right (answers.map Effect.writePty)
      ((List.mem_flatMap (f := fun c : Client =>
            frames.map fun frame => (Effect.send c.id (.output frame) : Effect Replay.Plan))).mpr
        ⟨c, List.mem_filter.mpr ⟨joined, attached⟩, member⟩)
  rw [← effects] at sent
  simp [Session.without, Effect.rendered] at sent

theorem step_input_exact (s : State) (id : Nat) (chunk : List UInt8) {c : Client}
    {dec : Wire.Decoder} {inputs : List (List UInt8)} (hc : s.client? id = some c)
    (typist : c.mode = .writable) (read : c.decoder.feed chunk = (dec, inputs.map Wire.Msg.input))
    (healthy : dec.errored = false) :
    (Session.step s (.bytes id chunk)).2 = inputs.map Effect.writePty :=
  Session.step_input_exact s id chunk hc typist read healthy

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
  intro h
  obtain ⟨joined, -⟩ := Session.connected_client_witness
  have wrote :=
    @h (Session.trace Session.step (State.boot (Vt.Vt.init 1 1) [] []) [.connected 1]).1 1
      (Wire.encode (.input [0x61])) { id := 1 } {} [[0x61]] joined rfl
      (Session.feed_encode_fresh (.input [0x61]) (by simp [Wire.Msg.Fits, Wire.maxPayload])) rfl
  simp at wrote

theorem input_exact (reads : Pty.Mode → ByteArray → ByteArray) (delivers : Pty.Delivers reads)
    {cap : Nat} {accepted written : ByteArray} {b : Buf.Buf}
    (life :
      Buf.InputLife Buf.Buf.empty Buf.bufOffer Buf.bufAdvance Buf.writeFrom cap accepted written
        b) :
    written ++ Buf.writeFrom b = accepted ∧
      reads .raw written ++ Buf.writeFrom b = accepted ∧
      ∀ more, (Buf.bufOffer cap b more).2 = true ↔ cap < Buf.owedLen b + more.size := by
  have exact := Buf.inputLife_exact life
  refine ⟨exact, ?_, fun more => Buf.bufOffer_refuses_iff cap b more⟩
  rw [delivers written]
  exact exact

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
  intro h
  have life :=
    Buf.InputLife.offer (empty := Buf.Buf.empty) (offer :=
      fun (_ : Nat) (b : Buf.Buf) (_ : ByteArray) => (b, false)) (advance := Buf.bufAdvance)
      (pending := Buf.writeFrom) (cap := 1) ByteArray.empty ByteArray.empty Buf.Buf.empty ⟨#[0x61]⟩
      .empty
  -- the kernel of this world hands a raw program every byte, as the claim says
  have lost := congrArg ByteArray.size (h (fun _ written => written) (fun _ => rfl) life).1
  simp [Buf.writeFrom_empty] at lost
  exact absurd lost (by decide)

theorem decode_encode_chunked (ms : List Wire.Msg) (fits : ∀ m ∈ ms, m.Fits)
    (chunks : List (List UInt8)) (cut : chunks.flatten = ms.flatMap Wire.encode) :
    Wire.feedAll Wire.Decoder.feed {} chunks = ({ buf := [], errored := false }, ms) := by
  rw [Wire.feedAll_feed]
  exact Wire.decode_encode_chunked ms (fun m hm => Wire.fits_wf m (fits m hm)) chunks cut

theorem decode_encode_chunked_rejects_silence :
    ¬∀ (ms : List Wire.Msg),
        (∀ m ∈ ms, m.Fits) →
          ∀ (chunks : List (List UInt8)),
            chunks.flatten = ms.flatMap (fun (_ : Wire.Msg) => ([] : List UInt8)) →
              Wire.feedAll Wire.Decoder.feed {} chunks = ({ buf := [], errored := false }, ms) := by
  intro h
  have read := h [.done] (by simp [Wire.Msg.Fits]) [] (by simp)
  exact absurd (congrArg Prod.snd read) (by simp [Wire.feedAll])

theorem inputFrames_exact (bytes : List UInt8) :
    ∃ chunks : List (List UInt8),
      Wire.inputFrames bytes = chunks.map Wire.Msg.input ∧
        chunks.flatten = bytes ∧ ∀ m ∈ Wire.inputFrames bytes, m.Fits :=
  Wire.inputFrames_exact bytes

theorem inputFrames_exact_rejects_one :
    ¬∀ (bytes : List UInt8),
        ∃ chunks : List (List UInt8),
          (fun (bytes : List UInt8) => [Wire.Msg.input bytes]) bytes = chunks.map Wire.Msg.input ∧
            chunks.flatten = bytes ∧
            ∀ m ∈ (fun (bytes : List UInt8) => [Wire.Msg.input bytes]) bytes, m.Fits := by
  intro h
  obtain ⟨_, _, _, fits⟩ := h (List.replicate (Wire.maxPayload + 1) 0)
  have whole := fits _ (List.mem_singleton_self _)
  simp only [Wire.Msg.Fits, List.length_replicate] at whole
  omega

theorem step_attach_focus (s : State) (id : Nat) (chunk : List UInt8) {c : Client}
    {dec : Wire.Decoder} {mode : Mode} {cols rows : UInt32} (hc : s.client? id = some c)
    (read : c.decoder.feed chunk = (dec, [.attach mode cols rows])) (healthy : dec.errored = false)
    (bytes : List UInt8) :
    Effect.writePty bytes ∈ (Session.step s (.bytes id chunk)).2 ↔
      bytes = [0x1B, 0x5B, 0x49] ∧
        s.terminal.getModes.focusEvents = true ∧
        c.attached = false ∧
        mode = .writable ∧
        ∀ other ∈ s.roster, other.id ≠ id → (other.attached && other.mode == .writable) = false :=
  Session.step_attach_focus s id chunk hc read healthy bytes

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
  intro h
  obtain ⟨joined, -⟩ := Session.connected_client_witness
  have heard :=
    (@h (Session.trace Session.step (State.boot (Vt.Vt.init 1 1) [] []) [.connected 1]).1 1
          (Wire.encode (.attach .readOnly 80 24)) { id := 1 } {} .readOnly 80 24 joined
          (Session.feed_encode_fresh (.attach .readOnly 80 24) trivial) rfl [0x1B, 0x5B, 0x49]).mp
      (by simp)
  exact absurd heard.2.2.2.1 (by decide)

theorem step_closed_focus (s : State) (id : Nat) (bytes : List UInt8) :
    Effect.writePty bytes ∈ (Session.step s (.closed id)).2 ↔
      bytes = [0x1B, 0x5B, 0x4F] ∧
        s.terminal.getModes.focusEvents = true ∧
        (s.client? id).any (·.mode == .writable) = true ∧
        s.roster.any (fun c => c.attached && c.mode == .writable) = true ∧
        (Session.step s (.closed id)).1.roster.any (fun c => c.attached && c.mode == .writable) =
          false := Session.step_closed_focus s id bytes

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
  intro h
  obtain ⟨-, none⟩ := Session.connected_client_witness
  have heard := (h (State.boot (Vt.Vt.init 1 1) [] []) 1 [0x1B, 0x5B, 0x4F]).mp (by simp)
  rw [none] at heard
  exact absurd heard.2.2.1 (by decide)

end Linger
