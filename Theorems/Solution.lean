module

public import Linger.App.Answer
public import Linger.App.Capture
public import Linger.App.Commands
public import Linger.App.Entry
public import Linger.App.Recovery
public import Linger.App.Wait
public import Linger.Display.Listing
public import Linger.Display.Status
public import Linger.Display.View
public import Linger.Import.Resurrect
public import Linger.Selector.Picker
public import Linger.Display.Title
public import Linger.Os.Env
public import Linger.Session
public import Linger.Session.Buf
public import Linger.Session.Checkpoint
public import Linger.Session.Claim
public import Linger.Session.Driver
public import Linger.Session.Spec
public import Linger.Target.Name
public import Linger.Target.Remote
public import Linger.Target.Spec
public import Terminal.Mediation
public import Terminal.Render
public import Terminal.Replay
public import Terminal.Spec
public import Terminal.Title
import all Linger.App.Proofs.Answer
import all Linger.App.Proofs.Capture
import all Linger.App.Proofs.Commands
import all Linger.App.Proofs.Entry
import all Linger.App.Proofs.Recovery
import all Linger.App.Proofs.Wait
import Linger.Display.Proofs.Clean
import all Linger.Display.Proofs.Listing
import all Linger.Display.Proofs.Status
import all Linger.Display.Proofs.View
import all Linger.Import.Proofs.Resurrect
import Linger.Selector.Proofs.Frame
import all Linger.Selector.Proofs.Picker
import all Linger.Display.Proofs.Title
import all Linger.Os.Proofs.Env
import all Os.Proofs.Wait
import Linger.Target.Proofs.Name
import Linger.Target.Proofs.Remote
import all Linger.Session.Proofs.Buf
import all Linger.Session.Proofs.Checkpoint
import all Linger.Session.Proofs.Claim
import all Linger.Session.Proofs.Driver
import all Linger.Session.Proofs.Record
import all Linger.Session.Proofs.Session
import all Linger.Session.Proofs.Start
import all Linger.Session.Proofs.Wire
public import Linger.Session.Record
public import Linger.Session.Wire
public import Linger.Session.Start
import all Terminal.Vt
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

/-! # Proofs of the headline theorems and their kills

`Challenge.lean` states these theorems; each proof here cites the component theorems it
restates. `./lake comparator` checks that the statements match. -/

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

theorem one_owner (grant : Claim.State → Nat → Nat → Bool) (exclusive : Claim.Exclusive grant)
    {s : Claim.State} (reached : Claim.Reachable grant Claim.enters s) {a b resource : Nat}
    {left right : Claim.Lease} (ha : s.active a = some left) (hb : s.active b = some right)
    (leftUses : left.Uses resource) (rightUses : right.Uses resource) : a = b :=
  Claim.at_most_one_owner exclusive reached ha hb leftUses rightUses

theorem one_owner_rejects_socket :
    ¬∀ (grant : Claim.State → Nat → Nat → Bool),
        Claim.Exclusive grant →
          ∀ {s : Claim.State},
            Claim.Reachable grant (fun (socket _ : Bool) => socket) s →
              ∀ {a b resource : Nat} {left right : Claim.Lease},
                s.active a = some left →
                  s.active b = some right → left.Uses resource → right.Uses resource → a = b := by
  intro h
  -- the operating system grants every free lock, and only a free one
  let grant : Claim.State → Nat → Nat → Bool := fun s _ resource => s.locks resource == none
  have exclusive : Claim.Exclusive grant := fun s _ resource granted => by
    simpa [grant] using granted
  -- process 1 takes socket 1 and acts on lease (1, 3); process 2 takes socket 2 and checkpoint 3
  let s1 : Claim.State := { Claim.initial with locks := Claim.put Claim.initial.locks 1 (some 1) }
  let s2 : Claim.State := { s1 with active := Claim.put s1.active 1 (some ⟨1, 3⟩) }
  let s3 : Claim.State := { s2 with locks := Claim.put s2.locks 2 (some 2) }
  let s4 : Claim.State := { s3 with locks := Claim.put s3.locks 3 (some 2) }
  let s5 : Claim.State := { s4 with active := Claim.put s4.active 2 (some ⟨2, 3⟩) }
  have reached : Claim.Reachable grant (fun (socket _ : Bool) => socket) s5 :=
    ((((Claim.Reachable.initial.next (.acquire _ 1 1 rfl)).next (.enter _ 1 ⟨1, 3⟩ rfl rfl)).next
              (.acquire _ 2 2 rfl)).next
          (.acquire _ 2 3 rfl)).next
      (.enter _ 2 ⟨2, 3⟩ rfl rfl)
  have same := @h grant exclusive s5 reached 1 2 3 ⟨1, 3⟩ ⟨2, 3⟩ rfl rfl (.inr rfl) (.inr rfl)
  exact absurd same (by decide)

theorem step_labels_requested (s : State) (ev : Event)
    (changed : (Session.step s ev).1.labelList ≠ s.labelList) :
    ∃ id chunk c,
      ev = .bytes id chunk ∧
        s.client? id = some c ∧
        (c.attached = false ∨ c.mode = .writable) ∧
        ∃ m ∈ (c.decoder.feed chunk).2, m.ChangesLabels := Session.step_labels_sources s ev changed

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
  intro h
  obtain ⟨-, -, -, -, labelled, -⟩ := Session.boot_observed (Vt.Vt.init 1 1) [("a", "b")] []
  obtain ⟨-, -, -, -, emptied, -⟩ :=
    Session.boot_observed (State.boot (Vt.Vt.init 1 1) [("a", "b")] []).terminal [] []
  have changed :
    (State.boot (State.boot (Vt.Vt.init 1 1) [("a", "b")] []).terminal [] []).labelList ≠
      (State.boot (Vt.Vt.init 1 1) [("a", "b")] []).labelList := by
    rw [emptied, labelled]
    simp [maxLabels]
  obtain ⟨_, _, _, ticked, -⟩ := h (State.boot (Vt.Vt.init 1 1) [("a", "b")] []) (.tick 0) changed
  cases ticked

theorem infoFields_boot (vt : Vt.Vt) (labels metadata : List (String × String)) (evs : List Event) :
    ∃ rest,
      Session.infoFields (Session.trace Session.step (State.boot vt labels metadata) evs).1 =
        metadata ++ rest := by
  rw [Session.trace_step]
  exact Session.run_boot_infoFields vt labels metadata evs

theorem infoFields_boot_rejects_reboot :
    ¬∀ (vt : Vt.Vt) (labels metadata : List (String × String)) (evs : List Event),
        ∃ rest,
          Session.infoFields
              (Session.trace
                  (fun (_ : State) (_ : Event) =>
                    (State.boot (Vt.Vt.init 1 1) [] [], ([] : List (Effect Replay.Plan))))
                  (State.boot vt labels metadata) evs).1 =
            metadata ++ rest := by
  intro h
  obtain ⟨rest, named⟩ := h (Vt.Vt.init 1 1) [] [("name", "a")] [.tick 0]
  obtain ⟨tail, counted⟩ := Session.infoFields_metaKv (State.boot (Vt.Vt.init 1 1) [] [])
  have booted :
    (Session.trace
          (fun (_ : State) (_ : Event) =>
            (State.boot (Vt.Vt.init 1 1) [] [], ([] : List (Effect Replay.Plan))))
          (State.boot (Vt.Vt.init 1 1) [] [("name", "a")]) [.tick 0]).1 =
      State.boot (Vt.Vt.init 1 1) [] [] :=
    rfl
  rw [booted, counted, Session.boot_metaKv] at named
  simp at named

theorem step_terminal_sources (s : State) (ev : Event) :
    (∃ chunk, ev = .ptyOut chunk ∧ (Session.step s ev).1.terminal = s.terminal.feed chunk) ∨
      ∃ sizes : List (Nat × Nat),
        (Session.step s ev).1.terminal =
          sizes.foldl (fun v (size : Nat × Nat) => v.resize size.1 size.2) s.terminal :=
  Session.step_vt_sources s ev

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
  intro h
  obtain ⟨-, -, kept, -, -, -⟩ := Session.boot_observed (Vt.Vt.init 2 1) [] []
  obtain ⟨-, -, printed, -, -, -⟩ :=
    Session.boot_observed ((State.boot (Vt.Vt.init 2 1) [] []).terminal.feed [0x41]) [] []
  rcases h (State.boot (Vt.Vt.init 2 1) [] []) (.tick 0) with ⟨_, ticked, -⟩ | ⟨sizes, resized⟩
  · cases ticked
  · change
      (State.boot ((State.boot (Vt.Vt.init 2 1) [] []).terminal.feed [0x41]) [] []).terminal =
        _ at resized
    rw [printed, kept] at resized
    have moved : ((Vt.Vt.init 2 1).feed [0x41]).cursorPos = (1, 0) := by decide +kernel
    rw [resized, Session.foldl_resize_origin _ (by decide +kernel)] at moved
    simp at moved

theorem start_plan (live saved : Bool) :
    Start.plan live saved = if live then .running else if saved then .saved else .take :=
  Start.plan_eq live saved

theorem start_plan_rejects_take :
    ¬∀ (live saved : Bool),
        (fun (_ _ : Bool) => Start.Plan.take) live saved =
          if live then .running else if saved then .saved else .take := by
  intro h
  cases h true false

theorem run_bytes_isolates (s : State) (id : Nat) (chunks : List (List UInt8)) {other : Nat}
    (h : other ≠ id) :
    (Session.trace Session.step s (chunks.map (Event.bytes id))).1.client? other =
      s.client? other := by
  rw [Session.trace_step]
  exact Session.run_bytes_isolates s id chunks h

theorem run_bytes_isolates_rejects_reset :
    ¬∀ (s : State) (id : Nat) (chunks : List (List UInt8)) {other : Nat},
        other ≠ id →
          (Session.trace
                  (fun _ _ => (State.boot (Vt.Vt.init 1 1) [] [], ([] : List (Effect Replay.Plan))))
                  s (chunks.map (Event.bytes id))).1.client?
              other =
            s.client? other := by
  intro h
  obtain ⟨joined, empty⟩ := Session.connected_client_witness
  have forgot :=
    @h (Session.trace Session.step (State.boot (Vt.Vt.init 1 1) [] []) [.connected 1]).1 0 [[]] 1
      (by decide)
  have reset :
    (Session.trace
          (fun _ _ => (State.boot (Vt.Vt.init 1 1) [] [], ([] : List (Effect Replay.Plan))))
          (Session.trace Session.step (State.boot (Vt.Vt.init 1 1) [] []) [.connected 1]).1
          ([[]].map (Event.bytes 0))).1 =
      State.boot (Vt.Vt.init 1 1) [] [] :=
    rfl
  rw [reset, empty, joined] at forgot
  cases forgot

theorem run_readonly (s : State) (id : Nat) (chunks : List (List UInt8)) {c : Client}
    (hc : s.client? id = some c) (attached : c.attached = true) (watcher : c.mode = .readOnly) :
    (Session.trace Session.step s (chunks.map (Event.bytes id))).1.terminal = s.terminal ∧
      (Session.trace Session.step s (chunks.map (Event.bytes id))).1.labelList = s.labelList ∧
      ∀ eff ∈ (Session.trace Session.step s (chunks.map (Event.bytes id))).2,
        (∃ m, eff = .send id m) ∨ eff = .close id ∨ eff = .checkpoint := by
  rw [Session.trace_step]
  exact Session.run_readonly s id chunks hc attached watcher

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
  intro h
  obtain ⟨-, -, effects⟩ :=
    @h (State.boot (Vt.Vt.init 1 1) [] []) 0 [[]] { id := 0, attached := true, mode := .readOnly }
      rfl rfl rfl
  rcases effects .stopProgram (by simp [Session.trace]) with ⟨_, sent⟩ | closed | saved
  · cases sent
  · cases closed
  · cases saved

theorem step_attach_mode (s : State) (id : Nat) (chunk : List UInt8) {c : Client}
    {dec : Wire.Decoder} {mode : Mode} {cols rows : UInt32} (hc : s.client? id = some c)
    (fresh : c.attached = false) (read : c.decoder.feed chunk = (dec, [.attach mode cols rows]))
    (healthy : dec.errored = false) :
    ∃ c',
      (Session.step s (.bytes id chunk)).1.client? id = some c' ∧
        c'.attached = true ∧ c'.mode = mode :=
  Session.step_attach_mode s id chunk hc fresh read healthy

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
  intro h
  -- a writable attach from a terminal with no size: today's rule would make it read-only
  obtain ⟨joined, -⟩ := Session.connected_client_witness
  obtain ⟨c', seen, -, writable⟩ :=
    @h (Session.trace Session.step (State.boot (Vt.Vt.init 1 1) [] []) [.connected 1]).1 1
      (Wire.encode (.attach .writable 0 0)) { id := 1 } {} .writable 0 0 (by simp [joined]) rfl
      (Session.feed_encode_fresh (.attach .writable 0 0) trivial) rfl
  dsimp only at seen
  rw [Session.step_attach_record joined rfl (Session.feed_encode_fresh _ trivial) rfl] at seen
  simp only [Option.map_some, Option.some.injEq] at seen
  rw [← seen] at writable
  simp at writable

theorem step_resize_mode (s : State) (id : Nat) (chunk : List UInt8) {c : Client}
    {dec : Wire.Decoder} {sizes : List (UInt32 × UInt32)} (hc : s.client? id = some c)
    (read : c.decoder.feed chunk = (dec, sizes.map fun size => .resize size.1 size.2))
    (healthy : dec.errored = false) :
    ((Session.step s (.bytes id chunk)).1.client? id).map (·.mode) = some c.mode :=
  Session.step_resize_mode s id chunk hc read healthy

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
  intro h
  -- a writable client at 80×24 whose terminal loses its size: today's rule would drop its typing
  have joined := Session.attached_client_witness
  have kept :=
    @h
      (Session.trace Session.step (State.boot (Vt.Vt.init 1 1) [] [])
          [.connected 1, .bytes 1 (Wire.encode (.attach .writable 80 24))]).1
      1 (Wire.encode (.resize 0 0)) { id := 1, attached := true, cols := 80, rows := 24 } {}
      [(0, 0)] (by simp [joined]) (Session.feed_encode_fresh (.resize 0 0) trivial) rfl
  dsimp only at kept
  rw [Session.step_resize_record joined rfl (Session.feed_encode_fresh (.resize 0 0) trivial)
      rfl] at kept
  simp at kept

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
                cols.toNat = Vt.clampDim width.toNat ∧ rows.toNat = Vt.clampDim height.toNat :=
  Session.step_resizes_sized s ev cols rows resized

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
  intro h
  have zero := h (State.boot (Vt.Vt.init 1 1) [] []) (.tick 0) 0 0 (by simp)
  exact absurd zero.1 (by decide)

theorem remotesFile_home (home : Option String) :
    Os.Env.remotesFile home = none ↔ home = none ∨ home = some "" :=
  Os.Env.remotesFile_eq_none_iff home

theorem remotesFile_home_rejects_shared :
    ¬∀ (home : Option String),
        (fun (_ : Option String) => some "remotes") home = none ↔ home = none ∨ home = some "" := by
  intro h
  exact absurd ((h none).mpr (.inl rfl)) (by simp)

theorem rowFields_name (socketName : String) (info : List (String × String)) :
    (Listing.rowFields socketName info).lookup "name" = some socketName :=
  Listing.rowFields_name socketName info

theorem rowFields_name_rejects_reply :
    ¬∀ (socketName : String) (info : List (String × String)),
        ((fun (_ : String) (info : List (String × String)) => info) socketName info).lookup "name" =
          some socketName := by
  intro h
  exact absurd (h "s" []) (by simp)

theorem picker_attach_listed (s : Selector.Picker.State) (key : Selector.Key) (target : String)
    (h : Selector.Picker.step s key = .attach target) : target ∈ s.candidates :=
  (Selector.Picker.step_attach_mem s key target h).1

theorem picker_attach_listed_rejects_fixed :
    ¬∀ (s : Selector.Picker.State) (key : Selector.Key) (target : String),
        (fun (_ : Selector.Picker.State) (_ : Selector.Key) => Selector.Picker.Outcome.attach "s") s
              key =
            .attach target →
          target ∈ s.candidates := by
  intro h
  exact absurd (h { candidates := [] } .accept "s" rfl) (by simp)

theorem picker_create_new (s : Selector.Picker.State) (key : Selector.Key) (target : String)
    (h : Selector.Picker.step s key = .create target) :
    target ∉ s.candidates ∧ target ≠ "" ∧ Name.Valid ((target.splitOn "@").headD "") := by
  obtain ⟨-, absent, nonempty, -, valid, -⟩ := Selector.Picker.step_create_valid s key target h
  exact ⟨absent, nonempty, valid⟩

theorem picker_create_new_rejects_empty :
    ¬∀ (s : Selector.Picker.State) (key : Selector.Key) (target : String),
        (fun (_ : Selector.Picker.State) (_ : Selector.Key) => Selector.Picker.Outcome.create "") s
              key =
            .create target →
          target ∉ s.candidates ∧ target ≠ "" ∧ Name.Valid ((target.splitOn "@").headD "") := by
  intro h
  exact absurd (h { candidates := [] } .accept "" rfl).2.1 (by simp)

theorem route_exact (args : List String) :
    App.Entry.route args =
      if args.head? = some Remote.marker then
        match Remote.decode args.tail with
        | some argv => App.Entry.Route.of argv
        | none => .malformed
      else App.Entry.Route.of args := App.Entry.route_eq args

theorem route_exact_rejects_selector :
    ¬∀ (args : List String),
        (fun (args : List String) => App.Entry.Route.session args) args =
          if args.head? = some Remote.marker then
            match Remote.decode args.tail with
            | some argv => App.Entry.Route.of argv
            | none => .malformed
          else App.Entry.Route.of args := by
  intro h
  exact absurd (h ["attach"]) (by simp [App.Entry.Route.of, Remote.marker])

theorem lookup_table :
    (App.Commands.table.flatMap fun command => command.word :: command.aliases).Nodup ∧
      ∀ command ∈ App.Commands.table,
        App.Commands.lookup command.word = some command ∧
          ∀ word ∈ command.aliases, App.Commands.lookup word = some command :=
  ⟨App.Commands.table_words_nodup, fun command member =>
    ⟨App.Commands.lookup_word command member, App.Commands.lookup_alias command member⟩⟩

theorem lookup_table_rejects_none :
    ¬((App.Commands.table.flatMap fun command => command.word :: command.aliases).Nodup ∧
        ∀ command ∈ App.Commands.table,
          (fun (_ : String) => (none : Option App.Commands.Command)) command.word = some command ∧
            ∀ word ∈ command.aliases,
              (fun (_ : String) => (none : Option App.Commands.Command)) word = some command) := by
  intro h
  obtain ⟨command, member⟩ := List.exists_mem_of_ne_nil _ App.Commands.table_ne_nil
  exact absurd (h.2 command member).1 (by simp)

theorem retired_free : ∀ entry ∈ App.Commands.retired, App.Commands.lookup entry.1 = none :=
  App.Commands.retired_free

theorem retired_free_rejects_any :
    ¬∀ entry ∈ App.Commands.retired,
        (fun (_ : String) =>
              some ({ word := "run", args := "", summary := "" } : App.Commands.Command))
            entry.1 =
          none := by
  intro h
  obtain ⟨entry, member⟩ := List.exists_mem_of_ne_nil _ App.Commands.retired_ne_nil
  exact absurd (h entry member) (by simp)

theorem usageLine_exact (command : App.Commands.Command) :
    App.Commands.usageLine command =
      if command.args.isEmpty then s!"usage: linger {command.word}"
      else s!"usage: linger {command.word} {command.args}" := App.Commands.usageLine_eq command

theorem usageLine_exact_rejects_bare :
    ¬∀ (command : App.Commands.Command),
        (fun (_ : App.Commands.Command) => "usage: linger") command =
          if command.args.isEmpty then s!"usage: linger {command.word}"
          else s!"usage: linger {command.word} {command.args}" := by
  intro h
  exact absurd (h { word := "help", args := "", summary := "" }) (by decide)

theorem plan_exact (existing : List String) (panes : List Import.Resurrect.Pane)
    (pane : Import.Resurrect.Pane) :
    pane ∈ Import.Resurrect.plan existing panes ↔ pane ∈ panes ∧ pane.name ∉ existing :=
  Import.Resurrect.mem_plan existing panes pane

theorem plan_exact_rejects_all :
    ¬∀ (existing : List String) (panes : List Import.Resurrect.Pane) (pane : Import.Resurrect.Pane),
        pane ∈
            (fun (_ : List String) (panes : List Import.Resurrect.Pane) => panes) existing panes ↔
          pane ∈ panes ∧ pane.name ∉ existing := by
  intro h
  have kept :=
    (h ["a"] [{ name := "a", dir := "", line := 0 }] { name := "a", dir := "", line := 0 }).mp
      (by simp)
  exact absurd kept.2 (by simp)

theorem plan_again_empty (existing : List String) (panes made : List Import.Resurrect.Pane)
    (first : made = Import.Resurrect.plan existing panes) :
    Import.Resurrect.plan (existing ++ made.map (·.name)) panes = [] := by
  rw [first]
  exact Import.Resurrect.plan_sequential_idempotent existing panes

theorem plan_again_empty_rejects_all :
    ¬∀ (existing : List String) (panes made : List Import.Resurrect.Pane),
        made =
            (fun (_ : List String) (panes : List Import.Resurrect.Pane) => panes) existing panes →
          (fun (_ : List String) (panes : List Import.Resurrect.Pane) => panes)
              (existing ++ made.map (·.name)) panes =
            [] := by
  intro h
  exact absurd (h [] [{ name := "a", dir := "", line := 0 }] _ rfl) (by simp)

theorem check_eq_some_iff (s result : String) :
    Name.check s = some result ↔ result = s ∧ Name.Valid s := Name.check_eq_some_iff s result

theorem check_eq_some_iff_rejects_any :
    ¬∀ (s result : String), (fun s => some s) s = some result ↔ result = s ∧ Name.Valid s := by
  intro h
  exact absurd ((h "" "").mp rfl).2.1 (by simp)

theorem command_exact (split : String → List String) (literal : Remote.Shell.Literal split)
    (verb : String) (words : List String) :
    ∃ args,
      split (Remote.command verb words) = "linger" :: args ∧
        App.Entry.route args = App.Entry.Route.of (verb :: words) := by
  obtain ⟨encoded, received, decoded⟩ := Remote.command_decode split literal verb words
  exact ⟨Remote.marker :: encoded, received, App.Entry.route_encoded encoded _ decoded⟩

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
  intro h
  -- fish keeps the world claim, and reads POSIX quoting of `send \'` as `send ''`
  obtain ⟨args, received, routed⟩ := h Remote.fishSplit Remote.fishSplit_literal "send" ["\\'"]
  dsimp only at received
  rw [Remote.fishSplit_quoted] at received
  simp only [List.cons.injEq, true_and] at received
  subst received
  rw [App.Entry.route_eq] at routed
  simp [App.Entry.Route.of, Remote.marker] at routed

theorem check_no_alias (a b name : String) (ha : Name.check a = some name)
    (hb : Name.check b = some name) : a = b := Name.check_no_alias ha hb

theorem check_no_alias_rejects_fold :
    ¬∀ (a b name : String),
        (fun (_ : String) => some "s") a = some name →
          (fun (_ : String) => some "s") b = some name → a = b := by
  intro h
  exact absurd (h "a" "b" "s" rfl rfl) (by decide)

theorem targetArgs_targetOperands (name : String) (rest : List String) :
    Remote.targetArgs (Remote.targetOperands name ++ rest) = some (name, rest) :=
  Remote.targetArgs_targetOperands name rest

theorem targetArgs_targetOperands_rejects_none :
    ¬∀ (name : String) (rest : List String),
        Remote.targetArgs ((fun (_ : String) => ([] : List String)) name ++ rest) =
          some (name, rest) := by
  intro h
  have read := h "s" []
  simp [Remote.targetArgs_nil] at read

theorem checkHosts_ok_iff (hosts result : List String) :
    Remote.checkHosts hosts = .ok result ↔
      result = hosts ∧ hosts.Nodup ∧ ∀ x ∈ hosts, Remote.hostClean x = true :=
  Remote.checkHosts_ok_iff hosts result

theorem checkHosts_ok_iff_rejects_any :
    ¬∀ (hosts result : List String),
        (fun (hosts : List String) => (.ok hosts : Except String (List String))) hosts =
            .ok result ↔
          result = hosts ∧ hosts.Nodup ∧ ∀ x ∈ hosts, Remote.hostClean x = true := by
  intro h
  have twice := ((h ["a", "a"] ["a", "a"]).mp rfl).2.1
  simp at twice

theorem detach_key (flag : Option String) :
    Os.Env.detachEnabled true flag = true ∧ Os.Env.detachEnabled false flag = flag.isNone :=
  ⟨Os.Env.detachEnabled_readOnly flag, Os.Env.detachEnabled_writable flag⟩

theorem detach_key_rejects_never :
    ¬∀ (flag : Option String),
        (fun (_ : Bool) (_ : Option String) => false) true flag = true ∧
          (fun (_ : Bool) (_ : Option String) => false) false flag = flag.isNone := by
  intro h
  exact absurd (h none).1 (by decide)

theorem resumeDir_where (home : Option String) (saved dir : String) (set : dir ≠ "") :
    Os.Env.resumeDir home saved true = some saved ∧
      Os.Env.resumeDir (some dir) saved false = some dir ∧
      Os.Env.resumeDir none saved false = none ∧ Os.Env.resumeDir (some "") saved false = none :=
  ⟨Os.Env.resumeDir_saved home saved, Os.Env.resumeDir_home set saved,
    (Os.Env.resumeDir_absent saved).1, (Os.Env.resumeDir_absent saved).2⟩

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
  intro h
  exact absurd (h none "a" "b" (by decide)).2.1 (by decide)

theorem failureStatus_exact (why : String) :
    Start.failureStatus (.directory why) = 125 ∧
      Start.failureStatus (.notFound why) = 127 ∧
      Start.failureStatus (.notRunnable why) = 126 := Start.failureStatus_exact why

theorem failureStatus_exact_rejects_alike :
    ¬∀ (why : String),
        (fun (_ : Spawn.Failure) => (1 : UInt8)) (.directory why) = 125 ∧
          (fun (_ : Spawn.Failure) => (1 : UInt8)) (.notFound why) = 127 ∧
          (fun (_ : Spawn.Failure) => (1 : UInt8)) (.notRunnable why) = 126 := by
  intro h
  exact absurd (h "").1 (by decide)

theorem metadata_dirs (name pid created cmd dir : String) (saved : Option String) :
    ("start_dir", dir) ∈ Start.metadata name pid created cmd dir saved ∧
      ∀ d,
        ("saved_dir", d) ∈ Start.metadata name pid created cmd dir saved ↔
          saved = some d ∧ d ≠ dir := Start.metadata_dirs name pid created cmd dir saved

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
  intro h
  have moved := ((h "" "" "" "" "b" (some "a")).2 "a").2 ⟨rfl, by decide⟩
  simp at moved

theorem programOf_exact (shell : String) (argv : List String) :
    Start.programOf shell argv = (argv.headD shell, (argv.drop 1).toArray) :=
  Start.programOf_exact shell argv

theorem programOf_exact_rejects_shell :
    ¬∀ (shell : String) (argv : List String),
        (fun (shell : String) (argv : List String) => (shell, #["-c", String.intercalate " " argv]))
            shell argv =
          (argv.headD shell, (argv.drop 1).toArray) := by
  intro h
  exact absurd (congrArg Prod.fst (h "sh" ["ls"])) (by decide)

theorem shellOf_choice (shell : String) (set : shell ≠ "") :
    Os.Env.shellOf (some shell) = shell ∧
      Os.Env.shellOf none = "sh" ∧ Os.Env.shellOf (some "") = "sh" :=
  ⟨Os.Env.shellOf_set set, Os.Env.shellOf_absent.1, Os.Env.shellOf_absent.2⟩

theorem shellOf_choice_rejects_fixed :
    ¬∀ (shell : String),
        shell ≠ "" →
          (fun (_ : Option String) => "sh") (some shell) = shell ∧
            (fun (_ : Option String) => "sh") none = "sh" ∧
            (fun (_ : Option String) => "sh") (some "") = "sh" := by
  intro h
  exact absurd (h "fish" (by decide)).1 (by decide)

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
  obtain ⟨hargv, hdir, henv⟩ := runs _ _ _ _ _ _ ok
  rw [Start.programOf_exact] at hargv
  refine ⟨by simpa using hargv, hdir, ?_, ?_, ?_, ?_, fun key hkey => ?_⟩
  all_goals rw [henv, Start.environment_lookup]
  · simp
  · simp
  · simp
  · simp
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hkey
    simp [hkey.1, hkey.2.1, hkey.2.2.1, hkey.2.2.2]

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
  intro h
  have runs :
    Spawn.Runs (fun _ => none) fun dir prog args extra _ =>
      some
        { argv := prog :: args.toList, dir,
          env := fun key => (extra.reverse.lookup key).orElse fun _ => none,
          ignored := fun _ => false, blocked := fun _ => false, descriptor := fun _ => none } := by
    intro dir prog args extra reset started hs
    cases hs
    exact ⟨rfl, rfl, fun _ => rfl⟩
  exact absurd (h _ _ runs "x" "" "sh" [] rfl).2.2.1 (by simp)

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
  obtain ⟨terminal, ignored, blocked, closed⟩ := clean _ _ _ _ _ _ ok
  obtain ⟨dispositions, mask, descriptors⟩ := Start.reset_clean
  refine ⟨ignored dispositions, blocked mask, fun fd => ?_⟩
  by_cases low : fd < 3
  · rw [ite_eq_left low]
    exact terminal fd low
  · rw [ite_eq_right low]
    exact closed descriptors fd (Nat.le_of_not_lt low)

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
  intro h
  -- a start that leaves every signal ignored unless it is asked to reset them
  have clean :
    Spawn.Clean fun _ _ _ _ reset =>
      some
        { argv := [], dir := "", env := fun _ => none, ignored := fun _ => !reset.dispositions,
          blocked := fun _ => false,
          descriptor := fun fd => if fd < 3 then some .terminal else none } := by
    intro dir prog args extra reset started hs
    cases hs
    refine ⟨fun fd low => ite_eq_left low, fun asked _ => by simp [asked], fun _ _ => rfl, ?_⟩
    exact fun _ fd high => ite_eq_right (Nat.not_lt_of_le high)
  exact absurd ((h _ clean "x" "" "sh" [] rfl).1 2) (by simp)

theorem step_kill_stops (s : State) (id : Nat) (chunk : List UInt8) {c : Client}
    {dec : Wire.Decoder} {rest : List Wire.Msg} (hc : s.client? id = some c)
    (writable : c.mode = .writable) (read : c.decoder.feed chunk = (dec, .kill :: rest))
    (healthy : dec.errored = false) :
    (Session.step s (.bytes id chunk)).2 = [.stopProgram, .close id] ∧
      (Session.step s (.bytes id chunk)).1.terminal = s.terminal ∧
      (Session.step s (.bytes id chunk)).1.labelList = s.labelList :=
  Session.step_kill_stops s id chunk hc writable read healthy

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
  intro h
  obtain ⟨joined, -⟩ := Session.connected_client_witness
  have stopped :=
    (@h (Session.trace Session.step (State.boot (Vt.Vt.init 1 1) [] []) [.connected 1]).1 1
        (Wire.encode .kill) { id := 1 } {} [] joined rfl
        (Session.feed_encode_fresh .kill (by simp [Wire.Msg.Fits])) rfl).1
  simp at stopped

theorem step_ended_reports (s : State) (ev : Event) :
    (Effect.exit ∈ (Session.step s ev).2 ↔ ev.ends.isSome) ∧
      ∀ e keep,
        ev.ends = some (e, keep) →
          ∃ front,
            (Session.step s ev).2 =
                front ++
                  [.record e.record, if keep then Effect.checkpoint else Effect.dropCheckpoint,
                    .exit] ∧
              Effect.checkpoint ∉ front ∧
              Effect.dropCheckpoint ∉ front ∧
              (∀ c ∈ s.roster,
                c.attached = true ∨ c.waiting = true → e.told.map (Effect.send c.id) <:+: front) ∧
              (Session.step s ev).1.terminal = s.terminal := Session.step_ended_reports s ev

theorem step_ended_reports_rejects_status :
    ¬∀ (s : State) (ev : Event),
        (Effect.exit ∈
              ((fun s _ =>
                    (s,
                      ([.send 0 (.exited 1), .record (.ended .unknown), .checkpoint, .exit] :
                        List (Effect Replay.Plan))))
                  s ev).2 ↔
            ev.ends.isSome) ∧
          ∀ e keep,
            ev.ends = some (e, keep) →
              ∃ front,
                ((fun s _ =>
                          (s,
                            ([.send 0 (.exited 1), .record (.ended .unknown), .checkpoint, .exit] :
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
                            ([.send 0 (.exited 1), .record (.ended .unknown), .checkpoint, .exit] :
                              List (Effect Replay.Plan))))
                        s ev).1.terminal =
                    s.terminal := by
  intro h
  obtain ⟨front, effects, -, -, heard, -⟩ :=
    (h (State.boot (Vt.Vt.init 1 1) [] []) (.childExited .unknown)).2 (.program .unknown) true rfl
  have only :
    [Effect.send 0 (.exited 1)] ++ [.record (.ended .unknown), .checkpoint, .exit] =
      front ++ [.record (.ended .unknown), .checkpoint, .exit] :=
    effects
  rw [← List.append_cancel_right only] at heard
  -- the ending's two messages cannot fit in the one the wrong daemon sends
  have short := (heard { id := 0, attached := true } (by simp) (.inl rfl)).length_le
  simp [Ending.told] at short

theorem step_signal_saves (s : State) (n : UInt8) :
    ∃ front,
      (Session.step s (.signal n)).2 =
          .stopProgram :: front ++ [.record (.saved n), .checkpoint, .exit] ∧
        Effect.dropCheckpoint ∉ front ∧
        (∀ c ∈ s.roster,
          c.attached = true ∨ c.waiting = true → Effect.send c.id (.saved n) ∈ front) ∧
        (Session.step s (.signal n)).1.terminal = s.terminal := Session.step_signal_saves s n

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
  intro h
  obtain ⟨front, effects, -⟩ := h (State.boot (Vt.Vt.init 1 1) [] []) 15
  have short := congrArg List.length effects
  simp only [List.length_cons, List.length_append, List.length_nil] at short
  have empty : front = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst empty
  simp at effects

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
  intro h
  obtain ⟨front, effects, -, heard, -⟩ := h (State.boot (Vt.Vt.init 1 1) [] []) 15
  have short := congrArg List.length effects
  simp only [List.length_cons, List.length_append, List.length_nil] at short
  have empty : front = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst empty
  simpa using heard { id := 0, attached := true } (by simp) (.inl rfl)

theorem step_stopped_discards (s : State) (o : Outcome) :
    (∃ front,
        (Session.step s (.stopped o)).2 = front ++ [.dropCheckpoint, .exit] ∧
          Effect.checkpoint ∉ front) ∧
      (Session.step s (.stopped o)).1.terminal = s.terminal := Session.step_stopped_discards s o

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
  intro h
  obtain ⟨⟨front, effects, unsaved⟩, -⟩ := h (State.boot (Vt.Vt.init 1 1) [] []) .unknown
  have saved :
    [Effect.checkpoint] ++ [.dropCheckpoint, .exit] = front ++ [.dropCheckpoint, .exit] := effects
  rw [← List.append_cancel_right saved] at unsaved
  exact unsaved (List.mem_singleton_self _)

theorem step_childExited_keeps (s : State) (o : Outcome) :
    (∃ front,
        (Session.step s (.childExited o)).2 = front ++ [.checkpoint, .exit] ∧
          Effect.dropCheckpoint ∉ front) ∧
      (Session.step s (.childExited o)).1.terminal = s.terminal :=
  Session.step_childExited_keeps s o

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
  intro h
  obtain ⟨⟨front, effects, kept⟩, -⟩ := h (State.boot (Vt.Vt.init 1 1) [] []) .unknown
  have dropped : [Effect.dropCheckpoint] ++ [.checkpoint, .exit] = front ++ [.checkpoint, .exit] :=
    effects
  rw [← List.append_cancel_right dropped] at kept
  exact kept (List.mem_singleton_self _)

theorem record_answer (afterSave : List UInt8 → Option (List UInt8)) (kept : Record.Kept afterSave)
    (o : Outcome) (n : UInt8) (seen : Option Seen) (file : Option (List UInt8)) :
    Record.answer (afterSave (Record.encode (.ended o))) = some (.program o) ∧
      Record.answer (afterSave (Record.encode (.saved n))) = some (.saved n) ∧
      Record.answer (afterSave (Record.encode (.running seen))) = some (.program .unknown) ∧
      (Record.answer file).isSome = file.isSome := by
  rw [kept, kept, kept]
  exact
    ⟨Record.answer_ended o, Record.answer_saved n, Record.answer_running seen,
      Record.answer_isSome file⟩

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
  intro h
  -- a file system that keeps every record whole, as the claim says
  exact absurd (h some (fun _ => rfl) (.exited 0) 15 none none).1 (by simp)

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
  intro h
  -- a daemon whose end records all say its program still runs, as one that a signal killed left
  have ended := (h some (fun _ => rfl) (.exited 0) 15 none none).1
  simp [Record.answer_running] at ended

theorem wait_ending (deadline heldSince : Option Nat) (now : Nat) (e : Ending) :
    App.Wait.decide deadline heldSince now (.ended e) = .answer (App.Answer.ofEnding e) ∧
      App.Wait.decide deadline heldSince now (.recorded (some e)) =
        .answer (App.Answer.ofEnding e) := App.Wait.wait_ending deadline heldSince now e

theorem wait_ending_rejects_failed :
    ¬∀ (deadline heldSince : Option Nat) (now : Nat) (e : Ending),
        (fun (_ _ : Option Nat) (_ : Nat) (_ : App.Wait.Heard) => App.Wait.Next.answer .failed)
              deadline heldSince now (.ended e) =
            .answer (App.Answer.ofEnding e) ∧
          (fun (_ _ : Option Nat) (_ : Nat) (_ : App.Wait.Heard) => App.Wait.Next.answer .failed)
              deadline heldSince now (.recorded (some e)) =
            .answer (App.Answer.ofEnding e) := by
  intro h
  have told := (h none none 0 (.program (.exited 0))).1
  simp [App.Answer.ofEnding, App.Answer.ofOutcome] at told

theorem wait_held (deadline heldSince : Option Nat) (now : Nat) (heard : App.Wait.Heard) :
    (App.Wait.decide deadline heldSince now heard = .answer .failed ↔
        heard = .ended (.program .unknown) ∨
          heard = .recorded (some (.program .unknown)) ∨
          heard = .held ∧ ∃ since, heldSince = some since ∧ since + App.Wait.heldNameMs ≤ now) ∧
      (heard = .held →
        (∀ due, deadline = some due → now < due) →
        (∀ since, heldSince = some since → now < since + App.Wait.heldNameMs) →
        App.Wait.decide deadline heldSince now heard = .again (some (heldSince.getD now))) :=
  App.Wait.wait_held deadline heldSince now heard

theorem wait_held_rejects_eager :
    ¬∀ (deadline heldSince : Option Nat) (now : Nat) (heard : App.Wait.Heard),
        ((fun (_ _ : Option Nat) (_ : Nat) (_ : App.Wait.Heard) => App.Wait.Next.answer .failed)
                deadline heldSince now heard =
              .answer .failed ↔
            heard = .ended (.program .unknown) ∨
              heard = .recorded (some (.program .unknown)) ∨
              heard = .held ∧ ∃ since, heldSince = some since ∧ since + App.Wait.heldNameMs ≤ now) ∧
          (heard = .held →
            (∀ due, deadline = some due → now < due) →
            (∀ since, heldSince = some since → now < since + App.Wait.heldNameMs) →
            (fun (_ _ : Option Nat) (_ : Nat) (_ : App.Wait.Heard) => App.Wait.Next.answer .failed)
                deadline heldSince now heard =
              .again (some (heldSince.getD now))) := by
  intro h
  have failed := ((h none none 0 .held).1).mp rfl
  simp at failed

theorem held_covers_ending :
    Session.drainTimeoutMs + (Session.ending.map (·.2)).sum ≤ App.Wait.heldNameMs :=
  App.Wait.held_covers_ending

theorem held_covers_ending_rejects_drain :
    ¬Session.drainTimeoutMs + (Session.ending.map (·.2)).sum ≤ Session.drainTimeoutMs := by decide

theorem code_documented (status : UInt32) :
    App.Answer.code .done = 0 ∧
      App.Answer.code .notDone = 1 ∧
      App.Answer.code .usage = 2 ∧
      App.Answer.code .timedOut = 124 ∧
      App.Answer.code .failed = 125 ∧
      App.Answer.code .cannotRun = 126 ∧
      App.Answer.code .notFound = 127 ∧
      App.Answer.code .interrupted = 130 ∧ App.Answer.code (.program status) = status :=
  App.Answer.code_documented status

theorem code_documented_rejects_zero :
    ¬∀ (status : UInt32),
        (fun (_ : App.Answer) => (0 : UInt32)) .done = 0 ∧
          (fun (_ : App.Answer) => (0 : UInt32)) .notDone = 1 ∧
          (fun (_ : App.Answer) => (0 : UInt32)) .usage = 2 ∧
          (fun (_ : App.Answer) => (0 : UInt32)) .timedOut = 124 ∧
          (fun (_ : App.Answer) => (0 : UInt32)) .failed = 125 ∧
          (fun (_ : App.Answer) => (0 : UInt32)) .cannotRun = 126 ∧
          (fun (_ : App.Answer) => (0 : UInt32)) .notFound = 127 ∧
          (fun (_ : App.Answer) => (0 : UInt32)) .interrupted = 130 ∧
          (fun (_ : App.Answer) => (0 : UInt32)) (.program status) = status := by
  intro h
  exact absurd (h 0).2.1 (by decide)

theorem listed_once : App.Answer.listed.Nodup ∧ ∀ a, a ∈ App.Answer.listed ↔ a.Own :=
  App.Answer.listed_once

theorem listed_once_rejects_empty :
    ¬(([] : List App.Answer).Nodup ∧ ∀ a, a ∈ ([] : List App.Answer) ↔ a.Own) := by
  intro h
  exact absurd ((h.2 .done).mpr trivial) List.not_mem_nil

theorem outcomeFields_injective (o₁ o₂ : Outcome)
    (h : Session.outcomeFields o₁ = Session.outcomeFields o₂) : o₁ = o₂ :=
  Session.outcomeFields_injective h

theorem outcomeFields_injective_rejects_silence :
    ¬∀ (o₁ o₂ : Outcome),
        (fun (_ : Outcome) => ([] : List (String × String))) o₁ =
            (fun (_ : Outcome) => ([] : List (String × String))) o₂ →
          o₁ = o₂ := by
  intro h
  exact absurd (h (.exited 0) .unknown rfl) (by simp)

theorem endingFields_injective (e₁ e₂ : Ending)
    (h : Session.endingFields e₁ = Session.endingFields e₂) : e₁ = e₂ :=
  Session.endingFields_injective h

theorem endingFields_injective_rejects_unknown :
    ¬∀ (e₁ e₂ : Ending),
        (fun (e : Ending) => Session.endingFields (if e = .saved 15 then .program .unknown else e))
              e₁ =
            (fun (e : Ending) =>
                Session.endingFields (if e = .saved 15 then .program .unknown else e))
              e₂ →
          e₁ = e₂ := by
  intro h
  -- a reader that hears a saved session as one whose program's ending is unknown
  have same := h (.saved 15) (.program .unknown) (by simp)
  cases same

theorem infoFields_protocol (s : State) :
    ("protocol", toString Wire.protocol) ∈ Session.infoFields s := (Session.infoFields_protocol s).1

theorem infoFields_protocol_rejects_empty :
    ¬∀ (s : State),
        ("protocol", toString Wire.protocol) ∈
          (fun (_ : State) => ([] : List (String × String))) s := by
  intro h
  exact absurd (h (State.boot (Vt.Vt.init 1 1) [] [])) (by simp)

theorem admits_level (level : Option Nat) :
    Wire.admits level = true ↔ level = some Wire.protocol := Wire.admits_iff level

theorem admits_level_rejects_any :
    ¬∀ (level : Option Nat),
        (fun (_ : Option Nat) => true) level = true ↔ level = some Wire.protocol := by
  intro h
  cases (h none).1 rfl

theorem step_unknown_refused (s : State) (id : Nat) (chunk : List UInt8) {c : Client}
    {dec : Wire.Decoder} {tag : UInt8} {payload : List UInt8} (hc : s.client? id = some c)
    (read : c.decoder.feed chunk = (dec, [.unknown tag payload])) (healthy : dec.errored = false) :
    (Session.step s (.bytes id chunk)).2 = [.send id (.err "unknown message".toUTF8.toList)] ∧
      (Session.step s (.bytes id chunk)).1.terminal = s.terminal ∧
      (Session.step s (.bytes id chunk)).1.labelList = s.labelList :=
  Session.step_unknown_refused s id chunk hc read healthy

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
  intro h
  obtain ⟨joined, -⟩ := Session.connected_client_witness
  have refused :=
    (@h (Session.trace Session.step (State.boot (Vt.Vt.init 1 1) [] []) [.connected 1]).1 1
        (Wire.encode (.unknown 200 [])) { id := 1 } {} 200 [] joined
        (Session.feed_encode_fresh (.unknown 200 []) ⟨by simp, by decide⟩) rfl).1
  simp at refused

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
        (Driver.run execute r events).exiting = exits :=
  Driver.run_refines execute ending succeeds r events running

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
  intro h
  obtain ⟨handled, exits, handles, -, -, stayed⟩ :=
    @h Unit (fun _ world eff => (world, Driver.success .unknown eff)) .unknown (fun _ _ _ => rfl)
      { st := State.boot (Vt.Vt.init 1 1) [] [], world := () } [.childExited .unknown] rfl
  have ends :=
    (Session.step_exit_iff (State.boot (Vt.Vt.init 1 1) [] []) (.childExited .unknown)).mpr rfl
  cases handles with
  | exit => simp [Driver.inert] at stayed
  | next _ _ _ _ _ stays => exact stays ends

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
  have live : LiveVt r.st := (Session.liveVt_iff _).mpr (Checkpoint.live_decoded_iff.mp hlive)
  obtain ⟨out, ok, ⟨bounded, _⟩, kept⟩ :=
    Driver.run_total_safe execute hw r events
      ⟨(Session.bounded_iff_bounds _).mpr hb, Vt.good_of_liveReachable live⟩ live
  exact
    ⟨out, ok, (Session.bounded_iff_bounds _).mp bounded,
      Checkpoint.live_decoded_iff.mpr ((Session.liveVt_iff _).mp kept)⟩

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
  intro h
  obtain ⟨-, -, wide, roster, -, scanner⟩ := Session.boot_observed (Vt.Vt.init 80 24) [] []
  obtain ⟨-, -, narrow, -, -, -⟩ := Session.boot_observed (Vt.Vt.init 1 1) [] []
  let execute : State → Unit → (eff : Effect Replay.Plan) → Except Unit (Unit × Driver.Reply eff) :=
    fun _ world eff => .ok (world, Driver.success .unknown eff)
  obtain ⟨out, jumped, bounds, -⟩ :=
    @h Unit Unit execute (fun _ _ _ => ⟨_, rfl⟩)
      { st := State.boot (Vt.Vt.init 80 24) [] [], world := () } []
      ⟨by
        rw [roster]; decide, by
        rw [wide]; decide +kernel, fun c member =>
        absurd member
          (by
            rw [roster]; exact List.not_mem_nil),
        by
        rw [scanner]; trivial⟩
      (by
        rw [wide]; exact .init 80 24)
  cases jumped
  have overflow := bounds.labelsLe
  rw [narrow] at overflow
  exact absurd overflow (by decide +kernel)

theorem run_feedback_alive {World : Type}
    (execute : State → World → (eff : Effect Replay.Plan) → Id (World × Driver.Reply eff))
    (r : Driver.Result State World) (events : List Event) (running : r.exiting = false)
    (failures : ∀ ev ∈ events, ev = .checkpointFailed ∨ ∃ id, ev = .closed id) :
    (Driver.run execute r events).exiting = false :=
  Driver.run_feedback_alive execute r events running failures

theorem run_feedback_alive_rejects_halt :
    ¬∀ {World : Type}
        (execute : State → World → (eff : Effect Replay.Plan) → Id (World × Driver.Reply eff))
        (r : Driver.Result State World) (events : List Event),
        r.exiting = false →
          (∀ ev ∈ events, ev = .checkpointFailed ∨ ∃ id, ev = .closed id) →
          (Driver.halt execute r events).exiting = false := by
  intro h
  have stopped :=
    @h Unit (fun _ world eff => (world, Driver.success .unknown eff))
      { st := State.boot (Vt.Vt.init 1 1) [] [], world := () } [] rfl (by simp)
  exact absurd stopped (by decide)

theorem run_exited {m : Type → Type} [Monad m] {World : Type}
    (execute : State → World → (eff : Effect Replay.Plan) → m (World × Driver.Reply eff))
    (r : Driver.Result State World) (events : List Event) (exited : r.exiting = true) :
    Driver.run execute r events = pure r := Driver.run_exited execute r events exited

theorem run_exited_rejects_jump :
    ¬∀ {m : Type → Type} [Monad m] {World : Type}
        (execute : State → World → (eff : Effect Replay.Plan) → m (World × Driver.Reply eff))
        (r : Driver.Result State World) (events : List Event),
        r.exiting = true →
          Driver.jump (State.boot (Vt.Vt.init 1 1) [] []) execute r events = pure r := by
  intro h
  have moved :=
    @h Id _ Unit (fun _ world eff => (world, Driver.success .unknown eff))
      { st := State.boot (Vt.Vt.init 1 1) [("a", "b")] [], world := (), exiting := true } [] rfl
  have labels := congrArg (fun (out : Driver.Result State Unit) => out.st.labelList) moved
  change
    (State.boot (Vt.Vt.init 1 1) [] []).labelList =
      (State.boot (Vt.Vt.init 1 1) [("a", "b")] []).labelList at labels
  obtain ⟨-, -, -, -, empty, -⟩ := Session.boot_observed (Vt.Vt.init 1 1) [] []
  obtain ⟨-, -, -, -, labelled, -⟩ := Session.boot_observed (Vt.Vt.init 1 1) [("a", "b")] []
  rw [empty, labelled] at labels
  simp [maxLabels] at labels

theorem run_stop_exits {World : Type}
    (execute : State → World → (eff : Effect Replay.Plan) → Id (World × Driver.Reply eff))
    (r : Driver.Result State World) (ev : Event) (running : r.exiting = false)
    (stops : Effect.stopProgram ∈ (Session.step r.st ev).2) :
    (Driver.run execute r [ev]).exiting = true := Driver.run_stop_exits execute r ev running stops

theorem run_stop_exits_rejects_jump :
    ¬∀ {World : Type}
        (execute : State → World → (eff : Effect Replay.Plan) → Id (World × Driver.Reply eff))
        (r : Driver.Result State World) (ev : Event),
        r.exiting = false →
          Effect.stopProgram ∈ (Session.step r.st ev).2 →
          (Driver.jump (State.boot (Vt.Vt.init 1 1) [] []) execute r [ev]).exiting = true := by
  intro h
  obtain ⟨joined, -⟩ := Session.connected_client_witness
  have stops :=
    (Session.step_kill_stops _ 1 (Wire.encode .kill) joined rfl
        (Session.feed_encode_fresh .kill (by simp [Wire.Msg.Fits])) rfl).1
  have jumped :=
    @h Unit (fun _ world eff => (world, Driver.success .unknown eff))
      { st := (Session.trace Session.step (State.boot (Vt.Vt.init 1 1) [] []) [.connected 1]).1,
        world := () }
      (.bytes 1 (Wire.encode .kill)) rfl
      (by
        rw [stops]; simp)
  simp [Driver.jump] at jumped

theorem reachableIn_bound {cap : Nat} {b : Buf.Buf}
    (h : Buf.InputReach Buf.Buf.empty Buf.bufOffer Buf.bufAdvance cap b) : Buf.owedLen b ≤ cap :=
  Buf.reachableIn_bound h

theorem reachableIn_bound_rejects_append :
    ¬∀ {cap : Nat} {b : Buf.Buf},
        Buf.InputReach Buf.Buf.empty Buf.bufEnqueue Buf.bufAdvance cap b → Buf.owedLen b ≤ cap := by
  intro h
  have owed :=
    @h 0 (Buf.bufEnqueue 0 Buf.Buf.empty (ByteArray.mk #[0])).1
      (.offer Buf.Buf.empty (ByteArray.mk #[0]) .empty)
  obtain ⟨empty, -, -, -, appended, -⟩ := Buf.buf_observed 0 0 Buf.Buf.empty (ByteArray.mk #[0])
  rw [appended, empty] at owed
  exact absurd owed (by decide)

theorem reachableOut_bound {cap : Nat} {b : Buf.Buf}
    (h : Buf.OutputReach Buf.Buf.empty Buf.bufEnqueue Buf.bufAdvance cap b) :
    Buf.owedLen b ≤ cap := Buf.reachableOut_bound h

theorem reachableOut_bound_rejects_uncut :
    ¬∀ {cap : Nat} {b : Buf.Buf},
        Buf.OutputReach Buf.Buf.empty (fun cap b more => ((Buf.bufEnqueue cap b more).1, false))
            Buf.bufAdvance cap b →
          Buf.owedLen b ≤ cap := by
  intro h
  have owed :=
    @h 0 (Buf.bufEnqueue 0 Buf.Buf.empty (ByteArray.mk #[0])).1
      (.enqueue Buf.Buf.empty (ByteArray.mk #[0]) .empty rfl)
  obtain ⟨empty, -, -, -, appended, -⟩ := Buf.buf_observed 0 0 Buf.Buf.empty (ByteArray.mk #[0])
  rw [appended, empty] at owed
  exact absurd owed (by decide)

theorem step_bytes_one_reply (s : State) (id : Nat) (chunk : List UInt8) :
    ((Session.step s (.bytes id chunk)).2.all (!·.rendered) ∨
        ∃ pre frames post,
          (Session.step s (.bytes id chunk)).2 = pre ++ frames ++ Effect.send id .done :: post ∧
            frames.all (·.rendered) ∧ (pre ++ post).all (!·.rendered)) ∧
      (((Session.step s (.bytes id chunk)).1.client? id).all (!·.attached) →
        ((Session.step s (.bytes id chunk)).2.filter (·.resizes)).length ≤ 1) :=
  Session.step_bytes_one_reply_observed s id chunk

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
  intro h
  obtain ⟨-, none⟩ := Session.connected_client_witness
  have twice := (h (State.boot (Vt.Vt.init 1 1) [] []) 1 []).2 (by simp [none])
  exact absurd twice (by decide)

theorem captureBytes_bounded (contents : String) :
    (Import.Resurrect.captureBytes contents).length ≤ 2 * Import.Resurrect.captureLimit :=
  Import.Resurrect.captureBytes_bounded contents

theorem captureBytes_bounded_rejects_unbounded :
    ¬∀ (contents : String),
        ((fun (_ : String) => List.replicate (2 * Import.Resurrect.captureLimit + 1) (0 : UInt8))
              contents).length ≤
          2 * Import.Resurrect.captureLimit := by
  intro h
  exact absurd (h "") (by simp)

theorem ending_clean (gone : UInt32 → Nat → Nat → Bool) (ends : Signal.Ends gone)
    (alive : List Nat) :
    (Session.ending.head?.map (·.1)) = some 1 ∧
      Session.ending.foldl
          (fun still (signal : UInt32 × Nat) => still.filter (!gone signal.1 signal.2 ·)) alive =
        [] := by
  rw [Session.ending_eq]
  refine ⟨rfl, List.filter_eq_nil_iff.mpr fun pid _ => ?_⟩
  simp [ends pid 1000 (Nat.le_refl _)]

theorem ending_clean_rejects_hangup :
    ¬∀ (gone : UInt32 → Nat → Nat → Bool),
        Signal.Ends gone →
          ∀ (alive : List Nat),
            (([(1, 1000)] : List (UInt32 × Nat)).head?.map (·.1)) = some 1 ∧
              ([(1, 1000)] : List (UInt32 × Nat)).foldl
                  (fun still (signal : UInt32 × Nat) => still.filter (!gone signal.1 signal.2 ·))
                  alive =
                [] := by
  intro h
  -- an operating system where SIGKILL ends every process at once and no other signal ends any
  have ends : Signal.Ends fun sig _ _ => sig == 9 := fun _ _ _ => rfl
  have survives := (h _ ends [1]).2
  exact absurd survives (by decide)

theorem loadBytes_saveBytes_live (c : Checkpoint.Ckpt Vt.Vt)
    (h :
      Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
        (Checkpoint.Decoded Checkpoint.loadBytes) c.vt) :
    Checkpoint.loadBytes (Checkpoint.saveBytes c) = some { c with vt := c.vt.quiesce } :=
  Checkpoint.loadBytes_saveBytes_live c (Checkpoint.live_of_decoded h)

theorem loadBytes_saveBytes_live_rejects_refusal :
    ¬∀ (c : Checkpoint.Ckpt Vt.Vt),
        Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
            (Checkpoint.Decoded (fun _ => none : ByteArray → Option (Checkpoint.Ckpt Vt.Vt))) c.vt →
          (fun _ => none : ByteArray → Option (Checkpoint.Ckpt Vt.Vt)) (Checkpoint.saveBytes c) =
            some { c with vt := c.vt.quiesce } := by
  intro h
  cases h ⟨Vt.Vt.init 1 1, "", []⟩ (.init 1 1)

theorem resume_restores (c : Checkpoint.Ckpt Vt.Vt)
    (h :
      Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
        (Checkpoint.Decoded Checkpoint.loadBytes) c.vt)
    (metaKv : List (String × String)) :
    let saved := Checkpoint.loadBytes (Checkpoint.saveBytes c)
    let booted := State.boot (bootVt (saved.map (·.vt))) ((saved.map (·.labels)).getD []) metaKv
    booted.terminal = c.vt.quiesce ∧ booted.labelList = c.labels.take maxLabels := by
  intro saved booted
  have loaded : saved = some { c with vt := c.vt.quiesce } :=
    Checkpoint.loadBytes_saveBytes_live c (Checkpoint.live_of_decoded h)
  obtain ⟨_, restored, terminal, -, labels, -⟩ := Session.boot_observed c.vt.quiesce c.labels metaKv
  simp only [booted, loaded, Option.map_some, Option.getD_some, restored]
  exact ⟨terminal, labels⟩

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
  intro h
  have fresh := (h ⟨Vt.Vt.init 2 1, "", []⟩ (.init 2 1) []).1
  obtain ⟨-, -, terminal, -, -, -⟩ :=
    Session.boot_observed (Vt.Vt.init 1 1)
      (((Checkpoint.loadBytes (Checkpoint.saveBytes ⟨Vt.Vt.init 2 1, "", []⟩)).map (·.labels)).getD
        [])
      []
  rw [terminal] at fresh
  exact absurd (congrArg Vt.Vt.colCount fresh) (by decide +kernel)

theorem loadBytes_resave {b : ByteArray} {c : Checkpoint.Ckpt Vt.Vt}
    (h : Checkpoint.loadBytes b = some c) :
    Checkpoint.loadBytes (Checkpoint.saveBytes c) = some c := Checkpoint.loadBytes_resave h

theorem loadBytes_resave_rejects_fixed :
    ¬∀ {b : ByteArray} {c : Checkpoint.Ckpt Vt.Vt},
        Checkpoint.loadBytes b = some c →
          Checkpoint.loadBytes
              ((fun (_ : Checkpoint.Ckpt Vt.Vt) => Checkpoint.saveBytes ⟨Vt.Vt.init 1 1, "x", []⟩)
                c) =
            some c := by
  intro h
  have empty := loadBytes_saveBytes_live ⟨Vt.Vt.init 1 1, "", []⟩ (.init 1 1)
  have other := loadBytes_saveBytes_live ⟨Vt.Vt.init 1 1, "x", []⟩ (.init 1 1)
  have same := (h empty).symm.trans other
  exact absurd (congrArg (Option.map Checkpoint.Ckpt.cwd) same) (by decide)

theorem recovery_exact (create : Bool) (file : Option ByteArray) :
    App.Recovery.decide create file =
      (file.map fun bytes =>
            ((Checkpoint.loadBytes bytes).map App.Recovery.resume).getD (.refuse .notDone)).getD
        (if create then .fresh else .refuse .notFound) := App.Recovery.recovery_exact create file

theorem recovery_exact_rejects_missing :
    ¬∀ (create : Bool) (file : Option ByteArray),
        (fun (create : Bool) (file : Option ByteArray) =>
              ((file.bind Checkpoint.loadBytes).map App.Recovery.resume).getD
                (if create then App.Recovery.fresh else .refuse .notFound))
            create file =
          (file.map fun bytes =>
                ((Checkpoint.loadBytes bytes).map App.Recovery.resume).getD (.refuse .notDone)).getD
            (if create then .fresh else .refuse .notFound) := by
  intro h
  have empty : Checkpoint.loadBytes ByteArray.empty = none := rfl
  have taken := h true (some ByteArray.empty)
  simp [empty] at taken

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
  have resumes (c : Checkpoint.Ckpt Vt.Vt)
    (h :
      Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
        (Checkpoint.Decoded Checkpoint.loadBytes) c.vt) :
    App.Recovery.decide create (some (Checkpoint.saveBytes c)) =
      .resume { c with vt := c.vt.quiesce } := by
    rw [App.Recovery.recovery_exact create _]
    simp only [Option.map_some, Option.getD_some]
    rw [loadBytes_saveBytes_live c h]
    rfl
  obtain ⟨kept, torn⟩ := durable (some (Checkpoint.saveBytes old)) (Checkpoint.saveBytes new)
  cases synced with
  | true => exact ⟨_, by rw [kept, resumes new hnew], .inl rfl⟩
  | false =>
    rcases torn with found | found
    · exact ⟨_, by rw [found, resumes old hold], .inr ⟨rfl, rfl⟩⟩
    · exact ⟨_, by rw [found, resumes new hnew], .inl rfl⟩

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
  intro h
  obtain ⟨_, fresh, -⟩ :=
    h (fun _ new _ => some new) (fun _ _ => ⟨rfl, .inr rfl⟩) true true ⟨Vt.Vt.init 1 1, "", []⟩
      ⟨Vt.Vt.init 1 1, "", []⟩ (.init 1 1) (.init 1 1)
  cases fresh

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
  intro s after changed unsaved
  exact
    Session.unsaved_due s ev post (Session.boot_lastCkptMs_le vt labels metaKv pre) changed unsaved

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
  intro h
  have printed :
    (Session.step (State.boot (Vt.Vt.init 2 1) [] []) (.ptyOut [0x41])).1.terminal =
      (Vt.Vt.init 2 1).feed [0x41] :=
    Session.step_ptyOut_vt _ _
  have moved : ((Vt.Vt.init 2 1).feed [0x41]).cursorPos = (1, 0) := by decide +kernel
  have home : (Vt.Vt.init 2 1).cursorPos = (0, 0) := by decide +kernel
  have quiet :
    Effect.checkpoint ∉ (Session.step (State.boot (Vt.Vt.init 2 1) [] []) (.ptyOut [0x41])).2 := by
    rw [Session.step_ptyOut_effects]
    simp [Session.broadcast, Session.State.boot]
  obtain ⟨_, -, ⟨_, asleep, -⟩, -⟩ :=
    h (Vt.Vt.init 2 1) [] [] [] [] (.ptyOut [0x41])
      (.inl fun same => by
        have := congrArg Vt.Vt.cursorPos same
        change
          ((Session.step (State.boot (Vt.Vt.init 2 1) [] [])
                  (.ptyOut [0x41])).1.terminal).cursorPos =
            (State.boot (Vt.Vt.init 2 1) [] []).terminal.cursorPos at this
        rw [printed, moved] at this
        exact absurd (this.trans home) (by decide))
      (by simpa [Session.trace] using quiet)
  cases asleep

theorem checkpoint_metadata (pane : Import.Resurrect.Pane) (contents : Option String) :
    (Import.Resurrect.checkpoint pane contents).cwd = pane.dir ∧
      (Import.Resurrect.checkpoint pane contents).labels.lookup "tmux.command" =
        some pane.details.command ∧
      (Import.Resurrect.checkpoint pane contents).labels.lookup "tmux.saved-command" =
        some pane.details.savedCommand ∧
      (Import.Resurrect.checkpoint pane contents).labels.lookup "tmux.capture" =
        some (if contents.isSome then "saved" else "none") :=
  Import.Resurrect.checkpoint_metadata pane contents

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
  intro h
  exact absurd (h { name := "a", dir := "x", line := 0 } none).1 (by decide)

theorem infoText_text (s : State) :
    ∃ cs : List Char,
      Session.infoText s = cs.flatMap String.utf8EncodeChar ∧
        ∀ c ∈ cs,
          c = '\t' ∨
            c = '\n' ∨ (0x20 ≤ c.toNat ∧ c.toNat ≠ 0x7F ∧ ¬(0x80 ≤ c.toNat ∧ c.toNat < 0xA0)) := by
  obtain ⟨cs, text, safe⟩ := Session.infoText_text s
  refine ⟨cs, ?_, safe⟩
  rw [text]
  exact congrArg (cs.flatMap ·) (funext Render.utf8_eq_utf8EncodeChar)

theorem infoText_text_rejects_escape :
    ¬∀ (s : State),
        ∃ cs : List Char,
          (fun (_ : State) => ([0x1B] : List UInt8)) s = cs.flatMap String.utf8EncodeChar ∧
            ∀ c ∈ cs,
              c = '\t' ∨
                c = '\n' ∨
                (0x20 ≤ c.toNat ∧ c.toNat ≠ 0x7F ∧ ¬(0x80 ≤ c.toNat ∧ c.toNat < 0xA0)) := by
  intro h
  obtain ⟨cs, text, safe⟩ := h (State.boot (Vt.Vt.init 1 1) [] [])
  have escape : (0x1B : UInt8) ∈ cs.flatMap String.utf8EncodeChar := by
    rw [← text]
    exact List.mem_singleton_self _
  obtain ⟨c, member, byte⟩ := List.mem_flatMap.mp escape
  rcases safe c member with tab | newline | ⟨printable, notDel, -⟩
  · subst tab
    revert byte
    decide
  · subst newline
    revert byte
    decide
  · rw [← Render.utf8_eq_utf8EncodeChar] at byte
    exact absurd (Render.utf8_no_ctl c printable notDel _ byte).1 (by decide)

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
  have info (s : State) : Display.Clean (Session.infoText s) := by
    obtain ⟨cs, text, safe⟩ := infoText_text s
    rw [text]
    exact
      Display.clean_text fun c hc =>
        (safe c hc).elim (fun tab => .inr (.inr tab)) fun rest =>
          rest.elim (fun newline => .inr (.inl newline)) .inl
  exact
    ⟨Display.terminalListing_clean, Selector.Picker.frame_clean, Selector.Picker.enterAnsi_clean,
      Selector.Picker.exitAnsi_clean, Display.title_ansi_clean, Display.title_update_clean,
      Display.screenText_clean, Display.history_clean, info, Display.leaveAnsi_clean⟩

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
        (∀ s, Display.Clean (Session.infoText s)) ∧ Display.Clean Terminal.Render.leaveAnsi) :=
  fun h => Display.not_clean_reset (h.1 true [])

theorem ticks_settle (s : State) (now t₁ t₂ : Nat)
    (h₁ : (Session.trace Session.step s [.tick now]).1.nextTick = some t₁)
    (h₂ : (Session.trace Session.step s [.tick now, .tick t₁]).1.nextTick = some t₂) :
    (Session.trace Session.step s [.tick now, .tick t₁, .tick t₂]).1.nextTick = none :=
  Session.ticks_settle s now t₁ t₂ h₁ h₂

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
  intro h
  exact absurd (h (State.boot (Vt.Vt.init 1 1) [] []) 0 0 0 rfl rfl) (by simp)

theorem poll_wakes (quiet : Int32 → Nat → Prop) (sleeps : Poll.Sleeps quiet) (now : Nat)
    (deadlines : List Nat) (fit : ∀ d ∈ deadlines, d - now ≤ 2147483647) (ms : Nat)
    (woke : quiet (Session.pollTimeout now deadlines) ms) :
    ∃ due, deadlines.min? = some due ∧ due - now ≤ ms := by
  have waited := sleeps _ _ woke
  rw [Session.pollTimeout_eq] at waited
  cases h : deadlines.min? with
  | none =>
    simp only [h, Option.map_none, Option.getD_none] at waited
    exact absurd waited.1 (by decide)
  | some due =>
    have near : due - now ≤ 2147483647 := fit due (List.min?_mem h)
    have small : due - now < 2 ^ 31 := by omega
    rw [h] at waited
    simp only [Option.map_some, Option.getD_some, Nat.min_eq_left near,
      Int32.toInt_ofNat_of_lt small] at waited
    exact ⟨due, rfl, by omega⟩

theorem poll_wakes_rejects_polling :
    ¬∀ (quiet : Int32 → Nat → Prop),
        Poll.Sleeps quiet →
          ∀ (now : Nat) (deadlines : List Nat),
            (∀ d ∈ deadlines, d - now ≤ 2147483647) →
              ∀ (ms : Nat),
                quiet ((fun (_ : Nat) (_ : List Nat) => (100 : Int32)) now deadlines) ms →
                  ∃ due, deadlines.min? = some due ∧ due - now ≤ ms := by
  intro h
  -- a poll that waits out its timeout and then returns, as the claim allows
  have sleeps : Poll.Sleeps fun (t : Int32) (ms : Nat) => 0 ≤ t.toInt ∧ t.toInt ≤ ms :=
    fun _ _ waited => waited
  obtain ⟨_, none_due, -⟩ := h _ sleeps 0 [] (by simp) 100 ⟨by decide, by decide⟩
  simp at none_due

theorem start_answer_true (r : Start.Request) (h : Start.Reachable Start.proceeds Start.answer r) :
    (r.answer = some .started → r.runs = true) ∧ (r.answer = some .notStarted → r.runs = false) :=
  Start.answer_true h

theorem start_answer_true_rejects_started :
    ¬∀ (r : Start.Request),
        Start.Reachable Start.proceeds (fun _ _ => Start.Answer.started) r →
          (r.answer = some .started → r.runs = true) ∧
            (r.answer = some .notStarted → r.runs = false) := by
  intro h
  have taken :=
    Start.Reachable.step (proceeds := Start.proceeds) (answer := fun _ _ => Start.Answer.started)
      .init (.commandTakes {} rfl rfl)
  exact absurd ((h _ taken).1 rfl) (by decide)

theorem start_answer_true_rejects_proceed :
    ¬∀ (r : Start.Request),
        Start.Reachable (fun _ => true) Start.answer r →
          (r.answer = some .started → r.runs = true) ∧
            (r.answer = some .notStarted → r.runs = false) := by
  intro h
  have taken :=
    Start.Reachable.step (proceeds := fun _ => true) (answer := Start.answer) .init
      (.commandTakes {} rfl rfl)
  have ran := Start.Reachable.step taken (.daemonDecides _ rfl rfl true)
  exact absurd ((h _ ran).2 (by simp [Start.answer_command])) (by decide)

theorem offloop_coalesces {R W : Type} (start : W → R) (ws : List W) :
    (ws.foldl (Offloop.run Offloop.ask start) {}).running = ws.head?.map start ∧
      (ws.foldl (Offloop.run Offloop.ask start) {}).waiting =
        if ws.length ≤ 1 then none else ws.getLast? := Session.offloop_coalesces start ws

theorem offloop_coalesces_rejects_eager :
    ¬∀ {R W : Type} (start : W → R) (ws : List W),
        (ws.foldl (Offloop.run (fun (o : Offloop R W) (w : W) => (o, some w)) start) {}).running =
            ws.head?.map start ∧
          (ws.foldl (Offloop.run (fun (o : Offloop R W) (w : W) => (o, some w)) start) {}).waiting =
            if ws.length ≤ 1 then none else ws.getLast? := by
  intro h
  have first := (@h Nat Nat id [0, 1]).1
  simp [Offloop.run] at first

theorem capture_waits_unlocked :
    (App.Capture.work App.Capture.plan false).map Prod.fst = [.load, .render, .write] ∧
      (.load, true) ∈ App.Capture.work App.Capture.plan false ∧
      ∀ step, (step, true) ∈ App.Capture.work App.Capture.plan false → step.waitsOutside = false :=
  App.Capture.waits_unlocked

theorem capture_waits_unlocked_rejects_inside :
    ¬((App.Capture.work [.acquire, .load, .render, .write, .release] false).map Prod.fst =
          [.load, .render, .write] ∧
        (.load, true) ∈ App.Capture.work [.acquire, .load, .render, .write, .release] false ∧
        ∀ step,
          (step, true) ∈ App.Capture.work [.acquire, .load, .render, .write, .release] false →
            step.waitsOutside = false) := by
  -- the write runs holding the locks, and it waits on whoever reads it
  rintro ⟨-, -, unheld⟩
  exact absurd (unheld .write (by decide)) (by decide)

theorem classify_iff (o : Status.Obs) (s : Status.Status) : Status.classify o = s ↔ Status.Is s o :=
  Status.classify_iff o s

theorem classify_iff_rejects_idle :
    ¬∀ (o : Status.Obs) (s : Status.Status),
        (fun (_ : Status.Obs) => Status.Status.idle) o = s ↔ Status.Is s o := by
  intro h
  exact absurd ((h { known := false } .unknown).mpr rfl) (by decide)

theorem icon_glyphs :
    Status.icon .working = '⣷' ∧
      Status.icon .wantsYou = '⣿' ∧
      Status.icon .idle = '⣀' ∧
      Status.icon .exitedOk = '✓' ∧
      Status.icon .exitedBad = '!' ∧
      Status.icon .resumable = '~' ∧
      Status.icon .unknown = '?' := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem icon_glyphs_rejects_unknown :
    ¬((fun (_ : Status.Status) => '?') .working = '⣷' ∧
        (fun (_ : Status.Status) => '?') .wantsYou = '⣿' ∧
        (fun (_ : Status.Status) => '?') .idle = '⣀' ∧
        (fun (_ : Status.Status) => '?') .exitedOk = '✓' ∧
        (fun (_ : Status.Status) => '?') .exitedBad = '!' ∧
        (fun (_ : Status.Status) => '?') .resumable = '~' ∧
        (fun (_ : Status.Status) => '?') .unknown = '?') := by
  intro h
  exact absurd h.1 (by decide)

theorem summary_exact (statuses : List Status.Status) :
    Status.summary statuses =
      String.intercalate " "
        ((if statuses.count .wantsYou = 0 then []
          else [(toString (statuses.count .wantsYou)).push (Status.icon .wantsYou)]) ++
          (if statuses.count .exitedBad = 0 then []
          else [(toString (statuses.count .exitedBad)).push (Status.icon .exitedBad)]) ++
          (if statuses.count .unknown = 0 then []
          else [(toString (statuses.count .unknown)).push (Status.icon .unknown)])) :=
  Status.summary_exact statuses

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
  intro h
  exact absurd (h []) (by simp)

theorem rowStatus_saved (status : Nat) (st : Status.Status) :
    Listing.rowStatus (.ended status) = (if status = 0 then .exitedOk else .exitedBad) ∧
      Listing.rowStatus (.remote false (Status.name st)) =
        if st = .exitedOk ∨ st = .exitedBad then st else .resumable :=
  ⟨Listing.rowStatus_ended status, Listing.rowStatus_remote_saved st⟩

theorem rowStatus_saved_rejects_unknown :
    ¬∀ (status : Nat) (st : Status.Status),
        (fun (_ : Listing.Row) => Status.Status.unknown) (.ended status) =
            (if status = 0 then .exitedOk else .exitedBad) ∧
          (fun (_ : Listing.Row) => Status.Status.unknown) (.remote false (Status.name st)) =
            if st = .exitedOk ∨ st = .exitedBad then st else .resumable := by
  intro h
  exact absurd (h 0 .unknown).1 (by decide)

theorem compose_attention_last (session application summary : String) (capacity : Nat) :
    Title.compose session application summary capacity =
      Title.compose session application ""
          (capacity - (if summary.isEmpty then "" else " · " ++ summary).length) ++
        (if summary.isEmpty then "" else " · " ++ summary) :=
  Title.compose_attention_last session application summary capacity

theorem compose_attention_last_rejects_first :
    ¬∀ (session application summary : String) (capacity : Nat),
        (fun (session application summary : String) (_ : Nat) => summary ++ session ++ application)
            session application summary capacity =
          (fun (session application summary : String) (_ : Nat) =>
                summary ++ session ++ application)
              session application ""
              (capacity - (if summary.isEmpty then "" else " · " ++ summary).length) ++
            (if summary.isEmpty then "" else " · " ++ summary) := by
  intro h
  exact absurd (h "" "" "x" 0) (by decide)

theorem sort_attention_first {α : Type} (status : α → Status.Status) (rows : List α) :
    (View.sort status rows).Perm rows ∧
      ∃ first rest,
        View.sort status rows = first ++ rest ∧
          (∀ x ∈ first, status x = .wantsYou ∨ status x = .exitedBad ∨ status x = .unknown) ∧
          ∀ x ∈ rest, ¬(status x = .wantsYou ∨ status x = .exitedBad ∨ status x = .unknown) := by
  obtain ⟨first, rest, split, front, back⟩ := View.sort_attention_first status rows
  exact
    ⟨View.sort_perm status rows, first, rest, split, fun x hx =>
      (View.mem_attention _).mp (front x hx), fun x hx => fun h =>
      back x hx ((View.mem_attention _).mpr h)⟩

theorem sort_attention_first_rejects_arrival :
    ¬∀ {α : Type} (status : α → Status.Status) (rows : List α),
        ((fun (_ : α → Status.Status) (rows : List α) => rows) status rows).Perm rows ∧
          ∃ first rest,
            (fun (_ : α → Status.Status) (rows : List α) => rows) status rows = first ++ rest ∧
              (∀ x ∈ first, status x = .wantsYou ∨ status x = .exitedBad ∨ status x = .unknown) ∧
              ∀ x ∈ rest,
                ¬(status x = .wantsYou ∨ status x = .exitedBad ∨ status x = .unknown) := by
  intro h
  obtain ⟨-, first, rest, split, front, back⟩ := h id [Status.Status.idle, .wantsYou]
  match first, split with
  | [], split =>
    have whole : rest = [.idle, .wantsYou] := by simpa using split.symm
    exact back .wantsYou (by simp [whole]) (by simp)
  | a :: _, split =>
    have head : a = .idle := (List.cons.inj split).1.symm
    exact absurd (front a (by simp)) (by simp [head])

theorem groups_exact (keys : List String) :
    ((View.groups keys).map (·.2)).sum = keys.length ∧
      ∀ (k : String) (n : Nat), (k, n) ∈ View.groups keys → n = keys.count k :=
  ⟨View.groups_sum keys, View.groups_count keys⟩

theorem groups_exact_rejects_fixed :
    ¬∀ (keys : List String),
        (((fun (_ : List String) => [("", 1)]) keys).map (·.2)).sum = keys.length ∧
          ∀ (k : String) (n : Nat),
            (k, n) ∈ (fun (_ : List String) => [("", 1)]) keys → n = keys.count k := by
  intro h
  exact absurd (h []).1 (by simp)

theorem hidden_adds_up (targets : List String) :
    (View.hidden targets).2 = [] ∨
      ((View.hidden targets).2.map (·.2)).sum = (View.hidden targets).1 :=
  View.hidden_adds_up targets

theorem hidden_adds_up_rejects_short :
    ¬∀ (targets : List String),
        ((fun (_ : List String) => (1, [("a", 0)])) targets).2 = [] ∨
          (((fun (_ : List String) => (1, [("a", 0)])) targets).2.map (·.2)).sum =
            ((fun (_ : List String) => (1, [("a", 0)])) targets).1 := by
  intro h
  exact absurd (h []) (by simp)

theorem matchCount_push (s typed : Selector.Picker.State) (c : Char)
    (push : typed = { s with query := s.query.push c }) :
    Selector.Picker.matchCount typed ≤ Selector.Picker.matchCount s := by
  rw [push]
  exact Selector.Picker.matchCount_push s c

theorem matchCount_push_rejects_length :
    ¬∀ (s typed : Selector.Picker.State) (c : Char),
        typed = { s with query := s.query.push c } →
          (fun (s : Selector.Picker.State) => s.query.length) typed ≤
            (fun (s : Selector.Picker.State) => s.query.length) s := by
  intro h
  exact absurd (h { candidates := [] } _ 'a' rfl) (by simp)

end Linger
