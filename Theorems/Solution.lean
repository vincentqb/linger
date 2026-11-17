module

public import Linger.App.CoreCode.Api
public import Linger.App.CoreCode.Capture
public import Linger.App.CoreCode.Commands
public import Linger.App.CoreCode.Entry
public import Linger.App.CoreCode.Fields
public import Linger.App.CoreCode.Recovery
public import Linger.App.CoreCode.Wait
public import Linger.Display.CoreCode.Alert
public import Linger.Display.CoreCode.Listing
public import Linger.Display.CoreCode.Status
public import Linger.Display.CoreCode.View
public import Linger.Import.CoreCode.Resurrect
public import Linger.Selector.CoreCode.Picker
public import Linger.Selector.CoreCode.Fetch
public import Linger.Display.CoreCode.Title
public import Linger.Os.CoreCode.Answer
public import Linger.Os.CoreCode.Env
public import Linger.Session.CoreCode
public import Linger.Session.CoreCode.Buf
public import Linger.Session.CoreCode.Checkpoint
public import Linger.Session.CoreCode.Handoff
public import Linger.Session.CoreCode.Claim
public import Linger.Session.CoreCode.Names
public import Os.WorldSpec
public import Linger.Session.CoreCode.Driver
public import Linger.Session.CoreSpec
public import Linger.Session.WorldSpec
public import Linger.Target.CoreCode.Name
public import Linger.Target.CoreCode.Remote
public import Linger.Target.CoreSpec
public import Linger.Target.WorldSpec
public import Terminal.CoreCode.Mediation
public import Terminal.CoreCode.Render
public import Terminal.CoreCode.Replay
public import Terminal.CoreSpec
public import Terminal.CoreCode.Title
import all Linger.App.Proofs.Api
import all Linger.App.Proofs.Capture
import all Linger.App.Proofs.Commands
import all Linger.App.Proofs.Entry
import all Linger.App.Proofs.Recovery
import all Linger.App.Proofs.Wait
import Linger.Display.Proofs.Clean
import all Linger.App.Proofs.Fields
import all Linger.App.Proofs.Owned
import all Linger.Display.Proofs.Alert
import all Linger.Display.Proofs.Listing
import all Linger.Display.Proofs.Status
import all Linger.Display.Proofs.View
import all Linger.Import.Proofs.Resurrect
import Linger.Selector.Proofs.Frame
import Linger.Selector.Proofs.Repaint
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
public import Linger.Session.CoreCode.Start
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

theorem names_one_to_one (t : Names.Table) (wf : Names.Wf t) (a b id : String) :
    (Names.resolve t a = some id → Names.resolve t b = some id → a = b) ∧
      (Names.resolve t a = some id ↔ Names.nameOf t id = some a) ∧
      Names.resolve [] a = Name.check a :=
  ⟨Names.resolve_injective wf, Names.resolve_iff_nameOf wf a id, Names.resolve_nil a⟩

theorem names_one_to_one_rejects_stale :
    ¬∀ (t : Names.Table),
        Names.Wf t →
          ∀ (a b id : String),
            (Names.resolveStale t a = some id → Names.resolveStale t b = some id → a = b) ∧
              (Names.resolveStale t a = some id ↔ Names.nameOf t id = some a) ∧
              Names.resolveStale [] a = Name.check a := by
  intro h
  -- `x` renamed `y`: the stale resolution still reaches it by `x`
  have wf : Names.Wf [("y", "x")] := by simp [Names.Wf]
  have := (h [("y", "x")] wf "x" "y" "x").1 (by decide) (by decide)
  exact absurd this (by decide)

theorem rename_moves (t : Names.Table) (wf : Names.Wf t) (old new id : String)
    (found : Names.resolve t old = some id) (free : t.lookup new = none) (other : old ≠ new) :
    Names.Wf (Names.rename t old new id) ∧
      Names.resolve (Names.rename t old new id) new = some id ∧
      Names.resolve (Names.rename t old new id) old ≠ some id ∧
      ∀ n, n ≠ old → n ≠ new → Names.resolve (Names.rename t old new id) n = Names.resolve t n :=
  Names.rename_moves wf found free other

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
  intro h
  have valid : Name.check "a" = some "a" :=
    (Name.check_eq_some_iff "a" "a").mpr
      ⟨rfl, by
        unfold Name.Valid; decide⟩
  have found : Names.resolve [] "a" = some "a" := by rw [Names.resolve_nil, valid]
  have moved := (h [] (by simp [Names.Wf]) "a" "b" "a" found (by decide) (by decide)).2.1
  have : Names.resolve (Names.renameReid [] "a" "b" "a") "b" = some "b" := by
    simp [Names.renameReid, Names.resolve]
  rw [this] at moved
  exact absurd moved (by decide)

theorem claim_fresh (t : Names.Table) (wf : Names.Wf t) (name id : String)
    (unnamed : Names.resolve t name = none) (fresh : Names.Fresh id) (unused : id ∉ t.map (·.2)) :
    Names.Wf (Names.claim t name id) ∧
      Names.resolve (Names.claim t name id) name = some id ∧
      ∀ n, n ≠ name → Names.resolve (Names.claim t name id) n = Names.resolve t n :=
  Names.claim_fresh wf unnamed fresh unused

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
  intro h
  -- `n` renamed `x`, so `n` leads nowhere; a start that took `n` for the ID would share it
  have unnamed : Names.resolve [("x", "n")] "n" = none := by simp [Names.resolve, List.lookup_cons]
  have fresh : Names.Fresh ".a" := ⟨['a'], rfl, by simp, by decide⟩
  have := (h [("x", "n")] (by simp [Names.Wf]) "n" ".a" unnamed fresh (by decide)).2.1
  simp [Names.claimSelf, Names.resolve] at this

theorem nameOf_shown (t : Names.Table) (id name : String) (shown : Names.nameOf t id = some name) :
    (name, id) ∈ t ∨ Name.check id = some name := Names.nameOf_shown t id name shown

theorem nameOf_shown_rejects_bare :
    ¬∀ (t : Names.Table) (id name : String),
        Names.nameOfBare t id = some name → (name, id) ∈ t ∨ Name.check id = some name := by
  intro h
  rcases h [] ".a" ".a" rfl with mem | checked
  · simp at mem
  · have := ((Name.check_eq_some_iff ".a" ".a").mp checked).2
    exact absurd this.2.2.2 (by decide)

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
  rw [Names.rename_plan_eq]
  cases valid <;> cases oldHeld <;> cases older <;> cases newHeld <;> simp

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
  intro h
  cases ((h false true false false).1.mp rfl).1

theorem one_name
    (placed : Bool → (String → Option Nat) → String → String → Option (String → Option Nat))
    (noReplace : Os.Place.NoReplace placed) (first second : Names.Op) (names : String → Option Nat)
    (src src' dst : String) (file : Nat) (named : names src = some file)
    {after : String → Option Nat}
    (placedFirst : (Names.call first).run placed names src dst = some after) :
    after dst = some file ∧ (Names.call second).run placed after src' dst = none :=
  Names.call_second_fails noReplace first second named placedFirst

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
  intro h
  -- an operating system that places a name only where none is
  let placed : Bool → (String → Option Nat) → String → String → Option (String → Option Nat) :=
    fun rename names src dst =>
    if (names dst).isSome ∨ src = dst then none
    else
      some fun p =>
        if p = dst then names src
        else if p = src then (if rename then none else names src) else names p
  have noReplace : Os.Place.NoReplace placed := by
    intro rename names src dst
    refine ⟨fun taken => by simp [placed, taken], fun after placedOk => ?_⟩
    simp only [placed] at placedOk
    split at placedOk
    · cases placedOk
    · rename_i free
      cases placedOk
      have ne : src ≠ dst := fun e => free (Or.inr e)
      refine ⟨ne, by simp, by simp [ne], fun other h1 h2 => by simp [h1, h2]⟩
  have :=
    (@h placed noReplace .create .create (fun p => if p = "s" then some 0 else none) "s" "s" "d" 0
        (by simp)
        (fun p =>
          if p = "d" then (if "s" = "s" then some 0 else none)
          else if p = "s" then none else (if p = "s" then some 0 else none))
        rfl).2
  simp [Names.Call.run] at this

theorem step_fields_kept (s : State) (ev : Event) :
    (Session.step s ev).1.fieldList = s.fieldList := Session.step_fields_kept s ev

theorem step_fields_kept_rejects_reset :
    ¬∀ (s : State) (ev : Event),
        ((fun (s : State) (_ : Event) =>
                (State.boot s.terminal [] [], ([] : List (Effect Replay.Plan))))
              s ev).1.fieldList =
          s.fieldList := by
  intro h
  obtain ⟨-, -, -, -, labelled, -⟩ :=
    Session.boot_observed (Vt.Vt.init 1 1) [("description", "b")] []
  obtain ⟨-, -, -, -, emptied, -⟩ :=
    Session.boot_observed (State.boot (Vt.Vt.init 1 1) [("description", "b")] []).terminal [] []
  have kept := h (State.boot (Vt.Vt.init 1 1) [("description", "b")] []) (.tick 0)
  simp only at kept
  rw [emptied, labelled] at kept
  simp [maxFields, recordField] at kept

theorem infoFields_boot (vt : Vt.Vt) (fields metadata : List (String × String)) (evs : List Event) :
    ∃ rest,
      Session.infoFields (Session.trace Session.step (State.boot vt fields metadata) evs).1 =
        metadata ++ rest := by
  rw [Session.trace_step]
  exact Session.run_boot_infoFields vt fields metadata evs

theorem infoFields_boot_rejects_reboot :
    ¬∀ (vt : Vt.Vt) (fields metadata : List (String × String)) (evs : List Event),
        ∃ rest,
          Session.infoFields
              (Session.trace
                  (fun (_ : State) (_ : Event) =>
                    (State.boot (Vt.Vt.init 1 1) [] [], ([] : List (Effect Replay.Plan))))
                  (State.boot vt fields metadata) evs).1 =
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
        s.owned.asks = true) :=
  ⟨fun chunk hev => by
    subst hev
    exact Session.step_ptyOut_owned s chunk, fun o hev => by
    subst hev
    exact Session.step_observed_owned s o, fun d hev => by
    subst hev
    exact Session.step_notified_owned s d, fun id chunk hev => by
    subst hev
    exact Session.step_bytes_owned s id chunk,
    fun id chunk c dec m hev hc fresh read healthy looks => by
    subst hev
    exact Session.step_look_owned s id chunk hc fresh read healthy looks, fun out seen read heard =>
    Session.step_owned_kept s ev out seen read heard, Status.classify_running_asks _ _ _ _⟩

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
  -- a session that rings the bell on a client's read asks, with no output and no look
  intro h
  rcases (h (State.boot (Vt.Vt.init 80 24) [] []) (.bytes 0 [])).2.2.2.1 0 [] rfl with kept |
    ⟨-, c, hc, -⟩
  · have := congrArg Owned.asks kept
    simp only at this
    rw [Session.rung_asks] at this
    cases this
  · cases hc

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
  -- today's rule lists a session whose program rang the bell by its output, never as asking
  intro h
  have heard :=
    ((h (Session.step (State.boot (Vt.Vt.init 80 24) [] []) (.ptyOut [0x07])).1
            (.tick 0)).2.2.2.2.2.2).mpr
      Session.rung_asks
  have never : ∀ o : Status.Obs, (Status.lumped Status.classify o).attention ≠ .asked :=
    fun o hasks => by
    unfold Status.lumped at hasks
    simp [Status.classify, Status.attentionOf] at hasks
    split at hasks <;> simp at hasks
  exact never _ heard

theorem notify_exact (received : Nat → List (List UInt8) → List (List UInt8))
    (whole : Os.Dgram.Whole received) (vt : Vt.Vt) (fields metadata : List (String × String))
    (evs : List Event) (sent : List (List UInt8)) (fits : ∀ d ∈ sent, d.length ≤ Notify.cap)
    (heard : Notify.heard evs = received Notify.cap sent) :
    (Session.trace Session.step (State.boot vt fields metadata) evs).1.owned.ready =
        Notify.ready sent ∧
      (Session.trace Session.step (State.boot vt fields metadata) evs).1.owned.status =
        Notify.status sent := by
  have sent' : Notify.heard evs = sent := heard.trans (whole _ _ fits)
  obtain ⟨ready, status⟩ := Session.trace_notified (State.boot vt fields metadata) evs
  rw [ready, status, sent']
  exact ⟨rfl, Option.or_none⟩

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
  -- a session that reads its program's output as notifications is ready once it prints `READY=1`
  intro h
  have :=
    (h (fun _ sent => sent) (fun _ _ _ => rfl) (Vt.Vt.init 1 1) [] []
        [.ptyOut [0x52, 0x45, 0x41, 0x44, 0x59, 0x3D, 0x31]] [] (by simp) rfl).1
  rw [Session.outputNotifies_ready] at this
  cases this

theorem start_plan (live saved : Bool) :
    (Start.plan live saved = .take ↔ live = false ∧ saved = false) ∧
      (Start.plan live saved = .running ↔ live = true) ∧
      (Start.plan live saved = .saved ↔ live = false ∧ saved = true) := by
  rw [Start.plan_eq]
  cases live <;> cases saved <;> decide

theorem start_plan_rejects_take :
    ¬∀ (live saved : Bool),
        ((fun (_ _ : Bool) => Start.Plan.take) live saved = .take ↔ live = false ∧ saved = false) ∧
          ((fun (_ _ : Bool) => Start.Plan.take) live saved = .running ↔ live = true) ∧
          ((fun (_ _ : Bool) => Start.Plan.take) live saved = .saved ↔
            live = false ∧ saved = true) := by
  intro h
  cases ((h true false).1.mp rfl).1

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
      (Session.trace Session.step s (chunks.map (Event.bytes id))).1.fieldList = s.fieldList ∧
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
                  (chunks.map (Event.bytes id))).1.fieldList =
              s.fieldList ∧
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

theorem rowFields_name (socketName : String) (info : List (String × String)) :
    (Listing.rowFields socketName info).lookup "name" = some socketName :=
  Listing.rowFields_name socketName info

theorem rowFields_name_rejects_reply :
    ¬∀ (socketName : String) (info : List (String × String)),
        ((fun (_ : String) (info : List (String × String)) => info) socketName info).lookup "name" =
          some socketName := by
  intro h
  exact absurd (h "s" []) (by simp)

theorem rowText_sources (width : Option Nat) (layout : Listing.Layout)
    (info info' : List (String × String))
    (h : ∀ key ∈ Listing.sources, info.lookup key = info'.lookup key) :
    Listing.rowText width layout info = Listing.rowText width layout info' :=
  Listing.rowText_sources width layout info info' h

theorem rowText_sources_rejects_every_field :
    ¬∀ (width : Option Nat) (layout : Listing.Layout) (info info' : List (String × String)),
        (∀ key ∈ Listing.sources, info.lookup key = info'.lookup key) →
          (fun (_ : Option Nat) (_ : Listing.Layout) (info : List (String × String)) =>
                info.flatMap fun kv => kv.2.toList)
              width layout info =
            (fun (_ : Option Nat) (_ : Listing.Layout) (info : List (String × String)) =>
                info.flatMap fun kv => kv.2.toList)
              width layout info' := by
  intro h
  have := h none {} [("label.k", "a")] [("label.k", "b")] (by simp [Listing.sources, List.lookup])
  simp at this

theorem caption_precedence (info : List (String × String)) :
    ((info.lookup "title").getD "" ≠ "" → Listing.caption info = (info.lookup "title").getD "") ∧
      ((info.lookup "title").getD "" = "" →
        (info.lookup "status_text").getD "" ≠ "" →
        Listing.caption info = (info.lookup "status_text").getD "") ∧
      ((info.lookup "title").getD "" = "" →
        (info.lookup "status_text").getD "" = "" →
        Listing.caption info = (info.lookup "description").getD "") ∧
      (Listing.program info = "" ∨
        ¬(Listing.command (Listing.program info)).toList <:+: (Listing.caption info).toList) :=
  Listing.caption_precedence info

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
  intro h
  have := (h [("description", "d"), ("title", "t")]).1 (by simp [List.lookup])
  simp [List.lookup] at this

theorem info_foreground (reported seen : UInt32 → Option Foreground)
    (foreground : Pty.Foreground reported seen) (s : State) (master : UInt32) (o : Observation)
    (read : o.foreground = reported master) {fg : Foreground} (found : reported master = some fg) :
    ∃ process,
      seen master = some process ∧
        ("fg", String.intercalate " " process.argv) ∈
          Session.infoFields (Session.step s (.observed o)).1 ∧
        ("fgpid", toString process.pid) ∈ Session.infoFields (Session.step s (.observed o)).1 ∧
        ("fgdir", process.dir) ∈ Session.infoFields (Session.step s (.observed o)).1 := by
  rw [found] at read
  exact ⟨fg, foreground master fg found, Session.infoFields_foreground s o read⟩

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
  intro h
  -- a report that leaves the foreground out
  have shell : Foreground := ⟨1, ["sh"], "/"⟩
  obtain ⟨_, -, missing, -⟩ :=
    h (fun _ => some shell) (fun _ => some shell) (fun _ _ found => found)
      (State.boot (Vt.Vt.init 1 1) [] []) 0
      { nowMs := 0, wallS := 0, login := false, foreground := some shell } rfl rfl
  simp at missing

theorem info_echo (reported set : UInt32 → Option Bool) (echo : Pty.Echo reported set) (s : State)
    (master : UInt32) (o : Observation) (read : o.echo = reported master) {on : Bool}
    (found : reported master = some on) :
    set master = some on ∧
      ("echo", toString on) ∈ Session.infoFields (Session.step s (.observed o)).1 := by
  rw [found] at read
  exact ⟨echo master on found, Session.infoFields_echo s o read⟩

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
  intro h
  -- a report that leaves the echo out
  obtain ⟨-, missing⟩ :=
    h (fun _ => some true) (fun _ => some true) (fun _ _ found => found)
      (State.boot (Vt.Vt.init 1 1) [] []) 0
      { nowMs := 0, wallS := 0, login := false, foreground := none, echo := some true } rfl rfl
  simp at missing

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
  refine ⟨Listing.rowText_head width layout info, fun w hw => ?_⟩
  subst hw
  exact Listing.rowText_width w layout info

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
  intro h
  have := (h (some 0) {} []).2 0 rfl
  exact absurd this (by decide)

theorem rowText_clean (width : Option Nat) (layout : Listing.Layout)
    (info : List (String × String)) :
    ∀ c ∈ Listing.rowText width layout info, Display.Printable c :=
  Listing.rowText_printable width layout info

theorem rowText_clean_rejects_escape :
    ¬∀ (width : Option Nat) (layout : Listing.Layout) (info : List (String × String)),
        ∀
          c ∈
            (fun (_ : Option Nat) (_ : Listing.Layout) (_ : List (String × String)) => ['\x1b'])
              width layout info,
          Display.Printable c := by
  intro h
  have := h none {} [] '\x1b' (by simp)
  simp [Display.Printable] at this

theorem columns_aligned (layout : Listing.Layout) (info : List (String × String)) :
    (∃ blanks : List Char,
        (∀ c ∈ blanks, c = ' ') ∧
          (Listing.columns layout info).flatten = Listing.rowText none layout info ++ blanks) ∧
      ((((info.lookup "name").getD "").toList.map Terminal.Vt.charWidth).sum ≤ layout.nameCol →
        (Listing.columns layout info).map (fun part => (part.map Terminal.Vt.charWidth).sum) =
          layout.spans) := Listing.columns_aligned layout info

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
  intro h
  have := (h {} []).2 (by decide)
  simp [Listing.Layout.spans] at this

theorem cells_sources (i : Nat) (info info' : List (String × String))
    (h : ∀ key ∈ Listing.cellSources.getD i [], info.lookup key = info'.lookup key) :
    (Listing.cells info)[i]? = (Listing.cells info')[i]? := Listing.cells_sources i info info' h

theorem cells_sources_rejects_all :
    ¬∀ (i : Nat) (info info' : List (String × String)),
        (∀ key ∈ Listing.cellSources.getD i [], info.lookup key = info'.lookup key) →
          ((fun (info : List (String × String)) => [String.join (info.map (·.2))]) info)[i]? =
            ((fun (info : List (String × String)) => [String.join (info.map (·.2))])
                info')[i]? := by
  intro h
  have := h 0 [("x", "a")] [] (by decide)
  simp at this

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
    target ∉ s.candidates ∧ target ≠ "" ∧ Name.Accepted ((target.splitOn "@").headD "") := by
  obtain ⟨-, absent, nonempty, valid, -⟩ := Selector.Picker.step_create_valid s key target h
  exact ⟨absent, nonempty, valid⟩

theorem picker_create_new_rejects_empty :
    ¬∀ (s : Selector.Picker.State) (key : Selector.Key) (target : String),
        (fun (_ : Selector.Picker.State) (_ : Selector.Key) => Selector.Picker.Outcome.create "") s
              key =
            .create target →
          target ∉ s.candidates ∧ target ≠ "" ∧ Name.Accepted ((target.splitOn "@").headD "") := by
  intro h
  exact absurd (h { candidates := [] } .accept "" rfl).2.1 (by simp)

theorem relist_keeps_rows (s : Selector.Picker.State) (resort : Bool) (ordered : List String)
    (descriptions : List (String × String)) :
    (Selector.Picker.relist s resort ordered descriptions).candidates =
        (if resort then ordered
        else
          s.candidates.filter (fun t => ordered.contains t) ++
            ordered.filter fun t => !s.candidates.contains t) ∧
      (Selector.Picker.relist s resort ordered descriptions).query = s.query ∧
      (Selector.Picker.relist s resort ordered descriptions).descriptions = descriptions :=
  Selector.Picker.relist_rows s resort ordered descriptions

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
  intro h
  have kept := (h { candidates := ["a", "b"] } false ["b", "a"] []).1
  exact absurd kept (by decide)

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
        (Selector.Picker.enter s shown focus ordered descriptions).cursor = 0) :=
  Selector.Picker.enter_returns s shown focus ordered descriptions

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
  intro h
  have chosen := (h { candidates := [] } [] (some "b") ["a", "b"] []).2.2.1 "b" rfl rfl (by simp)
  exact absurd chosen (by decide)

theorem picker_eof_empty (s : Selector.Picker.State) :
    Selector.Picker.step s .deleteCharEof = if s.query = "" then .cancel else .stay s :=
  Selector.Picker.step_deleteCharEof s

theorem picker_eof_empty_rejects_cancel :
    ¬∀ (s : Selector.Picker.State),
        (fun (_ : Selector.Picker.State) (_ : Selector.Key) => Selector.Picker.Outcome.cancel) s
            .deleteCharEof =
          if s.query = "" then .cancel else .stay s := by
  intro h
  -- a Ctrl-D that cancelled whatever the query held would end a visit with a query typed
  have typed := h { candidates := [], query := "a" }
  simp at typed

theorem route_exact (args : List String) :
    App.Entry.route args =
      if args.head? = some Remote.marker then
        (Remote.decode args.tail).elim .malformed App.Entry.Route.of
      else App.Entry.Route.of args := by
  rw [App.Entry.route_eq args]
  cases Remote.decode args.tail <;> rfl

theorem route_exact_rejects_selector :
    ¬∀ (args : List String),
        (fun (args : List String) => App.Entry.Route.session args) args =
          if args.head? = some Remote.marker then
            (Remote.decode args.tail).elim .malformed App.Entry.Route.of
          else App.Entry.Route.of args := by
  intro h
  exact absurd (h ["attach"]) (by simp [App.Entry.Route.of, Remote.marker])

theorem op_meaning (args argv : List String) (request : App.Api.Request) (found : App.Api.Found) :
    App.Entry.route args = .session argv →
      App.Api.parse argv = some request →
      (App.Commands.lookup (argv.headD "")).map (·.op) = some request.op ∧
        App.Api.plan request = request.act ∧
        (request.op.finds found = true → App.Api.answer found = found.answer) :=
  -- the entry's route only says which words reach the session CLI
  fun _ parsed =>
  ⟨App.Api.parse_op parsed, App.Api.plan_act request, fun _ => App.Api.answer_eq found⟩

theorem op_meaning_rejects_crossed :
    ¬∀ (args argv : List String) (request : App.Api.Request) (found : App.Api.Found),
        App.Entry.route args = .session argv →
          App.Api.parse argv = some request →
          (App.Commands.lookup (argv.headD "")).map (·.op) = some request.op ∧
            App.Api.Request.crossed request = request.act ∧
            (request.op.finds found = true → App.Api.answer found = found.answer) := by
  intro h
  -- `detach x` would take `kill`'s transition
  have :=
    (h ["detach", "x"] ["detach", "x"] (.detach "x") .done App.Api.route_detach
        App.Api.parse_detach).2.1
  simp [App.Api.Request.crossed, App.Api.Request.act] at this

theorem op_meaning_rejects_outside :
    ¬∀ (args argv : List String) (request : App.Api.Request) (found : App.Api.Found),
        App.Entry.route args = .session argv →
          App.Api.parse argv = some request →
          (App.Commands.lookup (argv.headD "")).map (·.op) = some request.op ∧
            App.Api.plan request = request.act ∧
            (request.op.finds found = true →
              (fun (_ : App.Api.Found) => Os.Answer.timedOut) found = found.answer) := by
  intro h
  -- a `detach` that did what was asked would answer that its time ran out
  have :=
    (h ["detach", "x"] ["detach", "x"] (.detach "x") .done App.Api.route_detach
          App.Api.parse_detach).2.2
      rfl
  simp [App.Api.Found.answer] at this

theorem said_rendered (said : App.Api.Said) :
    App.Api.Said.render said =
      (if said.fresh then "\r\n" else "") ++ "linger: " ++ said.text ++ "\n" := by
  rfl

theorem said_rendered_rejects_bare :
    ¬∀ (said : App.Api.Said),
        (fun (said : App.Api.Said) => said.text ++ "\n") said =
          (if said.fresh then "\r\n" else "") ++ "linger: " ++ said.text ++ "\n" := by
  intro h
  have := h { text := "" }
  simp at this

theorem commands_minimal :
    (∀ op : App.Commands.Op,
        ∃ word,
          (App.Commands.lookup word).map (·.op) = some op ∧
            ∀ other, (App.Commands.lookup other).map (·.op) = some op → other = word) ∧
      App.Commands.table.map (·.op) = App.Commands.Op.all ∧
      App.Commands.helpLines = App.Commands.table.map App.Commands.helpLine ∧
      ∀ command ∈ App.Commands.table,
        App.Commands.lookup command.word = some command ∧
          ∃ rest, App.Commands.helpLine command = command.word ++ " " ++ rest :=
  ⟨App.Commands.one_spelling, App.Commands.table_ops, App.Commands.helpLines_eq,
    fun command member =>
    ⟨App.Commands.lookup_word command member, App.Commands.helpLine_word command⟩⟩

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
  intro h
  obtain ⟨word, _, unique⟩ := h.1 .attach
  have long : "attach" = word := unique "attach" (by decide)
  have short : "a" = word := unique "a" (by decide)
  exact absurd (long.trans short.symm) (by decide)

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
              fun kv => App.Fields.owns App.Fields.table .program kv.1 :=
  ⟨App.Fields.keys_nodup, App.Fields.sources_listed, App.Fields.kind_shown,
    App.Fields.user_one_writer, fun vt vt' fields fields' metadata evs evs' kept owned => by
    rw [App.Fields.infoFields_programs _
        (by
          rw [App.Fields.trace_metaKv]; exact kept),
      App.Fields.infoFields_programs _
        (by
          rw [App.Fields.trace_metaKv]; exact kept),
      owned]⟩

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
  intro h
  have := h.2.1 "status" (by decide)
  revert this
  decide

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
  -- a title read from the clients changes with a connection, which no source of it is
  intro h
  have owned :
    (Session.trace Session.step (State.boot (Vt.Vt.init 1 1) [] []) []).1.owned =
      (Session.trace Session.step (State.boot (Vt.Vt.init 1 1) [] []) [.connected 0]).1.owned :=
    (Session.step_owned_kept _ _ (fun _ h => by cases h) (fun _ h => by cases h)
        (fun _ _ h => by cases h) (fun _ h => by cases h)).symm
  have := h.2.2.2.2 (Vt.Vt.init 1 1) (Vt.Vt.init 1 1) [] [] [] [] [.connected 0] (by simp) owned
  revert this
  simp [Session.trace, Session.step, State.roster, State.boot, App.Fields.owns, App.Fields.table,
    Session.maxClients]

theorem listed_unrecorded (records : Session.Records) (panes : List Import.Resurrect.Pane)
    (pane : Import.Resurrect.Pane) :
    pane ∈ Import.Resurrect.listed records panes ↔ pane ∈ panes ∧ records.holds pane.name = false :=
  Import.Resurrect.mem_listed records panes pane

theorem listed_unrecorded_rejects_never :
    ¬∀ (records : Session.Records) (panes : List Import.Resurrect.Pane)
        (pane : Import.Resurrect.Pane),
        pane ∈
            (fun (_ : Session.Records) (_ : List Import.Resurrect.Pane) =>
                ([] : List Import.Resurrect.Pane))
              records panes ↔
          pane ∈ panes ∧ records.holds pane.name = false := by
  intro h
  have :=
    (h ⟨[], [], [], [], [], []⟩ [{ name := "a", dir := "", line := 0 }]
          { name := "a", dir := "", line := 0 }).mpr
      ⟨by simp, by decide⟩
  simp at this

theorem adopt_exclusive (records : Session.Records) (pane : Import.Resurrect.Pane)
    (contents : Option String) :
    Import.Resurrect.adopt records pane contents =
      if records.holds pane.name then none else some (Import.Resurrect.checkpoint pane contents) :=
  Import.Resurrect.adopt_eq records pane contents

theorem adopt_exclusive_rejects_overwrite :
    ¬∀ (records : Session.Records) (pane : Import.Resurrect.Pane) (contents : Option String),
        (fun (_ : Session.Records) (pane : Import.Resurrect.Pane) (contents : Option String) =>
              some (Import.Resurrect.checkpoint pane contents))
            records pane contents =
          if records.holds pane.name then none
          else some (Import.Resurrect.checkpoint pane contents) := by
  intro h
  have := h ⟨["a"], [], [], [], [], []⟩ { name := "a", dir := "", line := 0 } none
  simp [Session.Records.holds] at this

theorem dismiss_hides (records later : Session.Records) (pane : Import.Resurrect.Pane)
    (panes : List Import.Resurrect.Pane)
    (kept : ∀ name ∈ (Import.Resurrect.dismiss records pane.name).endings, name ∈ later.endings) :
    (Import.Resurrect.dismiss records pane.name).sockets = records.sockets ∧
      (Import.Resurrect.dismiss records pane.name).checkpoints = records.checkpoints ∧
      (∀ name,
        name ∈ (Import.Resurrect.dismiss records pane.name).endings ↔
          name = pane.name ∨ name ∈ records.endings) ∧
      pane ∉ Import.Resurrect.listed later panes :=
  Import.Resurrect.dismiss_hides records later pane panes kept

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
  intro h
  have :=
    ((h ⟨[], [], [], [], [], []⟩ ⟨[], [], [], [], [], []⟩ { name := "a", dir := "", line := 0 } []
              (by simp)).2.2.1
          "a").mpr
      (Or.inl rfl)
  simp at this

theorem dismissal_happened (afterSave : List UInt8 → Option (List UInt8))
    (kept : Record.Kept afterSave) (deadline heldSince : Option Nat) (now : Nat) :
    Record.answer (afterSave (Record.encode Import.Resurrect.dismissal)) = some .dismissed ∧
      App.Wait.Next.told
          (App.Wait.decide deadline heldSince now
            (.recorded (Record.answer (afterSave (Record.encode Import.Resurrect.dismissal))))) =
        some .notFound := by
  have read :
    Record.answer (afterSave (Record.encode Import.Resurrect.dismissal)) = some .dismissed := by
    rw [kept]; rfl
  exact
    ⟨read, by
      rw [read]; rfl⟩

theorem dismissal_happened_rejects_hangup :
    ¬∀ (afterSave : List UInt8 → Option (List UInt8)),
        Record.Kept afterSave →
          ∀ (deadline heldSince : Option Nat) (now : Nat),
            Record.answer (afterSave (Record.encode (Record.ended (.signaled 1)))) =
                some .dismissed ∧
              App.Wait.Next.told
                  (App.Wait.decide deadline heldSince now
                    (.recorded
                      (Record.answer (afterSave (Record.encode (Record.ended (.signaled 1))))))) =
                some .notFound := by
  intro h
  have := (h some (fun _ => rfl) none none 0).1
  rw [Record.answer_ended] at this
  cases this

theorem names_round_trip (s name : String) :
    (Name.accept s = some name ↔ name = s ∧ Name.Accepted s) ∧
      (Name.Usable name →
        Remote.targetArgs (Remote.targetOperands name) = some (name, []) ∧
          Names.entryName (Names.entryFile name) = some name) ∧
      Name.accept "build · ✓ tests" = some "build · ✓ tests" := by
  refine
    ⟨Name.accept_eq_some_iff s name, fun usable => ⟨?_, Names.entryName_entryFile name usable⟩,
      (Name.accept_eq_some_iff _ _).mpr ⟨rfl, .inl ((Name.usable_iff _).mp (by decide))⟩⟩
  simpa using Remote.targetArgs_targetOperands name []

theorem names_round_trip_rejects_keyed :
    ¬∀ (s name : String),
        (Name.keyed s = some name ↔ name = s ∧ Name.Accepted s) ∧
          (Name.Usable name →
            Remote.targetArgs (Remote.targetOperands name) = some (name, []) ∧
              Names.entryName (Names.entryFile name) = some name) ∧
          Name.keyed "build · ✓ tests" = some "build · ✓ tests" := by
  intro h
  have := (h "a b" "a b").1.mpr ⟨rfl, .inl ((Name.usable_iff _).mp (by decide))⟩
  revert this
  decide

theorem check_eq_some_iff (s result : String) :
    Name.check s = some result ↔ result = s ∧ Name.Valid s := Name.check_eq_some_iff s result

theorem check_eq_some_iff_rejects_any :
    ¬∀ (s result : String), (fun s => some s) s = some result ↔ result = s ∧ Name.Valid s := by
  intro h
  exact absurd ((h "" "").mp rfl).2.1 (by simp)

theorem command_exact (split : String → List String) (literal : Remote.Shell.Literal split)
    (verb : String) (words : List String) :
    ∃ args,
      split (String.intercalate " " (Remote.commandWords verb words)) = "linger" :: args ∧
        App.Entry.route args = App.Entry.Route.of (verb :: words) := by
  obtain ⟨encoded, received, decoded⟩ := Remote.command_decode split literal verb words
  rw [← Remote.intercalate_commandWords] at received
  exact ⟨Remote.marker :: encoded, received, App.Entry.route_encoded encoded _ decoded⟩

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
  intro h
  -- fish keeps the world claim, and reads POSIX quoting of `send \'` as `send ''`
  obtain ⟨args, received, routed⟩ := h Remote.fishSplit Remote.fishSplit_literal "send" ["\\'"]
  dsimp only at received
  rw [Remote.fishSplit_quoted] at received
  simp only [List.cons.injEq, true_and] at received
  subst received
  rw [App.Entry.route_eq] at routed
  simp [App.Entry.Route.of, Remote.marker] at routed

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
  refine ⟨?_, Remote.targetArgs_targetOperands name args⟩
  refine
    ⟨Remote.marker ::
        (verb :: options ++
              (if verb = "attach" ∨ verb = "capture" ∨ verb = "ls" then Remote.targetOperands name
              else [name]) ++
              args).map
          Remote.encodeWord,
      Remote.targetArgv_eq t verb options name args, ?_,
      App.Entry.route_encoded _ _ (Remote.decode_map_encodeWord _)⟩
  intro received ran
  -- the words after `linger` are plain, so the transport runs a `linger` with exactly them
  have plain :
    ∀
      word ∈
        Remote.marker ::
          (verb :: options ++
                (if verb = "attach" ∨ verb = "capture" ∨ verb = "ls" then Remote.targetOperands name
                else [name]) ++
                args).map
            Remote.encodeWord,
      Remote.Shell.plain word = true := by
    intro word member
    simp only [List.mem_cons, List.mem_map] at member
    rcases member with rfl | ⟨original, -, rfl⟩
    · exact Remote.plain_marker
    · exact Remote.plain_encodeWord original
  have chosen : (if verb = "attach" then t.attach else t.query) ∈ [t.query, t.attach] := by
    split <;> simp
  rcases delivers _ chosen _ plain with nothing | exactly
  · rw [nothing] at ran
    cases ran
  · rw [exactly] at ran
    exact (Option.some.inj ran).symm

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
  intro h
  -- a transport the remotes file names, `docker`, which ssh hard-coded in its place ignores
  obtain ⟨⟨line, ran, -, -⟩, -⟩ :=
    h { query := ["docker"], attach := ["docker"] } "send" "w" [] [] (fun _ words => some words)
      (fun _ _ _ _ => Or.inr rfl)
  simp at ran

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
  intro h
  -- a target placed as nothing, which the far end cannot read back as the name
  have read :=
    (h { query := ["ssh"], attach := ["ssh"] } "attach" "s" [] [] (fun _ words => some words)
        (fun _ _ _ _ => Or.inr rfl)).2
  simp [Remote.targetArgs_nil] at read

theorem env_defaults (home flag : Option String) (shell dir saved : String) (named : shell ≠ "")
    (set : dir ≠ "") :
    (Os.Env.shellOf (some shell) = shell ∧
        Os.Env.shellOf none = "sh" ∧ Os.Env.shellOf (some "") = "sh") ∧
      (Os.Env.remotesFile home = none ↔ home = none ∨ home = some "") ∧
      (Os.Env.detachEnabled true flag = true ∧ Os.Env.detachEnabled false flag = flag.isNone) ∧
      Os.Env.resumeDir home saved true = some saved ∧
      Os.Env.resumeDir (some dir) saved false = some dir ∧
      Os.Env.resumeDir none saved false = none ∧ Os.Env.resumeDir (some "") saved false = none :=
  ⟨⟨Os.Env.shellOf_set named, Os.Env.shellOf_absent.1, Os.Env.shellOf_absent.2⟩,
    Os.Env.remotesFile_eq_none_iff home,
    ⟨Os.Env.detachEnabled_readOnly flag, Os.Env.detachEnabled_writable flag⟩,
    Os.Env.resumeDir_saved home saved, Os.Env.resumeDir_home set saved,
    (Os.Env.resumeDir_absent saved).1, (Os.Env.resumeDir_absent saved).2⟩

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
  intro h
  exact absurd (h none none "fish" "b" "a" (by decide) (by decide)).1.1 (by decide)

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
  intro h
  exact absurd ((h none none "fish" "b" "a" (by decide) (by decide)).2.1.mpr (.inl rfl)) (by simp)

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
  intro h
  exact absurd (h none none "fish" "b" "a" (by decide) (by decide)).2.2.1.1 (by decide)

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
  intro h
  exact absurd (h none none "fish" "b" "a" (by decide) (by decide)).2.2.2.2.2.1 (by decide)

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

theorem input_unrecorded (vt : Vt.Vt) (fields metadata : List (String × String))
    (evs evs' : List Event) (framed : ∀ ev ∈ evs, Framed Wire.encode ev)
    (typed : Typed Wire.encode evs evs') :
    (Session.trace Session.step (State.boot vt fields metadata) evs).1 =
        (Session.trace Session.step (State.boot vt fields metadata) evs').1 ∧
      (Session.trace Session.step (State.boot vt fields metadata) evs).2.map Effect.blind =
        (Session.trace Session.step (State.boot vt fields metadata) evs').2.map Effect.blind :=
  Session.trace_typed _ (Session.boot_whole vt fields metadata) evs evs' framed typed

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
  -- a session that keeps what a client typed in its terminal tells two typings apart
  intro h
  have fits : ∀ bytes : List UInt8, bytes.length ≤ 2 → ∀ m ∈ [Wire.Msg.input bytes], m.Fits := by
    intro bytes hb m hm
    simp only [List.mem_singleton] at hm
    subst hm
    simp only [Wire.Msg.Fits]
    exact Nat.le_trans hb (by decide)
  have typed :
    Typed Wire.encode [.connected 0, .bytes 0 ([Wire.Msg.input [0x41]].flatMap Wire.encode)]
      [.connected 0, .bytes 0 ([Wire.Msg.input [0x41, 0x41]].flatMap Wire.encode)] :=
    .same _ (.input 0 _ _ (fits [0x41] (by decide)) (fits [0x41, 0x41] (by decide)) rfl .nil)
  have framed :
    ∀ ev ∈ [Event.connected 0, .bytes 0 ([Wire.Msg.input [0x41]].flatMap Wire.encode)],
      Framed Wire.encode ev := by
    intro ev hev
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hev
    rcases hev with rfl | rfl
    · trivial
    · exact ⟨_, rfl, fits [0x41] (by decide)⟩
  have same :=
    congrArg (fun s => s.terminal.cursorPos) (h (Vt.Vt.init 10 1) [] [] _ _ framed typed).1
  rw [Session.keepsInput_terminal _ (by decide), Session.keepsInput_terminal _ (by decide)] at same
  revert same
  decide +kernel

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
  obtain ⟨hargv, hdir, henv⟩ := runs _ _ _ _ _ _ ok
  rw [Start.programOf_exact] at hargv
  refine ⟨by simpa using hargv, hdir, ?_, ?_, ?_, ?_, ?_, ?_, fun key hkey => ?_⟩
  all_goals rw [henv, Start.environment_lookup _ _ _ _ _ (named _)]
  · simp
  · simp
  · simp
  · simp
  · simp
  · simp
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hkey
    simp [hkey.1, hkey.2.1, hkey.2.2.1, hkey.2.2.2.1, hkey.2.2.2.2.1, hkey.2.2.2.2.2]

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
  intro h
  -- a caller with `LINGER_DIR` set, which an environment that unsets nothing passes through
  let inherited := fun key : String => if key = "LINGER_DIR" then some "state" else none
  have runs :
    Spawn.Runs inherited fun dir prog args extra _ =>
      some
        { argv := prog :: args.toList, dir,
          env := fun key => (extra.reverse.lookup key).getD (inherited key),
          ignored := fun _ => false, blocked := fun _ => false, descriptor := fun _ => none } := by
    intro dir prog args extra reset started hs
    cases hs
    exact ⟨rfl, rfl, fun _ => rfl⟩
  have named : ∀ key, (inherited key).isSome → key ∈ ["LINGER_DIR"] := by
    intro key h
    by_cases dirKey : key = "LINGER_DIR"
    · simp [dirKey]
    · simp [inherited, dirKey] at h
  have passed :=
    (h _ _ runs ["LINGER_DIR"] named "x" "n" "" "sh" [] rfl).2.2.2.2.2.2.2.2 "LINGER_DIR"
      (by decide)
  simp [Start.lingers, Start.environment, Start.session, List.lookup, inherited] at passed

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
  exact absurd ((h _ clean "x" "n" "" "sh" [] [] rfl).1 2) (by simp)

theorem step_kill_stops (s : State) (id : Nat) (chunk : List UInt8) {c : Client}
    {dec : Wire.Decoder} {rest : List Wire.Msg} (hc : s.client? id = some c)
    (writable : c.mode = .writable) (read : c.decoder.feed chunk = (dec, .kill :: rest))
    (healthy : dec.errored = false) :
    (Session.step s (.bytes id chunk)).2 = [.stopProgram, .close id] ∧
      (Session.step s (.bytes id chunk)).1.terminal = s.terminal ∧
      (Session.step s (.bytes id chunk)).1.fieldList = s.fieldList :=
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
                  (.bytes id chunk)).1.fieldList =
              s.fieldList := by
  intro h
  obtain ⟨joined, -⟩ := Session.connected_client_witness
  have stopped :=
    (@h (Session.trace Session.step (State.boot (Vt.Vt.init 1 1) [] []) [.connected 1]).1 1
        (Wire.encode .kill) { id := 1 } {} [] joined rfl
        (Session.feed_encode_fresh .kill (by simp [Wire.Msg.Fits])) rfl).1
  simp at stopped

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
              (Session.step s ev).1.terminal = s.terminal := Session.step_ended_reports s ev

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
  intro h
  obtain ⟨front, effects, -, -, heard, -⟩ :=
    (h (State.boot (Vt.Vt.init 1 1) [] []) (.childExited .unknown)).2 (.program .unknown) false rfl
  have only :
    [Effect.send 0 (.exited 1)] ++ [.record (.ended .unknown), .dropCheckpoint, .exit] =
      front ++ [.record (.ended .unknown), .dropCheckpoint, .exit] :=
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

theorem visit_result (afterSave : List UInt8 → Option (List UInt8)) (kept : Record.Kept afterSave)
    (readOnly : Bool) (o : Outcome) (n : UInt8) (seen : Option Seen) :
    App.Recovery.visit readOnly (afterSave (Record.encode (.ended o))) =
        [.show, .tell o, .discard] ∧
      App.Recovery.visit readOnly (afterSave (Record.encode (.saved n))) =
        (if readOnly then [.show] else [.resume]) ∧
      App.Recovery.visit readOnly (afterSave (Record.encode (.running seen))) =
        (if readOnly then [.show] else [.resume]) ∧
      App.Recovery.visit readOnly none = (if readOnly then [.show] else [.resume]) := by
  rw [kept, kept, kept]
  exact
    ⟨App.Recovery.visit_ended readOnly o, App.Recovery.visit_saved readOnly n,
      App.Recovery.visit_running readOnly seen, App.Recovery.visit_none readOnly⟩

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
  intro h
  have shown := (h some (fun _ => rfl) false .unknown 0 none).1
  simp at shown

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
    App.Wait.decide deadline heldSince now (.ended e) = .answer (.ended e) ∧
      App.Wait.decide deadline heldSince now (.recorded (some e)) = .answer (.ended e) :=
  App.Wait.wait_ending deadline heldSince now e

theorem wait_ending_rejects_failed :
    ¬∀ (deadline heldSince : Option Nat) (now : Nat) (e : Ending),
        (fun (_ _ : Option Nat) (_ : Nat) (_ : App.Wait.Heard) => App.Wait.Next.answer .unknown)
              deadline heldSince now (.ended e) =
            .answer (.ended e) ∧
          (fun (_ _ : Option Nat) (_ : Nat) (_ : App.Wait.Heard) => App.Wait.Next.answer .unknown)
              deadline heldSince now (.recorded (some e)) =
            .answer (.ended e) := by
  intro h
  have told := (h none none 0 (.program (.exited 0))).1
  simp at told

theorem wait_held (deadline heldSince : Option Nat) (now : Nat) (heard : App.Wait.Heard) :
    (App.Wait.Next.told (App.Wait.decide deadline heldSince now heard) = some .failed ↔
        heard = .ended (.program .unknown) ∨
          heard = .recorded (some (.program .unknown)) ∨
          heard = .held ∧ ∃ since, heldSince = some since ∧ since + App.Wait.heldNameMs ≤ now) ∧
      (heard = .held →
        (∀ due, deadline = some due → now < due) →
        (∀ since, heldSince = some since → now < since + App.Wait.heldNameMs) →
        App.Wait.decide deadline heldSince now heard = .again (some (heldSince.getD now))) ∧
      (heard = .held →
        ∀ since,
          heldSince = some since →
            now < since + (Session.drainTimeoutMs + (Session.ending.map (·.wait)).sum) →
            App.Wait.Next.told (App.Wait.decide deadline heldSince now heard) ≠ some .failed) := by
  refine
    ⟨(App.Wait.wait_held deadline heldSince now heard).1,
      (App.Wait.wait_held deadline heldSince now heard).2, ?_⟩
  intro held since named ending failed
  have := (App.Wait.wait_held deadline heldSince now heard).1.mp failed
  subst held
  rcases this with h | h | ⟨-, since', named', late⟩
  · cases h
  · cases h
  · rw [named] at named'
    cases named'
    have := App.Wait.held_covers_ending
    omega

theorem wait_held_rejects_eager :
    ¬∀ (deadline heldSince : Option Nat) (now : Nat) (heard : App.Wait.Heard),
        (App.Wait.Next.told
                ((fun (_ _ : Option Nat) (_ : Nat) (_ : App.Wait.Heard) =>
                    App.Wait.Next.answer .unknown)
                  deadline heldSince now heard) =
              some .failed ↔
            heard = .ended (.program .unknown) ∨
              heard = .recorded (some (.program .unknown)) ∨
              heard = .held ∧ ∃ since, heldSince = some since ∧ since + App.Wait.heldNameMs ≤ now) ∧
          (heard = .held →
            (∀ due, deadline = some due → now < due) →
            (∀ since, heldSince = some since → now < since + App.Wait.heldNameMs) →
            (fun (_ _ : Option Nat) (_ : Nat) (_ : App.Wait.Heard) => App.Wait.Next.answer .unknown)
                deadline heldSince now heard =
              .again (some (heldSince.getD now))) ∧
          (heard = .held →
            ∀ since,
              heldSince = some since →
                now < since + (Session.drainTimeoutMs + (Session.ending.map (·.wait)).sum) →
                App.Wait.Next.told
                    ((fun (_ _ : Option Nat) (_ : Nat) (_ : App.Wait.Heard) =>
                        App.Wait.Next.answer .unknown)
                      deadline heldSince now heard) ≠
                  some .failed) := by
  intro h
  have failed := ((h none none 0 .held).1).mp rfl
  simp at failed

theorem wait_held_rejects_drain :
    ¬∀ (deadline heldSince : Option Nat) (now : Nat) (heard : App.Wait.Heard),
        (App.Wait.Next.told (App.Wait.decide deadline heldSince now heard) = some .failed ↔
            heard = .ended (.program .unknown) ∨
              heard = .recorded (some (.program .unknown)) ∨
              heard = .held ∧
                ∃ since, heldSince = some since ∧ since + Session.drainTimeoutMs ≤ now) ∧
          (heard = .held →
            (∀ due, deadline = some due → now < due) →
            (∀ since, heldSince = some since → now < since + Session.drainTimeoutMs) →
            App.Wait.decide deadline heldSince now heard = .again (some (heldSince.getD now))) ∧
          (heard = .held →
            ∀ since,
              heldSince = some since →
                now < since + (Session.drainTimeoutMs + (Session.ending.map (·.wait)).sum) →
                App.Wait.Next.told (App.Wait.decide deadline heldSince now heard) ≠
                  some .failed) := by
  intro h
  -- a wait that fails once a drain has passed, while the ending's signals still wait
  have k := h none (some 0) Session.drainTimeoutMs .held
  exact k.2.2 rfl 0 rfl (by decide) (k.1.mpr (.inr (.inr ⟨rfl, 0, rfl, by simp⟩)))

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
      Os.Answer.code (.program status) = status := Os.Answer.code_documented status signal

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
  intro h
  exact absurd (h 0 0).2.1 (by decide)

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
  intro h
  -- SIGTERM's status is 143, which the rule that answered 130 for every signal does not give
  exact absurd (h 0 15).2.2.2.2.2.2.2.2.1 (by decide)

theorem endingFields_injective :
    (∀ o, Session.endingFields (.program o) = Session.outcomeFields o) ∧
      ∀ e₁ e₂, Session.endingFields e₁ = Session.endingFields e₂ → e₁ = e₂ :=
  ⟨Session.endingFields_program, fun _ _ h => Session.endingFields_injective h⟩

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
  intro h
  -- a reader that hears a saved session as one whose program's ending is unknown
  have same := h.2 (.saved 15) (.program .unknown) (by simp)
  cases same

theorem endingFields_injective_rejects_silence :
    ¬((∀ o,
          Session.endingFields (.program o) =
            (fun (_ : Outcome) => ([] : List (String × String))) o) ∧
        ∀ e₁ e₂, Session.endingFields e₁ = Session.endingFields e₂ → e₁ = e₂) := by
  intro h
  -- a listing of end records that reports no ending at all
  exact
    Session.outcomeFields_ne_nil (.exited 0) ((Session.endingFields_program _).symm.trans (h.1 _))

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
      (Session.step s (.bytes id chunk)).1.fieldList = s.fieldList :=
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
                  (.bytes id chunk)).1.fieldList =
              s.fieldList := by
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
    (Session.step_exit_iff (State.boot (Vt.Vt.init 1 1) [] []) (.childExited .unknown) false).mpr
      rfl
  cases handles with
  | exit => simp [Driver.inert] at stayed
  | next _ _ _ _ _ stays => exact stays ends

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
  have overflow := bounds.fieldsLe
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

theorem locks_named (records : Session.Records) (name : String)
    (before : ∀ held ∈ records.locks, held = name ∨ records.holds held = true) :
    (Session.Locks.release records name).sockets = records.sockets ∧
      (Session.Locks.release records name).notifies = records.notifies ∧
      (Session.Locks.release records name).checkpoints = records.checkpoints ∧
      (Session.Locks.release records name).endings = records.endings ∧
      (∀ held ∈ records.locks,
        records.holds held = true → held ∈ (Session.Locks.release records name).locks) ∧
      ∀ held ∈ (Session.Locks.release records name).locks,
        (Session.Locks.release records name).holds held = true :=
  Session.Locks.release_named records name before

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
  intro h
  have :=
    (h { sockets := [], checkpoints := [], endings := [], locks := ["a"] } "a" (by simp)).2.2.2.2.2
      "a" (by simp)
  simp [Session.Records.holds] at this

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
    (member reaches : Nat → Nat → Bool) (group : Os.Signal.Group member reaches) (program : Nat)
    (alive : List Nat) (members : ∀ pid ∈ alive, member program pid = true) :
    (Session.ending.head?.map (·.signal)) = some 1 ∧
      Session.ending.foldl (Stop.survivors (Stop.reach program reaches) gone) alive = [] := by
  rw [Session.ending_eq]
  refine ⟨rfl, List.filter_eq_nil_iff.mpr fun pid mem => ?_⟩
  -- SIGKILL to the group reaches each process of it that SIGHUP left, which then ends
  have inGroup := members pid (List.mem_filter.mp mem).1
  simp [Stop.reach, group program pid inGroup, ends pid Stop.grace (Nat.le_refl _)]

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
  intro h
  -- a group of two, the program 0 and its job 1, where every signal ends what it reaches: the
  -- job, which no signal to the program alone reaches, outlives the stop
  have ends : Signal.Ends fun _ _ _ => true := fun _ _ _ => rfl
  have group : Os.Signal.Group (fun _ _ => true) fun _ _ => true := fun _ _ _ => rfl
  have survives := (h _ ends _ _ group 0 [1] fun _ _ => rfl).2
  exact absurd survives (by decide)

theorem handoff_carries (s : State) (w : Handoff.World)
    (h :
      Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
        (Checkpoint.Decoded Checkpoint.loadBytes) s.terminal)
    (quiet : s.terminal.quiesce = s.terminal) : Handoff.decode (Handoff.encode s w) = some (s, w) :=
  Handoff.decode_encode s w (Checkpoint.live_of_decoded h) quiet

/-- A world a daemon could hand over, for the kills. -/
private def someWorld : Handoff.World :=
  { listenFd := 0, ptyFd := 0, childPid := 0, signals := (0, 0), locks := [], conns := [],
    ptyIn := [], login := false, asker := 0 }

private theorem init_quiet : (Vt.Vt.init 1 1).quiesce = Vt.Vt.init 1 1 := Vt.quiesce_of_quiet rfl

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
  intro h
  have carried := h (State.boot (Vt.Vt.init 1 1) [] [("k", "v")]) someWorld (.init 1 1) init_quiet
  rw [Handoff.decode_encode _ _ (.init 1 1) init_quiet] at carried
  simp [State.boot, State.terminal, State.fieldList] at carried

theorem upgrade_keeps (exec : Nat → List Nat → List Nat → Nat × List Nat × List Nat)
    (keeps : Os.Exec.Keeps exec) (pid : Nat) (w : Handoff.World) :
    (exec pid [w.childPid] (Handoff.kept w)).1 = pid ∧
      (exec pid [w.childPid] (Handoff.kept w)).2.1 = [w.childPid] ∧
      ∀ fd ∈ w.fds, fd ∈ (exec pid [w.childPid] (Handoff.kept w)).2.2 := by
  rw [keeps pid [w.childPid] (Handoff.kept w)]
  exact ⟨rfl, rfl, Handoff.fds_kept w⟩

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
  intro h
  -- an exec that keeps the socket and the pty, and closes a lock
  have kept :=
    (h (fun pid children kept => (pid, children, kept)) (fun _ _ _ => rfl) 0
          { listenFd := 3, ptyFd := 4, childPid := 1, signals := (5, 6), locks := [7], conns := [],
            ptyIn := [], login := false, asker := 0 }).2.2
      7 (by simp [Handoff.World.fds])
  simp at kept

theorem handoff_versioned (s : State) (w : Handoff.World) (v : Nat) (rest : List UInt8) :
    Handoff.version ∈ Handoff.formats ∧
      (Handoff.encode s w).take (Handoff.header Handoff.version).length =
        Handoff.header Handoff.version ∧
      (v ∉ Handoff.formats → v < 256 → Handoff.decode (Handoff.header v ++ rest) = none) :=
  ⟨by decide, Handoff.encode_header s w, Handoff.decode_unknown v rest⟩

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
  intro h
  let s := State.boot (Vt.Vt.init 1 1) [] []
  let rest := (Handoff.encode s someWorld).drop (Handoff.header Handoff.version).length
  have refused := (h s someWorld 200 rest).2.2 (by decide) (by decide)
  have dropped :
    (Handoff.header 200 ++ rest).drop (Handoff.header Handoff.version).length = rest := by
    simp [Handoff.header]
  have whole : Handoff.header Handoff.version ++ rest = Handoff.encode s someWorld := by
    simp [rest, Handoff.encode]
  dsimp only at refused
  rw [dropped, whole, Handoff.decode_encode _ _ (.init 1 1) init_quiet] at refused
  cases refused

theorem upgrade_probes (reported : Option (List Nat)) :
    Upgrade.proceeds reported = true ↔
      ∃ formats, reported = some formats ∧ Handoff.version ∈ formats :=
  Upgrade.proceeds_iff reported

theorem upgrade_probes_rejects_unprobed :
    ¬∀ (reported : Option (List Nat)),
        (fun (_ : Option (List Nat)) => true) reported = true ↔
          ∃ formats, reported = some formats ∧ Handoff.version ∈ formats := by
  intro h
  obtain ⟨_, none_some, _⟩ := (h none).1 rfl
  cases none_some

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
    (State.boot (bootVt ((Checkpoint.loadBytes (Checkpoint.saveBytes c)).map (·.vt)))
            (((Checkpoint.loadBytes (Checkpoint.saveBytes c)).map (·.fields)).getD [])
            metaKv).terminal =
        c.vt.quiesce ∧
      (State.boot (bootVt ((Checkpoint.loadBytes (Checkpoint.saveBytes c)).map (·.vt)))
            (((Checkpoint.loadBytes (Checkpoint.saveBytes c)).map (·.fields)).getD [])
            metaKv).fieldList =
        (c.fields.filter (recordField ·.1)).take maxFields := by
  have loaded :
    Checkpoint.loadBytes (Checkpoint.saveBytes c) = some { c with vt := c.vt.quiesce } :=
    Checkpoint.loadBytes_saveBytes_live c (Checkpoint.live_of_decoded h)
  obtain ⟨_, restored, terminal, -, labels, -⟩ := Session.boot_observed c.vt.quiesce c.fields metaKv
  simp only [loaded, Option.map_some, Option.getD_some, restored]
  exact ⟨terminal, labels⟩

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
  intro h
  have fresh := (h ⟨Vt.Vt.init 2 1, "", []⟩ (.init 2 1) []).1
  obtain ⟨-, -, terminal, -, -, -⟩ :=
    Session.boot_observed (Vt.Vt.init 1 1)
      (((Checkpoint.loadBytes (Checkpoint.saveBytes ⟨Vt.Vt.init 2 1, "", []⟩)).map (·.fields)).getD
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
  intro changed unsaved
  exact
    Session.unsaved_due _ ev post (Session.boot_lastCkptMs_le vt fields metaKv pre) changed unsaved

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
      (Import.Resurrect.checkpoint pane contents).fields.lookup "tmux.command" =
        some pane.details.command ∧
      (Import.Resurrect.checkpoint pane contents).fields.lookup "tmux.saved-command" =
        some pane.details.savedCommand ∧
      (Import.Resurrect.checkpoint pane contents).fields.lookup "tmux.capture" =
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
  intro h
  exact absurd (h { name := "a", dir := "x", line := 0 } none).1 (by decide)

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
  rw [Checkpoint.loadBytes_format3 c (Checkpoint.live_of_decoded h) old format3]
  simp [Checkpoint.readFields, undescribed]

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
  intro h
  -- a reader that drops the description an older record reads with
  have k :=
    h ⟨Vt.Vt.init 1 1, "", [("tmux.window-title", "w")]⟩ (.init 1 1) (by simp)
      ⟨([0x4C, 0x4E, 0x47, 0x52, 3] ++
            (Checkpoint.saveBytes
                  ⟨Vt.Vt.init 1 1, "", [("tmux.window-title", "w")]⟩).data.toList.drop
              5).toArray⟩
      (by simp)
  simp only [] at k
  rw [older_record_described ⟨Vt.Vt.init 1 1, "", [("tmux.window-title", "w")]⟩ (.init 1 1)
      (by simp) _ (by simp)] at k
  simp [Checkpoint.importDescription] at k

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
  have info (s : State) : Display.Clean (Session.infoText s) := by
    obtain ⟨cs, text, safe⟩ := infoText_text s
    rw [text]
    exact
      Display.clean_text fun c hc =>
        (safe c hc).elim (fun tab => .inr (.inr tab)) fun rest =>
          rest.elim (fun newline => .inr (.inl newline)) .inl
  exact
    ⟨Display.terminalListing_clean, Selector.Picker.frame_clean, Selector.Picker.frameRows_clean,
      Selector.Picker.update_clean, Selector.Picker.enterAnsi_clean, Selector.Picker.exitAnsi_clean,
      Display.title_ansi_clean, Display.title_update_clean, Display.screenText_clean,
      Display.history_clean, info, Display.Alert.notification_clean, Display.leaveAnsi_clean⟩

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
        Display.Clean Terminal.Render.leaveAnsi) :=
  fun h => Display.not_clean_reset (h.1 true none [])

theorem withColor_iff (terminal : Bool) (noColor term : Option String) :
    Os.Env.withColor terminal noColor term = true ↔
      terminal = true ∧
        (noColor = none ∨ noColor = some "") ∧
        ∃ name, term = some name ∧ name ≠ "" ∧ name ≠ "dumb" :=
  Os.Env.withColor_iff terminal noColor term

theorem withColor_iff_rejects_presence :
    ¬∀ (terminal : Bool) (noColor term : Option String),
        (fun (terminal : Bool) (noColor : Option String) (_ : Option String) =>
                terminal && noColor.isNone)
              terminal noColor term =
            true ↔
          terminal = true ∧
            (noColor = none ∨ noColor = some "") ∧
            ∃ name, term = some name ∧ name ≠ "" ∧ name ≠ "dumb" := by
  intro h
  have colors :=
    (h true (some "") (some "xterm")).mpr ⟨rfl, .inr rfl, "xterm", rfl, by simp, by simp⟩
  exact absurd colors (by decide)

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
                    []).length).sum :=
  Selector.Picker.repaints_changes sa sb na nb fa fb la ca ta lb cb tb aa ab v hv between replacing
    wraps absolute top bottom ascii0 ascii1

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
  intro h
  have init :=
    Vt.Live.init (init := Vt.Vt.init) (feed := Vt.Vt.feed) (resize := Vt.Vt.resize) (quiesce :=
      Vt.Vt.quiesce) (decodable := Vt.Vt.Decodable) 1 1
  have bound :=
    (h (Selector.Picker.init []) (Selector.Picker.init []) {} {} (fun _ => default)
        (fun _ => default) false false false false false false none none (Vt.Vt.init 1 1) init
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)).2.2
  have zero : ∀ n, (List.replicate n (0 : Nat)).sum = 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [List.replicate_succ, List.sum_cons, ih]
  simp only [↓reduceIte, List.map_const', zero, List.length_append, List.length_cons,
    List.length_nil] at bound
  omega

theorem fetch_follows_events (events : List Selector.Picker.Event) :
    Selector.Picker.due Selector.Picker.fetch events = true ↔
      (∀ e ∈ events, e.isKey = true) ∨
        Selector.Picker.Event.key .refresh ∈ events.reverse.takeWhile Selector.Picker.Event.isKey :=
  Selector.Picker.due_fetch_iff events

theorem fetch_follows_events_rejects_polling :
    ¬∀ (events : List Selector.Picker.Event),
        Selector.Picker.due (fun (_ : Bool) (_ : Selector.Picker.Event) => true) events = true ↔
          (∀ e ∈ events, e.isKey = true) ∨
            Selector.Picker.Event.key .refresh ∈
              events.reverse.takeWhile Selector.Picker.Event.isKey := by
  intro h
  -- a chooser that fetched remote rows for every listing would fetch them for its second
  have second := (h [.list]).mp rfl
  simp at second

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
          (ops.filter Offloop.Op.isDone).length + 1 :=
  ⟨Session.Offloop.latest_started earlier w ends, Session.Offloop.started_bound⟩

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
  intro h
  -- two writes asked for at once both start, neither waiting for the other
  have twice := (h (W := Unit) [] () 0).2 [.ask (), .ask ()]
  simp [Offloop.cycle, Offloop.eager, Offloop.Op.isDone] at twice

theorem capture_waits_unlocked :
    (∀ steps,
        (App.Capture.phases steps).flatMap App.Capture.Phase.work = App.Capture.work steps false) ∧
      (App.Capture.work App.Capture.plan false).map Prod.fst = [.load, .render, .write] ∧
      (.load, true) ∈ App.Capture.work App.Capture.plan false ∧
      ∀ step, (step, true) ∈ App.Capture.work App.Capture.plan false → step.waitsOutside = false :=
  ⟨App.Capture.phases_work, App.Capture.waits_unlocked⟩

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
  -- the write runs holding the locks, and it waits on whoever reads it
  rintro ⟨-, -, -, unheld⟩
  exact absurd (unheld .write (by decide)) (by decide)

theorem capture_waits_unlocked_rejects_held :
    ¬((∀ steps,
          ((fun (steps : List App.Capture.Step) => [App.Capture.Phase.locked steps]) steps).flatMap
              App.Capture.Phase.work =
            App.Capture.work steps false) ∧
        (App.Capture.work App.Capture.plan false).map Prod.fst = [.load, .render, .write] ∧
        (.load, true) ∈ App.Capture.work App.Capture.plan false ∧
        ∀ step,
          (step, true) ∈ App.Capture.work App.Capture.plan false → step.waitsOutside = false) := by
  -- a shell that holds the locks through every step, the write included
  rintro ⟨phased, -⟩
  exact absurd (phased [.write]) (by decide)

theorem classify_iff (o : Status.Obs) (s : Status.Status) : Status.classify o = s ↔ Status.Is s o :=
  Status.classify_iff o s

theorem classify_iff_rejects_idle :
    ¬∀ (o : Status.Obs) (s : Status.Status),
        (fun (_ : Status.Obs) => ({ attention := .none, state := .idle } : Status.Status)) o = s ↔
          Status.Is s o := by
  intro h
  exact absurd ((h { known := false } ⟨.none, .unknown⟩).mpr ⟨⟨rfl, rfl⟩, rfl⟩) (by decide)

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
  refine ⟨Session.seen_progress s, Session.seen_running s, ?_⟩
  rw [Session.seen_progress, Session.seen_running]
  simp only [Status.classify, Status.stateOf]
  cases s.owned.progress with
  | none => cases s.owned.commands.running.isSome <;> simp
  | some p => cases p <;> simp

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
  -- a program that wrote a moment ago, and declared nothing, reads working by the window
  intro h
  have := (h (Session.step Session.wroteUnticked (.tick 0)).1).2.1
  rw [Session.windowed_ticked, Session.ticked_declares_nothing] at this
  cases this

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
  refine
    ⟨fun chunk hev => by
      subst hev
      exact Session.step_ptyOut_progress s chunk, fun out => Session.step_progress_kept s ev out,
      ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩⟩
  · simp [Status.classify, Status.stateOf, h]
  · simp [Status.classify, Status.stateOf, h]
  · rcases h with h | h <;> simp [Status.classify, Status.stateOf, h]

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
  -- an error read as progress under way is not the error the program declared
  intro h
  have := (h (State.boot (Vt.Vt.init 2 1) [] []) (.ptyOut (Session.report 0x32))).1 _ rfl
  rw [Session.errorWorks_report.1, Session.errorWorks_report.2] at this
  cases this

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
  -- a pause read as progress under way is not the pause the program declared
  intro h
  have := (h (State.boot (Vt.Vt.init 2 1) [] []) (.ptyOut (Session.report 0x34))).1 _ rfl
  rw [Session.pauseWorks_report.1, Session.pauseWorks_report.2] at this
  cases this

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
  -- an error the program never removed is lost at its next output
  intro h
  have := (h Session.declaredError (.ptyOut [])).1 [] rfl
  rw [Session.forgets_declaredError, Session.declaredError_kept] at this
  cases this

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
        (Session.step s ev).1.seen.unseen = true → s.seen.unseen = true) :=
  ⟨fun chunk hev => by
    subst hev
    exact Session.step_ptyOut_unseen s chunk,
    fun id chunk c dec m hev hc fresh read healthy looks => by
    subst hev
    exact Session.step_look_unseen s id chunk hc fresh read healthy looks, fun out raised =>
    Session.step_unseen_raised s ev out raised⟩

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
  -- output that adds no line to the history, here none at all, is unseen by any output
  intro h
  have := (h (State.boot (Vt.Vt.init 2 1) [] []) (.ptyOut [])).1 [] rfl
  rw [Session.anyOutput_output, Session.anyOutput_boot, Session.feed_nil_lines] at this
  simp at this

theorem status_clockless (s : State) (times : List Nat) :
    (Session.trace Session.step s (times.map Event.tick)).1.seen = s.seen :=
  Session.trace_ticks_seen s times

theorem status_clockless_rejects_window :
    ¬∀ (s : State) (times : List Nat),
        Seen.windowed Session.infoFields State.seen
            (Session.trace Session.step s (times.map Event.tick)).1 =
          Seen.windowed Session.infoFields State.seen s := by
  -- by the window, a program that wrote reads working once a tick records when
  intro h
  have := congrArg Seen.running (h Session.wroteUnticked [0])
  simp only [List.map_cons, List.map_nil, Session.trace] at this
  rw [Session.windowed_ticked, Session.windowed_unticked] at this
  cases this

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
          ∀ line ∈ states, ∃ s, line.toList.head? = some (Status.icon s) :=
  ⟨Status.mark_injective, Status.icon_injective, Status.mark_ne_icon, rfl, Status.legend_blocks⟩

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
  intro h
  cases h.2.1 .unknown .idle rfl

theorem summary_exact (attentions : List Status.Attention) :
    Status.summary attentions =
      String.intercalate " "
        ((if attentions.count .asked = 0 then []
          else [(toString (attentions.count .asked)).push (Status.mark .asked)]) ++
          (if attentions.count .unread = 0 then []
          else [(toString (attentions.count .unread)).push (Status.mark .unread)])) :=
  Status.summary_exact attentions

theorem summary_exact_rejects_count :
    ¬∀ (attentions : List Status.Attention),
        (fun (all : List Status.Attention) => toString all.length) attentions =
          String.intercalate " "
            ((if attentions.count .asked = 0 then []
              else [(toString (attentions.count .asked)).push (Status.mark .asked)]) ++
              (if attentions.count .unread = 0 then []
              else [(toString (attentions.count .unread)).push (Status.mark .unread)])) := by
  intro h
  exact absurd (h []) (by simp)

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
  refine
    ⟨?_, ?_, fun h => by
      rw [Listing.rowStatus_remote_saved]; simp [h]⟩
  · rw [Listing.rowStatus_ended]
    split <;> simp_all [Status.Is, Status.Attention.Is, Status.State.Is]
  · rw [Listing.rowStatus_remote_saved]
    obtain ⟨a, st⟩ := st
    refine
      ⟨{ daemonUp := false,
         exit := if st = .exitedOk then some 0 else if st = .exitedBad then some 1 else none,
         unseen := a == .unread, asks := a == .asked },
        rfl, rfl, ?_⟩
    cases a <;> cases st <;> simp [Status.Is, Status.Attention.Is, Status.State.Is]

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
  intro h
  exact absurd (h 0 default).1 (by simp [Status.Is, Status.Attention.Is])

theorem row_pair (layout : Listing.Layout) (info : List (String × String)) :
    (∀ a s, ∃ o, Status.classify o = { attention := a, state := s }) ∧
      (Listing.columns layout info).take 2 =
        [[Status.mark (Status.ofAttentionName ((info.lookup "attention").getD "")), ' '],
          [Status.icon (Status.ofName ((info.lookup "status").getD "")), ' ']] :=
  ⟨fun a s => Status.reachable a s, rfl⟩

theorem row_pair_rejects_single :
    ¬∀ (layout : Listing.Layout) (info : List (String × String)),
        (∀ a s, ∃ o, Status.single Status.classify o = { attention := a, state := s }) ∧
          (Listing.columns layout info).take 2 =
            [[Status.mark (Status.ofAttentionName ((info.lookup "attention").getD "")), ' '],
              [Status.icon (Status.ofName ((info.lookup "status").getD "")), ' ']] := by
  intro h
  obtain ⟨o, ho⟩ := (h {} []).1 .asked .working
  simp only [Status.single] at ho
  split at ho
  · split at ho
    · simp at ho
    · split at ho
      · simp_all
      · simp at ho
  · simp at ho

theorem attention_independent (o o' : Status.Obs) (asks : o.asks = o'.asks)
    (unseen : o.unseen = o'.unseen) :
    (Status.classify o).attention = (Status.classify o').attention :=
  Status.attention_independent o o' asks unseen

theorem attention_independent_rejects_single :
    ¬∀ (o o' : Status.Obs),
        o.asks = o'.asks →
          o.unseen = o'.unseen →
          (Status.single Status.classify o).attention =
            (Status.single Status.classify o').attention := by
  intro h
  exact absurd (h { unseen := true } { unseen := true, running := true } rfl rfl) (by decide)

theorem state_independent (o o' : Status.Obs) (known : o.known = o'.known)
    (daemonUp : o.daemonUp = o'.daemonUp) (exit : o.exit = o'.exit)
    (progress : o.progress = o'.progress) (running : o.running = o'.running) :
    (Status.classify o).state = (Status.classify o').state :=
  Status.state_independent o o' known daemonUp exit progress running

theorem state_independent_rejects_single :
    ¬∀ (o o' : Status.Obs),
        o.known = o'.known →
          o.daemonUp = o'.daemonUp →
          o.exit = o'.exit →
          o.progress = o'.progress →
          o.running = o'.running →
          (Status.single Status.classify o).state = (Status.single Status.classify o').state := by
  intro h
  exact
    absurd (h { running := true } { running := true, asks := true } rfl rfl rfl rfl rfl) (by decide)

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

theorem announce_changes (before current : List (String × Status.Attention)) (own name : String) :
    Alert.announce none current own = [] ∧
      (name ∈ Alert.announce (some before) current own ↔
        name ≠ own ∧
          (name, Status.Attention.asked) ∈ current ∧ (name, Status.Attention.asked) ∉ before) ∧
      ((current.map (·.1)).Nodup → (Alert.announce (some before) current own).Nodup) :=
  ⟨Alert.announce_first current own, Alert.mem_announce before current own name,
    Alert.announce_nodup before current own⟩

theorem announce_changes_rejects_every_sample :
    ¬∀ (before current : List (String × Status.Attention)) (own name : String),
        Alert.everySample none current own = [] ∧
          (name ∈ Alert.everySample (some before) current own ↔
            name ≠ own ∧
              (name, Status.Attention.asked) ∈ current ∧ (name, Status.Attention.asked) ∉ before) ∧
          ((current.map (·.1)).Nodup → (Alert.everySample (some before) current own).Nodup) := by
  intro h
  have := (h [] [("b", .asked)] "a" "b").1
  simp [Alert.everySample] at this

theorem announce_changes_rejects_self :
    ¬∀ (before current : List (String × Status.Attention)) (own name : String),
        Alert.withSelf none current own = [] ∧
          (name ∈ Alert.withSelf (some before) current own ↔
            name ≠ own ∧
              (name, Status.Attention.asked) ∈ current ∧ (name, Status.Attention.asked) ∉ before) ∧
          ((current.map (·.1)).Nodup → (Alert.withSelf (some before) current own).Nodup) := by
  intro h
  have := ((h [] [("a", .asked)] "a" "a").2.1).mp (by simp [Alert.withSelf])
  exact this.1 rfl

theorem sort_attention_first {α : Type} (status : α → Status.Status) (rows : List α) :
    (View.sort status rows).Perm rows ∧
      ∃ first rest,
        View.sort status rows = first ++ rest ∧
          (∀ x ∈ first, (status x).attention ≠ .none) ∧
          ∀ x ∈ rest, (status x).attention = .none := by
  obtain ⟨first, rest, split, front, back⟩ := View.sort_attention_first status rows
  exact ⟨View.sort_perm status rows, first, rest, split, front, back⟩

theorem sort_attention_first_rejects_arrival :
    ¬∀ {α : Type} (status : α → Status.Status) (rows : List α),
        (View.arrival status rows).Perm rows ∧
          ∃ first rest,
            View.arrival status rows = first ++ rest ∧
              (∀ x ∈ first, (status x).attention ≠ .none) ∧
              ∀ x ∈ rest, (status x).attention = .none := by
  intro h
  obtain ⟨-, first, rest, split, front, back⟩ :=
    h id [({ attention := .none, state := .idle } : Status.Status), ⟨.unread, .idle⟩]
  match first, split with
  | [],
    split =>
    have whole : rest = [⟨.none, .idle⟩, ⟨.unread, .idle⟩] := by
      simpa [View.arrival] using split.symm
    exact absurd (back ⟨.unread, .idle⟩ (by simp [whole])) (by decide)
  | a :: _, split =>
    have head : a = ⟨.none, .idle⟩ := (List.cons.inj split).1.symm
    exact absurd (front a (by simp)) (by simp [head])

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
    View.sort status rows = View.sort status' rows := View.sort_keeps_place status status' rows h

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
  intro h
  have kept :=
    h (α := Bool) (fun b => ⟨.none, if b then .working else .idle⟩)
      (fun b => ⟨.none, if b then .idle else .working⟩) [false, true] fun x _ => by cases x <;> simp
  exact absurd kept (by decide)

theorem sort_live_above_done {α : Type} (status : α → Status.Status) (rows first rest : List α)
    (split : View.sort status rows = first ++ rest) (x : α) (above : x ∈ first)
    (ended :
      (status x).state = .exitedOk ∨ (status x).state = .exitedBad ∨ (status x).state = .resumable)
    (y : α) (below : y ∈ rest) (same : (status y).attention = (status x).attention) :
    ¬((status y).state = .errored ∨
        (status y).state = .working ∨ (status y).state = .paused ∨ (status y).state = .idle) :=
  View.sort_live_above_done status rows first rest split x above ended y below same

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
  intro h
  exact
    h (fun b : Bool => (⟨.none, if b then .exitedOk else .working⟩ : Status.Status)) [true, false]
      [true] [false] (by decide) true (by simp) (by simp) false (by simp) rfl (by simp)

theorem sort_two_keys {α : Type} (status : α → Status.Status) (earlier : α → α → Prop)
    (rows : List α) (listed : rows.Pairwise earlier) :
    (View.sort status rows).Perm rows ∧
      (View.sort status rows).Pairwise fun a b =>
        View.needs (status a).attention < View.needs (status b).attention ∨
          View.needs (status a).attention = View.needs (status b).attention ∧
            (View.lifecycle (status a).state < View.lifecycle (status b).state ∨
              View.lifecycle (status a).state = View.lifecycle (status b).state ∧ earlier a b) :=
  ⟨View.sort_perm status rows, View.sort_two_keys status earlier rows listed⟩

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
  intro h
  have :=
    (h (α := Status.Status) id (fun _ _ => True) [⟨.none, .resumable⟩, ⟨.none, .exitedOk⟩]
        (by simp)).2
  revert this
  decide

theorem before_total (a b c : String) :
    View.before a a = false ∧
      (View.before a b = true → View.before b c = true → View.before a c = true) ∧
      (a ≠ b → View.before a b = true ∨ View.before b a = true) := View.before_total a b c

theorem before_total_rejects_none :
    ¬∀ (a b c : String),
        (fun (_ _ : String) => false) a a = false ∧
          ((fun (_ _ : String) => false) a b = true →
            (fun (_ _ : String) => false) b c = true → (fun (_ _ : String) => false) a c = true) ∧
          (a ≠ b →
            (fun (_ _ : String) => false) a b = true ∨
              (fun (_ _ : String) => false) b a = true) := by
  intro h
  exact absurd ((h "a" "b" "a").2.2 (by decide)) (by simp)

theorem before_number (p q : String) (n m : Nat) (h : n < m)
    (hp : ∀ c, p.toList.getLast? = some c → c.isDigit = false)
    (hq : ∀ c, q.toList.head? = some c → c.isDigit = false) :
    View.before (p ++ toString n ++ q) (p ++ toString m ++ q) = true :=
  View.before_number p q n m h hp hq

theorem before_number_rejects_lexicographic :
    ¬∀ (p q : String) (n m : Nat),
        n < m →
          (∀ c, p.toList.getLast? = some c → c.isDigit = false) →
          (∀ c, q.toList.head? = some c → c.isDigit = false) →
          (fun (a b : String) => decide (a < b)) (p ++ toString n ++ q) (p ++ toString m ++ q) =
            true := by
  intro h
  have wrong := h "p" "" 2 10 (by decide) (by decide) (by decide)
  exact absurd wrong (by decide)

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
