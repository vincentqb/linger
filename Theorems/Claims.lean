module

public import Linger.Session
public import Linger.Session.Buf
public import Linger.Session.Checkpoint
public import Linger.Session.Driver
public import Linger.Session.Spec
public import Linger.Target.Name
public import Linger.Target.Remote
public import Linger.Target.Spec
public import Linger.Terminal.Render
public import Linger.Terminal.Replay
public import Linger.Terminal.Spec
import Linger.Target.Proofs.Name
import Linger.Target.Proofs.Remote
import all Linger.Session.Proofs.Buf
import all Linger.Session.Proofs.Checkpoint
import all Linger.Session.Proofs.Driver
import all Linger.Session.Proofs.Session
import all Linger.Terminal.Vt
import all Linger.Terminal.Proofs.Vt
import all Linger.Terminal.Proofs.Vt.Renderable
import all Linger.Terminal.Proofs.Render.Grid
import all Linger.Terminal.Proofs.Render.History
import all Linger.Terminal.Proofs.Render.PendingWrap
import all Linger.Terminal.Proofs.Render.Scrollback
import all Linger.Terminal.Proofs.Render.Sticky
import all Linger.Terminal.Proofs.Replay
import all Linger.Terminal.Proofs.Vt.State

/-! # Proofs of the headline theorems

`Manifest.lean` states these theorems; each proof here cites the component theorems it
restates. `./lake comparator` checks that the statements match. -/

public section

namespace Linger.Claims

open Linger.Session Linger.Target Linger.Terminal

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
  have hv := Checkpoint.live_of_decoded hv
  have hw := Checkpoint.live_of_decoded hw
  refine ⟨Render.restore v, ?_, ?_⟩
  · rw [← Replay.start_faithful v]
    exact Replay.emits_remaining budget positive (Replay.start v)
  have dims := Vt.dims_feed (Render.restore v) (Vt.good_of_liveReachable hw)
  simp only [Vt.dims, Prod.mk.injEq] at dims
  have grid := Render.restore_grid_reachable v w hw hv hcols hrows
  have size := (Vt.renderable_of_liveReachable hv).main.1
  refine ⟨dims.1.trans hcols, dims.2.trans hrows, fun y below => ?_⟩
  have inside : y < v.grid.size := size ▸ below
  unfold Vt.Vt.getRow
  rw [grid]
  simp only [Array.getD, inside, dite_true]

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
  intro h
  obtain ⟨bytes, emits, -, -, rows⟩ :=
    h 1 Nat.one_pos ((Vt.Vt.init 2 1).feed [0x41]) (Vt.Vt.init 2 1) (.feed (.init 2 1) [0x41])
      (.init 2 1) (by decide +kernel) (by decide +kernel)
  cases emits with
  | step next => cases next
  | done =>
    have row := rows 0 (by decide +kernel)
    exact absurd (congrArg (fun r : Vt.Row => (r.getD 0 {}).base) row) (by decide +kernel)

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
  refine
    ⟨Render.restore v, ?_,
      Render.restore_sb_reachable v w (Checkpoint.live_of_decoded hw)
        (Checkpoint.live_of_decoded hv) hcols hrows retained⟩
  rw [← Replay.start_faithful v]
  exact Replay.emits_remaining budget positive (Replay.start v)

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
  intro h
  obtain ⟨bytes, emits, history⟩ :=
    h 1 Nat.one_pos ((Vt.Vt.init 2 1).feed [0x41, 0x0A]) (Vt.Vt.init 2 1)
      (.feed (.init 2 1) [0x41, 0x0A]) (.init 2 1) (by decide +kernel) (by decide +kernel)
      (by
        rw [Render.sbRows_observed]; rfl)
  cases emits with
  | step next => cases next
  | done =>
    rw [Render.sbRows_observed] at history
    exact absurd (congrArg List.length history) (by decide +kernel)

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
  refine ⟨Render.restore v, ?_, ?_⟩
  · rw [← Replay.start_faithful v]
    exact Replay.emits_remaining budget positive (Replay.start v)
  obtain ⟨x, y⟩ :=
    Render.restore_cursor_any v w (Vt.good_of_liveReachable (Checkpoint.live_of_decoded hv))
      (Vt.good_of_liveReachable (Checkpoint.live_of_decoded hw)) hcols hrows ho
  simp only [Vt.cursorPos_eq, x, y]

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
  intro h
  obtain ⟨bytes, emits, cursor⟩ :=
    h 1 Nat.one_pos (Vt.Vt.init 2 1) ((Vt.Vt.init 2 1).feed [0x41]) (.init 2 1)
      (.feed (.init 2 1) [0x41]) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  cases emits with
  | step next => cases next
  | done => exact absurd (congrArg Prod.fst cursor) (by decide +kernel)

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
    (hc : s.client? id = some c) (attached : c.attached = true) (watcher : c.sizer = false) :
    (Session.trace Session.step s (chunks.map (Event.bytes id))).1.terminal = s.terminal ∧
      (Session.trace Session.step s (chunks.map (Event.bytes id))).1.labelList = s.labelList ∧
      ∀ eff ∈ (Session.trace Session.step s (chunks.map (Event.bytes id))).2,
        (∃ m, eff = .send id m) ∨ eff = .close id ∨ eff = .checkpoint := by
  rw [Session.trace_step]
  exact Session.run_readonly s id chunks hc attached watcher

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
  intro h
  obtain ⟨-, -, effects⟩ :=
    @h (State.boot (Vt.Vt.init 1 1) [] []) 0 [[]] { id := 0, attached := true } rfl rfl rfl
  rcases effects .killChild (by simp [Session.trace]) with ⟨_, sent⟩ | closed | saved
  · cases sent
  · cases closed
  · cases saved

theorem check_eq_some_iff (s result : String) :
    Name.check s = some result ↔ result = s ∧ Name.Valid s := Name.check_eq_some_iff s result

theorem check_eq_some_iff_rejects_any :
    ¬∀ (s result : String), (fun s => some s) s = some result ↔ result = s ∧ Name.Valid s := by
  intro h
  exact absurd ((h "" "").mp rfl).2.1 (by simp)

theorem command_argv (verb : String) (words : List String) :
    Remote.Shell.Words (Remote.command verb words).toList
      (("linger" :: verb :: words).map String.toList) := Remote.command_argv verb words

theorem command_argv_rejects_empty :
    ¬∀ (verb : String) (words : List String),
        Remote.Shell.Words ((fun (_ : String) (_ : List String) => "") verb words).toList
          (("linger" :: verb :: words).map String.toList) := by
  intro h
  have words := h "" []
  cases words
  simp_all [Remote.Shell.word]

theorem step_ended_reports (s : State) (o : Outcome) {c : Client} (hc : c ∈ s.roster)
    (listening : c.attached = true ∨ c.waiting = true) :
    [Effect.send c.id (.ended o), Effect.send c.id (.exited o.status)] <:+:
        (Session.step s (.childExited o)).2 ∧
      (Session.step s (.childExited o)).2.getLast? = some .exit :=
  Session.step_ended_reports s o hc listening

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
  intro h
  obtain ⟨heard, -⟩ :=
    @h (State.boot (Vt.Vt.init 1 1) [] []) .unknown { id := 0, attached := true } (by simp)
      (.inl rfl)
  have same := heard.eq_of_length rfl
  simp at same

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
    fun _ world eff => .ok (world, Driver.success eff)
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

theorem screenText_text (v : Vt.Vt) :
    ∃ cs : List Char,
      Render.screenText v = cs.flatMap String.utf8EncodeChar ∧
        ∀ c ∈ cs,
          c = '\n' ∨ (0x20 ≤ c.toNat ∧ c.toNat ≠ 0x7F ∧ ¬(0x80 ≤ c.toNat ∧ c.toNat < 0xA0)) := by
  obtain ⟨cs, text, safe⟩ := Render.screenText_text v
  refine ⟨cs, ?_, safe⟩
  rw [text]
  exact congrArg (cs.flatMap ·) (funext Render.utf8_eq_utf8EncodeChar)

theorem screenText_text_rejects_escape :
    ¬∀ (v : Vt.Vt),
        ∃ cs : List Char,
          (fun (_ : Vt.Vt) => ([0x1B] : Render.Bytes)) v = cs.flatMap String.utf8EncodeChar ∧
            ∀ c ∈ cs,
              c = '\n' ∨
                (0x20 ≤ c.toNat ∧ c.toNat ≠ 0x7F ∧ ¬(0x80 ≤ c.toNat ∧ c.toNat < 0xA0)) := by
  intro h
  obtain ⟨cs, text, safe⟩ := h (Vt.Vt.init 1 1)
  have escape : (0x1B : UInt8) ∈ cs.flatMap String.utf8EncodeChar := by
    rw [← text]
    exact List.mem_singleton_self _
  obtain ⟨c, member, byte⟩ := List.mem_flatMap.mp escape
  rcases safe c member with newline | ⟨printable, notDel, -⟩
  · subst newline
    revert byte
    decide
  · rw [← Render.utf8_eq_utf8EncodeChar] at byte
    exact absurd (Render.utf8_no_ctl c printable notDel _ byte).1 (by decide)

theorem leave_canonical_all (w : Vt.Vt) (h2 : 2 ≤ w.rowCount) :
    (w.feed Render.leaveAnsi).atBoundary = true ∧
      (w.feed Render.leaveAnsi).getModes = ({} : Vt.Modes) ∧
      Vt.stick (w.feed Render.leaveAnsi) =
        { rows := w.rowCount, top := 0, bot := w.rowCount - 1, g0 := false, g1 := false,
          so := false, alt := false } ∧
      (w.feed Render.leaveAnsi).getPen = ({} : Vt.Pen) ∧
      (w.feed Render.leaveAnsi).windowTitle = "" := by
  obtain ⟨_, modes, sticky, pen, title⟩ := Render.leave_canonical_all w h2
  obtain ⟨ground, settled, _⟩ := Render.leave_boundary_title w
  exact ⟨by simp [Vt.Vt.atBoundary, ground, settled], modes, sticky, pen, title⟩

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
  intro h
  exact absurd (h (Vt.Vt.init 2 2) (by decide +kernel)).1 (by decide +kernel)

end Linger.Claims
