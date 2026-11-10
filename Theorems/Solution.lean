module

public import Linger.Display.Status
public import Linger.Display.Title
public import Linger.Os.Env
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
import all Linger.Display.Proofs.Status
import all Linger.Display.Proofs.Title
import all Linger.Os.Proofs.Env
import Linger.Target.Proofs.Name
import Linger.Target.Proofs.Remote
import all Linger.Session.Proofs.Buf
import all Linger.Session.Proofs.Checkpoint
import all Linger.Session.Proofs.Driver
import all Linger.Session.Proofs.Session
import all Linger.Session.Proofs.Start
public import Linger.Session.Start
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

/-! # Proofs of the headline theorems and their kills

`Challenge.lean` states these theorems; each proof here cites the component theorems it
restates. `./lake comparator` checks that the statements match. -/

public section

namespace Linger

open Linger.Display Linger.Session Linger.Target Linger.Terminal

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

theorem feed_inert (v : Vt.Vt) (bytes : List UInt8) (between : v.atBoundary = true)
    (inert : ∀ b ∈ bytes, b = 0x7F ∨ b < 0x07 ∨ 0x0F < b ∧ b < 0x20 ∧ b ≠ 0x1B) :
    v.feed bytes = v := by
  have ground : v.pstate = .ground ∧ v.u8need = 0 := by simpa [Vt.Vt.atBoundary] using between
  have hosc : ∀ acc e, v.pstate ≠ .osc acc e := by
    intro acc e
    rw [ground.1]
    simp
  have hstr : v.pstate ≠ .str true := by
    rw [ground.1]
    simp
  have step (b : UInt8) (hb : b = 0x7F ∨ b < 0x07 ∨ 0x0F < b ∧ b < 0x20 ∧ b ≠ 0x1B) :
    v.step b = v := by
    rcases hb with del | low | ⟨above, below, notEsc⟩
    · subst del
      exact Vt.step_del_inert ground.2 hosc hstr
    · have below : b < 0x20 := by
        simp only [UInt8.lt_iff_toNat_lt] at low ⊢
        simp only [UInt8.reduceToNat] at low ⊢
        omega
      have notEsc : b ≠ 0x1B := by
        rintro rfl
        exact absurd low (by decide)
      exact Vt.step_c0_inert below (.inl low) notEsc ground.2 hosc hstr
    · exact Vt.step_c0_inert below (.inr above) notEsc ground.2 hosc hstr
  show bytes.foldl Vt.Vt.step v = v
  induction bytes with
  | nil => rfl
  | cons b rest ih =>
    rw [List.foldl_cons, step b (inert b (by simp))]
    exact ih (fun b hb => inert b (by simp [hb]))

theorem feed_inert_rejects_print :
    ¬∀ (v : Vt.Vt) (bytes : List UInt8),
        v.atBoundary = true →
          (∀ b ∈ bytes, b = 0x7F ∨ b < 0x07 ∨ 0x0F < b ∧ b < 0x20 ∧ b ≠ 0x1B) →
          (fun (v : Vt.Vt) (bytes : List UInt8) =>
                v.feed (bytes.map fun b => if b = 0x7F then 0x3F else b))
              v bytes =
            v := by
  intro h
  have same := congrArg Vt.Vt.cursorPos (h (Vt.Vt.init 2 2) [0x7F] (by decide +kernel) (by simp))
  exact absurd same (by decide +kernel)

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

theorem remotesFile_home (home : Option String) :
    Os.Env.remotesFile home = none ↔ home = none ∨ home = some "" :=
  Os.Env.remotesFile_eq_none_iff home

theorem remotesFile_home_rejects_shared :
    ¬∀ (home : Option String),
        (fun (_ : Option String) => some "remotes") home = none ↔ home = none ∨ home = some "" := by
  intro h
  exact absurd ((h none).mpr (.inl rfl)) (by simp)

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

theorem shellQuote_roundtrip (s : String) (tail : List Char)
    (boundary : tail = [] ∨ ∃ rest, tail = ' ' :: rest) :
    Remote.Shell.word ((Remote.shellQuote s).toList ++ tail) = some (s.toList, tail) :=
  Remote.shellQuote_roundtrip s tail boundary

theorem shellQuote_roundtrip_rejects_bare :
    ¬∀ (s : String) (tail : List Char),
        (tail = [] ∨ ∃ rest, tail = ' ' :: rest) →
          Remote.Shell.word (((fun (s : String) => s) s).toList ++ tail) =
            some (s.toList, tail) := by
  intro h
  have read := h "" [] (.inl rfl)
  simp [Remote.Shell.word] at read

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

theorem repeatAtMost_eq_repeat (v : Vt.Vt) (cap count : Nat) (f : Vt.Vt → Vt.Vt) :
    v.repeatAtMost cap count f = Nat.repeat f (min count cap) v :=
  Vt.repeatAtMost_eq_repeat v cap count f

theorem repeatAtMost_eq_repeat_rejects_uncapped :
    ¬∀ (v : Vt.Vt) (cap count : Nat) (f : Vt.Vt → Vt.Vt),
        (fun (v : Vt.Vt) (_ count : Nat) (f : Vt.Vt → Vt.Vt) => Nat.repeat f count v) v cap count
            f =
          Nat.repeat f (min count cap) v := by
  intro h
  have same := congrArg Vt.Vt.colCount (h (Vt.Vt.init 1 1) 0 1 (fun _ => Vt.Vt.init 2 1))
  exact absurd same (by decide +kernel)

theorem next_bounded {budget : Nat} {p q : Replay.Plan} {bytes : Render.Bytes}
    (h : Replay.next budget p = some (bytes, q)) : bytes.length ≤ budget := Replay.next_bounded h

theorem next_bounded_rejects_overrun :
    ¬∀ {budget : Nat} {p q : Replay.Plan} {bytes : Render.Bytes},
        (fun (_ : Nat) (p : Replay.Plan) => some (([0] : Render.Bytes), p)) budget p =
            some (bytes, q) →
          bytes.length ≤ budget := by
  intro h
  exact
    absurd (@h 0 (Replay.start (Vt.Vt.init 1 1)) (Replay.start (Vt.Vt.init 1 1)) [0] rfl)
      (by decide)

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

theorem history_text (v : Vt.Vt) :
    ∃ cs : List Char,
      Render.history v = cs.flatMap String.utf8EncodeChar ∧
        ∀ c ∈ cs,
          c = '\n' ∨ (0x20 ≤ c.toNat ∧ c.toNat ≠ 0x7F ∧ ¬(0x80 ≤ c.toNat ∧ c.toNat < 0xA0)) := by
  obtain ⟨cs, text, safe⟩ := Render.history_text v
  refine ⟨cs, ?_, safe⟩
  rw [text]
  exact congrArg (cs.flatMap ·) (funext Render.utf8_eq_utf8EncodeChar)

theorem history_text_rejects_escape :
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

end Linger
