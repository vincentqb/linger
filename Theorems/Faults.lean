module

public import Linger.App.CoreCode.Capture
public import Linger.App.CoreCode.Recovery
public import Linger.App.CoreCode.Serve
public import Linger.Display.CoreCode.Listing
public import Linger.Display.CoreCode.Status
public import Linger.Session.CoreCode
public import Linger.Session.CoreCode.Buf
public import Linger.Session.CoreCode.Checkpoint
public import Linger.Session.CoreSpec
public import Linger.Session.WorldSpec
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

/-! # Part 10 of `Challenge.lean`, graceful under load and faults: the proofs of its headline theorems and their kills, and the lemmas `fault_contained` gathers

`Challenge.lean` states them; each proof cites the component theorems it restates, and
`Theorems.Solution` gathers every part for `./lake comparator`. -/

public section

namespace Linger

open Linger.Display Linger.Session Linger.Target Terminal

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

theorem capture_waits_unlocked :
    (∀ steps,
        (App.Capture.phases steps).flatMap App.Capture.Phase.work = App.Capture.work steps false) ∧
      (App.Capture.work App.Capture.plan false).map Prod.fst = [.load, .render, .write] ∧
      (.load, true) ∈ App.Capture.work App.Capture.plan false ∧
      ∀ step, (step, true) ∈ App.Capture.work App.Capture.plan false → step.waitsOutside = false :=
  ⟨App.Capture.phases_work, App.Capture.waits_unlocked⟩

theorem log_bounded {α : Type} (cap : Nat) (entries : List α) :
    (entries.foldl (App.Serve.Log.push cap) {}).tail = entries.drop (entries.length - cap) ∧
      (entries.foldl (App.Serve.Log.push cap) {}).dropped = entries.length - cap ∧
      (entries.foldl (App.Serve.Log.push cap) {}).tail.length +
          (entries.foldl (App.Serve.Log.push cap) {}).dropped =
        entries.length := by
  obtain ⟨tail, dropped⟩ := App.Serve.Log.fold_push cap entries {} (by simp)
  simp only [List.nil_append] at tail dropped
  refine ⟨tail, by simpa using dropped, ?_⟩
  rw [tail, dropped, List.length_drop]
  simp only [Nat.zero_add]
  omega

theorem reachableOut_bound {cap : Nat} {b : Buf.Buf}
    (h : Buf.OutputReach Buf.Buf.empty Buf.bufEnqueue Buf.bufAdvance cap b) :
    Buf.owedLen b ≤ cap := Buf.reachableOut_bound h

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
    rw [Checkpoint.loadBytes_saveBytes_live c (Checkpoint.live_of_decoded h)]
    rfl
  obtain ⟨kept, torn⟩ := durable (some (Checkpoint.saveBytes old)) (Checkpoint.saveBytes new)
  cases synced with
  | true => exact ⟨_, by rw [kept, resumes new hnew], .inl rfl⟩
  | false =>
    rcases torn with found | found
    · exact ⟨_, by rw [found, resumes old hold], .inr ⟨rfl, rfl⟩⟩
    · exact ⟨_, by rw [found, resumes new hnew], .inl rfl⟩

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

theorem table_converges (s : App.Serve.State) (version : String) (id : App.Serve.Id)
    (told latest rows : List App.Serve.Record) (ready : s.phase = .ready version)
    (subscribed : s.subscription = some id) (was : s.told = some told)
    (now : s.latest = some latest) (keyed : (latest.map App.Serve.Record.key).Nodup) :
    (App.Serve.step s (.opened id rows)).2 = [] ∧
      (App.Serve.step s (.opened id rows)).1.told = some rows ∧
      (App.Serve.step s (.opened id rows)).1.latest = some rows ∧
      (App.Serve.step s (.sampled rows)).2 = [] ∧
      (App.Serve.step s (.sampled rows)).1.subscription = some id ∧
      (App.Serve.step s (.sampled rows)).1.told = some told ∧
      (App.Serve.step s (.sampled rows)).1.latest = some rows ∧
      ∀ params,
        App.Serve.Effect.send (.notify "sessions/changed" params) ∈ (App.Serve.step s .writable).2 →
          ∃ records gone,
            params = App.Serve.update id records gone ∧
              ∀ key,
                (App.Serve.View.apply (App.Serve.View.of told) records gone key).map
                    App.Serve.Record.reading =
                  (App.Serve.View.of latest key).map App.Serve.Record.reading := by
  obtain ⟨opened, toldFirst, latestFirst⟩ :=
    App.Serve.step_opened s version id rows ready subscribed
  obtain ⟨sampled, stillOpen, stillTold, nowLatest⟩ :=
    App.Serve.step_sampled s version id told rows ready subscribed was
  refine ⟨opened, toldFirst, latestFirst, sampled, stillOpen, stillTold, nowLatest, ?_⟩
  intro params sent
  obtain ⟨effects, -, -, -⟩ :=
    App.Serve.step_writable s version id told latest ready subscribed was now
  rw [effects] at sent
  split at sent
  · simp at sent
  · simp only [List.mem_singleton, App.Serve.Effect.send.injEq, App.Serve.Outgoing.notify.injEq,
      true_and] at sent
    exact ⟨_, _, sent, App.Serve.View.converges told latest keyed⟩

/-- A disk that keeps every save whole, which `Disk.Durable` allows: a fault's kill needs one. -/
private theorem keeps_new :
    Disk.Durable (fun (_ : Option ByteArray) (new : ByteArray) (_ : Bool) => some new) := fun _ _ =>
  ⟨rfl, .inr rfl⟩

theorem fault_contained (f : App.Fault)
    (afterCrash : Option ByteArray → ByteArray → Bool → Option ByteArray)
    (durable : Disk.Durable afterCrash) :
    App.Fault.Contained App.Recovery.decide Checkpoint.saveBytes Checkpoint.loadBytes Vt.Vt.init
      Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Session.step State.boot State.terminal State.fieldList
      State.nextTick State.roster Buf.Buf.empty Buf.bufOffer Buf.bufEnqueue Buf.bufAdvance
      Buf.owedLen App.Serve.step App.Serve.State.phase App.Serve.State.subscription
      App.Serve.State.told App.Serve.State.latest App.Serve.Log.push Listing.rowStatus
      Status.classify App.Capture.phases App.Capture.plan Offloop.ask Offloop.done afterCrash f
      f.cost := by
  cases f
  · exact ⟨crash_resumes afterCrash durable, unsaved_due⟩
  · intro s id
    obtain ⟨frame, -⟩ := Session.step_closed_frame s id
    refine ⟨?_, ?_, ?_, Session.closed_effects s id⟩ <;> rw [frame] <;> rfl
  · exact ⟨Buf.reachableIn_bound, reachableOut_bound, table_converges, log_bounded⟩
  · exact (Status.classify_iff _ _).mpr ⟨⟨rfl, rfl⟩, rfl⟩
  · exact (Status.classify_iff _ _).mpr ⟨⟨rfl, rfl⟩, rfl⟩
  · exact ⟨capture_waits_unlocked, offloop_coalesces⟩

theorem fault_contained_rejects_uncut :
    ¬∀ f afterCrash,
        Disk.Durable afterCrash →
          App.Fault.Contained App.Recovery.decide Checkpoint.saveBytes Checkpoint.loadBytes
            Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Session.step State.boot State.terminal
            State.fieldList State.nextTick State.roster Buf.Buf.empty Buf.bufOffer
            (fun cap b more => ((Buf.bufEnqueue cap b more).1, false)) Buf.bufAdvance Buf.owedLen
            App.Serve.step App.Serve.State.phase App.Serve.State.subscription App.Serve.State.told
            App.Serve.State.latest App.Serve.Log.push Listing.rowStatus Status.classify
            App.Capture.phases App.Capture.plan Offloop.ask Offloop.done afterCrash f f.cost := by
  intro h
  obtain ⟨-, out, -⟩ := h .slowClient _ keeps_new
  have owed :=
    @out 0 (Buf.bufEnqueue 0 Buf.Buf.empty (ByteArray.mk #[0])).1
      (.enqueue Buf.Buf.empty (ByteArray.mk #[0]) .empty rfl)
  obtain ⟨empty, -, -, -, appended, -⟩ := Buf.buf_observed 0 0 Buf.Buf.empty (ByteArray.mk #[0])
  rw [appended, empty] at owed
  exact absurd owed (by decide)

theorem fault_contained_rejects_fresh :
    ¬∀ f afterCrash,
        Disk.Durable afterCrash →
          App.Fault.Contained (fun _ _ => .fresh) Checkpoint.saveBytes Checkpoint.loadBytes
            Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Session.step State.boot State.terminal
            State.fieldList State.nextTick State.roster Buf.Buf.empty Buf.bufOffer Buf.bufEnqueue
            Buf.bufAdvance Buf.owedLen App.Serve.step App.Serve.State.phase
            App.Serve.State.subscription App.Serve.State.told App.Serve.State.latest
            App.Serve.Log.push Listing.rowStatus Status.classify App.Capture.phases App.Capture.plan
            Offloop.ask Offloop.done afterCrash f f.cost := by
  intro h
  obtain ⟨crash, -⟩ := h .daemonCrash _ keeps_new
  obtain ⟨_, fresh, -⟩ :=
    crash true true ⟨Vt.Vt.init 1 1, "", []⟩ ⟨Vt.Vt.init 1 1, "", []⟩ (.init 1 1) (.init 1 1)
  cases fresh

theorem fault_contained_rejects_never :
    ¬∀ f afterCrash,
        Disk.Durable afterCrash →
          App.Fault.Contained App.Recovery.decide Checkpoint.saveBytes Checkpoint.loadBytes
            Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Session.step State.boot State.terminal
            State.fieldList (fun _ => none) State.roster Buf.Buf.empty Buf.bufOffer Buf.bufEnqueue
            Buf.bufAdvance Buf.owedLen App.Serve.step App.Serve.State.phase
            App.Serve.State.subscription App.Serve.State.told App.Serve.State.latest
            App.Serve.Log.push Listing.rowStatus Status.classify App.Capture.phases App.Capture.plan
            Offloop.ask Offloop.done afterCrash f f.cost := by
  intro h
  obtain ⟨-, unsaved⟩ := h .daemonCrash _ keeps_new
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
    unsaved (Vt.Vt.init 2 1) [] [] [] [] (.ptyOut [0x41])
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

theorem fault_contained_rejects_exits :
    ¬∀ f afterCrash,
        Disk.Durable afterCrash →
          App.Fault.Contained App.Recovery.decide Checkpoint.saveBytes Checkpoint.loadBytes
            Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce (App.Fault.exitsOnClose Session.step)
            State.boot State.terminal State.fieldList State.nextTick State.roster Buf.Buf.empty
            Buf.bufOffer Buf.bufEnqueue Buf.bufAdvance Buf.owedLen App.Serve.step
            App.Serve.State.phase App.Serve.State.subscription App.Serve.State.told
            App.Serve.State.latest App.Serve.Log.push Listing.rowStatus Status.classify
            App.Capture.phases App.Capture.plan Offloop.ask Offloop.done afterCrash f f.cost := by
  intro h
  -- the daemon stops as the client leaves
  obtain ⟨-, -, -, effects⟩ := h .clientDeath _ keeps_new (State.boot (Vt.Vt.init 1 1) [] []) 0
  rcases effects .exit (by simp [App.Fault.exitsOnClose]) with stops | stops <;> cases stops

theorem fault_contained_rejects_queued :
    ¬∀ f afterCrash,
        Disk.Durable afterCrash →
          App.Fault.Contained App.Recovery.decide Checkpoint.saveBytes Checkpoint.loadBytes
            Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Session.step State.boot State.terminal
            State.fieldList State.nextTick State.roster Buf.Buf.empty Buf.bufOffer Buf.bufEnqueue
            Buf.bufAdvance Buf.owedLen (App.Serve.queued App.Serve.step) App.Serve.State.phase
            App.Serve.State.subscription App.Serve.State.told App.Serve.State.latest
            App.Serve.Log.push Listing.rowStatus Status.classify App.Capture.phases App.Capture.plan
            Offloop.ask Offloop.done afterCrash f f.cost := by
  intro h
  obtain ⟨-, -, table, -⟩ := h .slowClient _ keeps_new
  -- a listing would be queued as an update as it comes
  have :=
    (table
        { stage := .ready "1", open? := some (.number 1), toldRecords := some [],
          latestRecords := some [] }
        "1" (.number 1) [] [] [] rfl rfl rfl rfl (by simp)).2.2.2.1
  simp [App.Serve.queued] at this

theorem fault_contained_rejects_keep_all :
    ¬∀ f afterCrash,
        Disk.Durable afterCrash →
          App.Fault.Contained App.Recovery.decide Checkpoint.saveBytes Checkpoint.loadBytes
            Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Session.step State.boot State.terminal
            State.fieldList State.nextTick State.roster Buf.Buf.empty Buf.bufOffer Buf.bufEnqueue
            Buf.bufAdvance Buf.owedLen App.Serve.step App.Serve.State.phase
            App.Serve.State.subscription App.Serve.State.told App.Serve.State.latest
            App.Serve.Log.keepAll Listing.rowStatus Status.classify App.Capture.phases
            App.Capture.plan Offloop.ask Offloop.done afterCrash f f.cost := by
  intro h
  obtain ⟨-, -, -, log⟩ := h .slowClient _ keeps_new
  -- a log that keeps every entry keeps one past a cap of none
  have := (@log Unit 0 [()]).1
  simp [App.Serve.Log.keepAll] at this

theorem fault_contained_rejects_idle :
    ¬∀ f afterCrash,
        Disk.Durable afterCrash →
          App.Fault.Contained App.Recovery.decide Checkpoint.saveBytes Checkpoint.loadBytes
            Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Session.step State.boot State.terminal
            State.fieldList State.nextTick State.roster Buf.Buf.empty Buf.bufOffer Buf.bufEnqueue
            Buf.bufAdvance Buf.owedLen App.Serve.step App.Serve.State.phase
            App.Serve.State.subscription App.Serve.State.told App.Serve.State.latest
            App.Serve.Log.push (fun _ => ⟨.none, .idle⟩) Status.classify App.Capture.phases
            App.Capture.plan Offloop.ask Offloop.done afterCrash f f.cost := by
  intro h
  -- a daemon that sent nothing would read as idle
  have := h .stuckDaemon _ keeps_new
  simp [App.Fault.Contained, App.Fault.cost] at this

theorem fault_contained_rejects_inside :
    ¬∀ f afterCrash,
        Disk.Durable afterCrash →
          App.Fault.Contained App.Recovery.decide Checkpoint.saveBytes Checkpoint.loadBytes
            Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Session.step State.boot State.terminal
            State.fieldList State.nextTick State.roster Buf.Buf.empty Buf.bufOffer Buf.bufEnqueue
            Buf.bufAdvance Buf.owedLen App.Serve.step App.Serve.State.phase
            App.Serve.State.subscription App.Serve.State.told App.Serve.State.latest
            App.Serve.Log.push Listing.rowStatus Status.classify App.Capture.phases
            [.acquire, .load, .render, .write, .release] Offloop.ask Offloop.done afterCrash f
            f.cost := by
  intro h
  -- the write runs holding the locks, and it waits on whoever reads it
  obtain ⟨⟨-, -, -, unheld⟩, -⟩ := h .optionalWork _ keeps_new
  exact absurd (unheld .write (by decide)) (by decide)

theorem fault_contained_rejects_held :
    ¬∀ f afterCrash,
        Disk.Durable afterCrash →
          App.Fault.Contained App.Recovery.decide Checkpoint.saveBytes Checkpoint.loadBytes
            Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Session.step State.boot State.terminal
            State.fieldList State.nextTick State.roster Buf.Buf.empty Buf.bufOffer Buf.bufEnqueue
            Buf.bufAdvance Buf.owedLen App.Serve.step App.Serve.State.phase
            App.Serve.State.subscription App.Serve.State.told App.Serve.State.latest
            App.Serve.Log.push Listing.rowStatus Status.classify (fun steps => [.locked steps])
            App.Capture.plan Offloop.ask Offloop.done afterCrash f f.cost := by
  intro h
  -- a shell that holds the locks through every step, the write included
  obtain ⟨⟨phased, -⟩, -⟩ := h .optionalWork _ keeps_new
  exact absurd (phased [.write]) (by decide)

theorem fault_contained_rejects_eager :
    ¬∀ f afterCrash,
        Disk.Durable afterCrash →
          App.Fault.Contained App.Recovery.decide Checkpoint.saveBytes Checkpoint.loadBytes
            Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Session.step State.boot State.terminal
            State.fieldList State.nextTick State.roster Buf.Buf.empty Buf.bufOffer Buf.bufEnqueue
            Buf.bufAdvance Buf.owedLen App.Serve.step App.Serve.State.phase
            App.Serve.State.subscription App.Serve.State.told App.Serve.State.latest
            App.Serve.Log.push Listing.rowStatus Status.classify App.Capture.phases App.Capture.plan
            Offloop.eager Offloop.done afterCrash f f.cost := by
  intro h
  obtain ⟨-, offloop⟩ := h .optionalWork _ keeps_new
  -- two writes asked for at once both start, neither waiting for the other
  have twice := (offloop (W := Unit) [] () 0).2 [.ask (), .ask ()]
  simp [Offloop.cycle, Offloop.eager, Offloop.Op.isDone] at twice

end Linger
