module

public import Linger.Import.CoreCode.Resurrect
public import Linger.Session.CoreCode
public import Linger.Session.CoreCode.Buf
public import Linger.Session.CoreCode.Claim
public import Os.WorldSpec
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

/-! # Part 6 of `Challenge.lean`, bounded and clean: the proofs of its headline theorems and their kills

`Challenge.lean` states them; each proof cites the component theorems it restates, and
`Theorems.Solution` gathers every part for `./lake comparator`. -/

public section

namespace Linger

open Linger.Display Linger.Session Linger.Target Terminal

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

end Linger
