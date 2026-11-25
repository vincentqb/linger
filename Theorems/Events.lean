module

public import Linger.App.CoreCode.Serve
public import Linger.Selector.CoreCode.Picker
public import Linger.Selector.CoreCode.Fetch
public import Linger.Session.CoreCode
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

/-! # Part 9 of `Challenge.lean`, work follows events: the proofs of its headline theorems and their kills

`Challenge.lean` states them; each proof cites the component theorems it restates, and
`Theorems.Solution` gathers every part for `./lake comparator`. -/

public section

namespace Linger

open Linger.Display Linger.Session Linger.Target Terminal

theorem changed_exactly (s : App.Serve.State) (version : String) (id : App.Serve.Id)
    (told latest : List App.Serve.Record) (ready : s.phase = .ready version)
    (subscribed : s.subscription = some id) (was : s.told = some told)
    (now : s.latest = some latest) :
    (App.Serve.step s .writable).2 =
        (if App.Serve.changes told latest = [] ∧ App.Serve.removed told latest = [] then []
        else
          [.send
              (.notify "sessions/changed"
                (App.Serve.update id (App.Serve.changes told latest)
                  (App.Serve.removed told latest)))]) ∧
      (App.Serve.step s .writable).1.subscription = some id ∧
      (App.Serve.step s .writable).1.told = some latest ∧
      (App.Serve.step s .writable).1.latest = some latest :=
  App.Serve.step_writable s version id told latest ready subscribed was now

theorem changed_exactly_rejects_chatty :
    ¬∀ (s : App.Serve.State) (version : String) (id : App.Serve.Id)
        (told latest : List App.Serve.Record),
        s.phase = .ready version →
          s.subscription = some id →
          s.told = some told →
          s.latest = some latest →
          (App.Serve.chatty App.Serve.step s .writable).2 =
              (if App.Serve.changes told latest = [] ∧ App.Serve.removed told latest = [] then []
              else
                [.send
                    (.notify "sessions/changed"
                      (App.Serve.update id (App.Serve.changes told latest)
                        (App.Serve.removed told latest)))]) ∧
            (App.Serve.chatty App.Serve.step s .writable).1.subscription = some id ∧
            (App.Serve.chatty App.Serve.step s .writable).1.told = some latest ∧
            (App.Serve.chatty App.Serve.step s .writable).1.latest = some latest := by
  intro h
  -- with nothing changed, a free writer would still send an update
  have :=
    (h
        { stage := .ready "1", open? := some (.number 1), toldRecords := some [],
          latestRecords := some [] }
        "1" (.number 1) [] [] rfl rfl rfl rfl).1
  simp [App.Serve.chatty, App.Serve.changes, App.Serve.removed] at this

theorem screen_table_exact (s : App.Serve.State) (version : String) (id : App.Serve.Id)
    (told latest screen : App.Serve.Screen) (left : App.Serve.Log App.Serve.Line)
    (ready : s.phase = .ready version) :
    App.Serve.ScreenTable App.Serve.State.watching App.Serve.step App.Serve.result
      App.Serve.Screen.changes s id told latest screen left :=
  ⟨fun asked => App.Serve.watched_screen_opens s version id screen left ready asked, fun holds =>
    ⟨(App.Serve.watched_screen s version id told latest screen left ready holds).1,
      (App.Serve.watched_screen s version id told latest screen left ready holds).2,
      (App.Serve.flush_screen s version id told latest ready holds).1,
      (App.Serve.flush_screen s version id told latest ready holds).2⟩,
    App.Serve.changes_exact told latest⟩

theorem screen_table_exact_rejects_every_line :
    ¬∀ (s : App.Serve.State) (version : String) (id : App.Serve.Id)
        (told latest screen : App.Serve.Screen) (left : App.Serve.Log App.Serve.Line),
        s.phase = .ready version →
          App.Serve.ScreenTable App.Serve.State.watching App.Serve.step App.Serve.result
            App.Serve.Screen.everyLine s id told latest screen left := by
  intro h
  -- an update of every line sends a line the subscriber holds already
  let line : App.Serve.Line := { text := [], spans := [] }
  let screen : App.Serve.Screen := { lines := [line], cursor := ⟨0, 0, true⟩, title := "" }
  have exact :=
    (h ({ stage := .ready "1" } : App.Serve.StateRec) "1" (.number 1) screen screen screen {}
        rfl).2.2
  have := (exact.2.2.2.1 0 line).mp (by simp [App.Serve.Screen.everyLine, screen])
  simp [screen] at this

theorem screen_table_exact_rejects_first_change :
    ¬∀ (s : App.Serve.State) (version : String) (id : App.Serve.Id)
        (told latest screen : App.Serve.Screen) (left : App.Serve.Log App.Serve.Line),
        s.phase = .ready version →
          App.Serve.ScreenTable App.Serve.State.watching App.Serve.step App.Serve.result
            App.Serve.Screen.firstChange s id told latest screen left := by
  intro h
  -- an update of the first changed line alone leaves the second as the subscriber held it
  let before : App.Serve.Line := { text := [], spans := [] }
  let after : App.Serve.Line := { text := [0x41], spans := [] }
  let told : App.Serve.Screen := { lines := [before, before], cursor := ⟨0, 0, true⟩, title := "" }
  let latest : App.Serve.Screen := { lines := [after, after], cursor := ⟨0, 0, true⟩, title := "" }
  have exact :=
    (h ({ stage := .ready "1" } : App.Serve.StateRec) "1" (.number 1) told latest latest {} rfl).2.2
  have := exact.1 1
  simp [App.Serve.Screen.View.line, App.Serve.Screen.firstChange, told, latest, before, after,
    List.lookup] at this

theorem ticks_settle (s : State) (now t₁ : Nat)
    (h₁ : (Session.trace Session.step s [.tick now]).1.nextTick = some t₁) :
    (Session.trace Session.step s [.tick now, .tick t₁]).1.nextTick = none :=
  Session.ticks_settle s now t₁ h₁

theorem ticks_settle_rejects_poll :
    ¬∀ (s : State) (now t₁ : Nat),
        (fun (_ : State) => (some 0 : Option Nat)) (Session.trace Session.step s [.tick now]).1 =
            some t₁ →
          (fun (_ : State) => (some 0 : Option Nat))
              (Session.trace Session.step s [.tick now, .tick t₁]).1 =
            none := by
  intro h
  exact absurd (h (State.boot (Vt.Vt.init 1 1) [] []) 0 0 rfl) (by simp)

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

end Linger
