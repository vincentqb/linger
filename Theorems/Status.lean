module

public import Linger.Display.CoreCode.Alert
public import Linger.Display.CoreCode.Listing
public import Linger.Display.CoreCode.Status
public import Linger.Display.CoreCode.View
public import Linger.Selector.CoreCode.Picker
public import Linger.Display.CoreCode.Title
public import Linger.Session.CoreCode
public import Linger.Session.CoreSpec
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

/-! # The status rule of `Challenge.lean`: the proofs of its headline theorems and their kills

`Challenge.lean` states them; each proof cites the component theorems it restates, and
`Theorems.Solution` gathers every part for `./lake comparator`. -/

public section

namespace Linger

open Linger.Display Linger.Session Linger.Target Terminal

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
