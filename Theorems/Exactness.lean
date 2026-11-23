module

public import Linger.App.CoreCode.Api
public import Linger.App.CoreCode.Commands
public import Linger.App.CoreCode.Entry
public import Linger.App.CoreCode.Fields
public import Linger.App.CoreCode.Serve
public import Linger.App.CoreCode.Wait
public import Linger.Display.CoreCode.Listing
public import Linger.Import.CoreCode.Resurrect
public import Linger.Selector.CoreCode.Picker
public import Linger.Os.CoreCode.Answer
public import Linger.Os.CoreCode.Env
public import Linger.Session.CoreCode
public import Linger.Session.CoreCode.Names
public import Linger.Session.CoreSpec
public import Linger.Session.WorldSpec
public import Linger.Target.CoreCode.Name
public import Linger.Target.CoreCode.Remote
public import Linger.Target.CoreSpec
public import Linger.Target.WorldSpec
public import Terminal.CoreCode.Render
public import Terminal.CoreCode.Replay
public import Terminal.CoreSpec
import all Linger.App.Proofs.Api
import all Linger.App.Proofs.Capture
import all Linger.App.Proofs.Commands
import all Linger.App.Proofs.Entry
import all Linger.App.Proofs.Kill
import all Linger.App.Proofs.Recovery
import all Linger.App.Proofs.Serve
import all Linger.App.Proofs.Stream
import all Linger.App.Proofs.Hosts
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
import Linger.Selector.Proofs.Porcelain
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

/-! # Part 3 of `Challenge.lean`, exactness: the proofs of its headline theorems and their kills

`Challenge.lean` states them; each proof cites the component theorems it restates, and
`Theorems.Solution` gathers every part for `./lake comparator`. -/

public section

namespace Linger

open Linger.Display Linger.Session Linger.Target Terminal

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

theorem serve_renders_api (method : String) (params : App.Serve.Json) (found : App.Api.Found)
    (members : List (String × App.Serve.Json)) :
    App.Serve.parse method params =
        (App.Serve.words method params).bind
          (fun argv =>
            (App.Api.parse argv).bind fun request =>
              (App.Serve.input method params).map fun bytes => (request, bytes)) ∧
      (∀ request bytes,
        App.Serve.parse method params = some (request, bytes) →
          (App.Serve.methods.lookup method).map (·.1) = some request.op) ∧
      App.Serve.result found members =
        .obj
          (("answer", .str (App.Serve.answerName (App.Api.answer found))) ::
            ("code", .number (toString (App.Api.answer found).code)) :: members) :=
  ⟨App.Serve.parse_eq method params, fun _ _ parsed => App.Serve.parse_op parsed,
    App.Serve.result_eq found members⟩

theorem serve_renders_api_rejects_crossed :
    ¬∀ (method : String) (params : App.Serve.Json) (found : App.Api.Found)
        (members : List (String × App.Serve.Json)),
        (fun (method : String) (params : App.Serve.Json) =>
                App.Serve.parse (if method = "session/detach" then "session/kill" else method)
                  params)
              method params =
            (App.Serve.words method params).bind
              (fun argv =>
                (App.Api.parse argv).bind fun request =>
                  (App.Serve.input method params).map fun bytes => (request, bytes)) ∧
          (∀ request bytes,
            (fun (method : String) (params : App.Serve.Json) =>
                    App.Serve.parse (if method = "session/detach" then "session/kill" else method)
                      params)
                  method params =
                some (request, bytes) →
              (App.Serve.methods.lookup method).map (·.1) = some request.op) ∧
          App.Serve.result found members =
            .obj
              (("answer", .str (App.Serve.answerName (App.Api.answer found))) ::
                ("code", .number (toString (App.Api.answer found).code)) :: members) := by
  intro h
  -- `session/detach x` would take `kill x`'s request
  have := (h "session/detach" (.obj [("name", .str "x")]) .done []).1
  revert this
  decide

theorem serve_renders_api_rejects_outside :
    ¬∀ (method : String) (params : App.Serve.Json) (found : App.Api.Found)
        (members : List (String × App.Serve.Json)),
        App.Serve.parse method params =
            (App.Serve.words method params).bind
              (fun argv =>
                (App.Api.parse argv).bind fun request =>
                  (App.Serve.input method params).map fun bytes => (request, bytes)) ∧
          (∀ request bytes,
            App.Serve.parse method params = some (request, bytes) →
              (App.Serve.methods.lookup method).map (·.1) = some request.op) ∧
          (fun (_ : App.Api.Found) (members : List (String × App.Serve.Json)) =>
                App.Serve.Json.obj (("answer", .str "done") :: ("code", .number "0") :: members))
              found members =
            .obj
              (("answer", .str (App.Serve.answerName (App.Api.answer found))) ::
                ("code", .number (toString (App.Api.answer found).code)) :: members) := by
  intro h
  -- a request that found no session would answer that it did what was asked
  have := (h "" .null .missing []).2.2
  simp [App.Serve.answerName, App.Api.answer, App.Api.Found.answer] at this

theorem chooser_same_list (rows : List (List (String × String)))
    (named :
      ∀ record ∈ App.Serve.records rows,
        ∃ rest,
          record = ("name", App.Serve.Record.key record) :: rest ∧
            Remote.targetValid (App.Serve.Record.key record) = true ∧
            ∀ field ∈ rest, field.1 ≠ "name")
    (distinct : ((App.Serve.records rows).map App.Serve.Record.key).Nodup) :
    ∃ snapshot,
      Selector.Picker.parseSnapshot (Listing.porcelain rows) = .ok snapshot ∧
        snapshot.candidates = (App.Serve.records rows).map App.Serve.Record.key ∧
        ∀ record ∈ App.Serve.records rows,
          Selector.Picker.Snapshot.row snapshot (App.Serve.Record.key record) = record :=
  Selector.Picker.porcelain_read rows named distinct

theorem chooser_same_list_rejects_own :
    ¬∀ (rows : List (List (String × String))),
        (∀ record ∈ App.Serve.records rows,
            ∃ rest,
              record = ("name", App.Serve.Record.key record) :: rest ∧
                Remote.targetValid (App.Serve.Record.key record) = true ∧
                ∀ field ∈ rest, field.1 ≠ "name") →
          ((App.Serve.records rows).map App.Serve.Record.key).Nodup →
          ∃ snapshot,
            Selector.Picker.ownList (Listing.porcelain rows) = .ok snapshot ∧
              snapshot.candidates = (App.Serve.records rows).map App.Serve.Record.key ∧
              ∀ record ∈ App.Serve.records rows,
                Selector.Picker.Snapshot.row snapshot (App.Serve.Record.key record) = record := by
  intro h
  -- a chooser that read a list of its own would show a session `mine` where the listing shows none
  obtain ⟨snapshot, read, names, -⟩ :=
    h [] (by simp [App.Serve.records, Linger.Display.Listing.records])
      (by simp [App.Serve.records, Linger.Display.Listing.records])
  simp only [Selector.Picker.ownList, Except.ok.injEq] at read
  subst read
  simp [App.Serve.records, Linger.Display.Listing.records] at names

theorem serve_negotiated (s : App.Serve.State) (ev : App.Serve.Event) :
    App.Serve.Negotiated App.Serve.State.init App.Serve.State.phase App.Serve.State.subscription
      App.Serve.State.watching App.Serve.step s ev := by
  unfold App.Serve.Negotiated
  exact
    ⟨App.Serve.init_phase, App.Serve.step_negotiating s ev, App.Serve.step_ready s ev,
      App.Serve.step_welcome s ev, fun id method params received => by
      subst received
      exact App.Serve.step_answers s id method params, App.Serve.step_notify_open s ev,
      App.Serve.step_relays_open s ev, App.Serve.step_opens s ev,
      fun id params version ready received => by
      subst received
      exact App.Serve.subscribe_opens s id params version ready,
      fun id asked params version ready subscribed received names => by
      subst received
      exact App.Serve.unsubscribe_closes s id asked params version ready subscribed names,
      App.Serve.step_watch_opens s ev, fun id asked params version ready held received names => by
      subst received
      exact App.Serve.unsubscribe_closes_watch s id asked params version ready held names⟩

theorem serve_negotiated_rejects_eager :
    ¬∀ (s : App.Serve.State) (ev : App.Serve.Event),
        App.Serve.Negotiated App.Serve.State.init App.Serve.State.phase App.Serve.State.subscription
          App.Serve.State.watching (App.Serve.eager App.Serve.step) s ev := by
  intro h
  -- a fresh connection would answer `sessions/list` before its handshake
  have heard :=
    h App.Serve.State.init (.received (.request (.number "1") "sessions/list" (.obj [])))
  unfold App.Serve.Negotiated at heard
  have := heard.2.1 (fun _ ready => by simp [App.Serve.State.init, App.Serve.State.phase] at ready)
  simp [App.Serve.eager, App.Serve.Effect.Negotiating, App.Serve.welcome] at this

theorem serve_negotiated_rejects_chatty :
    ¬∀ (s : App.Serve.State) (ev : App.Serve.Event),
        App.Serve.Negotiated App.Serve.State.init App.Serve.State.phase App.Serve.State.subscription
          App.Serve.State.watching (App.Serve.chatty App.Serve.step) s ev := by
  intro h
  -- a ready connection with no subscription open would notify each time its writer is free
  have heard := h ({ stage := .ready "1" } : App.Serve.StateRec) .writable
  unfold App.Serve.Negotiated at heard
  have :=
    heard.2.2.2.2.2.1 (.send (.notify "sessions/changed" (.obj []))) (by simp [App.Serve.chatty])
      "sessions/changed" (.obj []) rfl
  obtain ⟨id, names, -⟩ := this
  simp [App.Serve.Json.member?] at names

theorem one_renderer (v : Vt.Vt) (row : Vt.Row)
    (hv : Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable v) :
    ((App.Serve.Screen.render v).lines.map fun line => line.text ++ [0x0A]).flatten =
        Render.screenText v ∧
      (App.Serve.Screen.render v).lines =
        (List.range v.rowCount).map (fun y => App.Serve.Line.of (v.getRow y)) ∧
      (App.Serve.Line.of row).text = Render.rowText row ∧
      App.Serve.Span.expand (App.Serve.Line.of row).spans = App.Serve.Line.pens row ∧
      App.Serve.Span.Compact (App.Serve.Line.of row).spans ∧
      (App.Serve.Screen.render v).cursor =
        { x := v.cursorPos.1, y := v.cursorPos.2, visible := v.getModes.cursorVisible } ∧
      (App.Serve.Screen.render v).title = v.windowTitle.map Render.textChar :=
  ⟨App.Serve.Screen.render_capture v hv, App.Serve.Screen.render_lines v,
    App.Serve.Line.of_text row, App.Serve.Line.of_spans row, App.Serve.Line.of_compact row,
    App.Serve.Screen.render_cursor v, App.Serve.Screen.render_title v⟩

theorem one_renderer_rejects_untrimmed :
    ¬∀ (v : Vt.Vt) (row : Vt.Row),
        Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable v →
          ((App.Serve.Screen.untrimmed (fun (v : Vt.Vt) => (List.range v.rowCount).map v.getRow)
                      v).lines.map
                  fun line => line.text ++ [0x0A]).flatten =
              Render.screenText v ∧
            (App.Serve.Screen.untrimmed (fun (v : Vt.Vt) => (List.range v.rowCount).map v.getRow)
                  v).lines =
              (List.range v.rowCount).map (fun y => App.Serve.Line.of (v.getRow y)) ∧
            (App.Serve.Line.of row).text = Render.rowText row ∧
            App.Serve.Span.expand (App.Serve.Line.of row).spans = App.Serve.Line.pens row ∧
            App.Serve.Span.Compact (App.Serve.Line.of row).spans ∧
            (App.Serve.Screen.untrimmed (fun (v : Vt.Vt) => (List.range v.rowCount).map v.getRow)
                  v).cursor =
              { x := v.cursorPos.1, y := v.cursorPos.2, visible := v.getModes.cursorVisible } ∧
            (App.Serve.Screen.untrimmed (fun (v : Vt.Vt) => (List.range v.rowCount).map v.getRow)
                  v).title =
              v.windowTitle.map Render.textChar := by
  intro h
  -- a renderer that keeps a fresh cell's trailing blank prints it, where `capture` prints nothing
  have := (h (Vt.Vt.init 1 1) #[] (.init 1 1)).1
  rw [App.Serve.untrimmed_init_one, App.Serve.screenText_init_one] at this
  simp at this

theorem history_log_exact (s : App.Serve.State) (version : String) (id : App.Serve.Id)
    (pending left : App.Serve.Log App.Serve.Line) (screen : App.Serve.Screen)
    (ready : s.phase = .ready version) :
    App.Serve.HistoryLog App.Serve.State.watching App.Serve.step App.Serve.result s id pending
      screen left :=
  ⟨fun asked =>
    ⟨(App.Serve.watched_history_opens s version id screen left ready asked).1, _,
      (App.Serve.watched_history_opens s version id screen left ready asked).2, by
      simpa [App.Serve.Log.reads] using App.Serve.Log.append_masks App.Serve.historyCap {} left⟩,
    fun holds =>
    ⟨(App.Serve.watched_history s version id pending screen left ready holds).1,
      ⟨_, (App.Serve.watched_history s version id pending screen left ready holds).2,
        App.Serve.Log.append_masks _ pending left⟩,
      (App.Serve.flush_history s version id pending ready holds).1,
      (App.Serve.flush_history s version id pending ready holds).2⟩⟩

theorem history_log_exact_rejects_uncounted :
    ¬∀ (s : App.Serve.State) (version : String) (id : App.Serve.Id)
        (pending left : App.Serve.Log App.Serve.Line) (screen : App.Serve.Screen),
        s.phase = .ready version →
          App.Serve.HistoryLog App.Serve.State.watching (App.Serve.uncounted App.Serve.step)
            App.Serve.result s id pending screen left := by
  intro h
  -- a connection that forgets a look's count of drops reads no gap where the look dropped a line
  let screen : App.Serve.Screen := { lines := [], cursor := ⟨0, 0, true⟩, title := "" }
  have held :=
    (h ({ stage := .ready "1", watches := [(.number "1", .history {})] } : App.Serve.StateRec) "1"
          (.number "1") {} { tail := [], dropped := 1 } screen rfl).2
      (by simp [App.Serve.State.watching])
  obtain ⟨kept, holds, masks⟩ := held.2.1
  simp [App.Serve.uncounted, App.Serve.step, App.Serve.watched, App.Serve.State.phase,
    App.Serve.State.watching, App.Serve.State.setWatch, App.Serve.Log.append] at holds
  subst holds
  simp [App.Serve.Log.reads, App.Serve.Log.Masks] at masks

theorem serve_attach_exact (s : App.Serve.State) (version : String) (id : App.Serve.Id)
    (dec : Wire.Decoder) (pending bytes : List UInt8) (ready : s.phase = .ready version) :
    App.Serve.AttachStream App.Serve.State.watching App.Serve.step App.Serve.result
      Wire.Decoder.feed s id dec pending bytes :=
  App.Serve.attach_stream s version id dec pending bytes ready

theorem serve_attach_exact_rejects_unpainted :
    ¬∀ (s : App.Serve.State) (version : String) (id : App.Serve.Id) (dec : Wire.Decoder)
        (pending bytes : List UInt8),
        s.phase = .ready version →
          App.Serve.AttachStream App.Serve.State.watching
            (App.Serve.unpainted App.Serve.State.watching App.Serve.step) App.Serve.result
            Wire.Decoder.feed s id dec pending bytes := by
  intro h
  -- a stream that drops its first read's bytes, which open the repaint, leaves its subscriber
  -- waiting for none of them
  have painted :
    Wire.Decoder.feed {} (Wire.encode (.output [65])) =
      ({ buf := [], errored := false }, [.output [65]]) := by
    simpa [Wire.decode] using
      Wire.decode_encode_stream [.output [65]]
        (by simpa using Wire.fits_wf _ (by simp [Wire.Msg.Fits, Wire.maxPayload]))
  have quiet : Wire.Decoder.feed {} [] = ({ buf := [], errored := false }, []) := by
    simpa [Wire.decode] using Wire.decode_encode_stream [] (by simp)
  obtain ⟨rest, sent, streamed⟩ :=
    (h ({ stage := .ready "1", watches := [(.number "1", .attaching)] } : App.Serve.StateRec) "1"
          (.number "1") {} [] (Wire.encode (.output [65])) rfl).1
      (by simp [App.Serve.State.watching])
  simp [App.Serve.unpainted, App.Serve.State.watching, App.Serve.step, App.Serve.readAttach,
    App.Serve.State.phase, App.Serve.streamed, quiet, App.Serve.State.setWatch] at sent streamed
  subst sent
  simp [App.Serve.Streamed, painted, Wire.shown, Wire.Msg.ends] at streamed

theorem remote_rows_exact (host : String) (messages : List App.Serve.Json) (status : UInt32)
    (records : List App.Serve.Record) :
    App.Serve.Remote.Exact App.Serve.Remote.heard App.Serve.Remote.rows Name.accept host messages
      status records :=
  ⟨App.Serve.Remote.heard_listed messages status records,
    App.Serve.Remote.heard_older messages status, App.Serve.Remote.rows_keys host records⟩

theorem remote_rows_exact_rejects_unshaken :
    ¬∀ (host : String) (messages : List App.Serve.Json) (status : UInt32)
        (records : List App.Serve.Record),
        App.Serve.Remote.Exact App.Serve.Remote.unshaken App.Serve.Remote.rows Name.accept host
          messages status records := by
  intro h
  -- a reading that takes request 2's records whatever request 1 got lists a host that never
  -- shook hands
  have listed :=
    (h "far"
        [.obj
            [("id", .number "2"), ("result", .obj [("answer", .str "done"), ("records", .arr [])])]]
        0 []).1
  have shook :=
    (listed.mp
        (by
          simp [App.Serve.Remote.unshaken, App.Serve.Remote.answerOf, App.Serve.Json.member?,
            App.Serve.Id.of, List.lookup])).1
  obtain ⟨result, version, found, -⟩ := shook
  simp [App.Serve.Remote.answerOf, App.Serve.Json.member?, App.Serve.Id.of, List.lookup] at found

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

end Linger
