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
import all Linger.App.CoreCode.Codec
import all Linger.App.Proofs.Codec
import Linger.Display.Proofs.Record
public import ExactJSON.Solution
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

theorem route_exact (args : List String) : App.Entry.route args = App.Entry.Route.of args :=
  App.Entry.route_eq args

theorem route_exact_rejects_selector :
    ¬∀ (args : List String),
        (fun (args : List String) => App.Entry.Route.session args) args =
          App.Entry.Route.of args := by
  intro h
  exact absurd (h ["attach"]) (by simp [App.Entry.Route.of])

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

theorem serve_renders_api (method : String) (params : ExactJSON.Value) (request : App.Api.Request)
    (bytes : List UInt8) (found : App.Api.Found) (shows : App.Serve.Shows) :
    (App.Serve.parse method params = some (request, bytes) ↔
        ∃ call : App.Serve.Call,
          call.method = method ∧
            call.params = params ∧
            App.Api.parse call.words = some request ∧ call.input = some bytes) ∧
      (App.Serve.parse method params = some (request, bytes) →
        (App.Serve.methods.lookup method).map (·.1) = some request.op) ∧
      App.Serve.result found shows =
        App.Serve.Result.json
          { toShows := shows, answer := App.Serve.answerName (App.Api.answer found),
            code := (App.Api.answer found).code.toNat } :=
  ⟨App.Serve.parse_iff method params request bytes, App.Serve.parse_op,
    App.Serve.result_eq found shows⟩

theorem serve_renders_api_rejects_crossed :
    ¬∀ (method : String) (params : ExactJSON.Value) (request : App.Api.Request) (bytes : List UInt8)
        (found : App.Api.Found) (shows : App.Serve.Shows),
        ((fun (method : String) (params : ExactJSON.Value) =>
                  App.Serve.parse (if method = "session/detach" then "session/kill" else method)
                    params)
                method params =
              some (request, bytes) ↔
            ∃ call : App.Serve.Call,
              call.method = method ∧
                call.params = params ∧
                App.Api.parse call.words = some request ∧ call.input = some bytes) ∧
          ((fun (method : String) (params : ExactJSON.Value) =>
                  App.Serve.parse (if method = "session/detach" then "session/kill" else method)
                    params)
                method params =
              some (request, bytes) →
            (App.Serve.methods.lookup method).map (·.1) = some request.op) ∧
          App.Serve.result found shows =
            App.Serve.Result.json
              { toShows := shows, answer := App.Serve.answerName (App.Api.answer found),
                code := (App.Api.answer found).code.toNat } := by
  intro h
  -- `session/detach x` would take `kill x`'s request
  have crossed :=
    (h "session/detach" (App.Serve.Named.json ⟨"x"⟩) (.kill "x") [] .done {}).1.mp
      (by
        simp [App.Serve.parse_read (App.Serve.read_kill ⟨"x"⟩)]; decide)
  obtain ⟨call, methodIs, paramsAre, parsed, -⟩ := crossed
  cases call with
  | detach p =>
    obtain ⟨name⟩ := p
    have named : name = "x" := by
      simpa [App.Serve.Call.params, App.Serve.Named.json] using paramsAre
    subst named
    revert parsed
    decide
  | _ => simp [App.Serve.Call.method] at methodIs

theorem serve_renders_api_rejects_outside :
    ¬∀ (method : String) (params : ExactJSON.Value) (request : App.Api.Request) (bytes : List UInt8)
        (found : App.Api.Found) (shows : App.Serve.Shows),
        (App.Serve.parse method params = some (request, bytes) ↔
            ∃ call : App.Serve.Call,
              call.method = method ∧
                call.params = params ∧
                App.Api.parse call.words = some request ∧ call.input = some bytes) ∧
          (App.Serve.parse method params = some (request, bytes) →
            (App.Serve.methods.lookup method).map (·.1) = some request.op) ∧
          (fun (_ : App.Api.Found) (shows : App.Serve.Shows) =>
                App.Serve.Result.json { toShows := shows, answer := "done", code := 0 })
              found shows =
            App.Serve.Result.json
              { toShows := shows, answer := App.Serve.answerName (App.Api.answer found),
                code := (App.Api.answer found).code.toNat } := by
  intro h
  -- a request that found no session would answer that it did what was asked
  have := (h "" .null .serve [] .missing {}).2.2
  simp [App.Serve.Result.json, App.Serve.answerName, App.Api.answer, App.Api.Found.answer] at this

theorem serve_refuses_params (s : App.Serve.State) (version : String) (id : App.Serve.Id)
    (method : String) (params : ExactJSON.Value) (ready : s.phase = .ready version)
    (listed : (App.Serve.methods.lookup method).isSome = true)
    (plain :
      ¬(method = "session/resize" ∨ method = "session/detach") ∨
        App.Serve.member? "subscription" params = none)
    (undefined : ∀ call : App.Serve.Call, call.method = method → call.params ≠ params) :
    App.Serve.step s (.received (.request id method params)) =
      (s,
        [.send
            (.error (some id) (-32602) "invalid params"
              (App.Serve.Result.json
                { answer := App.Serve.answerName .usage,
                  code := (Os.Answer.code .usage).toNat }))]) :=
  App.Serve.step_refuses_params s version id method params ready listed plain undefined

theorem serve_refuses_params_rejects_eager :
    ¬∀ (s : App.Serve.State) (version : String) (id : App.Serve.Id) (method : String)
        (params : ExactJSON.Value),
        s.phase = .ready version →
          (App.Serve.methods.lookup method).isSome = true →
          (¬(method = "session/resize" ∨ method = "session/detach") ∨
            App.Serve.member? "subscription" params = none) →
          (∀ call : App.Serve.Call, call.method = method → call.params ≠ params) →
          App.Serve.eager App.Serve.step s (.received (.request id method params)) =
            (s,
              [.send
                  (.error (some id) (-32602) "invalid params"
                    (App.Serve.Result.json
                      { answer := App.Serve.answerName .usage,
                        code := (Os.Answer.code .usage).toNat }))]) := by
  intro h
  -- an eager connection performs a request whatever its params, even ones `session/kill` does not
  -- define
  have :=
    h { stage := .ready "1" } "1" (.number 1) "session/kill"
      (.table #[("force", .boolean true), ("name", .string "x")]) rfl (by decide) (.inl (by decide))
      (fun call methodIs paramsAre => by
        cases call with
        | kill p => simp [App.Serve.Call.params, App.Serve.Named.json] at paramsAre
        | _ => simp [App.Serve.Call.method] at methodIs)
  simp [App.Serve.eager] at this

theorem serve_refuses_uncanonical (s : App.Serve.State) (line reason : String)
    (refused : ExactJSON.Value.parse line = .error reason) :
    App.Serve.decode line = .invalid none (some reason) ∧
      App.Serve.step s (.received (.invalid none (some reason))) =
        (s,
          [.send
              (.error none (-32700) "parse error"
                (App.Serve.Result.json
                  { answer := App.Serve.answerName .usage, code := (Os.Answer.code .usage).toNat,
                    reason? := some reason }))]) :=
  ⟨App.Serve.decode_uncanonical refused, App.Serve.step_uncanonical s reason⟩

/-- Some line is no canonical text: the text of an invalid value, a NaN, is not read. -/
theorem parse_refused : ∃ line reason, ExactJSON.Value.parse line = .error reason := by
  have invalid : ¬(ExactJSON.Value.float Float.nan).Valid := by
    show ¬(ExactJSON.finiteFloat Float.nan = true)
    rw [show ExactJSON.finiteFloat Float.nan = false by decide +kernel]
    decide
  have unread := ExactJSON.parse_render_invalid _ invalid
  cases parsed : ExactJSON.Value.parse (ExactJSON.Value.float Float.nan).render with
  | error e => exact ⟨_, e, parsed⟩
  | ok v =>
    rw [parsed] at unread
    cases unread

theorem serve_refuses_uncanonical_rejects_unreasoned :
    ¬∀ (s : App.Serve.State) (line reason : String),
        ExactJSON.Value.parse line = .error reason →
          App.Serve.unreasoned App.Serve.decode line = .invalid none (some reason) ∧
            App.Serve.step s (.received (.invalid none (some reason))) =
              (s,
                [.send
                    (.error none (-32700) "parse error"
                      (App.Serve.Result.json
                        { answer := App.Serve.answerName .usage,
                          code := (Os.Answer.code .usage).toNat, reason? := some reason }))]) := by
  intro h
  -- a line that is no canonical text would have its reason go unsaid
  obtain ⟨line, reason, refused⟩ := parse_refused
  have read := (h App.Serve.State.init line reason refused).1
  simp [App.Serve.unreasoned, App.Serve.decode_uncanonical refused] at read

/-- An object's text opens with `{`. -/
theorem render_table_head (members : List (String × ExactJSON.Value)) :
    (ExactJSON.Value.render (.table members.toArray)).toList.head? = some '{' := by
  rw [show members.toArray = (⟨members⟩ : Array (String × ExactJSON.Value)) from rfl,
    ExactJSON.Value.text_table]
  rfl

theorem porcelain_records (rows : List (List (String × String))) :
    App.Serve.records rows =
        rows.map
          (fun row =>
            Listing.Record.ofRow
              (row.map fun field =>
                (field.1.map Terminal.Render.textChar, field.2.map Terminal.Render.textChar))) ∧
      Listing.porcelain rows = ExactJSON.encodeLines (App.Serve.records rows).toArray := ⟨rfl, rfl⟩

theorem porcelain_records_rejects_tsv :
    ¬∀ (rows : List (List (String × String))),
        App.Serve.records rows =
            rows.map
              (fun row =>
                Listing.Record.ofRow
                  (row.map fun field =>
                    (field.1.map Terminal.Render.textChar, field.2.map Terminal.Render.textChar))) ∧
          Listing.tsv rows = ExactJSON.encodeLines (App.Serve.records rows).toArray := by
  intro h
  -- a session `a`'s porcelain opens with `{`, where the tab-separated block opens with `name`
  have same := congrArg (fun text : String => text.toList.head?) (h [[("name", "a")]]).2
  have opens :
    (ExactJSON.Value.render
          (ExactJSON.toValue
            (Listing.Record.ofRow
              [("name".map Terminal.Render.textChar,
                  "a".map Terminal.Render.textChar)]))).toList.head? =
      some '{' := by
    rw [App.Serve.toValue_record, App.Serve.Record.json]
    exact render_table_head _
  have lines :
    ((App.Serve.records [[("name", "a")]]).toArray.map ExactJSON.toValue).toList =
      [ExactJSON.toValue
          (Listing.Record.ofRow
            [("name".map Terminal.Render.textChar, "a".map Terminal.Render.textChar)])] := by
    simp only [Array.toList_map]
    rfl
  rw [ExactJSON.encodeLines_eq, ExactJSON.renderLines_eq, lines] at same
  simp only [List.map_cons, List.map_nil, String.join_cons, String.join_nil, String.append_empty,
    String.toList_append, List.head?_append, opens, Option.some_or] at same
  simp [Listing.tsv] at same

theorem records_clean (rows : List (List (String × String))) (record : App.Serve.Record)
    (key : String) (field : Listing.Field) (listed : record ∈ App.Serve.records rows)
    (held : record[key]? = some field) :
    ∀ c ∈ key.toList ++ field.render.toList,
      Display.Printable c ∧ (ExactJSON.mustEscape c = true → c = '\u2028' ∨ c = '\u2029') :=
  Linger.Display.Listing.records_clean rows record key field listed held

theorem records_clean_rejects_raw :
    ¬∀ (rows : List (List (String × String))) (record : App.Serve.Record) (key : String)
        (field : Listing.Field),
        record ∈
            (fun (rows : List (List (String × String))) => rows.map Listing.Record.ofRow) rows →
          record[key]? = some field →
          ∀ c ∈ key.toList ++ field.render.toList,
            Display.Printable c ∧
              (ExactJSON.mustEscape c = true → c = '\u2028' ∨ c = '\u2029') := by
  intro h
  -- a name with an escape character would reach the encoder as the escape it is
  have :=
    h [[("name", "\x1b")]] (Listing.Record.ofRow [("name", "\x1b")]) "name" (.text "\x1b") (by simp)
      (Linger.Display.Listing.ofRow_head "name" "\x1b" (.text "\x1b") []
        (by simp [Listing.Field.of, Listing.flagKeys, Listing.countKeys]))
      '\x1b' (by simp [Listing.Field.render])
  exact
    absurd this.1
      (by
        simp only [Display.Printable]; decide)

theorem chooser_same_list (rows : List (List (String × String)))
    (named :
      ∀ record ∈ App.Serve.records rows, Remote.targetValid (App.Serve.Record.key record) = true)
    (distinct : ((App.Serve.records rows).map App.Serve.Record.key).Nodup) :
    ∃ snapshot,
      Selector.Picker.parseSnapshot (Listing.porcelain rows) = .ok snapshot ∧
        snapshot.candidates = (App.Serve.records rows).map App.Serve.Record.key ∧
        ∀ record ∈ App.Serve.records rows,
          Selector.Picker.Snapshot.row snapshot (App.Serve.Record.key record) =
            Listing.Record.fields record := Selector.Picker.porcelain_read rows named distinct

theorem chooser_same_list_rejects_own :
    ¬∀ (rows : List (List (String × String))),
        (∀ record ∈ App.Serve.records rows,
            Remote.targetValid (App.Serve.Record.key record) = true) →
          ((App.Serve.records rows).map App.Serve.Record.key).Nodup →
          ∃ snapshot,
            Selector.Picker.ownList (Listing.porcelain rows) = .ok snapshot ∧
              snapshot.candidates = (App.Serve.records rows).map App.Serve.Record.key ∧
              ∀ record ∈ App.Serve.records rows,
                Selector.Picker.Snapshot.row snapshot (App.Serve.Record.key record) =
                  Listing.Record.fields record := by
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
      App.Serve.step_relays_open s ev, App.Serve.step_opens s ev, fun id version ready received =>
      by
      subst received
      exact App.Serve.subscribe_opens s id version ready,
      fun id asked version ready subscribed received => by
      subst received
      exact App.Serve.unsubscribe_closes s id asked version ready subscribed,
      App.Serve.step_watch_opens s ev, fun id asked version ready held received => by
      subst received
      exact App.Serve.unsubscribe_closes_watch s id asked version ready held⟩

theorem serve_negotiated_rejects_eager :
    ¬∀ (s : App.Serve.State) (ev : App.Serve.Event),
        App.Serve.Negotiated App.Serve.State.init App.Serve.State.phase App.Serve.State.subscription
          App.Serve.State.watching (App.Serve.eager App.Serve.step) s ev := by
  intro h
  -- a fresh connection would answer `sessions/list` before its handshake
  have heard :=
    h App.Serve.State.init (.received (.request (.number 1) "sessions/list" (.table #[])))
  unfold App.Serve.Negotiated at heard
  have := heard.2.1 (fun _ ready => by simp [App.Serve.State.init, App.Serve.State.phase] at ready)
  simp [App.Serve.eager, App.Serve.Effect.Negotiating, App.Serve.welcome,
    App.Serve.Welcome.json] at this

theorem serve_negotiated_rejects_chatty :
    ¬∀ (s : App.Serve.State) (ev : App.Serve.Event),
        App.Serve.Negotiated App.Serve.State.init App.Serve.State.phase App.Serve.State.subscription
          App.Serve.State.watching (App.Serve.chatty App.Serve.step) s ev := by
  intro h
  -- a ready connection with no subscription open would notify each time its writer is free
  have heard := h ({ stage := .ready "1" } : App.Serve.StateRec) .writable
  unfold App.Serve.Negotiated at heard
  have :=
    heard.2.2.2.2.2.1 (.send (.notify "sessions/changed" (.table #[]))) (by simp [App.Serve.chatty])
      "sessions/changed" (.table #[]) rfl
  obtain ⟨id, names, -⟩ := this
  simp [App.Serve.member?] at names

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
    (h ({ stage := .ready "1", watches := [(.number 1, .history {})] } : App.Serve.StateRec) "1"
          (.number 1) {} { tail := [], dropped := 1 } screen rfl).2
      (by simp [App.Serve.State.watching])
  obtain ⟨kept, holds, masks⟩ := held.2.1
  simp [App.Serve.uncounted, App.Serve.step, App.Serve.watched, App.Serve.State.phase,
    App.Serve.State.watching, App.Serve.State.setWatch, App.Serve.Log.append] at holds
  subst holds
  simp [App.Serve.Log.reads, App.Serve.Log.Masks] at masks

theorem serve_attach_exact (s : App.Serve.State) (version : String) (id : App.Serve.Id)
    (dec : Wire.Decoder) (pending bytes screen : List UInt8) (found : App.Api.Found)
    (said : App.Serve.Log String) (ready : s.phase = .ready version) :
    App.Serve.AttachStream App.Serve.State.watching App.Serve.step App.Serve.result App.Api.answer
      Os.Answer.code App.Serve.paint Wire.Decoder.feed s id dec pending bytes screen found said :=
  App.Serve.attach_stream s version id dec pending bytes screen found said ready

theorem serve_attach_exact_rejects_unpainted :
    ¬∀ (s : App.Serve.State) (version : String) (id : App.Serve.Id) (dec : Wire.Decoder)
        (pending bytes screen : List UInt8) (found : App.Api.Found) (said : App.Serve.Log String),
        s.phase = .ready version →
          App.Serve.AttachStream App.Serve.State.watching
            (App.Serve.unpainted App.Serve.State.watching App.Serve.step) App.Serve.result
            App.Api.answer Os.Answer.code App.Serve.paint Wire.Decoder.feed s id dec pending bytes
            screen found said := by
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
    ((h ({ stage := .ready "1", watches := [(.number 1, .attaching)] } : App.Serve.StateRec) "1"
            (.number 1) {} [] (Wire.encode (.output [65])) [] .done {} rfl).1
        (by simp [App.Serve.State.watching])).1
  simp [App.Serve.unpainted, App.Serve.State.watching, App.Serve.step, App.Serve.readAttach,
    App.Serve.State.phase, App.Serve.streamed, quiet, App.Serve.State.setWatch] at sent streamed
  subst sent
  simp [App.Serve.Streamed, painted, Wire.shown, Wire.Msg.ends] at streamed

theorem serve_attach_exact_rejects_unframed :
    ¬∀ (s : App.Serve.State) (version : String) (id : App.Serve.Id) (dec : Wire.Decoder)
        (pending bytes screen : List UInt8) (found : App.Api.Found) (said : App.Serve.Log String),
        s.phase = .ready version →
          App.Serve.AttachStream App.Serve.State.watching App.Serve.step App.Serve.result
            App.Api.answer Os.Answer.code App.Serve.unframed Wire.Decoder.feed s id dec pending
            bytes screen found said := by
  intro h
  -- a screen read as its bytes, unframed, is read as frames: the bytes of an input frame leave
  -- nothing waiting for the subscriber, where the screen should
  have framed :
    Wire.Decoder.feed {} (Wire.encode (.input [66])) =
      ({ buf := [], errored := false }, [.input [66]]) := by
    simpa [Wire.decode] using
      Wire.decode_encode_stream [.input [66]]
        (by simpa using Wire.fits_wf _ (by simp [Wire.Msg.Fits, Wire.maxPayload]))
  obtain ⟨_, _, shown, _⟩ :=
    (h ({ stage := .ready "1", watches := [(.number 1, .attaching)] } : App.Serve.StateRec) "1"
          (.number 1) {} [] [] (Wire.encode (.input [66])) .done {} rfl).1
      (by simp [App.Serve.State.watching])
  simp [App.Serve.unframed, App.Serve.State.watching, App.Serve.step, App.Serve.readAttach,
    App.Serve.State.phase, App.Serve.streamed, framed, Wire.shown, Wire.Msg.ends,
    App.Serve.State.setWatch] at shown
  simp [Wire.encode] at shown

theorem serve_attach_exact_rejects_done_anyway :
    ¬∀ (s : App.Serve.State) (version : String) (id : App.Serve.Id) (dec : Wire.Decoder)
        (pending bytes screen : List UInt8) (found : App.Api.Found) (said : App.Serve.Log String),
        s.phase = .ready version →
          App.Serve.AttachStream App.Serve.State.watching App.Serve.step App.Serve.result
            App.Serve.doneAnyway Os.Answer.code App.Serve.paint Wire.Decoder.feed s id dec pending
            bytes screen found said := by
  intro h
  -- the last update of an attach that found no session says `notFound`, not `done`
  obtain ⟨_, _, _, _, ⟨params, closed, last, _, closedIs, named, -⟩, _⟩ :=
    (h ({ stage := .ready "1", watches := [(.number 1, .stream {} [])] } : App.Serve.StateRec) "1"
          (.number 1) {} [] [] [] .missing {} rfl).2
      (by simp [App.Serve.State.watching])
  simp [App.Serve.State.watching, App.Serve.step, App.Serve.unwatched,
    App.Serve.State.phase] at last
  subst last
  rw [App.Serve.Output.update_closing] at closedIs
  have same := congrArg (App.Serve.member? "answer") (Option.some.inj closedIs)
  rw [App.Serve.Result.json_answer, App.Serve.Result.json_answer, named] at same
  simp [App.Serve.closedResult, App.Serve.answered, App.Serve.doneAnyway, App.Api.answer,
    App.Api.Found.answer, App.Serve.answerName] at same

theorem remote_rows_exact (host : String) (messages : List ExactJSON.Value) (status : UInt32)
    (records : List App.Serve.Record) :
    App.Serve.Remote.Rows App.Serve.Remote.heard App.Serve.Remote.rows Name.accept Os.Answer.code
      host messages status records := by
  refine ⟨?_, App.Serve.Remote.rows_keys host records⟩
  unfold App.Serve.Remote.Lists
  constructor
  · rintro ⟨shows, heard, listed⟩
    obtain ⟨shook, answered⟩ :=
      (App.Serve.Remote.heard_answered messages status .done shows).mp heard
    exact ⟨shook, shows, answered, listed⟩
  · rintro ⟨shook, shows, answered, listed⟩
    exact
      ⟨shows, (App.Serve.Remote.heard_answered messages status .done shows).mpr ⟨shook, answered⟩,
        listed⟩

theorem remote_rows_exact_rejects_unshaken :
    ¬∀ (host : String) (messages : List ExactJSON.Value) (status : UInt32)
        (records : List App.Serve.Record),
        App.Serve.Remote.Rows App.Serve.Remote.unshaken App.Serve.Remote.rows Name.accept
          Os.Answer.code host messages status records := by
  intro h
  -- a reading that takes request 2's answer whatever request 1 got lists a host that never
  -- shook hands
  have listed :=
    (h "far"
        [.table
            #[("id", .integer 2),
              ("result", .table #[("answer", .string "done"), ("code", .integer 0)])]]
        0 []).1
  have shook :=
    (listed.mp
        ⟨{ records? := some [] }, by
          simp [App.Serve.Remote.unshaken, App.Serve.Remote.answerOf, App.Serve.member?,
            App.Serve.Id.of, List.lookup],
          rfl⟩).1
  obtain ⟨welcome, found, -⟩ := shook
  simp [App.Serve.Remote.answerOf, App.Serve.member?, App.Serve.Id.of, List.lookup] at found

theorem remote_exact (request : App.Api.Request) (name : String) (input : List UInt8)
    (messages : List ExactJSON.Value) (status : UInt32) (answer : Os.Answer)
    (shows : App.Serve.Shows) (host : String) (t : Remote.Transport)
    (carry : List String → List UInt8 → Option (List UInt8))
    (delivers : Remote.Transport.Delivers carry t) (bytes : List UInt8) :
    App.Serve.Remote.Exact App.Serve.Remote.call App.Serve.parse App.Serve.Remote.heard
        Os.Answer.code App.Serve.Remote.found App.Api.answer App.Serve.Remote.said Remote.scrub
        request name input messages status answer shows host ∧
      Remote.argv t = t.command ++ ["linger", "serve"] ∧
      (carry (Remote.argv t) bytes = none ∨ carry (Remote.argv t) bytes = some bytes) := by
  refine
    ⟨⟨App.Serve.Remote.call_parse request name input,
        App.Serve.Remote.heard_answered messages status answer shows,
        App.Serve.Remote.heard_refused messages status, App.Serve.Remote.found_answer answer shows,
        App.Serve.Remote.said_eq host shows⟩,
      Remote.argv_eq t, ?_⟩
  rw [Remote.argv_eq]
  exact delivers bytes

theorem remote_exact_rejects_crossed :
    ¬∀ (request : App.Api.Request) (name : String) (input : List UInt8)
        (messages : List ExactJSON.Value) (status : UInt32) (answer : Os.Answer)
        (shows : App.Serve.Shows) (host : String) (t : Remote.Transport)
        (carry : List String → List UInt8 → Option (List UInt8)),
        Remote.Transport.Delivers carry t →
          ∀ (bytes : List UInt8),
            App.Serve.Remote.Exact
                (fun (request : App.Api.Request) (name : String) (input : List UInt8) =>
                  App.Serve.Remote.call (if request.op = .detach then .kill name else request) name
                    input)
                App.Serve.parse App.Serve.Remote.heard Os.Answer.code App.Serve.Remote.found
                App.Api.answer App.Serve.Remote.said Remote.scrub request name input messages status
                answer shows host ∧
              Remote.argv t = t.command ++ ["linger", "serve"] ∧
              (carry (Remote.argv t) bytes = none ∨ carry (Remote.argv t) bytes = some bytes) := by
  intro h
  -- a call that crosses `detach` to `kill` has the host kill the session it was to detach
  have crossed :=
    (h (.detach "x") "x" [] [] 0 .done {} "far" { command := ["ssh"] } (fun _ bytes => some bytes)
        (fun _ => Or.inr rfl) []).1.1
  simp only [App.Api.Request.op, ↓reduceIte] at crossed
  rw [App.Serve.Remote.call_parse] at crossed
  simp [App.Serve.Remote.asked] at crossed

theorem remote_attach_exact (id : App.Serve.Id) (stream : List (ExactJSON.Value × List UInt8))
    (typed : List UInt8) :
    App.Serve.Remote.Relays App.Serve.Remote.relay App.Serve.Remote.keys id stream typed :=
  App.Serve.Remote.relays id stream typed

theorem remote_attach_exact_rejects_undecoded :
    ¬∀ (id : App.Serve.Id) (stream : List (ExactJSON.Value × List UInt8)) (typed : List UInt8),
        App.Serve.Remote.Relays App.Serve.Remote.undecoded App.Serve.Remote.keys id stream typed :=
  App.Serve.Remote.relays_rejects_undecoded

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
        Remote.targetArgs ["--", name] = some (name, []) ∧
          Names.entryName (Names.entryFile name) = some name) ∧
      Name.accept "build · ✓ tests" = some "build · ✓ tests" :=
  ⟨Name.accept_eq_some_iff s name, fun usable =>
    ⟨Remote.targetArgs_separated name [], Names.entryName_entryFile name usable⟩,
    (Name.accept_eq_some_iff _ _).mpr ⟨rfl, .inl ((Name.usable_iff _).mp (by decide))⟩⟩

theorem names_round_trip_rejects_keyed :
    ¬∀ (s name : String),
        (Name.keyed s = some name ↔ name = s ∧ Name.Accepted s) ∧
          (Name.Usable name →
            Remote.targetArgs ["--", name] = some (name, []) ∧
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
