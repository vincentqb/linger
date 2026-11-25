module

public import Linger.App.CoreCode.Api
public import Linger.App.CoreCode.Entry
public import Linger.App.CoreCode.Serve
public import Linger.Display.CoreCode.Listing
public import Linger.Display.CoreCode.View
public import Linger.Import.CoreCode.Resurrect
public import Linger.Selector.CoreCode.Picker
public import ExactJSON.Solution
public import Linger.Session.CoreCode
public import Linger.Session.CoreCode.Buf
public import Linger.Session.CoreCode.Checkpoint
public import Linger.Session.CoreCode.Claim
public import Linger.Session.CoreCode.Driver
public import Linger.Session.CoreCode.Handoff
public import Linger.Session.CoreCode.Names
public import Linger.Session.CoreCode.Start
public import Linger.Session.CoreCode.Wire
public import Linger.Session.CoreSpec
public import Linger.Session.WorldSpec
public import Linger.Target.CoreCode.Name
public import Linger.Target.CoreCode.Remote
public import Os.WorldSpec
public import Terminal.CoreCode.Replay
public import Terminal.CoreSpec
import all Linger.App.Proofs.Api
import all Linger.App.Proofs.Serve
import all Linger.Display.Proofs.Listing
import all Linger.Display.Proofs.View
import all Linger.Import.Proofs.Resurrect
import all Linger.Display.CoreCode.Listing
import all Terminal.CoreCode.Render
import all Linger.Selector.Proofs.Picker
import all Linger.Session.Proofs.Buf
import all Linger.Session.Proofs.Checkpoint
import all Linger.Session.Proofs.Claim
import all Linger.Session.Proofs.Driver
import all Linger.Session.Proofs.Names
import all Linger.Session.Proofs.Session
import all Linger.Session.Proofs.Start
import all Linger.Session.Proofs.Wire
import Linger.Target.Proofs.Name
import all Terminal.CoreCode.Vt
import all Terminal.Proofs.Vt

/-! # The witnesses of the headline theorems' hypotheses

A headline whose hypotheses are about a hole has a witness in `Challenge.lean`, marked
`@[witness headline]`: the existence of inputs that meet them, up to the last that mentions a hole,
so that the headline is not true only because nothing meets its hypotheses. Each is proved here of
the implementation, by inputs the kills use too; `Theorems.Solution` gathers them for
`./lake comparator`. -/

public section

namespace Linger

open Linger.Display Linger.Session Linger.Target Terminal

theorem step_attach_repaint_applies :
    ∃ (s : Session.State) (id : Nat) (chunk : List UInt8) (c : Session.Client) (dec :
      Session.Wire.Decoder) (mode : Session.Mode) (cols : UInt32) (rows : UInt32) (_ :
      s.client? id = some c) (_ : c.attached = false),
      c.decoder.feed chunk = (dec, [Session.Wire.Msg.attach mode cols rows]) :=
  ⟨_, 1, Wire.encode (.attach .writable 80 24), { id := 1 }, {}, .writable, 80, 24,
    Session.connected_client_witness.1, rfl, Session.feed_encode_fresh _ trivial⟩

theorem step_input_exact_applies :
    ∃ (s : Session.State) (id : Nat) (chunk : List UInt8) (c : Session.Client) (dec :
      Session.Wire.Decoder) (inputs : List (List UInt8)) (_ : s.client? id = some c) (_ :
      c.mode = Session.Mode.writable),
      c.decoder.feed chunk = (dec, List.map Session.Wire.Msg.input inputs) :=
  ⟨_, 1, Wire.encode (.input [0x61]), { id := 1 }, {}, [[0x61]], Session.connected_client_witness.1,
    rfl, Session.feed_encode_fresh (.input [0x61]) (by simp [Wire.Msg.Fits, Wire.maxPayload])⟩

theorem input_exact_applies :
    ∃ (reads : Session.Pty.Mode → ByteArray → ByteArray) (_ : Session.Pty.Delivers reads) (cap :
      Nat) (accepted : ByteArray) (written : ByteArray) (b : Session.Buf.Buf),
      Session.Buf.InputLife Session.Buf.Buf.empty Session.Buf.bufOffer Session.Buf.bufAdvance
        Session.Buf.writeFrom cap accepted written b :=
  ⟨fun _ written => written, fun _ => rfl, 0, .empty, .empty, Buf.Buf.empty, .empty⟩

theorem decode_encode_chunked_applies :
    ∃ (ms : List Session.Wire.Msg) (_ : ∀ (m : Session.Wire.Msg), m ∈ ms → m.Fits) (chunks :
      List (List UInt8)), chunks.flatten = List.flatMap Session.Wire.encode ms :=
  ⟨[], by simp, [], rfl⟩

theorem step_attach_focus_applies :
    ∃ (s : Session.State) (id : Nat) (chunk : List UInt8) (c : Session.Client) (dec :
      Session.Wire.Decoder) (mode : Session.Mode) (cols : UInt32) (rows : UInt32) (_ :
      s.client? id = some c),
      c.decoder.feed chunk = (dec, [Session.Wire.Msg.attach mode cols rows]) :=
  ⟨_, 1, Wire.encode (.attach .readOnly 80 24), { id := 1 }, {}, .readOnly, 80, 24,
    Session.connected_client_witness.1, Session.feed_encode_fresh _ trivial⟩

theorem one_owner_applies :
    ∃ (grant : Session.Claim.State → Nat → Nat → Bool) (_ : Session.Claim.Exclusive grant) (s :
      Session.Claim.State), Session.Claim.Reachable grant Session.Claim.enters s :=
  ⟨fun s _ resource => s.locks resource == none, fun s _ resource granted => by simpa using granted,
    Claim.initial, .initial⟩

theorem rename_moves_applies :
    ∃ (t : Session.Names.Table) (_ : Session.Names.Wf t) (old : String) (_ : String) (id : String),
      Session.Names.resolve t old = some id := by
  have valid : Name.check "a" = some "a" :=
    (Name.check_eq_some_iff "a" "a").mpr
      ⟨rfl, by
        unfold Name.Valid; decide⟩
  exact ⟨[], by simp [Names.Wf], "a", "b", "a", by rw [Names.resolve_nil, valid]⟩

theorem claim_fresh_applies :
    ∃ (t : Session.Names.Table) (_ : Session.Names.Wf t) (name : String) (_ : String),
      Session.Names.resolve t name = none :=
  ⟨[("x", "n")], by simp [Names.Wf], "n", ".a", by simp [Names.resolve, List.lookup_cons]⟩

theorem nameOf_shown_applies :
    ∃ (t : Session.Names.Table) (id : String) (name : String),
      Session.Names.nameOf t id = some name :=
  have valid : Name.check "a" = some "a" :=
    (Name.check_eq_some_iff "a" "a").mpr
      ⟨rfl, by
        unfold Name.Valid; decide⟩
  ⟨[], "a", "a", by simp [Names.nameOf, valid]⟩

theorem one_name_applies :
    ∃ (placed : Bool → (String → Option Nat) → String → String → Option (String → Option Nat)) (_ :
      Os.Place.NoReplace placed) (first : Session.Names.Op) (_ : Session.Names.Op) (names :
      String → Option Nat) (src : String) (_ : String) (dst : String) (file : Nat) (_ :
      names src = some file) (after : String → Option Nat),
      Session.Names.Call.run placed (Session.Names.call first) names src dst = some after := by
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
  refine
    ⟨placed, noReplace, .create, .create, fun p => if p = "s" then some 0 else none, "s", "s", "d",
      0, by simp, ?_⟩
  simp [Names.Call.run, Names.call, placed]

theorem run_readonly_applies :
    ∃ (s : Session.State) (id : Nat) (_ : List (List UInt8)) (c : Session.Client),
      s.client? id = some c := ⟨_, 1, [], { id := 1 }, Session.connected_client_witness.1⟩

theorem step_attach_mode_applies :
    ∃ (s : Session.State) (id : Nat) (chunk : List UInt8) (c : Session.Client) (dec :
      Session.Wire.Decoder) (mode : Session.Mode) (cols : UInt32) (rows : UInt32) (_ :
      s.client? id = some c) (_ : c.attached = false),
      c.decoder.feed chunk = (dec, [Session.Wire.Msg.attach mode cols rows]) :=
  ⟨_, 1, Wire.encode (.attach .writable 0 0), { id := 1 }, {}, .writable, 0, 0,
    Session.connected_client_witness.1, rfl, Session.feed_encode_fresh _ trivial⟩

theorem step_resize_mode_applies :
    ∃ (s : Session.State) (id : Nat) (chunk : List UInt8) (c : Session.Client) (dec :
      Session.Wire.Decoder) (sizes : List (UInt32 × UInt32)) (_ : s.client? id = some c),
      c.decoder.feed chunk =
        (dec,
          List.map (fun (size : UInt32 × UInt32) => Session.Wire.Msg.resize size.fst size.snd)
            sizes) :=
  ⟨_, 1, Wire.encode (.resize 0 0), { id := 1 }, {}, [(0, 0)], Session.connected_client_witness.1,
    Session.feed_encode_fresh (.resize 0 0) trivial⟩

theorem step_resizes_sized_applies :
    ∃ (s : Session.State) (ev : Session.Event) (cols : UInt32) (rows : UInt32),
      Session.Effect.resizePty cols rows ∈ (Session.step s ev).snd := by
  -- a client that attaches at 80×24 to a session at 1×1 resizes its pty
  have resizes :
    ((Session.step (Session.trace Session.step (State.boot (Vt.Vt.init 1 1) [] []) [.connected 1]).1
            (.bytes 1 (Wire.encode (.attach .writable 80 24)))).2.any
        fun eff =>
        match eff with
        | .resizePty _ _ => true
        | _ => false) =
      true := by
    decide +kernel
  obtain ⟨eff, member, found⟩ := List.any_eq_true.mp resizes
  cases eff <;>
    first
    | exact ⟨_, _, _, _, member⟩
    | exact absurd found (by simp)

theorem rowText_clean_applies :
    ∃ (width : Option Nat) (layout : Display.Listing.Layout) (info : List (String × String)) (c :
      Char), c ∈ Display.Listing.rowText width layout info := ⟨none, {}, [], '?', by decide⟩

theorem picker_attach_listed_applies :
    ∃ (s : Selector.Picker.State) (key : Selector.Key) (target : String),
      Selector.Picker.step s key = Selector.Picker.Outcome.attach target :=
  ⟨{ candidates := ["s"] }, .accept, "s", rfl⟩

theorem picker_create_new_applies :
    ∃ (s : Selector.Picker.State) (key : Selector.Key) (target : String),
      Selector.Picker.step s key = Selector.Picker.Outcome.create target :=
  ⟨Selector.Picker.init [], .accept, _, Selector.Picker.step_init_empty⟩

theorem picker_moves_cycle_applies :
    ∃ (s : Selector.Picker.State) (n : Nat) (_ : Nat),
      ∀ (i : Nat),
        (∃ (next : Selector.Picker.State),
            Selector.Picker.step
                { candidates := s.candidates, query := s.query, cursor := i,
                  allowCreate := s.allowCreate, descriptions := s.descriptions }
                Selector.Key.accept =
              Selector.Picker.Outcome.stay next) ↔
          n ≤ i :=
  ⟨{ candidates := [], allowCreate := false }, 0, 0, fun _ =>
    ⟨fun _ => Nat.zero_le _, fun _ => ⟨_, rfl⟩⟩⟩

theorem op_meaning_applies :
    ∃ (args : List String) (argv : List String) (request : App.Api.Request) (_ : App.Api.Found) (_ :
      App.Entry.route args = App.Entry.Route.session argv), App.Api.parse argv = some request :=
  ⟨["detach", "x"], ["detach", "x"], .detach "x", .done, App.Api.route_detach, App.Api.parse_detach⟩

theorem serve_refuses_uncanonical_applies :
    ∃ (_ : App.Serve.State) (line : String) (reason : String),
      ExactJSON.Value.parse line = Except.error reason := by
  -- the text of an invalid value, a NaN, is no canonical text
  have invalid : ¬(ExactJSON.Value.float Float.nan).Valid := by
    show ¬(ExactJSON.finiteFloat Float.nan = true)
    rw [show ExactJSON.finiteFloat Float.nan = false by decide +kernel]
    decide
  have unread := ExactJSON.parse_render_invalid _ invalid
  cases parsed : ExactJSON.Value.parse (ExactJSON.Value.float Float.nan).render with
  | error e => exact ⟨App.Serve.State.init, _, e, parsed⟩
  | ok v =>
    rw [parsed] at unread
    cases unread

theorem serve_refuses_params_applies :
    ∃ (s : App.Serve.State) (version : String) (_ : App.Serve.Id) (_ : String) (_ :
      ExactJSON.Value), s.phase = App.Serve.Phase.ready version :=
  ⟨{ stage := .ready "1" }, "1", .number 1, "session/kill", .null, rfl⟩

theorem records_clean_applies :
    ∃ (rows : List (List (String × String))) (record : App.Serve.Record) (_ : String) (_ :
      Display.Listing.Field), record ∈ App.Serve.records rows := by
  exact ⟨[[("name", "a")]], _, "name", .text "a", List.mem_singleton_self _⟩

theorem chooser_same_list_applies :
    ∃ (rows : List (List (String × String))) (_ :
      ∀ (record : App.Serve.Record),
        record ∈ App.Serve.records rows →
          Target.Remote.targetValid (App.Serve.Record.key record) = true),
      (List.map App.Serve.Record.key (App.Serve.records rows)).Nodup :=
  ⟨[], by simp [App.Serve.records, Linger.Display.Listing.records], by
    simp [App.Serve.records, Linger.Display.Listing.records]⟩

theorem history_log_exact_applies :
    ∃ (s : App.Serve.State) (version : String) (_ : App.Serve.Id) (_ : App.Serve.Log App.Serve.Line)
      (_ : App.Serve.Log App.Serve.Line) (_ : App.Serve.Screen),
      s.phase = App.Serve.Phase.ready version :=
  ⟨({ stage := .ready "1" } : App.Serve.StateRec), "1", .number 1, {}, {},
    { lines := [], cursor := ⟨0, 0, true⟩, title := "" }, rfl⟩

theorem serve_attach_exact_applies :
    ∃ (s : App.Serve.State) (version : String) (_ : App.Serve.Id) (_ : Session.Wire.Decoder) (_ :
      List UInt8) (_ : List UInt8) (_ : List UInt8) (_ : App.Api.Found) (_ : App.Serve.Log String),
      s.phase = App.Serve.Phase.ready version :=
  ⟨({ stage := .ready "1" } : App.Serve.StateRec), "1", .number 1, {}, [], [], [], .done, {}, rfl⟩

theorem dismiss_hides_applies :
    ∃ (records : Session.Records) (later : Session.Records) (pane : Import.Resurrect.Pane) (_ :
      List Import.Resurrect.Pane),
      ∀ (name : String),
        name ∈ (Import.Resurrect.dismiss records pane.name).endings → name ∈ later.endings :=
  ⟨⟨[], [], [], [], [], []⟩, Import.Resurrect.dismiss ⟨[], [], [], [], [], []⟩ "a",
    { name := "a", dir := "", line := 0 }, [], fun _ member => member⟩

theorem input_unrecorded_applies :
    ∃ (_ : Vt.Vt) (_ : List (String × String)) (_ : List (String × String)) (evs :
      List Session.Event) (evs' : List Session.Event) (_ :
      ∀ (ev : Session.Event), ev ∈ evs → Session.Framed Session.Wire.encode ev),
      Session.Typed Session.Wire.encode evs evs' := ⟨Vt.Vt.init 1 1, [], [], [], [], by simp, .nil⟩

theorem start_runs_applies :
    ∃ (inherited : String → Option String) (start :
      String →
        String →
        Array String →
        List (String × Option String) → Session.Spawn.Reset → Option Session.Spawn.Started)
      (_ : Session.Spawn.Runs inherited start) (names : List String) (_ :
      ∀ (key : String), (inherited key).isSome = true → key ∈ names) (id : String) (notify : String)
      (dir : String) (shell : String) (argv : List String) (started : Session.Spawn.Started),
      start dir (Session.Start.programOf shell argv).fst (Session.Start.programOf shell argv).snd
          (Session.Start.environment id notify names) Session.Start.reset =
        some started := by
  -- a caller that sets nothing, and a start that runs exactly what it is asked
  let inherited := fun _ : String => (none : Option String)
  have runs :
    Spawn.Runs inherited fun dir prog args extra _ =>
      some
        { argv := prog :: args.toList, dir,
          env := fun key => (extra.reverse.lookup key).getD (inherited key),
          ignored := fun _ => false, blocked := fun _ => false, descriptor := fun _ => none } := by
    intro dir prog args extra reset started hs
    cases hs
    exact ⟨rfl, rfl, fun _ => rfl⟩
  exact
    ⟨inherited, _, runs, [], fun _ none => by simp [inherited] at none, "x", "n", "", "sh", [], _,
      rfl⟩

theorem start_clean_applies :
    ∃ (start :
      String →
        String →
        Array String →
        List (String × Option String) → Session.Spawn.Reset → Option Session.Spawn.Started)
      (_ : Session.Spawn.Clean start) (name : String) (notify : String) (dir : String) (shell :
      String) (names : List String) (argv : List String) (started : Session.Spawn.Started),
      start dir (Session.Start.programOf shell argv).fst (Session.Start.programOf shell argv).snd
          (Session.Start.environment name notify names) Session.Start.reset =
        some started := by
  -- a start that resets everything its start asks to
  have clean :
    Spawn.Clean fun _ _ _ _ _ =>
      some
        { argv := [], dir := "", env := fun _ => none, ignored := fun _ => false,
          blocked := fun _ => false,
          descriptor := fun fd => if fd < 3 then some .terminal else none } := by
    intro dir prog args extra reset started hs
    cases hs
    refine ⟨fun fd low => ite_eq_left low, fun _ _ => rfl, fun _ _ => rfl, ?_⟩
    exact fun _ fd high => ite_eq_right (Nat.not_lt_of_le high)
  exact ⟨_, clean, "x", "n", "", "sh", [], [], _, rfl⟩

theorem step_kill_stops_applies :
    ∃ (s : Session.State) (id : Nat) (chunk : List UInt8) (c : Session.Client) (dec :
      Session.Wire.Decoder) (rest : List Session.Wire.Msg) (_ : s.client? id = some c) (_ :
      c.mode = Session.Mode.writable),
      c.decoder.feed chunk = (dec, Session.Wire.Msg.kill :: rest) :=
  ⟨_, 1, Wire.encode .kill, { id := 1 }, {}, [], Session.connected_client_witness.1, rfl,
    Session.feed_encode_fresh .kill (by simp [Wire.Msg.Fits])⟩

theorem step_unknown_refused_applies :
    ∃ (s : Session.State) (id : Nat) (chunk : List UInt8) (c : Session.Client) (dec :
      Session.Wire.Decoder) (tag : UInt8) (payload : List UInt8) (_ : s.client? id = some c),
      c.decoder.feed chunk = (dec, [Session.Wire.Msg.unknown tag payload]) :=
  ⟨_, 1, Wire.encode (.unknown 200 []), { id := 1 }, {}, 200, [],
    Session.connected_client_witness.1,
    Session.feed_encode_fresh (.unknown 200 []) ⟨by simp, by decide⟩⟩

theorem run_refines_applies :
    ∃ (World : Type) (execute :
      Session.State →
        World → (eff : Session.Effect Replay.Plan) → Id (World × Session.Driver.Reply eff))
      (ending : Session.Outcome) (_ :
      ∀ (st : Session.State) (world : World) (eff : Session.Effect Replay.Plan),
        (execute st world eff).snd = Session.Driver.success ending eff)
      (r : Session.Driver.Result Session.State World) (_ : List Session.Event), r.exiting = false :=
  ⟨Unit, fun _ world eff => (world, Driver.success .unknown eff), .unknown, fun _ _ _ => rfl,
    { st := State.boot (Vt.Vt.init 1 1) [] [], world := () }, [], rfl⟩

theorem run_total_safe_applies :
    ∃ (World : Type) (ε : Type) (execute :
      Session.State →
        World → (eff : Session.Effect Replay.Plan) → Except ε (World × Session.Driver.Reply eff))
      (_ : Session.Driver.Responds execute) (r : Session.Driver.Result Session.State World) (_ :
      List Session.Event) (_ :
      Session.Bounds Session.State.roster Session.State.fieldList Session.State.scanner r.st),
      Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
        (Session.Checkpoint.Decoded Session.Checkpoint.loadBytes) r.st.terminal := by
  obtain ⟨-, -, wide, roster, fields, scanner⟩ := Session.boot_observed (Vt.Vt.init 80 24) [] []
  let execute : State → Unit → (eff : Effect Replay.Plan) → Except Unit (Unit × Driver.Reply eff) :=
    fun _ world eff => .ok (world, Driver.success .unknown eff)
  exact
    ⟨Unit, Unit, execute, fun _ _ _ => ⟨_, rfl⟩,
      { st := State.boot (Vt.Vt.init 80 24) [] [], world := () }, [],
      ⟨by
        rw [roster]; decide, by
        show (State.boot (Vt.Vt.init 80 24) [] []).fieldList.length ≤ maxFields
        rw [fields]; decide, fun c member =>
        absurd member
          (by
            rw [roster]; exact List.not_mem_nil),
        by
        rw [scanner]; trivial⟩,
      by
      rw [wide]; exact .init 80 24⟩

theorem run_feedback_alive_applies :
    ∃ (World : Type) (_ :
      Session.State →
        World → (eff : Session.Effect Replay.Plan) → Id (World × Session.Driver.Reply eff))
      (r : Session.Driver.Result Session.State World) (_ : List Session.Event), r.exiting = false :=
  ⟨Unit, fun _ world eff => (world, Driver.success .unknown eff),
    { st := State.boot (Vt.Vt.init 1 1) [] [], world := () }, [], rfl⟩

theorem run_stop_exits_applies :
    ∃ (World : Type) (_ :
      Session.State →
        World → (eff : Session.Effect Replay.Plan) → Id (World × Session.Driver.Reply eff))
      (r : Session.Driver.Result Session.State World) (ev : Session.Event) (_ : r.exiting = false),
      Session.Effect.stopProgram ∈ (Session.step r.st ev).snd := by
  obtain ⟨joined, -⟩ := Session.connected_client_witness
  have stops :=
    (Session.step_kill_stops _ 1 (Wire.encode .kill) joined rfl
        (Session.feed_encode_fresh .kill (by simp [Wire.Msg.Fits])) rfl).1
  exact
    ⟨Unit, fun _ world eff => (world, Driver.success .unknown eff),
      { st := (Session.trace Session.step (State.boot (Vt.Vt.init 1 1) [] []) [.connected 1]).1,
        world := () },
      .bytes 1 (Wire.encode .kill), rfl, by
      rw [stops]; simp⟩

theorem reachableIn_bound_applies :
    ∃ (cap : Nat) (b : Session.Buf.Buf),
      Session.Buf.InputReach Session.Buf.Buf.empty Session.Buf.bufOffer Session.Buf.bufAdvance cap
        b := ⟨0, Buf.Buf.empty, .empty⟩

theorem handoff_carries_applies :
    ∃ (s : Session.State) (_ : Session.Handoff.World) (_ :
      Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
        (Session.Checkpoint.Decoded Session.Checkpoint.loadBytes) s.terminal),
      s.terminal.quiesce = s.terminal :=
  ⟨State.boot (Vt.Vt.init 1 1) [] [],
    { listenFd := 0, ptyFd := 0, childPid := 0, signals := (0, 0), locks := [], conns := [],
      ptyIn := [], login := false, asker := 0 },
    .init 1 1, Vt.quiesce_of_quiet rfl⟩

theorem loadBytes_saveBytes_live_applies :
    ∃ (c : Session.Checkpoint.Ckpt Vt.Vt),
      Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
        (Session.Checkpoint.Decoded Session.Checkpoint.loadBytes)
        c.vt := ⟨⟨Vt.Vt.init 1 1, "", []⟩, .init 1 1⟩

theorem resume_restores_applies :
    ∃ (c : Session.Checkpoint.Ckpt Vt.Vt),
      Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
        (Session.Checkpoint.Decoded Session.Checkpoint.loadBytes)
        c.vt := ⟨⟨Vt.Vt.init 1 1, "", []⟩, .init 1 1⟩

theorem loadBytes_resave_applies :
    ∃ (b : ByteArray) (c : Session.Checkpoint.Ckpt Vt.Vt),
      Session.Checkpoint.loadBytes b = some c :=
  ⟨_, _,
    Checkpoint.loadBytes_saveBytes_live ⟨Vt.Vt.init 1 1, "", []⟩
      (Checkpoint.live_of_decoded (.init 1 1))⟩

theorem older_record_described_applies :
    ∃ (c : Session.Checkpoint.Ckpt Vt.Vt) (_ :
      Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
        (Session.Checkpoint.Decoded Session.Checkpoint.loadBytes) c.vt)
      (_ : List.lookup "description" c.fields = none) (old : ByteArray),
      old.data.toList =
        [76, 78, 71, 82, 3] ++ List.drop 5 (Session.Checkpoint.saveBytes c).data.toList :=
  ⟨⟨Vt.Vt.init 1 1, "", []⟩, .init 1 1, rfl,
    ⟨([0x4C, 0x4E, 0x47, 0x52, 3] ++
          (Checkpoint.saveBytes ⟨Vt.Vt.init 1 1, "", []⟩).data.toList.drop 5).toArray⟩,
    by simp⟩

theorem changed_exactly_applies :
    ∃ (s : App.Serve.State) (version : String) (id : App.Serve.Id) (told : List App.Serve.Record)
      (latest : List App.Serve.Record) (_ : s.phase = App.Serve.Phase.ready version) (_ :
      s.subscription = some id) (_ : s.told = some told), s.latest = some latest :=
  ⟨{ stage := .ready "1", open? := some (.number 1), toldRecords := some [],
     latestRecords := some [] },
    "1", .number 1, [], [], rfl, rfl, rfl, rfl⟩

theorem screen_table_exact_applies :
    ∃ (s : App.Serve.State) (version : String) (_ : App.Serve.Id) (_ : App.Serve.Screen) (_ :
      App.Serve.Screen) (_ : App.Serve.Screen) (_ : App.Serve.Log App.Serve.Line),
      s.phase = App.Serve.Phase.ready version :=
  ⟨({ stage := .ready "1" } : App.Serve.StateRec), "1", .number 1,
    { lines := [], cursor := ⟨0, 0, true⟩, title := "" },
    { lines := [], cursor := ⟨0, 0, true⟩, title := "" },
    { lines := [], cursor := ⟨0, 0, true⟩, title := "" }, {}, rfl⟩

theorem ticks_settle_applies :
    ∃ (s : Session.State) (now : Nat) (t₁ : Nat),
      (Session.trace Session.step s [Session.Event.tick now]).fst.nextTick = some t₁ :=
  -- a session that printed has unsaved changes, which a tick before their deadline leaves
  ⟨(Session.step (State.boot (Vt.Vt.init 1 1) [] []) (.ptyOut [0x41])).1, 0, 60000, by
    decide +kernel⟩

theorem poll_wakes_applies :
    ∃ (quiet : Int32 → Nat → Prop) (_ : Session.Poll.Sleeps quiet) (now : Nat) (deadlines :
      List Nat) (_ : ∀ (d : Nat), d ∈ deadlines → d - now ≤ 2147483647) (ms : Nat),
      quiet (Session.pollTimeout now deadlines) ms :=
  ⟨fun (t : Int32) (ms : Nat) => 0 ≤ t.toInt ∧ t.toInt ≤ ms, fun _ _ waited => waited, 0, [5], by
    simp, 5, ⟨by decide, by decide⟩⟩

theorem start_answer_true_applies :
    ∃ (r : Session.Start.Request),
      Session.Start.Reachable Session.Start.proceeds Session.Start.answer r := ⟨_, .init⟩

theorem sort_live_above_done_applies :
    ∃ (α : Type) (status : α → Display.Status.Status) (rows : List α) (first : List α) (rest :
      List α), Display.View.sort status rows = first ++ rest :=
  ⟨Bool, fun _ => ⟨.none, .working⟩, [], [], [], by simp [Display.View.sort]⟩

end Linger
