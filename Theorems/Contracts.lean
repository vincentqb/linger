module

import all Theorems.Buf
import all Theorems.Checkpoint
import all Theorems.Claim
import all Theorems.Driver
import all Theorems.Entry
import all Theorems.Fuzzy
import all Theorems.Input
import all Theorems.Name
import all Theorems.Picker
import all Theorems.Remote
import all Theorems.Render.Grid
import all Theorems.Render.Modes
import all Theorems.Render.PendingWrap
import all Theorems.Render.Scrollback
import all Theorems.Render.Sticky
import all Theorems.Render.Tabs
import all Theorems.Replay
import all Theorems.Resurrect
import all Theorems.Session
import all Theorems.Status
import all Theorems.Title
import all Theorems.Vt.Renderable
import all Theorems.Vt.State
import all Theorems.Wire

/-! # Contract statements

`THEOREMS.md` cites the theorems below. Each `example` restates one and closes it with
that theorem at reducible transparency, so weakening a cited hypothesis or conclusion
fails here instead of passing the citation gate. -/

open Linger.Core Linger.Tools

-- Checkpoints
example (c : Checkpoint.Ckpt) (h : Vt.LiveReachableVt c.vt) :
    Checkpoint.load (Checkpoint.save c) =
      some { vt := c.vt.quiesce, cwd := c.cwd, labels := c.labels } := by
  with_reducible exact Checkpoint.load_save_live c h

example {l : List UInt8} {c : Checkpoint.Ckpt} (h : Checkpoint.load l = some c) :
    Checkpoint.load (Checkpoint.save c) = some c := by with_reducible exact Checkpoint.load_resave h

-- Session events
example (s : Session.State) (evs : List Session.Event) (h : Session.WF s) :
    Session.WF (Session.run s evs).fst := by with_reducible exact Session.run_wf s evs h

example (s : Session.State) (id : Nat) (chunks : List (List UInt8)) {other : Nat} (h : other ≠ id) :
    (Session.run s (List.map (Session.Event.bytes id) chunks)).fst.client? other =
      s.client? other := by
  with_reducible exact Session.run_bytes_isolates s id chunks h

-- Event driver
example {World ε : Type}
    (execute : Session.State → World → (eff : Session.Effect) → Except ε (World × Driver.Reply eff))
    (hw : Driver.Responds execute) (r : Driver.Result World) (events : List Session.Event)
    (hwf : Session.WF r.st) (hlive : Session.LiveVt r.st) :
    ∃ out,
      Driver.run execute r events = Except.ok out ∧ Session.WF out.st ∧ Session.LiveVt out.st := by
  with_reducible exact Driver.run_total_safe execute hw r events hwf hlive

-- Failure feedback
example {World : Type} (execute : Driver.Interpreter World) (st : Session.State) (world : World)
    (depth : Nat) (effs : List Session.Effect)
    (h : ∀ (eff : Session.Effect), eff ∈ effs → Driver.effectDepth eff ≤ depth) :
    let answered := Driver.effects (m := Id) execute st world depth effs h
    (answered.fst, List.map Subtype.val answered.snd) =
      List.foldl
        (fun (acc : World × List Session.Event) eff =>
          let answer := execute st acc.fst eff
          (answer.fst, acc.snd ++ Driver.feedback eff answer.snd))
        (world, []) effs := by
  with_reducible exact Driver.effects_in_order execute st world depth effs h

example {World : Type} (execute : Driver.Interpreter World) (r : Driver.Result World)
    (events : List Session.Event) :
    Driver.Execution execute r events (Driver.run (m := Id) execute r events) := by
  with_reducible exact Driver.run_execution execute r events

example (eff : Session.Effect) (reply : Driver.Reply eff) (ev : Session.Event)
    (h : ev ∈ Driver.feedback eff reply) : Driver.eventDepth ev < Driver.effectDepth eff := by
  with_reducible exact Driver.feedback_strictly_decreases eff reply ev h

example {World : Type} (execute : Driver.Interpreter World) (r : Driver.Result World)
    (ev : Session.Event) (hactive : r.exiting = false) (hdepth : Driver.eventDepth ev < 2) :
    (Driver.handle (m := Id) execute r ev).exiting = false := by
  with_reducible exact Driver.handle_feedback_keeps_alive execute r ev hactive hdepth

example {World : Type} {m : Type → Type} [Monad m]
    (execute : Session.State → World → (eff : Session.Effect) → m (World × Driver.Reply eff))
    (r : Driver.Result World) (events : List Session.Event) (h : r.exiting = true) :
    Driver.run execute r events = pure r := by
  with_reducible exact Driver.run_exited execute r events h

-- Terminal input
example {v : Vt.Vt} (bytes : List UInt8) (h : Vt.Good v) : Vt.Good (v.feed bytes) := by
  with_reducible exact Vt.Good.feed bytes h

example {v : Vt.Vt} (h : Vt.Renderable v) (bytes : List UInt8) : Vt.Renderable (v.feed bytes) := by
  with_reducible exact Vt.renderable_feed h bytes

-- Transport
example (ms : List Wire.Msg) (hms : ∀ (m : Wire.Msg), m ∈ ms → m.WF) (chunks : List (List UInt8))
    (hc : chunks.flatten = List.flatMap Wire.encode ms) :
    Wire.Decoder.feedAll {} chunks = ({ buf := [], errored := false }, ms) := by
  with_reducible exact Wire.decode_encode_chunked ms hms chunks hc

-- Ownership
example {s : Claim.State} (reached : Claim.Reachable s) : Claim.Protected s := by
  with_reducible exact Claim.reachable_protected reached

example {s : Claim.State} (reached : Claim.Reachable s) {a b resource : Nat}
    {left right : Claim.Lease} (ha : s.active a = some left) (hb : s.active b = some right)
    (leftUses : left.Uses resource) (rightUses : right.Uses resource) : a = b := by
  with_reducible exact Claim.at_most_one_owner reached ha hb leftUses rightUses

example {s : Claim.State} (reached : Claim.Reachable s) (actor : Nat) (lease : Claim.Lease)
    (idle : s.active actor = none) (socket : s.locks lease.socket = none)
    (checkpoint : s.locks lease.checkpoint = none) (distinct : lease.checkpoint ≠ lease.socket) :
    ∃ after, Claim.Reachable after ∧ after.active actor = some lease := by
  with_reducible exact Claim.claim_free reached actor lease idle socket checkpoint distinct

-- Buffers
example {cap : Nat} {b : Buf.Buf} (h : Buf.ReachableIn cap b) : Buf.owedLen b ≤ cap := by
  with_reducible exact Buf.reachableIn_bound h

example {cap : Nat} {b : Buf.Buf} (h : Buf.ReachableOut cap b) : Buf.owedLen b ≤ cap := by
  with_reducible exact Buf.reachableOut_bound h

-- Screen restoration
example (v w : Vt.Vt) (hgood : Vt.Good w) (hren : Vt.Renderable w) (hcols : w.cols = v.cols)
    (hrows : w.rows = v.rows) (hua : w.u8acc = 0) (hun : w.u8need = 0) (hvren : Vt.Renderable v) :
    (w.feed (Render.restore v)).grid = v.grid := by
  with_reducible exact Render.restore_grid_any v w hgood hren hcols hrows hua hun hvren

example (v w : Vt.Vt) (hgood : Vt.Good w) (hcols : w.cols = v.cols)
    (hvtabs : v.tabs.size = v.cols) : (w.feed (Render.restore v)).tabs = v.tabs := by
  with_reducible exact Render.restore_tabs_any v w hgood hcols hvtabs

example (v w : Vt.Vt) (hgood : Vt.Good w) (hren : Vt.Renderable w) (hgv : Vt.Good v)
    (hvren : Vt.Renderable v) (hcols : w.cols = v.cols) (hrows : w.rows = v.rows)
    (hua : w.u8acc = 0) (hun : w.u8need = 0) (hne : (Render.sbRows v).isEmpty = false) :
    (w.feed (Render.restore v)).sb.toList = (Render.sbRows v).toList := by
  with_reducible exact Render.restore_sb_any v w hgood hren hgv hvren hcols hrows hua hun hne

example (v w : Vt.Vt) (hgood : Vt.Good v) (hgw : Vt.Good w) (hcols : w.cols = v.cols)
    (hrows : w.rows = v.rows) (ho : v.modes.origin = false) :
    (w.feed (Render.restore v)).cursor.x = v.cursor.x ∧
      (w.feed (Render.restore v)).cursor.y = v.cursor.y := by
  with_reducible exact Render.restore_cursor_any v w hgood hgw hcols hrows ho

example (v w : Vt.Vt)
    (hmouse :
      v.modes.mouse = 0 ∨ v.modes.mouse = 1000 ∨ v.modes.mouse = 1002 ∨ v.modes.mouse = 1003) :
    (w.feed (Render.restore v)).modes = v.modes := by
  with_reducible exact Render.restore_modes_any v w hmouse

example (v w : Vt.Vt) : (w.feed (Render.restore v)).pen = v.pen := by
  with_reducible exact Render.restore_pen_any v w

example (v w : Vt.Vt) (hrows : w.rows = v.rows) (hlt : v.top < v.bot) (hbot : v.bot < v.rows)
    (hfits : v.rows < 65535) : Vt.stick (w.feed (Render.restore v)) = Vt.stick v := by
  with_reducible exact Render.restore_sticky_any v w hrows hlt hbot hfits

example (v w : Vt.Vt) :
    (w.feed (Render.restore v)).pstate = Vt.PState.ground ∧
      (w.feed (Render.restore v)).u8need = 0 := by
  with_reducible exact Render.restore_quiesced_any v w

-- Incremental replay
example (v : Vt.Vt) : Replay.remaining (Replay.start v) = Render.restore v := by
  with_reducible exact Replay.start_faithful v

example {budget : Nat} {p q : Replay.Plan} {bytes : Render.Bytes}
    (h : Replay.next budget p = some (bytes, q)) :
    Replay.remaining p = bytes ++ Replay.remaining q := by
  with_reducible exact Replay.next_faithful h

example {budget : Nat} {p q : Replay.Plan} {bytes : Render.Bytes}
    (h : Replay.next budget p = some (bytes, q)) : List.length bytes ≤ budget := by
  with_reducible exact Replay.next_bounded h

example {budget : Nat} {p q : Replay.Plan} {bytes : Render.Bytes} (positive : 0 < budget)
    (h : Replay.next budget p = some (bytes, q)) : Replay.work q < Replay.work p := by
  with_reducible exact Replay.next_progress positive h

example (budget : Nat) (positive : 0 < budget) (v : Vt.Vt) :
    Replay.drain budget positive (Replay.start v) = Render.restore v := by
  with_reducible exact Replay.drain_start budget positive v

-- Terminal handback
example (w : Vt.Vt) (h2 : 2 ≤ w.rows) :
    (w.feed Render.leaveAnsi).pstate = Vt.PState.ground ∧
      (w.feed Render.leaveAnsi).modes = {} ∧
      Vt.stick (w.feed Render.leaveAnsi) =
        { rows := w.rows, top := 0, bot := w.rows - 1, g0 := false, g1 := false, so := false,
          alt := false } ∧
      (w.feed Render.leaveAnsi).pen = {} ∧ (w.feed Render.leaveAnsi).title = "" := by
  with_reducible exact Render.leave_canonical_all w h2

-- Status and titles
example (o : Status.Obs) (s : Status.Status) : Status.classify o = s ↔ Status.Is s o := by
  with_reducible exact Status.classify_iff o s

example (statuses : List Status.Status) :
    Status.summary statuses =
      " ".intercalate
        (((if List.count Status.Status.wantsYou statuses = 0 then []
            else
              [(toString (List.count Status.Status.wantsYou statuses)).push
                  (Status.icon Status.Status.wantsYou)]) ++
            if List.count Status.Status.exitedBad statuses = 0 then []
            else
              [(toString (List.count Status.Status.exitedBad statuses)).push
                  (Status.icon Status.Status.exitedBad)]) ++
          if List.count Status.Status.unknown statuses = 0 then []
          else
            [(toString (List.count Status.Status.unknown statuses)).push
                (Status.icon Status.Status.unknown)]) := by
  with_reducible exact Status.summary_exact statuses

example (session application summary : String) (capacity : Nat) :
    let suffix := if summary.isEmpty = true then "" else " · " ++ summary
    Title.compose session application summary capacity =
      Title.compose session application "" (capacity - suffix.length) ++ suffix := by
  with_reducible exact Title.compose_attention_last session application summary capacity

-- Entry point
example : Entry.route [] = Entry.Route.session ["help"] := by
  with_reducible exact Entry.route_bare_help

example (args : List String) (readOnly : Bool) :
    Entry.route args = Entry.Route.selector readOnly ↔
      (args = "attach" :: if readOnly = true then ["--read-only"] else []) ∨
        args = "a" :: if readOnly = true then ["--read-only"] else [] := by
  with_reducible exact Entry.route_selector_iff args readOnly

example (command : String) (rest : List String) (hTmux : command ≠ "tmux")
    (hAttach : command ≠ "attach" ∨ rest ≠ [] ∧ rest ≠ ["--read-only"])
    (hAlias : command ≠ "a" ∨ rest ≠ [] ∧ rest ≠ ["--read-only"]) :
    Entry.route (command :: rest) = Entry.Route.session (command :: rest) := by
  with_reducible exact Entry.route_session_argv command rest hTmux hAttach hAlias

-- Session targets
example (s result : String) : Name.check s = some result ↔ result = s ∧ Name.Valid s := by
  with_reducible exact Name.check_eq_some_iff s result

example {a b name : String} (ha : Name.check a = some name) (hb : Name.check b = some name) :
    a = b := by with_reducible exact Name.check_no_alias ha hb

example (target : String) (result : Remote.Target) :
    Remote.parseTarget target = some result ↔
      Remote.targetValid target = true ∧
        result.name = (target.splitOn "@").headD "" ∧
        result.host =
          if (target.splitOn "@").tail.isEmpty = true then none
          else some ("@".intercalate (target.splitOn "@").tail) := by
  with_reducible exact Remote.parseTarget_exact target result

example {target : String} {result : Remote.Target} (h : Remote.parseTarget target = some result) :
    Name.Valid result.name := by with_reducible exact Remote.parseTarget_name_valid h

-- Remote commands
example (verb name : String) (args options : List String) :
    Remote.Shell.Words (Remote.command verb name args options).toList
      (List.map String.toList ("linger" :: verb :: (options ++ name :: args))) := by
  with_reducible exact Remote.command_argv verb name args options

example (s : String) (tail : List Char) (boundary : tail = [] ∨ ∃ rest, tail = ' ' :: rest) :
    Remote.Shell.word ((Remote.shellQuote s).toList ++ tail) = some (s.toList, tail) := by
  with_reducible exact Remote.shellQuote_roundtrip s tail boundary

-- Remote hosts
example (hosts result : List String) :
    Remote.checkHosts hosts = Except.ok result ↔
      result = hosts ∧ hosts.Nodup ∧ ∀ (x : String), x ∈ hosts → Remote.hostClean x = true := by
  with_reducible exact Remote.checkHosts_ok_iff hosts result

-- Selection
example (s : Picker.State) (key : Key) (target : String)
    (h : Picker.step s key = Picker.Outcome.attach target) :
    target ∈ s.candidates ∧ Picker.matches s.query target = true := by
  with_reducible exact Picker.step_attach_mem s key target h

example (s : Picker.State) (key : Key) (target : String)
    (h : Picker.step s key = Picker.Outcome.create target) :
    (target = if s.query.isEmpty = true then Name.defaultName else s.query) ∧
      ¬target ∈ s.candidates ∧
      target ≠ "" ∧
      Name.sanitize ((target.splitOn "@").headD "") = (target.splitOn "@").headD "" ∧
      Name.Valid ((target.splitOn "@").headD "") ∧
      (∀ (char : Char),
        char ∈ target.toList → 32 ≤ char.toNat ∧ (char.toNat < 127 ∨ 160 ≤ char.toNat)) ∧
      ((target.splitOn "@").tail = [] ∨ "@".intercalate (target.splitOn "@").tail ≠ "") := by
  with_reducible exact Picker.step_create_valid s key target h

example (s : Picker.State) (candidates : List String) (item : Picker.Item)
    (hselected : Picker.selected s = some item)
    (hpresent :
      ∃ next, next ∈ Picker.items candidates s.query s.allowCreate ∧ next.target = item.target) :
    Option.map Picker.Item.target (Picker.selected (Picker.refresh s candidates)) =
      some item.target := by
  with_reducible exact Picker.refresh_selected s candidates item hselected hpresent

-- Interactive fuzzy matching
example (config : Fuzzy.Config) (query target : String) (a b : Fuzzy.Alignment)
    (h : Fuzzy.alignWith config query target = some a)
    (hb :
      Fuzzy.Walk config.scoring (List.map (config.caseMode.fold query) query.toList)
        (Fuzzy.weighted config.scoring.word (config.caseMode.fold query) ' ' target.toList) false
        b) :
    b.score ≤ a.score := by
  with_reducible exact Fuzzy.alignWith_score_max config query target a b h hb

example (config : Fuzzy.Config) (query target : String) (a b : Fuzzy.Alignment)
    (h : Fuzzy.alignWith config query target = some a)
    (hb :
      Fuzzy.Walk config.scoring (List.map (config.caseMode.fold query) query.toList)
        (Fuzzy.weighted config.scoring.word (config.caseMode.fold query) ' ' target.toList) false b)
    (tie : b.score = a.score) :
    a.marks = b.marks ∨ List.Lex (fun x y => x = true ∧ y = false) a.marks b.marks := by
  with_reducible exact Fuzzy.alignWith_earliest config query target a b h hb tie

-- Input
example (state : Input.State) (byte : UInt8) (key : Input.Key) (hpaste : state.paste = true)
    (h : key ∈ (Input.feed state byte).snd) : ∃ char, key = Input.Key.text char := by
  with_reducible exact Input.feed_paste_only_text state byte key hpaste h

example (state : Input.State) (byte : UInt8) (hpaste : state.paste = true) :
    ¬Input.Key.enter ∈ (Input.feed state byte).snd ∧
      ¬Input.Key.escape ∈ (Input.feed state byte).snd ∧
      ¬Input.Key.up ∈ (Input.feed state byte).snd ∧
      ¬Input.Key.down ∈ (Input.feed state byte).snd ∧
      ¬Input.Key.home ∈ (Input.feed state byte).snd ∧
      ¬Input.Key.end ∈ (Input.feed state byte).snd ∧
      ¬Input.Key.backspace ∈ (Input.feed state byte).snd ∧
      ¬Input.Key.tab ∈ (Input.feed state byte).snd ∧
      ∀ (control : UInt8), ¬Input.Key.control control ∈ (Input.feed state byte).snd := by
  with_reducible exact Input.feed_paste_no_controls state byte hpaste

-- Saved sessions
example (home content : String) (panes : List Resurrect.Pane)
    (h : Resurrect.parseSave home content = Except.ok panes) :
    panes ≠ [] ∧
      (List.map Resurrect.Pane.name panes).Nodup ∧
      ∀ (pane : Resurrect.Pane),
        pane ∈ panes →
          Name.sanitize pane.name = pane.name ∧
            Name.Valid pane.name ∧ pane.dir.contains '\x00' = false := by
  with_reducible exact Resurrect.parseSave_valid home content panes h

example (existing : List String) (panes : List Resurrect.Pane) :
    Resurrect.plan (existing ++ List.map Resurrect.Pane.name (Resurrect.plan existing panes))
        panes =
      [] := by
  with_reducible exact Resurrect.plan_sequential_idempotent existing panes

example (home : String) (fields : List (String × String)) (content : String)
    (h : Resurrect.renderSave fields = Except.ok content) :
    ∃ panes,
      Resurrect.parseSave home content = Except.ok panes ∧ Resurrect.common panes = fields := by
  with_reducible exact Resurrect.renderSave_roundtrip home fields content h

example (content : String) (panes : List Resurrect.Pane) :
    List.map (fun row => (List.lookup "name" row, List.lookup "directory" row))
        (Resurrect.catalogRows content panes) =
      List.map (fun field => (some field.fst, some field.snd)) (Resurrect.common panes) := by
  with_reducible exact Resurrect.catalogRows_common content panes

example (name dir : String) (line : Nat) (canonical : Name.sanitize name = name)
    (nulFree : dir.contains '\x00' = false) :
    Resurrect.selectedPane name dir line = some { name := name, dir := dir, line := line } := by
  with_reducible exact Resurrect.selectedPane_exact name dir line canonical nulFree
