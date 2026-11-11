module

import all Linger.Session.Proofs.Buf
import all Linger.Session.Proofs.Checkpoint
import all Linger.Session.Proofs.Claim
import all Linger.Session.Proofs.Driver
import all Linger.App.Proofs.Entry
import all Linger.App.Proofs.Commands
import all Linger.Os.Proofs.Env
import all Linger.Os.Proofs.Wait
import all Fuzzy.Proofs
import all Input.Proofs
import all Linger.Display.Proofs.Listing
import all Linger.Display.Proofs.View
import all Linger.Target.Proofs.Name
import all Linger.Selector.Proofs.Picker
import all Linger.Target.Proofs.Remote
import all Terminal.Proofs.Render.Grid
import all Terminal.Proofs.Render.History
import all Terminal.Proofs.Render.Modes
import all Terminal.Proofs.Render.PendingWrap
import all Terminal.Proofs.Render.Scrollback
import all Terminal.Proofs.Render.Sticky
import all Terminal.Proofs.Render.Tabs
import all Terminal.Proofs.Replay
import all Linger.Import.Proofs.Resurrect
import all Linger.Session.Proofs.Session
import all Linger.Display.Proofs.Status
import all Linger.Display.Proofs.Title
import all Terminal.Proofs.Vt
import all Terminal.Proofs.Vt.History
import all Terminal.Proofs.Vt.Renderable
import all Terminal.Proofs.Vt.State
import all Linger.Session.Proofs.Wire
import all Linger.Session.Proofs.Record
import all Linger.Session.Proofs.Start

/-! # Contract statements

`THEOREMS.md` cites the theorems below. Each is restated by an `example` closed with that
theorem at reducible transparency, so weakening a cited hypothesis or conclusion fails here
instead of passing the citation gate. The `rfl` example under Resume ties the
`Session.resumeVt` those pins spell to `Session.bootVt`, which `Daemon.serve` calls, over
`Checkpoint.loadBytes`. -/

open Linger Linger.Session Linger.App Linger.Selector Linger.Import Linger.Os Linger.Target
  Linger.Display Terminal
open Terminal.Replay (Plan)

-- Checkpoints
example (c : Checkpoint.Ckpt Vt.Vt) (h : Vt.LiveReachableVt c.vt) :
    Checkpoint.loadBytes (Checkpoint.saveBytes c) =
      some { vt := c.vt.quiesce, cwd := c.cwd, labels := c.labels } := by
  with_reducible exact Checkpoint.loadBytes_saveBytes_live c h

example {b : ByteArray} {c : Checkpoint.Ckpt Vt.Vt} (h : Checkpoint.loadBytes b = some c) :
    Checkpoint.loadBytes (Checkpoint.saveBytes c) = some c := by
  with_reducible exact Checkpoint.loadBytes_resave h

-- Resume
example (b : ByteArray) :
    Session.resumeVt b = Session.bootVt ((Checkpoint.loadBytes b).map (·.vt)) := rfl

example (b : ByteArray) :
    Vt.LiveReachableVt (Session.bootVt ((Checkpoint.loadBytes b).map (·.vt))) := by
  with_reducible exact Session.liveReachableVt_resumeVt b

example (b : ByteArray) (labels metaKv : List (String × String)) (evs : List Session.Event) :
    Vt.Renderable (Session.run (Session.State.boot (Session.resumeVt b) labels metaKv) evs).1.vt ∧
      Vt.TabsOk (Session.run (Session.State.boot (Session.resumeVt b) labels metaKv) evs).1.vt := by
  with_reducible exact Session.run_resume_vt_shape b labels metaKv evs

example (b : ByteArray) (labels metaKv : List (String × String)) (evs : List Session.Event)
    (cwd : String) :
    Checkpoint.loadBytes
        (Checkpoint.saveBytes
          { vt := (Session.run (Session.State.boot (Session.resumeVt b) labels metaKv) evs).1.vt,
            cwd,
            labels :=
              (Session.run (Session.State.boot (Session.resumeVt b) labels metaKv)
                  evs).1.labels }) =
      some
        {
          vt :=
            (Session.run (Session.State.boot (Session.resumeVt b) labels metaKv) evs).1.vt.quiesce,
          cwd,
          labels :=
            (Session.run (Session.State.boot (Session.resumeVt b) labels metaKv)
                evs).1.labels } := by
  with_reducible exact Session.run_resume_load_save b labels metaKv evs cwd

-- Session events
example (s : Session.State) (evs : List Session.Event) (h : Session.WF s) :
    Session.WF (Session.run s evs).fst := by with_reducible exact Session.run_wf s evs h

example (s : Session.State) (id : Nat) (chunks : List (List UInt8)) {other : Nat} (h : other ≠ id) :
    (Session.run s (List.map (Session.Event.bytes id) chunks)).fst.client? other =
      s.client? other := by
  with_reducible exact Session.run_bytes_isolates s id chunks h

example (s : Session.State) (c : Session.Client) (bs : List UInt8)
    (h : (c.attached && !c.sizer) = true) : Session.onMsg s c (.input bs) = (s, []) := by
  with_reducible exact Session.onMsg_input_readonly s c bs h

example (s : Session.State) (id : Nat) (chunks : List (List UInt8)) {c : Session.Client}
    (hc : s.client? id = some c) (attached : c.attached = true) (watcher : c.sizer = false) :
    (Session.run s (chunks.map (Session.Event.bytes id))).1.terminal = s.terminal ∧
      (Session.run s (chunks.map (Session.Event.bytes id))).1.labelList = s.labelList ∧
      ∀ eff ∈ (Session.run s (chunks.map (Session.Event.bytes id))).2,
        (∃ m, eff = .send id m) ∨ eff = .close id ∨ eff = .checkpoint := by
  with_reducible exact Session.run_readonly s id chunks hc attached watcher

example (s : Session.State) (id : Nat) (chunk : List UInt8) {c : Session.Client}
    {dec : Wire.Decoder} {inputs : List (List UInt8)} (hc : s.client? id = some c)
    (typist : c.attached = false ∨ c.sizer = true)
    (read : c.decoder.feed chunk = (dec, inputs.map Wire.Msg.input))
    (healthy : dec.errored = false) :
    (Session.step s (.bytes id chunk)).2 = inputs.map Session.Effect.writePty := by
  with_reducible exact Session.step_input_exact s id chunk hc typist read healthy

example (s : Session.State) (ev : Session.Event)
    (changed : (Session.step s ev).1.labelList ≠ s.labelList) :
    ∃ id chunk c,
      ev = .bytes id chunk ∧
        s.client? id = some c ∧
        (c.attached = false ∨ c.sizer = true) ∧
        ∃ m ∈ (c.decoder.feed chunk).2, m.ChangesLabels := by
  with_reducible exact Session.step_labels_sources s ev changed

example (s : Session.State) (ev : Session.Event) : (Session.step s ev).1.metaKv = s.metaKv := by
  with_reducible exact Session.step_metaKv s ev

example (s : Session.State) (ev : Session.Event) :
    (∃ chunk, ev = .ptyOut chunk ∧ (Session.step s ev).1.vt = s.vt.feed chunk) ∨
      ∃ sizes : List (Nat × Nat),
        (Session.step s ev).1.vt =
          sizes.foldl (fun v (size : Nat × Nat) => v.resize size.1 size.2) s.vt := by
  with_reducible exact Session.step_vt_sources s ev

-- Listing rows
example (socketName : String) (info : List (String × String)) :
    (Listing.rowFields socketName info).lookup "name" = some socketName := by
  with_reducible exact Listing.rowFields_name socketName info

example (status : Nat) :
    Listing.rowStatus (.ended status) =
      if status = 0 then Status.Status.exitedOk else Status.Status.exitedBad := by
  with_reducible exact Listing.rowStatus_ended status

example (st : Status.Status) :
    Listing.rowStatus (.remote false (Status.name st)) =
      if st = .exitedOk ∨ st = .exitedBad then st else .resumable := by
  with_reducible exact Listing.rowStatus_remote_saved st

example (fresh unseen : Bool) (info : List (String × String))
    (hans : info.any (fun kv => (kv.1 == "pid" || kv.1 == "cmd") && kv.2 != "") = true)
    (hexit : info.lookup "exit" = none) (hfresh : (info.lookup "fresh" == some "true") = fresh)
    (hunseen : (info.lookup "unseen" == some "true") = unseen) :
    Listing.rowStatus (.published fresh unseen) = Listing.rowStatus (.live info) := by
  with_reducible exact Listing.rowStatus_published fresh unseen info hans hexit hfresh hunseen

example (seen : Option Session.Seen) :
    Session.Record.published (Session.Record.encode (.running seen)) = seen := by
  with_reducible exact Session.Record.published_running seen

example (s : Session.State) :
    ("fresh", toString s.seen.fresh) ∈ Session.infoFields s ∧
      ("unseen", toString s.seen.unseen) ∈ Session.infoFields s := by
  with_reducible exact Session.infoFields_seen s

-- Event driver
example {World ε : Type}
    (execute :
      Session.State → World → (eff : Session.Effect Plan) → Except ε (World × Driver.Reply eff))
    (hw : Driver.Responds execute) (r : Driver.Result Session.State World)
    (events : List Session.Event) (hwf : Session.WF r.st) (hlive : Session.LiveVt r.st) :
    ∃ out,
      Driver.run execute r events = Except.ok out ∧ Session.WF out.st ∧ Session.LiveVt out.st := by
  with_reducible exact Driver.run_total_safe execute hw r events hwf hlive

-- Failure feedback
example {World : Type} (execute : Driver.Interpreter World) (st : Session.State) (world : World)
    (depth : Nat) (effs : List (Session.Effect Plan))
    (h : ∀ (eff : Session.Effect Plan), eff ∈ effs → Driver.effectDepth eff ≤ depth) :
    let answered := Driver.effects (m := Id) execute st world depth effs h
    (answered.fst, List.map Subtype.val answered.snd) =
      List.foldl
        (fun (acc : World × List Session.Event) eff =>
          let answer := execute st acc.fst eff
          (answer.fst, acc.snd ++ Driver.feedback eff answer.snd))
        (world, []) effs := by
  with_reducible exact Driver.effects_in_order execute st world depth effs h

example {World : Type} (execute : Driver.Interpreter World) (r : Driver.Result Session.State World)
    (events : List Session.Event) :
    Driver.Execution execute r events (Driver.run (m := Id) execute r events) := by
  with_reducible exact Driver.run_execution execute r events

example (eff : Session.Effect Plan) (reply : Driver.Reply eff) (ev : Session.Event)
    (h : ev ∈ Driver.feedback eff reply) : Driver.eventDepth ev < Driver.effectDepth eff := by
  with_reducible exact Driver.feedback_strictly_decreases eff reply ev h

example {World : Type} (execute : Driver.Interpreter World) (r : Driver.Result Session.State World)
    (ev : Session.Event) (hactive : r.exiting = false) (hdepth : Driver.eventDepth ev < 2) :
    (Driver.handle (m := Id) execute r ev).exiting = false := by
  with_reducible exact Driver.handle_feedback_keeps_alive execute r ev hactive hdepth

example {World : Type} {m : Type → Type} [Monad m]
    (execute : Session.State → World → (eff : Session.Effect Plan) → m (World × Driver.Reply eff))
    (r : Driver.Result Session.State World) (events : List Session.Event) (h : r.exiting = true) :
    Driver.run execute r events = pure r := by
  with_reducible exact Driver.run_exited execute r events h

-- Terminal input
example {v : Vt.Vt} (bytes : List UInt8) (h : Vt.Good v) : Vt.Good (v.feed bytes) := by
  with_reducible exact Vt.Good.feed bytes h

example {v : Vt.Vt} (h : Vt.Renderable v) (bytes : List UInt8) : Vt.Renderable (v.feed bytes) := by
  with_reducible exact Vt.renderable_feed h bytes

example {v : Vt.Vt} (h : Vt.Good v) (hb : v.atBoundary = true) (bytes : List UInt8)
    (he : Vt.mayErase bytes = false) :
    ∃ added : List Vt.Row,
      (v.feed bytes).scrollback = Vt.newest Vt.sbCap (v.scrollback ++ added) := by
  with_reducible exact Vt.history_feed h hb bytes he

example {v : Vt.Vt} (h : Vt.Good v) (hr : Vt.Renderable v) (cols rows : Nat) :
    ∃ added : List Vt.Row,
      (v.resize cols rows).scrollback = Vt.newest Vt.sbCap (v.scrollback ++ added) ∧
        (v.inAlt = false →
          added = (List.range (v.rowCount - (v.resize cols rows).rowCount)).map v.getRow) := by
  with_reducible exact Vt.history_resize h hr cols rows

example {v : Vt.Vt} (hb : v.atBoundary = true) :
    (v.feed [0x1B, 0x5B, 0x33, 0x4A]).scrollback = [] := by with_reducible exact Vt.history_erase hb

example {v : Vt.Vt} (hb : v.atBoundary = true) :
    (v.feed [0x1B, 0x63]).scrollback = v.scrollback := by with_reducible exact Vt.history_reset hb

-- Terminal controls
example {v : Vt.Vt} (hu : v.u8need = 0) (hosc : ∀ acc e, v.pstate ≠ .osc acc e)
    (hstr : v.pstate ≠ .str true) : v.step 0x7F = v := by
  with_reducible exact Vt.step_del_inert hu hosc hstr

example {v : Vt.Vt} {b : UInt8} (hc0 : b < 0x20) (hact : b < 0x07 ∨ 0x0F < b) (hesc : b ≠ 0x1B)
    (hu : v.u8need = 0) (hosc : ∀ acc e, v.pstate ≠ .osc acc e) (hstr : v.pstate ≠ .str true) :
    v.step b = v := by with_reducible exact Vt.step_c0_inert hc0 hact hesc hu hosc hstr

-- Repeat counts
example (v : Vt.Vt) {s t : Vt.CsiState} (hs : s.ignore = false) (ht : t.ignore = false)
    (hsn : v.bot - v.top + 1 ≤ s.arg 0 1) (htn : v.bot - v.top + 1 ≤ t.arg 0 1) :
    v.csiDispatch s 0x53 = v.csiDispatch t 0x53 ∧ v.csiDispatch s 0x54 = v.csiDispatch t 0x54 := by
  with_reducible exact Vt.csiDispatch_scroll_saturates v hs ht hsn htn

example (v : Vt.Vt) {s t : Vt.CsiState} (hs : s.ignore = false) (ht : t.ignore = false)
    (hsn : v.cols ≤ s.arg 0 1) (htn : v.cols ≤ t.arg 0 1) :
    v.csiDispatch s 0x49 = v.csiDispatch t 0x49 ∧ v.csiDispatch s 0x5A = v.csiDispatch t 0x5A := by
  with_reducible exact Vt.csiDispatch_tab_saturates v hs ht hsn htn

example (v : Vt.Vt) (s : Vt.CsiState) :
    ∃ rows : List Vt.Row,
      rows.length ≤ v.bot - v.top + 1 ∧
        (v.csiDispatch s 0x53).sb = rows.foldl Vt.Ring.push v.sb := by
  with_reducible exact Vt.csiDispatch_su_history v s

example (v : Vt.Vt) (cap count : Nat) (f : Vt.Vt → Vt.Vt) :
    v.repeatAtMost cap count f = Nat.repeat f (min count cap) v := by
  with_reducible exact Vt.repeatAtMost_eq_repeat v cap count f

-- Waking
example (s : Session.State) :
    s.nextTick = none ↔ s.dirty = false ∧ (s.freshFlag = false ∨ s.lastOutMs = none) := by
  with_reducible exact Session.nextTick_eq_none s

example (s : Session.State) (h : s.dirty = true) :
    ∃ due, s.nextTick = some due ∧ due ≤ s.lastCkptMs + Session.ckptIntervalMs := by
  with_reducible exact Session.nextTick_save s h

example (s : Session.State) {t : Nat} (h : s.freshFlag = true) (ho : s.lastOutMs = some t) :
    ∃ due, s.nextTick = some due ∧ due ≤ t + Session.freshMs := by
  with_reducible exact Session.nextTick_stale s h ho

example (s : Session.State) (now : Nat) (hout : s.tickOutSeq < s.outSeq) :
    (Session.step s (.tick now)).1.freshFlag = true ∧
      ∃ due, (Session.step s (.tick now)).1.nextTick = some due ∧ due ≤ now + Session.freshMs := by
  with_reducible exact Session.step_tick_fresh s now hout

example (s : Session.State) (now : Nat) (hd : s.dirty = false) (hout : s.tickOutSeq = s.outSeq)
    (hstale : ∀ t, s.lastOutMs = some t → t + Session.freshMs ≤ now) :
    (Session.step s (.tick now)).1.nextTick = none := by
  with_reducible exact Session.step_tick_sleeps s now hd hout hstale

example (s : Session.State) (now t₁ t₂ : Nat)
    (h₁ : (Session.trace Session.step s [.tick now]).1.nextTick = some t₁)
    (h₂ : (Session.trace Session.step s [.tick now, .tick t₁]).1.nextTick = some t₂) :
    (Session.trace Session.step s [.tick now, .tick t₁, .tick t₂]).1.nextTick = none := by
  with_reducible exact Session.ticks_settle s now t₁ t₂ h₁ h₂

example (now : Nat) (deadlines : List Nat) :
    Session.pollTimeout now deadlines =
      (deadlines.min?.map fun due => Int32.ofNat (min (due - now) 2147483647)).getD (-1) := by
  with_reducible exact Session.pollTimeout_eq now deadlines

example (s : Session.State) (chunk : List UInt8) :
    ∀ eff ∈ (Session.step s (.ptyOut chunk)).2,
      (∃ bytes, eff = .writePty bytes) ∨
        ∃ c ∈ s.roster,
          c.attached = true ∧
            ∃ payload, eff = .send c.id (.output payload) ∧ payload.length ≤ 65536 := by
  with_reducible exact Session.step_ptyOut_audience s chunk

example {R W : Type} (start : W → R) (ws : List W) :
    (ws.foldl (Session.Offloop.run Session.Offloop.ask start) {}).running = ws.head?.map start ∧
      (ws.foldl (Session.Offloop.run Session.Offloop.ask start) {}).waiting =
        if ws.length ≤ 1 then none else ws.getLast? := by
  with_reducible exact Session.offloop_coalesces start ws

example (deadline step now : Nat) : Os.Wait.next deadline step now = none ↔ deadline ≤ now := by
  with_reducible exact Os.Wait.next_eq_none_iff deadline step now

example {deadline step now ms : Nat} (h : Os.Wait.next deadline step now = some ms) :
    0 < ms ∧ ms ≤ max step 1 ∧ now + ms ≤ deadline := by with_reducible exact Os.Wait.next_some h

example {after : Nat → Nat → Nat} (lasts : Os.Wait.Lasts after) (deadline step : Nat) :
    ∀ now,
      ∃ looks,
        looks ≤ deadline - now + 1 ∧ Os.Wait.Ends (Os.Wait.next deadline step) after now looks := by
  with_reducible exact Os.Wait.ends_within lasts deadline step

-- Focus reports
example (s : Session.State) (c : Session.Client) (cols rows : UInt32) (hc : s.client? c.id = some c)
    (h : c.attached = false) (hsize : (cols != 0 && rows != 0) = true)
    (hunfocused : s.focused = false) (hmode : s.vt.getModes.focusEvents = true) :
    Session.Effect.writePty (Session.focusReport true) ∈
      (Session.onMsg s c (.attach cols rows)).2 := by
  with_reducible exact Session.onMsg_attach_focus s c cols rows hc h hsize hunfocused hmode

example (s : Session.State) (id : Nat) {c : Session.Client} (hc : s.client? id = some c)
    (hs : c.sizer = true) (hfocused : s.focused = true) (hlast : (s.dropClient id).focused = false)
    (hmode : s.vt.getModes.focusEvents = true) :
    Session.Effect.writePty (Session.focusReport false) ∈ (Session.closeClient s id).2 := by
  with_reducible exact Session.closeClient_focus s id hc hs hfocused hlast hmode

example (s : Session.State) (id : Nat) {c : Session.Client} (hc : s.client? id = some c)
    (hs : c.sizer = false) : ∀ e ∈ (Session.closeClient s id).2, e = .checkpoint := by
  with_reducible exact Session.closeClient_watcher s id hc hs

example (typist before : Bool) (s : Session.State) (h : s.vt.getModes.focusEvents = false) :
    Session.focusEffects typist before s = [] := by
  with_reducible exact Session.focusEffects_off typist before s h

-- Request replies
example (s : Session.State) (id : Nat) (chunk : List UInt8) :
    ∃ pre ans post,
      (Session.step s (.bytes id chunk)).2 = pre ++ ans ++ post ∧
        (ans = [] ∨
          ∃ c t c' m,
            s.client? id = some c ∧
              m ∈ (c.decoder.feed chunk).2 ∧
              t.client? id = some c' ∧ ans = (Session.onMsg t c' m).2) ∧
        (pre ++ post).all (!·.rendered) ∧
        (((Session.step s (.bytes id chunk)).1.client? id).all (!·.attached) →
          (pre ++ post).all (!·.resizes)) := by
  with_reducible exact Session.step_bytes_one_reply s id chunk

example (s : Session.State) (c : Session.Client) (t : UInt8) (p : List UInt8) :
    Session.onMsg s c (.unknown t p) =
      (s, [.send c.id (.err "unknown message".toUTF8.toList)]) := by
  with_reducible exact Session.onMsg_unknown s c t p

example (s : Session.State) :
    ("protocol", toString Wire.protocol) ∈ Session.infoFields s ∧
      ("version", Terminal.Mediation.versionNumber) ∈ Session.infoFields s := by
  with_reducible exact Session.infoFields_protocol s

-- Program end
example (s : Session.State) (o : Session.Outcome) {c : Session.Client} (hc : c ∈ s.roster)
    (listening : c.attached = true ∨ c.waiting = true) :
    [Session.Effect.send c.id (.ended o), Session.Effect.send c.id (.exited o.status)] <:+:
        (Session.step s (.childExited o)).2 ∧
      (Session.step s (.childExited o)).2.getLast? = some .exit := by
  with_reducible exact Session.step_ended_reports s o hc listening

example (s : Session.State) (o : Session.Outcome) :
    (∃ front,
        (Session.step s (.childExited o)).2 = front ++ [.checkpoint, .exit] ∧
          Session.Effect.dropCheckpoint ∉ front) ∧
      (Session.step s (.childExited o)).1.terminal = s.terminal := by
  with_reducible exact Session.step_childExited_keeps s o

example {o₁ o₂ : Session.Outcome} (h : Session.outcomeFields o₁ = Session.outcomeFields o₂) :
    o₁ = o₂ := by with_reducible exact Session.outcomeFields_injective h

example : Session.ending = [(1, 1000), (9, 1000)] := by with_reducible exact Session.ending_eq

example (r : Session.Record) : Session.Record.decode (Session.Record.encode r) = some r := by
  with_reducible exact Session.Record.decode_encode r

example (file : Option (List UInt8)) : (Session.Record.answer file).isSome = file.isSome := by
  with_reducible exact Session.Record.answer_isSome file

example {file : Option (List UInt8)} {known : Option Session.Outcome}
    (h : Session.Record.settled file = some known) : Session.Record.answer file = known := by
  with_reducible exact Session.Record.settled_answer h

example (outcome : Session.Outcome) :
    Session.Record.answer (some (Session.Record.encode (.ended outcome))) = some outcome := by
  with_reducible exact Session.Record.answer_ended outcome

example (seen : Option Session.Seen) :
    Session.Record.answer (some (Session.Record.encode (.running seen))) = some .unknown := by
  with_reducible exact Session.Record.answer_running seen

-- Command table
example : App.Commands.words.Nodup := by with_reducible exact App.Commands.words_nodup

example : ∀ command ∈ App.Commands.table, App.Commands.lookup command.word = some command := by
  with_reducible exact App.Commands.lookup_word

example :
    ∀ command ∈ App.Commands.table,
      ∀ word ∈ command.aliases, App.Commands.lookup word = some command := by
  with_reducible exact App.Commands.lookup_alias

example (command : App.Commands.Command) (h : command.args.isEmpty = false) :
    App.Commands.usageLine command = s!"usage: linger {command.word} {command.args}" := by
  with_reducible exact App.Commands.usageLine_args command h

example : ∀ entry ∈ App.Commands.retired, App.Commands.lookup entry.1 = none := by
  with_reducible exact App.Commands.retired_free

-- Starting a session
example (live saved : Bool) :
    Session.Start.plan live saved = .take ↔ live = false ∧ saved = false := by
  with_reducible exact Session.Start.plan_take_iff live saved

example (r : Session.Start.Report) : Session.Start.Report.decode r.encode = some r := by
  with_reducible exact Session.Start.decode_encode r

example (live saved : Bool) :
    Session.Start.resumePlan live saved = .resume ↔ live = false ∧ saved = true := by
  with_reducible exact Session.Start.resumePlan_resume_iff live saved

example (live saved : Bool) :
    Session.Start.resumePlan live saved = .missing ↔ live = false ∧ saved = false := by
  with_reducible exact Session.Start.resumePlan_missing_iff live saved

example (r : Session.Start.Request)
    (h : Session.Start.Reachable Session.Start.proceeds Session.Start.answer r) :
    (r.answer = some .started → r.runs = true) ∧
      (r.answer = some .notStarted → r.runs = false) := by
  with_reducible exact Session.Start.answer_true h

example (shell : String) (argv : List String) :
    Session.Start.programOf shell argv = (argv.headD shell, (argv.drop 1).toArray) := by
  with_reducible exact Session.Start.programOf_exact shell argv

example (name key : String) (inherited : String → Option String) :
    ((Session.Start.environment name).reverse.lookup key).orElse (fun _ => inherited key) =
      if key = "LINGER_SESSION" then some name
      else
        if key = "TERM" then some "xterm-256color"
        else
          if key = "TERM_PROGRAM" then some "linger"
          else
            if key = "TERM_PROGRAM_VERSION" then some Terminal.Mediation.versionNumber
            else inherited key := by
  with_reducible exact Session.Start.environment_lookup name key inherited

example (why : String) :
    Session.Start.failureStatus (.directory why) = 125 ∧
      Session.Start.failureStatus (.notFound why) = 127 ∧
      Session.Start.failureStatus (.notRunnable why) = 126 := by
  with_reducible exact Session.Start.failureStatus_exact why

example (name pid created cmd dir : String) (saved : Option String) :
    ("start_dir", dir) ∈ Session.Start.metadata name pid created cmd dir saved ∧
      ∀ d,
        ("saved_dir", d) ∈ Session.Start.metadata name pid created cmd dir saved ↔
          saved = some d ∧ d ≠ dir := by
  with_reducible exact Session.Start.metadata_dirs name pid created cmd dir saved

-- Transport
example (ms : List Wire.Msg) (hms : ∀ (m : Wire.Msg), m ∈ ms → m.WF) (chunks : List (List UInt8))
    (hc : chunks.flatten = List.flatMap Wire.encode ms) :
    Wire.Decoder.feedAll {} chunks = ({ buf := [], errored := false }, ms) := by
  with_reducible exact Wire.decode_encode_chunked ms hms chunks hc

-- Ownership
example {grant : Claim.State → Nat → Nat → Bool} (exclusive : Claim.Exclusive grant)
    {s : Claim.State} (reached : Claim.Reachable grant Claim.enters s) : Claim.Protected s := by
  with_reducible exact Claim.reachable_protected exclusive reached

example {grant : Claim.State → Nat → Nat → Bool} (exclusive : Claim.Exclusive grant)
    {s : Claim.State} (reached : Claim.Reachable grant Claim.enters s) {a b resource : Nat}
    {left right : Claim.Lease} (ha : s.active a = some left) (hb : s.active b = some right)
    (leftUses : left.Uses resource) (rightUses : right.Uses resource) : a = b := by
  with_reducible exact Claim.at_most_one_owner exclusive reached ha hb leftUses rightUses

example {grant : Claim.State → Nat → Nat → Bool}
    (grants : ∀ s actor resource, s.locks resource = none → grant s actor resource = true)
    {s : Claim.State} (reached : Claim.Reachable grant Claim.enters s) (actor : Nat)
    (lease : Claim.Lease) (idle : s.active actor = none) (socket : s.locks lease.socket = none)
    (checkpoint : s.locks lease.checkpoint = none) (distinct : lease.checkpoint ≠ lease.socket) :
    ∃ after, Claim.Reachable grant Claim.enters after ∧ after.active actor = some lease := by
  with_reducible exact Claim.claim_free grants reached actor lease idle socket checkpoint distinct

-- Buffers
example {cap : Nat} {b : Buf.Buf} (h : Buf.ReachableIn cap b) : Buf.owedLen b ≤ cap := by
  with_reducible exact Buf.reachableIn_bound h

example {cap : Nat} {b : Buf.Buf} (h : Buf.ReachableOut cap b) : Buf.owedLen b ≤ cap := by
  with_reducible exact Buf.reachableOut_bound h

example {cap : Nat} {accepted written : ByteArray} {b : Buf.Buf}
    (life :
      Buf.InputLife Buf.Buf.empty Buf.bufOffer Buf.bufAdvance Buf.writeFrom cap accepted written
        b) :
    written ++ Buf.writeFrom b = accepted := by with_reducible exact Buf.inputLife_exact life

example (cap : Nat) (b : Buf.Buf) (more : ByteArray) :
    (Buf.bufOffer cap b more).2 = true ↔ cap < Buf.owedLen b + more.size := by
  with_reducible exact Buf.bufOffer_refuses_iff cap b more

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

-- Text output
example (v : Vt.Vt) :
    ∃ cs : List Char,
      Render.screenText v = cs.flatMap Render.utf8 ∧
        ∀ c ∈ cs,
          c = '\n' ∨ (0x20 ≤ c.toNat ∧ c.toNat ≠ 0x7F ∧ ¬(0x80 ≤ c.toNat ∧ c.toNat < 0xA0)) := by
  with_reducible exact Render.screenText_text v

example (v : Vt.Vt) :
    ∃ cs : List Char,
      Render.history v = cs.flatMap Render.utf8 ∧
        ∀ c ∈ cs,
          c = '\n' ∨ (0x20 ≤ c.toNat ∧ c.toNat ≠ 0x7F ∧ ¬(0x80 ≤ c.toNat ∧ c.toNat < 0xA0)) := by
  with_reducible exact Render.history_text v

example (s : Session.State) :
    ∃ cs : List Char,
      Session.infoText s = cs.flatMap Render.utf8 ∧
        ∀ c ∈ cs,
          c = '\t' ∨
            c = '\n' ∨ (0x20 ≤ c.toNat ∧ c.toNat ≠ 0x7F ∧ ¬(0x80 ≤ c.toNat ∧ c.toNat < 0xA0)) := by
  with_reducible exact Session.infoText_text s

example (nameCol : Nat) (info : List (String × String)) :
    ∃ cs : List Char,
      Listing.humanRow nameCol info = cs.flatMap Render.utf8 ∧
        ∀ c ∈ cs, 0x20 ≤ c.toNat ∧ c.toNat ≠ 0x7F ∧ ¬(0x80 ≤ c.toNat ∧ c.toNat < 0xA0) := by
  with_reducible exact Listing.humanRow_text nameCol info

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

example (statuses : List Status.Status) (s : Status.Status) :
    (∃ n, (s, n) ∈ Status.attentionCounts statuses) ↔
      s ∈ Status.attention ∧ statuses.count s ≠ 0 := by
  with_reducible exact Status.attention_counted statuses s

example (s : Status.Status) : s ∈ Status.legendOrder := by
  with_reducible exact Status.legendOrder_complete s

example : Status.legendOrder.Nodup := by with_reducible exact Status.legendOrder_nodup

example (s t : Status.Status) (h : Status.seen s = Status.seen t) : s = t := by
  with_reducible exact Status.seen_injective s t h

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
example (verb : String) (words : List String) :
    Remote.Shell.Words (Remote.command verb words).toList
      (List.map String.toList ("linger" :: verb :: words)) := by
  with_reducible exact Remote.command_argv verb words

example (s : String) (tail : List Char) (boundary : tail = [] ∨ ∃ rest, tail = ' ' :: rest) :
    Remote.Shell.word ((Remote.shellQuote s).toList ++ tail) = some (s.toList, tail) := by
  with_reducible exact Remote.shellQuote_roundtrip s tail boundary

-- Remote hosts
example (hosts result : List String) :
    Remote.checkHosts hosts = Except.ok result ↔
      result = hosts ∧ hosts.Nodup ∧ ∀ (x : String), x ∈ hosts → Remote.hostClean x = true := by
  with_reducible exact Remote.checkHosts_ok_iff hosts result

-- Command operands
example (name : String) (rest : List String) :
    Remote.targetArgs (Remote.targetOperands name ++ rest) = some (name, rest) := by
  with_reducible exact Remote.targetArgs_targetOperands name rest

example (name : String) (rest : List String) (option : name.startsWith "-" = true) :
    Remote.targetArgs (name :: rest) ≠ some (name, rest) := by
  with_reducible exact Remote.targetArgs_option_ne name rest option

example (name : String) (rest : List String) (option : name.startsWith "-" = true)
    (separator : name ≠ "--") : Remote.targetArgs (name :: rest) = none := by
  with_reducible exact Remote.targetArgs_option name rest option separator

-- Environment
example : Env.shellOf none = "sh" ∧ Env.shellOf (some "") = "sh" := by
  with_reducible exact Env.shellOf_absent

example {shell : String} (set : shell ≠ "") : Env.shellOf (some shell) = shell := by
  with_reducible exact Env.shellOf_set set

example (home : Option String) : Env.remotesFile home = none ↔ home = none ∨ home = some "" := by
  with_reducible exact Env.remotesFile_eq_none_iff home

example (flag : Option String) : Env.detachEnabled true flag = true := by
  with_reducible exact Env.detachEnabled_readOnly flag

example (saved : String) :
    Env.resumeDir none saved false = none ∧ Env.resumeDir (some "") saved false = none := by
  with_reducible exact Env.resumeDir_absent saved

example (home : Option String) (saved : String) : Env.resumeDir home saved true = some saved := by
  with_reducible exact Env.resumeDir_saved home saved

example {dir : String} (set : dir ≠ "") (saved : String) :
    Env.resumeDir (some dir) saved false = some dir := by
  with_reducible exact Env.resumeDir_home set saved

example (flag : Option String) : Env.detachEnabled false flag = flag.isNone := by
  with_reducible exact Env.detachEnabled_writable flag

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

-- Views
example {α : Type} (status : α → Display.Status.Status) (rows : List α) :
    (Display.View.sort status rows).Perm rows := by
  with_reducible exact Display.View.sort_perm status rows

example {α : Type} (status : α → Display.Status.Status) (rows : List α) :
    ∃ first rest,
      Display.View.sort status rows = first ++ rest ∧
        (∀ x ∈ first, status x ∈ Display.Status.attention) ∧
        ∀ x ∈ rest, status x ∉ Display.Status.attention := by
  with_reducible exact Display.View.sort_attention_first status rows

example {α : Type} (status : α → Display.Status.Status) (rows : List α)
    (st : Display.Status.Status) :
    (Display.View.sort status rows).filter (status · == st) = rows.filter (status · == st) := by
  with_reducible exact Display.View.sort_stable status rows st

example (labels : List String) (statuses : List Display.Status.Status)
    (h : (Display.Status.summary statuses).isEmpty = false) :
    Display.Status.summary statuses ∈ Display.View.headerParts labels statuses := by
  with_reducible exact Display.View.headerParts_summary labels statuses h

example (keys : List String) (k : String) (n : Nat) (h : (k, n) ∈ Display.View.groups keys) :
    n = keys.count k := by with_reducible exact Display.View.groups_count keys k n h

example (keys : List String) : ((Display.View.groups keys).map (·.2)).sum = keys.length := by
  with_reducible exact Display.View.groups_sum keys

example (depth : Nat) (target : String) :
    (Display.View.stem depth target).toList <+: target.toList := by
  with_reducible exact Display.View.stem_prefix depth target

example (targets : List String) (depth : Nat) (h : Display.View.chooseDepth targets = some depth) :
    Display.View.useful depth targets = true ∧
      ∀ other ∈ Display.View.depths,
        Display.View.useful other targets = true →
          Display.View.largest depth targets ≤ Display.View.largest other targets := by
  with_reducible exact Display.View.chooseDepth_best targets depth h

example (targets : List String) :
    (Display.View.hidden targets).2 = [] ∨
      (((Display.View.hidden targets).2).map (·.2)).sum = (Display.View.hidden targets).1 := by
  with_reducible exact Display.View.hidden_adds_up targets

example (s : Picker.State) (c : Char) :
    Picker.matchCount { s with query := s.query.push c } ≤ Picker.matchCount s := by
  with_reducible exact Picker.matchCount_push s c

example (candidates : List String) (target : String) (depth : Nat) (allowCreate : Bool)
    (h : target ∈ candidates) :
    Picker.Item.existing target ∈
      Picker.items candidates (Display.View.stem depth target) allowCreate := by
  with_reducible exact Picker.stem_items candidates target depth allowCreate h

example (state : Picker.State) (snapshot : Picker.Snapshot)
    (statusOf : String → Display.Status.Status) (loaded withColor savedTmux : Bool) (rows : Nat) :
    (Picker.frameLines state snapshot statusOf loaded withColor savedTmux rows).length ≤
      max 1 rows := by
  with_reducible exact Picker.frameLines_length _ _ _ _ _ _ _

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

example (existing : List String) (panes : List Resurrect.Pane) (pane : Resurrect.Pane) :
    pane ∈ Resurrect.plan existing panes ↔ pane ∈ panes ∧ pane.name ∉ existing := by
  with_reducible exact Resurrect.mem_plan existing panes pane

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

example (content : String) (panes : List Resurrect.Pane) (row : List (String × String))
    (h : row ∈ Resurrect.catalogRows content panes) (cmd saved text : String)
    (hc : row.lookup "command" = some cmd) (hs : row.lookup "saved-command" = some saved)
    (ht : row.lookup "cmd" = some text) :
    List.IsSuffix (Resurrect.diagnostic (if saved.isEmpty then cmd else saved)).toList
      text.toList := by
  with_reducible exact Resurrect.catalogRows_command _ _ _ h _ _ _ hc hs ht

example (name dir : String) (line : Nat) (canonical : Name.sanitize name = name)
    (nulFree : dir.contains '\x00' = false) :
    Resurrect.selectedPane name dir line = some { name := name, dir := dir, line := line } := by
  with_reducible exact Resurrect.selectedPane_exact name dir line canonical nulFree

-- Saved pane contents
example : Resurrect.captureLimit = 8 * 1024 * 1024 := by
  with_reducible exact Resurrect.captureLimit_eq

example (contents : String) :
    (Resurrect.captureBytes contents).length ≤ 2 * Resurrect.captureLimit := by
  with_reducible exact Resurrect.captureBytes_bounded contents

example (details : Resurrect.Details) :
    Resurrect.commandNotice details =
      let command := if details.savedCommand.isEmpty then details.command else details.savedCommand
      if command.isEmpty then ""
      else
        "\x1b[0m\x1b(B\x0f\x1b[?7h\r\nSaved foreground command: " ++ Resurrect.diagnostic command ++
          "\r\n" := by
  with_reducible exact Resurrect.commandNotice_eq details

example (details : Resurrect.Details) :
    (Resurrect.commandNotice details).toUTF8.toList.length ≤
      43 + 4 * (details.command.length + details.savedCommand.length) := by
  with_reducible exact Resurrect.commandNotice_bounded details

example (pane : Resurrect.Pane) (contents : Option String) :
    (Resurrect.checkpoint pane contents).vt =
      (((Vt.Vt.init pane.details.cols pane.details.rows).feed
              (Resurrect.captureBytes (contents.getD ""))).quiesce.feed
          (Resurrect.commandNotice pane.details).toUTF8.toList).quiesce := by
  with_reducible exact Resurrect.checkpoint_notice pane contents

example (pane : Resurrect.Pane) (contents : Option String) :
    Vt.LiveReachableVt (Resurrect.checkpoint pane contents).vt := by
  with_reducible exact Resurrect.checkpoint_live pane contents

example (pane : Resurrect.Pane) (contents : Option String) :
    Checkpoint.loadBytes (Checkpoint.saveBytes (Resurrect.checkpoint pane contents)) =
      some (Resurrect.checkpoint pane contents) := by
  with_reducible exact Resurrect.checkpoint_roundtrip pane contents

example (pane : Resurrect.Pane) (contents : Option String) :
    (Resurrect.checkpoint pane contents).cwd = pane.dir ∧
      (Resurrect.checkpoint pane contents).labels.lookup "tmux.command" =
        some pane.details.command ∧
      (Resurrect.checkpoint pane contents).labels.lookup "tmux.saved-command" =
        some pane.details.savedCommand ∧
      (Resurrect.checkpoint pane contents).labels.lookup "tmux.capture" =
        some (if contents.isSome then "saved" else "none") := by
  with_reducible exact Resurrect.checkpoint_metadata pane contents
